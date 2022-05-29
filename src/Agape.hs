{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}

module Agape where

import           Ledger
import           Ledger.Ada           as Ada
import qualified Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Plutus.Contract
import qualified PlutusTx
import           PlutusTx.Prelude

import           Control.Monad        (void, when)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.Text            (Text)
import           Data.List            (foldl')
import           GHC.Generics         (Generic)
import qualified Data.Map             as Map (singleton, fromList, toList)
import qualified Prelude
import           Prelude              (IO, String)
import           Text.Printf          (printf)

import           Playground.Contract  (KnownCurrency (..), ToSchema, ensureKnownCurrencies, mkSchemaDefinitions, printJson, printSchemas, stage)
import qualified Plutus.Contract as Constraints
import Plutus.Trace (runEmulatorTraceIO, activateContractWallet)


-- imports for EmulatorTrace testing
import Plutus.V1.Ledger.Ada (lovelaceValueOf)
import Wallet.Emulator.Wallet
import Plutus.Trace (EmulatorTrace, activateContractWallet, callEndpoint, runEmulatorTraceIO)
import qualified Plutus.Trace as Trace
import Data.Text (Text)
import qualified Control.Monad.Freer.Extras as Extras



-- ############# --
-- On-chain code --
-- ############# --

-- Parameters
-- > Campaign (description, deadline_campaign, deadline_objection, beneficiary, arbiter)
--
-- Datum
-- > contributor PPKH
-- > contributor objects
-- > Evidence
--
-- Redeemer
-- > Object
-- > Payout
-- > Refund

data Campaign = Campaign
    { cDescription    :: !BuiltinByteString
    , cDeadline       :: !POSIXTime
    , cDeadlineObject :: !POSIXTime
    , cBeneficiary    :: !PaymentPubKeyHash
    , cArbiter        :: !PaymentPubKeyHash
    }
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Campaign

data AgapeDatum = AgapeDatum
    { adContributor :: !PaymentPubKeyHash
    , adObjects     :: !Bool
    , adEvidence    :: !(Maybe BuiltinByteString)
    }

PlutusTx.unstableMakeIsData ''AgapeDatum

data AgapeAction = Payout | Refund | Object

PlutusTx.unstableMakeIsData ''AgapeAction


{-# INLINABLE mkValidatorAgape #-}
mkValidatorAgape :: Campaign -> AgapeDatum -> AgapeAction -> ScriptContext -> Bool
mkValidatorAgape c ad ac ctx = True

  where
    info :: TxInfo
    info = scriptContextTxInfo ctx


data AgapeType
instance Scripts.ValidatorTypes AgapeType where
    type RedeemerType AgapeType = AgapeAction
    type DatumType    AgapeType = AgapeDatum


agapeTypedValidator :: Campaign -> Scripts.TypedValidator AgapeType
agapeTypedValidator c = Scripts.mkTypedValidator @AgapeType
    ($$(PlutusTx.compile [|| mkValidatorAgape ||])
    `PlutusTx.applyCode` PlutusTx.liftCode c)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @AgapeDatum @AgapeAction


agapeValidator :: Campaign -> Validator
agapeValidator = Scripts.validatorScript . agapeTypedValidator

agapeValHash :: Campaign -> Ledger.ValidatorHash
agapeValHash = Scripts.validatorHash . agapeTypedValidator

agapeAddress :: Campaign -> Ledger.Address
agapeAddress = scriptAddress . agapeValidator



-- ############## --
-- Off-chain code --
-- ############## --

-- 5 endpoints
-- > contribute
-- > object
-- > payout
-- > refund
-- > evidence

data ProducerParams = ProducerParams
    { ppCampaignDescription :: !BuiltinByteString
    , ppCampaignDeadline    :: !POSIXTime
    , ppCampaignDeadlineObj :: !POSIXTime
    , ppCampaignBeneficiary :: !PaymentPubKeyHash
    , ppCampaignArbiter     :: !PaymentPubKeyHash
    , ppContributeAmt       :: !Integer
    , ppEvidence            :: !(Maybe BuiltinByteString)
    }
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)  

-- contribute to the campaign
contribute :: AsContractError e => ProducerParams -> Contract w s e ()
contribute ProducerParams{..} = do
    ownppkh <- ownPaymentPubKeyHash
    let campaign = Campaign
                   { cDescription    = ppCampaignDescription
                   , cDeadline       = ppCampaignDeadline
                   , cDeadlineObject = ppCampaignDeadlineObj
                   , cBeneficiary    = ppCampaignBeneficiary
                   , cArbiter        = ppCampaignArbiter
                   }

        dat = AgapeDatum
              { adContributor = ownppkh
              , adObjects     = False
              , adEvidence    = Nothing 
              }

        val = lovelaceValueOf ppContributeAmt

        tx = Constraints.mustPayToTheScript dat val
        
    ledgerTx <- submitTxConstraints (agapeTypedValidator campaign) tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "contributed to campaign"


-- object
-- find the UTXO which corresponds to the PPKH of the wallet, then spend it, and create new datum with objection = True
newtype ObjectionParams = ObjectionParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

objects :: AsContractError e => ObjectionParams -> Contract w s e ()
objects (ObjectionParams campaign@Campaign{..}) = do
    ownppkh <- ownPaymentPubKeyHash
    utxos <- findUTXOs campaign (Just ownppkh)

    let r = Redeemer $ PlutusTx.toBuiltinData Object

        obj_datum = AgapeDatum
                    { adContributor = ownppkh
                    , adObjects     = True
                    , adEvidence    = Nothing
                    }
        
        totalval = mconcat [_ciTxOutValue chainidx | (_, chainidx, _) <- utxos]

        lookups = Constraints.typedValidatorLookups (agapeTypedValidator campaign)              Prelude.<>
                  Constraints.otherScript (agapeValidator campaign)                             Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos])

        tx = Constraints.mustValidateIn (interval (cDeadline + 1) cDeadlineObject)          <>
             Constraints.mustPayToTheScript obj_datum totalval                              <>
             mconcat [Constraints.mustSpendScriptOutput outref r | (outref, _, _) <- utxos]

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "objection"

-- payout
-- > in order for payout, one of the valid UTXOs must be submitted by the beneficiary with evidence
-- > must be past the objection deadline
-- > must not have a successful objection (***TODO***)
-- > if objection is successful, then only proceed if signed by arbiter (**TODO**)
-- > Also need to mint NFT for every contributer

newtype PayoutParams = PayoutParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

payout :: PayoutParams -> Contract w s Text ()
payout (PayoutParams campaign@Campaign{..}) = do
    utxos <- findUTXOs campaign Nothing -- find all suitable utxos

    -- if cannot find evidence, then fail
    when (not $ evidenceFound utxos cBeneficiary) $ throwError "Evidence not found"

    let r = Redeemer $ PlutusTx.toBuiltinData Payout

        totalval = mconcat [_ciTxOutValue chainidx | (_, chainidx, _) <- utxos]

        lookups = Constraints.typedValidatorLookups (agapeTypedValidator campaign)              Prelude.<>
                  Constraints.otherScript (agapeValidator campaign)                             Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos])

        tx = Constraints.mustValidateIn (from cDeadlineObject) <>
             Constraints.mustPayToPubKey cBeneficiary totalval <>
             mconcat [Constraints.mustSpendScriptOutput oref r | (oref, _, _) <- utxos]

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "paid out"


-- searches the list of utxos to find if there is at least one which is submitted by the beneficiary with evidence attached
evidenceFound :: [(TxOutRef, ChainIndexTxOut, AgapeDatum)] -> PaymentPubKeyHash -> Bool
evidenceFound utxos benfPPKH = any (\(_, _, AgapeDatum{..}) -> adContributor == benfPPKH && isJust adEvidence) utxos


newtype RefundParams = RefundParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

-- refund to the contributors
-- **TODO**
-- > take into account objections, if objections are valid, then only proceed if signed by arbiter if not error.
refund :: AsContractError e => RefundParams -> Contract w s e ()
refund (RefundParams campaign@Campaign{..}) = do
    -- get the utxos, filter for the right Datum to get the Contributor, get the Value.
    -- then for each contributor ppkh, create a Constraint and put the value in as payment 
    utxos <- findUTXOs campaign Nothing

    let r = Redeemer $ PlutusTx.toBuiltinData Refund
   
        lookups = Constraints.typedValidatorLookups (agapeTypedValidator campaign)              Prelude.<>
                  Constraints.otherScript (agapeValidator campaign)                             Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos])

        tx = Constraints.mustValidateIn (from cDeadlineObject) <>
             foldl' buildConstraints mempty utxos -- build the Constraints to pay contributor and spend script output

        buildConstraints acc (outref, chainidx, AgapeDatum{..}) = Constraints.mustPayToPubKey adContributor (_ciTxOutValue chainidx) <>
                                                                  Constraints.mustSpendScriptOutput outref r                         <>
                                                                  acc

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "refunded"



-- evidence
-- > this is a producing transaction, so will be similar to contribute.
-- > if ownPPKH is the same as the Campaign's beneficiary, then only build the transaction, if not throw Error
evidence :: ProducerParams -> Contract w s Text ()
evidence ProducerParams{..} = do
    ownppkh <- ownPaymentPubKeyHash

    when (ownppkh /= ppCampaignBeneficiary) $ throwError "only beneficiary can provide evidence"
    when (isNothing ppEvidence)             $ throwError "no evidence provided"

    let campaign = Campaign
                   { cDescription    = ppCampaignDescription
                   , cDeadline       = ppCampaignDeadline
                   , cDeadlineObject = ppCampaignDeadlineObj
                   , cBeneficiary    = ppCampaignBeneficiary
                   , cArbiter        = ppCampaignArbiter
                   }

        dat = AgapeDatum
              { adContributor = ownppkh
              , adObjects     = False
              , adEvidence    = ppEvidence
              }

        val = lovelaceValueOf ppContributeAmt

        tx = Constraints.mustPayToTheScript dat val

    ledgerTx <- submitTxConstraints (agapeTypedValidator campaign) tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "beneficiary submitted evidence"





-- find valid UTXOs with valid datums at the script address. If provided with PPKH, will find UTXOs with that PPKH
-- a valid UTXO is one which:
-- > contains the AgapeDatum data object
findUTXOs :: AsContractError e => Campaign -> Maybe PaymentPubKeyHash -> Contract w s e [(TxOutRef, ChainIndexTxOut, AgapeDatum)]
findUTXOs c mppkh = do
    utxos <- utxosAt $ agapeAddress c
    
    let xs = Map.toList utxos

        -- filter the utxo list to ones which have AgapeDatum on it
        -- if mppkh is a Just, then look within the Datum for the PPKH
        filterdatum mp (_, o) = case _ciTxOutDatum o of
            Left _          -> False
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing             -> False
                Just AgapeDatum{..} -> case mp of
                    Nothing   -> True
                    Just ppkh -> adContributor == ppkh

        -- retrieve the AgapeDatum object
        getdatum (oref, o) = case _ciTxOutDatum o of
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Just agdatum -> (oref, o, agdatum) -- agdatum :: AgapeDatum

    return $ fmap getdatum (filter (filterdatum mppkh) xs)


type AgapeSchema =
        Endpoint "contribute" ProducerParams .\/ 
        Endpoint "refund" RefundParams       .\/
        Endpoint "payout" PayoutParams       .\/
        Endpoint "evidence" ProducerParams   .\/
        Endpoint "objects" ObjectionParams

endpoints :: Contract () AgapeSchema Text ()
endpoints = awaitPromise (contribute' `select` refund' `select` payout' `select` evidence' `select` objects') >> endpoints
  where
    contribute' = endpoint @"contribute" contribute
    refund'     = endpoint @"refund" refund
    payout'     = endpoint @"payout" payout
    evidence'   = endpoint @"evidence" evidence
    objects'    = endpoint @"objects" objects

--mkSchemaDefinitions ''AgapeSchema

-- contribute
test1 :: IO ()
test1 = runEmulatorTraceIO trace1

-- refund
test2 :: IO ()
test2 = runEmulatorTraceIO trace2

-- payout
test3 :: IO()
test3 = runEmulatorTraceIO trace3


trace1 :: EmulatorTrace ()
trace1 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints

    let 
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter

        producerParams = ProducerParams
                         { ppCampaignDescription = campaignDesc
                         , ppCampaignDeadline    = campaignDeadl
                         , ppCampaignDeadlineObj = campaignDeadlO
                         , ppCampaignBeneficiary = beneficiary
                         , ppCampaignArbiter     = arbiter
                         , ppContributeAmt       = 10_000_000
                         , ppEvidence            = Nothing
                         }

    callEndpoint @"contribute" h1 producerParams
    callEndpoint @"contribute" h2 producerParams

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s



trace2 :: EmulatorTrace ()
trace2 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints

    let 
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter

        producerParams = ProducerParams
                         { ppCampaignDescription = campaignDesc
                         , ppCampaignDeadline    = campaignDeadl
                         , ppCampaignDeadlineObj = campaignDeadlO
                         , ppCampaignBeneficiary = beneficiary
                         , ppCampaignArbiter     = arbiter
                         , ppContributeAmt       = 10_000_000
                         , ppEvidence            = Nothing
                         }

        campaign = Campaign
            { cDescription    = campaignDesc
            , cDeadline       = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            , cBeneficiary    = beneficiary
            , cArbiter        = arbiter
            }

        refundParams = RefundParams campaign

    callEndpoint @"contribute" h1 producerParams
    callEndpoint @"contribute" h2 producerParams

    void $ Trace.waitNSlots 25

    callEndpoint @"refund" h1 refundParams

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s



trace3 :: EmulatorTrace ()
trace3 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints
    h3 <- activateContractWallet (knownWallet 3) endpoints

    let 
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter
        evid           = "http://my_marathon_results.com"

        contributorParams = ProducerParams
            { ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 10_000_000
            , ppEvidence            = Nothing
            }

        evidenceParams = ProducerParams
            { ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 2_000_000
            , ppEvidence            = Just evid
            }
        
        campaign = Campaign
            { cDescription    = campaignDesc
            , cDeadline       = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            , cBeneficiary    = beneficiary
            , cArbiter        = arbiter
            }

        payoutParams = PayoutParams campaign

    callEndpoint @"contribute" h1 contributorParams
    callEndpoint @"contribute" h2 contributorParams

    void $ Trace.waitNSlots 1

    callEndpoint @"evidence" h3 evidenceParams

    void $ Trace.waitNSlots 25

    callEndpoint @"payout" h3 payoutParams 

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s

