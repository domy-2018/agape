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

import           Control.Monad        (void)
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
-- > Campaign (description, deadline_campaign, deadline_objection)
-- > Arbiter PPKH
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
    }
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Campaign

data AgapeDatum = AgapeDatum
    { adContributor :: !PaymentPubKeyHash
    , adObjects     :: !Bool
    , adEvidence    :: !BuiltinByteString
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

-- 4 endpoints
-- > contribute
-- > object
-- > payout
-- > refund

data ContributeParams = ContributeParams
    { cpCampaignDescription :: !BuiltinByteString
    , cpCampaignDeadline    :: !POSIXTime
    , cpCampaignDeadlineObj :: !POSIXTime
    , cpContributeAmt       :: !Integer
    }
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)  

-- contribute to the campaign
contribute :: AsContractError e => ContributeParams -> Contract w s e ()
contribute ContributeParams{..} = do
    ownppkh <- ownPaymentPubKeyHash
    let campaign = Campaign
                   { cDescription    = cpCampaignDescription
                   , cDeadline       = cpCampaignDeadline
                   , cDeadlineObject = cpCampaignDeadlineObj
                   }

        dat = AgapeDatum
              { adContributor = ownppkh
              , adObjects     = False
              , adEvidence    = emptyByteString
              }

        val = lovelaceValueOf cpContributeAmt

        tx = Constraints.mustPayToTheScript dat val
        
    ledgerTx <- submitTxConstraints (agapeTypedValidator campaign) tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "contributed to campaign"


newtype RefundParams = RefundParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

-- refund to the contributors
refund :: AsContractError e => RefundParams -> Contract w s e ()
refund (RefundParams campaign@Campaign{..}) = do
    -- get the utxos, filter for the right Datum to get the Contributor, get the Value.
    -- then for each contributor ppkh, create a Constraint and put the value in as payment 
    utxos <- findUTXOs campaign

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




-- find valid UTXOs with valid datums at the script address
-- TODO: JUST A Hack for now, need refinement and proper filtering!
findUTXOs :: AsContractError e => Campaign -> Contract w s e [(TxOutRef, ChainIndexTxOut, AgapeDatum)]
findUTXOs c = do
    utxos <- utxosAt $ agapeAddress c
    
    let xs = Map.toList utxos

        getdatum (oref, o) = case _ciTxOutDatum o of
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Just d@AgapeDatum{..} -> (oref, o, d)

    return $ fmap getdatum xs


type AgapeSchema =
        Endpoint "contribute" ContributeParams .\/ 
        Endpoint "refund" RefundParams

endpoints :: Contract () AgapeSchema Text ()
endpoints = awaitPromise (contribute' `select` refund') >> endpoints
  where
    contribute' = endpoint @"contribute" contribute
    refund'     = endpoint @"refund" refund

--mkSchemaDefinitions ''AgapeSchema


test1 :: IO ()
test1 = runEmulatorTraceIO trace1

test2 :: IO ()
test2 = runEmulatorTraceIO trace2



trace1 :: EmulatorTrace ()
trace1 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints

    let 
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20

        contributeParams = ContributeParams
                           { cpCampaignDescription = campaignDesc
                           , cpCampaignDeadline = campaignDeadl
                           , cpCampaignDeadlineObj = campaignDeadlO
                           , cpContributeAmt = 10_000_000
                           }

        campaign = Campaign
            { cDescription = campaignDesc
            , cDeadline = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            }

        refundParams = RefundParams campaign

    callEndpoint @"contribute" h1 contributeParams
    callEndpoint @"contribute" h2 contributeParams

    void $ Trace.waitNSlots 25

    callEndpoint @"refund" h1 refundParams

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

        contributeParams = ContributeParams
                           { cpCampaignDescription = campaignDesc
                           , cpCampaignDeadline = campaignDeadl
                           , cpCampaignDeadlineObj = campaignDeadlO
                           , cpContributeAmt = 10_000_000
                           }

    callEndpoint @"contribute" h1 contributeParams
    callEndpoint @"contribute" h2 contributeParams

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s




{-
data BetParams = BetParams
    { bpBet    :: Bool
    , bpAmount :: Integer
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

data PayoutParams = PayoutParams
    { ppSeed       :: BuiltinByteString
    , ppWinnerPPKH :: PaymentPubKeyHash
    , ppLoserPPKH  :: PaymentPubKeyHash
    }
    deriving stock (Prelude.Eq, Prelude.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)

type CoinFlipSchema =
        Endpoint "bet" BetParams
    .\/ Endpoint "payout" PayoutParams

-- | make a bet
bet :: AsContractError e => BetParams -> Contract w s e ()
bet bp = do
    let tx = Constraints.mustPayToTheScript (bpBet bp) $ Ada.lovelaceValueOf $ bpAmount bp
    ledgerTx <- submitTxConstraints agapeTypedValidator tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "bet %d lovelace on %s"
        (bpAmount bp)
        (if bpBet bp then "Heads" else "Tails" :: String)

-- | payout
payout :: AsContractError e => PayoutParams -> Contract w s e ()
payout PayoutParams {..} = do
    utxos <- utxosAt agapeAddress

    let amt = Prelude.foldl1 (<>) (map _ciTxOutValue (Map.elems utxos))
        tx  = Constraints.mustPayToPubKey ppWinnerPPKH amt <>
              Constraints.collectFromScript utxos ppSeed

    ledgerTx <- submitTxConstraintsSpending agapeTypedValidator utxos tx
    
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "collecting %d winnings with seed " (getLovelace $ fromValue amt)


endpoints :: Contract () CoinFlipSchema Text ()
endpoints = awaitPromise (bet' `select` payout') >> endpoints
  where
    bet' = endpoint @"bet" bet
    payout' = endpoint @"payout" payout

--mkSchemaDefinitions ''CoinFlipSchema
-}
