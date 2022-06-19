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
import           Ledger.Value         as Value

import           Control.Monad        (void, when)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.Text            (Text)
import           Data.List            (foldl')
import           GHC.Generics         (Generic)
import qualified Data.Map             as Map (singleton, fromList, toList)
import qualified Prelude
import           Prelude              (IO, String)
import           Data.String
import           Text.Printf          (printf)

import           Playground.Contract  (KnownCurrency (..), ToSchema, ensureKnownCurrencies, mkSchemaDefinitions, printJson, printSchemas, stage)
import qualified Plutus.Contract as Constraints


-- imports for EmulatorTrace testing
import Plutus.V1.Ledger.Ada (lovelaceValueOf)
import Wallet.Emulator.Wallet
import Plutus.Trace (EmulatorTrace, activateContractWallet, callEndpoint, runEmulatorTraceIO)
import qualified Plutus.Trace as Trace
import qualified Control.Monad.Freer.Extras as Extras


-- had to separate out the datum and redeemer object as I was getting an error when the minting policy also 
-- wanted to use these objects
import AgapeData
import AgapeMint


-- Improvements -> TODO: If Arbiter needs to act, then arbiter gets a portion of the funds as compensation
--                 TODO: Note that for multiple contributions, need to update the same UTXO, that it contributed before,
--                       this is to ensure that for every contributor, there is only one Datum. It gets complicated for refund purposes
--                       if there are multiple UTXOs with the same contributor PPKH
-- Limitations  -> May not work if too many UTXOs to validate in one transaction, so may need some kind of batching solution
-- Major ISSUE  -> How to ensure that all objections registered as a UTXO on the script address are counted?

-- ############# --
-- On-chain code --
-- ############# --


-- validator is to validate consuming script Address UTXO, so only three Redeemer actions possible:
-- Payout, Refund, Object
-- The currency symbol passed in, is to ensure that the correct NFT is minted for a Payout
-- Campaign is passed in as a parameter, so each different Campaign will have a unique script address
{-# INLINABLE mkValidatorAgape #-}
mkValidatorAgape :: CurrencySymbol -> Campaign -> AgapeDatum -> AgapeAction -> ScriptContext -> Bool
mkValidatorAgape cs Campaign{..} agapeDatum redeemerAction ctx =

    -- all the script UTXOs to the transaction must contain the valid datum, if not fail.
    -- Not sure if required, but I feel this will prevent someone trying to spend an invalid datum
    traceIfFalse "Some input UTXO has an invalid datum" (length ownInputsValidDatum == length ownInputs) &&

    case redeemerAction of
        -- objection validation rules:
        -- > after deadline and before objection deadline
        -- > signed by the same ppkh of contributor in Datum
        -- > the sum of continuing output is equal of the input for this contributor
        -- > continuing output has datum value of Objection is true
        Object -> traceIfFalse "outside of objection deadline" correctObjectionDeadline         &&
                  traceIfFalse "signed by contributor" correctObjectionSignature                &&
                  traceIfFalse "continuing output sum paid to script" correctObjectionValue     &&
                  traceIfFalse "continuing output datum Objection is set" correctObjectionDatum

        -- refund validation rules:
        -- > after objection deadline
        -- > no evidence provided
        -- > Refunding the correct amount back to the contributor
        Refund -> traceIfFalse "refund - have not passed objection deadline" correctPastObjectionDeadline &&
                  traceIfFalse "refund - amount refunded incorrect" correctRefundAmount                   &&
                  if objectionIsSuccessful
                  then traceIfFalse "refund - not signed by arbiter" signedByArbiter
                  else traceIfFalse "refund - evidence was provided" noEvidenceProvided

        -- payout validation rules:
        -- > after objection deadline
        -- > evidence provided
        -- > all amounts go to beneficiary ** PROBLEM 1 ** how do you ensure all the contributed amounts go to beneficiary?
        --                                                 what if an attacker created a transaction with just one evidence, and small contributed amount
        --                                                 and then created another transaction to refund the rest? 
        --                                                 Solution: just ensure that beneficiary needs to sign the payout transaction
        --                                 ** PROBLEM 2 ** what if beneficiary in quick succession puts a fake evidence then creates a transaction
        --                                                 after objection deadline to payout? There's nothing stopping the beneficiary from
        --                                                 putting some fake evidence after the objection deadline.
        --                                                 Solution: add a refund window? so gives some time to refund first if no evidence.
        -- > Each contributor gets one NFT
        -- > Check total minted NFT matches number of unique contributors
        Payout -> traceIfFalse "payout - have not passed objection deadline" correctPastObjectionDeadline &&
                  traceIfFalse "payout - amount paid to beneficiary incorrect" beneficiaryPaidCorrectly   &&
                  traceIfFalse "payout - total minted NFT matches contributor count" correctNFTMinted     &&
                  traceIfFalse "payout - every contributor must receive the NFT" correctContributorNFT    &&
                  if objectionIsSuccessful
                  then traceIfFalse "payout - not signed by arbiter" signedByArbiter
                  else traceIfFalse "payout - evidence not provided" evidenceProvided                     &&
                       traceIfFalse "payout - not signed by beneficiary" payoutSignedByBeneficiary

  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownValidatorHash :: ValidatorHash
    ownValidatorHash = ownHash ctx

    ownScriptAddress :: Address
    ownScriptAddress = scriptHashAddress ownValidatorHash

    ownInput :: Maybe TxInInfo
    ownInput = findOwnInput ctx

    ownInputs :: [TxOut]
    ownInputs = filter (\txout -> ownScriptAddress == txOutAddress txout) (fmap txInInfoResolved $ txInfoInputs info)

    -- list of script inputs with valid datum
    ownInputsValidDatum :: [(TxOut, AgapeDatum)]
    ownInputsValidDatum = fmap getValidDatum ownInputs

    -- function to get a tuple of txout and datum from txout
    getValidDatum :: TxOut -> (TxOut, AgapeDatum)
    getValidDatum tout = case txOutDatumHash tout of
            Nothing -> traceError "wrong output type"
            Just dh -> case findDatum dh info of
                Nothing        -> traceError "datum not found"
                Just (Datum d) -> case PlutusTx.fromBuiltinData d of
                    Just ad -> (tout, ad)
                    Nothing -> traceError "error decoding datum"

    -- total input value with valid datum
    totalInputValue :: Value
    totalInputValue = mconcat (fmap (txOutValue . fst) ownInputsValidDatum)

    -- check whether objection is successful or not here
    -- this is done by checking each UTXO, and summing up the amount which has objection flag set
    -- For an objection to be successful, the objection amount must be greater than 1/2 of total value
    --
    -- ** PROBLEM ** since the validator only checks the inputs to the transaction, and not all the UTXOs sitting at the script address,
    --               how can we be sure that the objection is really succesful or not? Since I don't have a view of all the UTXOs, only what is
    --               on this transaction?
    objectionIsSuccessful :: Bool
    objectionIsSuccessful = fromValue objectionPower > (fromValue totalInputValue `Ada.divide` lovelaceOf 2)
      where
        objectionPower :: Value
        objectionPower = mconcat [ txOutValue totov | (totov, agd) <- ownInputsValidDatum, adObjects agd ] -- filter objection = True

    signedByArbiter :: Bool
    signedByArbiter = txSignedBy info (unPaymentPubKeyHash cArbiter)

    -- Objection validations
    -- *********************
    correctObjectionDeadline :: Bool
    correctObjectionDeadline = interval cDeadline cDeadlineObject `contains` txInfoValidRange info

    correctObjectionSignature :: Bool
    correctObjectionSignature = txSignedBy info (unPaymentPubKeyHash $ adContributor agapeDatum)

    ownOutput      :: TxOut
    ownOutputDatum :: AgapeDatum
    (ownOutput, ownOutputDatum) = case getContinuingOutputs ctx of
        [o] -> getValidDatum o
        _   -> traceError "only one continuing output expected"
   
    correctObjectionDatum :: Bool
    correctObjectionDatum = adContributor ownOutputDatum == adContributor agapeDatum &&
                            adObjects ownOutputDatum

    -- sum of input value == output. Input value has been filtered first to only include all script input only
    correctObjectionValue :: Bool
    correctObjectionValue = totalInputValue == txOutValue ownOutput


    -- Refund validations
    -- ******************
    correctPastObjectionDeadline :: Bool
    correctPastObjectionDeadline = from cDeadlineObject `contains` txInfoValidRange info

    -- check through all input utxos, ensure contributor ppkh is beneficiary, and NO evidence provided
    noEvidenceProvided :: Bool
    noEvidenceProvided = not evidenceProvided

    -- this function checks that the evidence exists
    checkEvidence :: AgapeDatum -> Bool
    checkEvidence ad = adContributor ad == cBeneficiary && isJust (adEvidence ad)

    -- for the UTXO input that's being validated, check the output to ensure there is a corresponding payment
    correctRefundAmount :: Bool
    correctRefundAmount = case ownInput of
        Nothing -> traceError "no input found for refund to be validated"
        Just txininfo ->
            let refundtxout = txInInfoResolved txininfo
                refundval = txOutValue refundtxout
                refunddathash = txOutDatumHash refundtxout
            in
                case refunddathash of
                    Nothing -> traceError "datum hash not found for refund"
                    Just dh -> case findDatum dh info of
                        Nothing -> traceError "datum not found for refund"
                        Just (Datum d) -> case PlutusTx.fromBuiltinData d of
                            Nothing -> traceError "error decoding datum for refund"
                            Just ad ->
                                let
                                    os = [o | o <- txInfoOutputs info, txOutAddress o == pubKeyHashAddress (adContributor ad) Nothing] -- how to handle stake key?
                                in
                                    case os of
                                        [o] -> txOutValue o == refundval -- by only checking for one output means that the contributor cannot call the refund endpoint.
                                                                         -- because it will create two outputs paid to the same contributor (change + fees)
                                        _   -> traceError "expected only one refund output per contributor"

    -- Payout validations
    -- ******************
    evidenceProvided :: Bool
    evidenceProvided = any checkEvidence $ mapMaybe PlutusTx.fromBuiltinData $ fmap getDatum $ mapMaybe (`findDatum` info) $ mapMaybe txOutDatumHash ownInputs

    payoutSignedByBeneficiary :: Bool
    payoutSignedByBeneficiary = txSignedBy info (unPaymentPubKeyHash cBeneficiary)

    -- sum up the total value from inputs, and ensure this amount goes to the beneficiary
    -- Note: I check to ensure that for all the output UTXO, there is a value amount that is equal to the sum of all the input
    --       I don't just do a simple sum of output >= input, because the change could be greater than the input value locked in contract
    beneficiaryPaidCorrectly :: Bool
    beneficiaryPaidCorrectly = any (== totalInputValue) [txOutValue o | o <- txInfoOutputs info, txOutAddress o == pubKeyHashAddress cBeneficiary Nothing] -- stake key?

    ownInputsContributorsPPKH :: [PaymentPubKeyHash]
    ownInputsContributorsPPKH = nub [adContributor agd | (_, agd) <- ownInputsValidDatum, adContributor agd /= cBeneficiary]

    -- number of NFT minted is 1 and must match the currencySymbol of the correct NFT
    nftMintList :: [(CurrencySymbol, TokenName, Integer)]
    nftMintList = [(nftcs, nfttn, nftnum) | (nftcs, nfttn, nftnum) <- flattenValue (txInfoMint info), nftnum == 1 && nftcs == cs]

    -- check that the number of unique contributor PPKH equals the number of NFT minted
    correctNFTMinted :: Bool
    correctNFTMinted = length nftMintList == length ownInputsContributorsPPKH

    -- check that each Contributor received an NFT
    correctContributorNFT :: Bool
    correctContributorNFT = checkContributorNFT ownInputsContributorsPPKH (txInfoOutputs info)

    -- loop through each contributor PPKH, and look for the corresponding txout
    -- check that each one received one NFT
    checkContributorNFT :: [PaymentPubKeyHash] -> [TxOut] -> Bool
    checkContributorNFT [] _        = True
    checkContributorNFT (p:ps) txos = case [txOutValue txo | txo <- txos, txOutAddress txo == pubKeyHashAddress p Nothing] of
                                          [nval] -> length [ () | (nvalcs, _, nvalnum) <- flattenValue nval, nvalcs == cs && nvalnum == 1] == 1 && checkContributorNFT ps txos
                                          _      -> traceError "contributor TxOut not found"

data AgapeType
instance Scripts.ValidatorTypes AgapeType where
    type RedeemerType AgapeType = AgapeAction
    type DatumType    AgapeType = AgapeDatum


agapeTypedValidator :: CurrencySymbol -> Campaign -> Scripts.TypedValidator AgapeType
agapeTypedValidator cs c = Scripts.mkTypedValidator @AgapeType
    ($$(PlutusTx.compile [|| mkValidatorAgape ||])
    `PlutusTx.applyCode` PlutusTx.liftCode cs 
    `PlutusTx.applyCode` PlutusTx.liftCode c)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @AgapeDatum @AgapeAction


agapeValidator :: CurrencySymbol -> Campaign -> Validator
agapeValidator cs = Scripts.validatorScript . agapeTypedValidator cs

agapeValHash :: CurrencySymbol -> Campaign -> Ledger.ValidatorHash
agapeValHash cs = Scripts.validatorHash . agapeTypedValidator cs

agapeAddress :: CurrencySymbol -> Campaign -> Ledger.Address
agapeAddress cs = scriptAddress . agapeValidator cs





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
    { ppCampaignName        :: !BuiltinByteString
    , ppCampaignDescription :: !BuiltinByteString
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
                   { cName           = ppCampaignName
                   , cDescription    = ppCampaignDescription
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
        
        cs = curSymbolAgape campaign

        tx = Constraints.mustPayToTheScript dat val
        
    ledgerTx <- submitTxConstraints (agapeTypedValidator cs campaign) tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "contributed to campaign"


-- object
-- find the UTXO which corresponds to the PPKH of the wallet, then spend it, and create new datum with objection = True
newtype ObjectionParams = ObjectionParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON)

objects :: AsContractError e => ObjectionParams -> Contract w s e ()
objects (ObjectionParams campaign@Campaign{..}) = do
    ownppkh <- ownPaymentPubKeyHash
    let cs = curSymbolAgape campaign
    utxos <- findUTXOs cs campaign (Just ownppkh)

    let r = Redeemer $ PlutusTx.toBuiltinData Object

        -- new datum with objection set to True
        obj_datum = AgapeDatum
                    { adContributor = ownppkh
                    , adObjects     = True
                    , adEvidence    = Nothing
                    }
        
        totalval = mconcat [_ciTxOutValue chainidx | (_, chainidx, _) <- utxos]

        lookups = Constraints.typedValidatorLookups (agapeTypedValidator cs campaign)           Prelude.<>
                  Constraints.otherScript (agapeValidator cs campaign)                          Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos])

        tx = Constraints.mustValidateIn (interval cDeadline cDeadlineObject)                <>
             Constraints.mustPayToTheScript obj_datum totalval                              <>
             mconcat [Constraints.mustSpendScriptOutput outref r | (outref, _, _) <- utxos]

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "objection"

-- payout
-- > in order for payout, one of the valid UTXOs must be submitted by the beneficiary with evidence
-- > must be past the objection deadline
-- > must not have a successful objection
-- > if objection is successful, then only proceed if signed by arbiter
-- > Also need to mint NFT for every contributer

newtype PayoutParams = PayoutParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON)

payout :: PayoutParams -> Contract w s Text ()
payout (PayoutParams campaign@Campaign{..}) = do
    let cs = curSymbolAgape campaign
    utxos   <- findUTXOs cs campaign Nothing -- find all suitable utxos
    now     <- currentTime
    ownppkh <- ownPaymentPubKeyHash

    when (now < cDeadlineObject)                       $ throwError "Can only payout past objection deadline"

    if objectionSuccessful utxos
    then when (ownppkh /= cArbiter)                    $ throwError "You must be an arbiter to process the payout as objections are successful"
    else when (not $ evidenceFound utxos cBeneficiary) $ throwError "Evidence not found, cannot payout"

    logInfo @String $ printf "address is: %s" (Prelude.show $ agapeAddress (curSymbolAgape campaign) campaign) 

    let r = Redeemer $ PlutusTx.toBuiltinData Payout

        totalval = mconcat [_ciTxOutValue chainidx | (_, chainidx, _) <- utxos]

        nonBenifPPKH = nub [adContributor agd | (_, _, agd) <- utxos, adContributor agd /= cBeneficiary] -- list of unique PPKH which is not beneficiary

        -- generate the list of Value for each unique contributor PPKH, NFT TokenName = campaign name ++ "#" ++ number
        nftvals = take (length nonBenifPPKH) [Value.singleton (curSymbolAgape campaign) (TokenName $ appendByteString cName (fromString $ "#" ++ Prelude.show tokenid)) 1 | tokenid <- [1..]]

        lookups = Constraints.typedValidatorLookups (agapeTypedValidator cs campaign)           Prelude.<>
                  Constraints.otherScript (agapeValidator cs campaign)                          Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos]) Prelude.<>
                  Constraints.mintingPolicy (policyAgape campaign)

        tx = Constraints.mustValidateIn (from cDeadlineObject)                          <>
             Constraints.mustPayToPubKey cBeneficiary totalval                          <>
             mconcat [Constraints.mustSpendScriptOutput oref r | (oref, _, _) <- utxos] <>
             Constraints.mustMintValue (mconcat nftvals)                                <> -- mint all the NFTs
             -- pay to each of the contributor's ppkh note: needs to include the minimal ada
             mconcat [Constraints.mustPayToPubKey paytoppkh (onenft <> lovelaceValueOf 2_000_000) | (paytoppkh, onenft) <- zip nonBenifPPKH nftvals]

             
    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "paid out"


-- searches the list of utxos to find if there is at least one which is submitted by the beneficiary with evidence attached
evidenceFound :: [(TxOutRef, ChainIndexTxOut, AgapeDatum)] -> PaymentPubKeyHash -> Bool
evidenceFound utxos benfPPKH = any (\(_, _, AgapeDatum{..}) -> adContributor == benfPPKH && isJust adEvidence) utxos


newtype RefundParams = RefundParams Campaign
    deriving stock (Generic)
    deriving anyclass (FromJSON, ToJSON)

-- refund to the contributors
-- > take into account objections, if objections are valid, then only proceed if signed by arbiter if not error.
-- > check to ensure evidence was not provided
refund :: RefundParams -> Contract w s Text ()
refund (RefundParams campaign@Campaign{..}) = do
    -- get the utxos, filter for the right Datum to get the Contributor, get the Value.
    -- then for each contributor ppkh, create a Constraint and put the value in as payment 
    let cs = curSymbolAgape campaign
    utxos   <- findUTXOs cs campaign Nothing
    now     <- currentTime
    ownppkh <- ownPaymentPubKeyHash

    when (now < cDeadlineObject)                 $ throwError "Can only refund past objection deadline"

    if objectionSuccessful utxos
    then when (ownppkh /= cArbiter)              $ throwError "You must be an arbiter to process the refund as objections are successful"
    else when (evidenceFound utxos cBeneficiary) $ throwError "Evidence was found, cannot refund"

    let r = Redeemer $ PlutusTx.toBuiltinData Refund

        lookups = Constraints.typedValidatorLookups (agapeTypedValidator cs campaign)           Prelude.<>
                  Constraints.otherScript (agapeValidator cs campaign)                          Prelude.<>
                  Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- utxos])

        tx = Constraints.mustValidateIn (from cDeadlineObject) <>
             foldl' buildConstraints mempty utxos -- build the Constraints to pay contributor and spend script output

        buildConstraints acc (outref, chainidx, AgapeDatum{..}) = Constraints.mustPayToPubKey adContributor (_ciTxOutValue chainidx) <>
                                                                  Constraints.mustSpendScriptOutput outref r                         <>
                                                                  acc

    ledgerTx <- submitTxConstraintsWith lookups tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "refunded"

-- ** PROBLEM ** it is possible for an attacker to construct a transaction and not include any objections,
--               how can we be sure that the objection is really succesful or not?
objectionSuccessful :: [(TxOutRef, ChainIndexTxOut, AgapeDatum)] -> Bool
objectionSuccessful utxos = fromValue objectionPower > (fromValue totalUTXOValue `Ada.divide` lovelaceOf 2)
  where
    objectionPower :: Value
    objectionPower = mconcat [ _ciTxOutValue chainidx | (_, chainidx, agd) <- utxos, adObjects agd ] -- filter objection = True

    totalUTXOValue :: Value
    totalUTXOValue = mconcat [ _ciTxOutValue chainidx | (_, chainidx, _) <- utxos ] -- sum up all the value



-- evidence
-- > this is a producing transaction, so will be similar to contribute.
-- > only the Campaign beneficiary can provide evidence. If ownpppkh is not the beneficiary, throw an Error
evidence :: ProducerParams -> Contract w s Text ()
evidence ProducerParams{..} = do
    ownppkh <- ownPaymentPubKeyHash

    when (ownppkh /= ppCampaignBeneficiary) $ throwError "only beneficiary can provide evidence"
    when (isNothing ppEvidence)             $ throwError "no evidence provided"

    let campaign = Campaign
                   { cName           = ppCampaignName
                   , cDescription    = ppCampaignDescription
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

        cs = curSymbolAgape campaign

        tx = Constraints.mustPayToTheScript dat val

    ledgerTx <- submitTxConstraints (agapeTypedValidator cs campaign) tx
    void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
    logInfo @String $ printf "beneficiary submitted evidence"





-- find valid UTXOs with valid datums at the script address. If provided with PPKH, will find UTXOs with that PPKH
-- a valid UTXO is one which:
-- > contains the AgapeDatum data object
findUTXOs :: AsContractError e => CurrencySymbol -> Campaign -> Maybe PaymentPubKeyHash -> Contract w s e [(TxOutRef, ChainIndexTxOut, AgapeDatum)]
findUTXOs cs c mppkh = do
    utxos <- utxosAt $ agapeAddress cs c
    
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

-- refund after objection succesesful
test4 :: IO()
test4 = runEmulatorTraceIO trace4

-- payout after objection successful
test5 :: IO()
test5 = runEmulatorTraceIO trace5


trace1 :: EmulatorTrace ()
trace1 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints

    let 
        campaignName   = "CharityRun"
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter

        producerParams = ProducerParams
                         { ppCampaignName        = campaignName
                         , ppCampaignDescription = campaignDesc
                         , ppCampaignDeadline    = campaignDeadl
                         , ppCampaignDeadlineObj = campaignDeadlO
                         , ppCampaignBeneficiary = beneficiary
                         , ppCampaignArbiter     = arbiter
                         , ppContributeAmt       = 10_000_000
                         , ppEvidence            = Nothing
                         }

    -- wallet 1 and wallet 2 contributes 10 Ada to the Campaign
    callEndpoint @"contribute" h1 producerParams
    callEndpoint @"contribute" h2 producerParams

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s



trace2 :: EmulatorTrace ()
trace2 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints
    h3 <- activateContractWallet (knownWallet 3) endpoints

    let 
        campaignName   = "CharityRun"
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter

        producerParams = ProducerParams
                         { ppCampaignName        = campaignName
                         , ppCampaignDescription = campaignDesc
                         , ppCampaignDeadline    = campaignDeadl
                         , ppCampaignDeadlineObj = campaignDeadlO
                         , ppCampaignBeneficiary = beneficiary
                         , ppCampaignArbiter     = arbiter
                         , ppContributeAmt       = 10_000_000
                         , ppEvidence            = Nothing
                         }

        campaign = Campaign
            { cName           = campaignName
            , cDescription    = campaignDesc
            , cDeadline       = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            , cBeneficiary    = beneficiary
            , cArbiter        = arbiter
            }

        refundParams = RefundParams campaign

    callEndpoint @"contribute" h1 producerParams
    callEndpoint @"contribute" h2 producerParams

    void $ Trace.waitNSlots 25

    -- Beneficiary triggers refunds after no evidence is provided
    callEndpoint @"refund" h3 refundParams

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s



trace3 :: EmulatorTrace ()
trace3 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints
    h3 <- activateContractWallet (knownWallet 3) endpoints
    h4 <- activateContractWallet (knownWallet 4) endpoints

    let 
        campaignName   = "CharityRun"
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter
        evid           = "http://my_marathon_results.com"

        contributorParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 10_000_000
            , ppEvidence            = Nothing
            }

        evidenceParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 2_000_000
            , ppEvidence            = Just evid
            }
        
        campaign = Campaign
            { cName           = campaignName
            , cDescription    = campaignDesc
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

    -- wallet 3 (beneficiary) triggers payout after providing evidence
    callEndpoint @"payout" h3 payoutParams 

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s

trace4 :: EmulatorTrace ()
trace4 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints
    h3 <- activateContractWallet (knownWallet 3) endpoints
    h4 <- activateContractWallet (knownWallet 4) endpoints

    let 
        campaignName   = "CharityRun"
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter
        evid           = "http://my_marathon_results.com"

        contributorParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 10_000_000
            , ppEvidence            = Nothing
            }

        evidenceParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 2_000_000
            , ppEvidence            = Just evid
            }
        
        campaign = Campaign
            { cName           = campaignName
            , cDescription    = campaignDesc
            , cDeadline       = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            , cBeneficiary    = beneficiary
            , cArbiter        = arbiter
            }

        refundParams = RefundParams campaign

        objectionParams = ObjectionParams campaign

    callEndpoint @"contribute" h1 contributorParams
    callEndpoint @"contribute" h2 contributorParams

    void $ Trace.waitNSlots 1

    callEndpoint @"evidence" h3 evidenceParams

    void $ Trace.waitNSlots 15

    -- wallet 1 and wallet 2 objects
    callEndpoint @"objects" h1 objectionParams
    callEndpoint @"objects" h2 objectionParams

    void $ Trace.waitNSlots 10

    -- arbiter triggers refunds
    callEndpoint @"refund" h4 refundParams 

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s


trace5 :: EmulatorTrace ()
trace5 = do
    h1 <- activateContractWallet (knownWallet 1) endpoints
    h2 <- activateContractWallet (knownWallet 2) endpoints
    h3 <- activateContractWallet (knownWallet 3) endpoints
    h4 <- activateContractWallet (knownWallet 4) endpoints

    let 
        campaignName   = "CharityRun"
        campaignDesc   = "run a marathon for charity"
        campaignDeadl  = 1596059101000 -- slot 10
        campaignDeadlO = 1596059111000 -- slot 20
        beneficiary    = mockWalletPaymentPubKeyHash (knownWallet 3) -- beneficiary
        arbiter        = mockWalletPaymentPubKeyHash (knownWallet 4) -- arbiter
        evid           = "http://my_marathon_results.com"

        contributorParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 10_000_000
            , ppEvidence            = Nothing
            }

        evidenceParams = ProducerParams
            { ppCampaignName        = campaignName
            , ppCampaignDescription = campaignDesc
            , ppCampaignDeadline    = campaignDeadl
            , ppCampaignDeadlineObj = campaignDeadlO
            , ppCampaignBeneficiary = beneficiary
            , ppCampaignArbiter     = arbiter
            , ppContributeAmt       = 2_000_000
            , ppEvidence            = Just evid
            }
        
        campaign = Campaign
            { cName           = campaignName
            , cDescription    = campaignDesc
            , cDeadline       = campaignDeadl
            , cDeadlineObject = campaignDeadlO
            , cBeneficiary    = beneficiary
            , cArbiter        = arbiter
            }

        payoutParams = PayoutParams campaign

        objectionParams = ObjectionParams campaign

    callEndpoint @"contribute" h1 contributorParams
    callEndpoint @"contribute" h2 contributorParams

    void $ Trace.waitNSlots 1

    callEndpoint @"evidence" h3 evidenceParams

    void $ Trace.waitNSlots 15

    -- wallet 1 and wallet 2 objects
    callEndpoint @"objects" h1 objectionParams
    callEndpoint @"objects" h2 objectionParams

    void $ Trace.waitNSlots 10

    -- arbiter triggers payout
    callEndpoint @"payout" h4 payoutParams 

    s <- Trace.waitNSlots 1

    Extras.logInfo $ "Reached " ++ Prelude.show s

