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

module AgapeMint where

import           Ledger
import qualified Ledger.Typed.Scripts as Scripts
import qualified PlutusTx
import           PlutusTx.Prelude
import           Ledger.Value         as Value


import AgapeData

-- Minting policy for NFT on successful payout
-- > Only mints for Payout Redeemer action
-- > Ensure each token name minted can only be 1
-- > Ensure only happens when payout is successful
--   > past the objection deadline
--   > if objection successful, signed by Arbiter (Note: unable to do this because I could not pass in script address as Redeemer parameter)
--   > if objection not successful, evidence provided (Note: unable to do this because I could not pass in script address as Redeemer parameter)

-- Note: I feel like there are other checks from the Agape script validator, which does not need to be replicated here
-- because I feel like the mint policy script should only concern itself with when should the minting be allowed
-- It shouldn't need to care whether the beneficiary is paid correctly, or if the contributors received the NFT
-- So the above minting policy criteria is the bare minimum of when it is allowed to mint.

{-# INLINABLE mkPolicyAgape #-}
mkPolicyAgape :: Campaign -> AgapeAction -> ScriptContext -> Bool
mkPolicyAgape Campaign{..} redeemerAction ctx =

    case redeemerAction of
        -- only mint on Payout redeemer action
        Payout -> traceIfFalse "mint - Can only mint 1 per token name" correctMintValue            &&
                  traceIfFalse "mint - Payout objection deadline not passed" pastObjectionDeadline

        -- disallow minting for any other redeemer action
        _ -> False

    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        ownCS :: CurrencySymbol
        ownCS = ownCurrencySymbol ctx

        -- checks to ensure only 1 nft per token name
        correctMintValue :: Bool
        correctMintValue = all (\(nftcs, _, nftnum) -> nftnum == 1 && nftcs == ownCS) (flattenValue (txInfoMint info))

        -- ensures past objection deadline
        pastObjectionDeadline :: Bool
        pastObjectionDeadline = from cDeadlineObject `contains` txInfoValidRange info


policyAgape :: Campaign -> Scripts.MintingPolicy
policyAgape campaign = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| Scripts.wrapMintingPolicy . mkPolicyAgape ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode campaign

curSymbolAgape :: Campaign -> CurrencySymbol
curSymbolAgape campaign = scriptCurrencySymbol $ policyAgape campaign









{- Commenting out this code, because I tried to have a parameter to the redeemer action Payout Address, but 
 - it doesn't seem to work with Minting policies. I got it to work when minting policies was not involved, but the moment I included
 - the minting policy into the transaction with a parameer to the Redeemer action, it fails with an error when validating the contract


{-# INLINABLE mkPolicyAgape #-}
mkPolicyAgape :: Campaign -> AgapeAction -> ScriptContext -> Bool
mkPolicyAgape Campaign{..} redeemerAction ctx =

    case redeemerAction of
        -- only mint on Payout redeemer action
        (Payout agapeScriptAddress) -> traceIfFalse "mint - Can only mint 1 per token name" correctMintValue            &&
                                       traceIfFalse "mint - Payout objection deadline not passed" pastObjectionDeadline &&
                                       if objectionIsSuccessful agapeScriptAddress
                                       then traceIfFalse "mint - not signed by arbiter" signedByArbiter
                                       else traceIfFalse "mint - evidence not provided" (evidenceProvided agapeScriptAddress)

        -- disallow minting for any other redeemer action
        _ -> False

    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        ownCS :: CurrencySymbol
        ownCS = ownCurrencySymbol ctx

        -- checks to ensure only 1 nft per token name
        correctMintValue :: Bool
        correctMintValue = all (\(nftcs, _, nftnum) -> nftnum == 1 && nftcs == ownCS) (flattenValue (txInfoMint info))

        -- ensures past objection deadline
        pastObjectionDeadline :: Bool
        pastObjectionDeadline = from cDeadlineObject `contains` txInfoValidRange info

        ownInputs :: Address -> [TxOut]
        ownInputs agapeAdd = filter (\txout -> agapeAdd == txOutAddress txout) (fmap txInInfoResolved $ txInfoInputs info)

        -- list of script inputs with valid datum
        ownInputsValidDatum :: Address -> [(TxOut, AgapeDatum)]
        ownInputsValidDatum agapeAdd = fmap getValidDatum (ownInputs agapeAdd)

        -- function to get a tuple of txout and datum from txout
        getValidDatum :: TxOut -> (TxOut, AgapeDatum)
        getValidDatum tout = case txOutDatumHash tout of
            Nothing -> traceError "wrong output type"
            Just dh -> case findDatum dh info of
                Nothing        -> traceError "datum not found"
                Just (Datum d) -> case PlutusTx.fromBuiltinData d of
                    Just ad -> (tout, ad)
                    Nothing -> traceError "error decoding datum"

        -- totalinput value with valid datum
        totalInputValue :: Address -> Value
        totalInputValue agapeAdd = mconcat (fmap (txOutValue . fst) (ownInputsValidDatum agapeAdd)) 

        objectionIsSuccessful :: Address -> Bool
        objectionIsSuccessful agapeAdd = fromValue objectionPower > (fromValue (totalInputValue agapeAdd) `Ada.divide` lovelaceOf 2)
          where
            objectionPower :: Value
            objectionPower = mconcat [ txOutValue totov | (totov, agd) <- ownInputsValidDatum agapeAdd, adObjects agd ] -- filter objection = True

        -- if objection succesful, must be signed by arbiter
        signedByArbiter :: Bool
        signedByArbiter = txSignedBy info (unPaymentPubKeyHash cArbiter)

        checkEvidence :: AgapeDatum -> Bool
        checkEvidence ad = adContributor ad == cBeneficiary && isJust (adEvidence ad)

        evidenceProvided :: Address -> Bool
        evidenceProvided agapeAdd = any checkEvidence $ mapMaybe PlutusTx.fromBuiltinData $ fmap getDatum $ mapMaybe (`findDatum` info) $ mapMaybe txOutDatumHash (ownInputs agapeAdd)

-}


