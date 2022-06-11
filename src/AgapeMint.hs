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


import AgapeData
import Ledger (scriptCurrencySymbol)

-- Minting policy for NFT on successful payout
-- > Only mints for Payout Redeemer action
-- > Ensure each token name minted can only be 1
-- > Ensure only happens when payout is successful
-- > Ensure each conributor got an NFT

{-# INLINABLE mkPolicyAgape #-}
mkPolicyAgape :: Campaign -> AgapeAction -> ScriptContext -> Bool
mkPolicyAgape _ _ _ = True

policyAgape :: Campaign -> Scripts.MintingPolicy
policyAgape campaign = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| Scripts.wrapMintingPolicy . mkPolicyAgape ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode campaign

curSymbolAgape :: Campaign -> CurrencySymbol
curSymbolAgape campaign = scriptCurrencySymbol $ policyAgape campaign




















