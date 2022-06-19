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

module AgapeData where

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
    { cName           :: !BuiltinByteString
    , cDescription    :: !BuiltinByteString
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




