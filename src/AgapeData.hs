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
import qualified PlutusTx
import           PlutusTx.Prelude
import           Data.Aeson           (ToJSON, FromJSON)
import           GHC.Generics         (Generic)

-- Parameters
-- > Campaign (name, description, deadline_campaign, deadline_objection, beneficiary, arbiter)
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
    deriving (Generic, ToJSON, FromJSON)

PlutusTx.makeLift ''Campaign

data AgapeDatum = AgapeDatum
    { adContributor :: !PaymentPubKeyHash
    , adObjects     :: !Bool
    , adEvidence    :: !(Maybe BuiltinByteString)
    }

PlutusTx.unstableMakeIsData ''AgapeDatum

-- note for AgapeAction, I tried to include Payout with the script address
-- so that I can pass it to the Minting policy to search for UTXOs related to the
-- script address, but I kept getting an error for that.
data AgapeAction = Payout | Refund | Object

PlutusTx.unstableMakeIsData ''AgapeAction



