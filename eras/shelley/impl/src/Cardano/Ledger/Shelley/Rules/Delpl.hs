{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Shelley.Rules.Delpl
  ( ShelleyDELPL,
    DelplEnv (..),
    ShelleyDelplPredFailure (..),
    ShelleyDelplEvent,
    PredicateFailure,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    encodeListLen,
  )
import Cardano.Ledger.BaseTypes (ProtVer, ShelleyBase, invalidKey)
import Cardano.Ledger.Core
import Cardano.Ledger.Serialization (decodeRecordSum)
import Cardano.Ledger.Shelley.LedgerState
  ( AccountState,
    DPState,
    DState,
    PState,
    dpsDState,
    dpsPState,
  )
import Cardano.Ledger.Shelley.Rules.Deleg (DelegEnv (..), ShelleyDELEG, ShelleyDelegPredFailure)
import Cardano.Ledger.Shelley.Rules.Pool (PoolEnv (..), ShelleyPOOL, ShelleyPoolPredFailure)
import Cardano.Ledger.Shelley.TxBody
  ( DCert (..),
    DelegCert (..),
    GenesisDelegCert (..),
    PoolCert (..),
    Ptr,
  )
import Cardano.Ledger.Slot (SlotNo)
import Control.State.Transition
import Data.Typeable (Typeable)
import Data.Word (Word8)
import GHC.Generics (Generic)
import GHC.Records (HasField)
import NoThunks.Class (NoThunks (..))

data ShelleyDELPL era

data DelplEnv era = DelplEnv
  { delplSlotNo :: SlotNo,
    delPlPtr :: Ptr,
    delPlPp :: PParams era,
    delPlAcnt :: AccountState
  }

data ShelleyDelplPredFailure era
  = PoolFailure (PredicateFailure (EraRule "POOL" era)) -- Subtransition Failures
  | DelegFailure (PredicateFailure (EraRule "DELEG" era)) -- Subtransition Failures
  deriving (Generic)

data ShelleyDelplEvent era
  = PoolEvent (Event (ShelleyPOOL era))
  | DelegEvent (Event (ShelleyDELEG era))

deriving stock instance
  ( Eq (PredicateFailure (EraRule "DELEG" era)),
    Eq (PredicateFailure (EraRule "POOL" era))
  ) =>
  Eq (ShelleyDelplPredFailure era)

deriving stock instance
  ( Show (PredicateFailure (EraRule "DELEG" era)),
    Show (PredicateFailure (EraRule "POOL" era))
  ) =>
  Show (ShelleyDelplPredFailure era)

instance
  ( NoThunks (PredicateFailure (EraRule "DELEG" era)),
    NoThunks (PredicateFailure (EraRule "POOL" era))
  ) =>
  NoThunks (ShelleyDelplPredFailure era)

instance
  ( Era era,
    Embed (EraRule "DELEG" era) (ShelleyDELPL era),
    Environment (EraRule "DELEG" era) ~ DelegEnv era,
    State (EraRule "DELEG" era) ~ DState (Crypto era),
    Signal (EraRule "DELEG" era) ~ DCert (Crypto era),
    Embed (EraRule "POOL" era) (ShelleyDELPL era),
    Environment (EraRule "POOL" era) ~ PoolEnv era,
    State (EraRule "POOL" era) ~ PState (Crypto era),
    Signal (EraRule "POOL" era) ~ DCert (Crypto era)
  ) =>
  STS (ShelleyDELPL era)
  where
  type State (ShelleyDELPL era) = DPState (Crypto era)
  type Signal (ShelleyDELPL era) = DCert (Crypto era)
  type Environment (ShelleyDELPL era) = DelplEnv era
  type BaseM (ShelleyDELPL era) = ShelleyBase
  type PredicateFailure (ShelleyDELPL era) = ShelleyDelplPredFailure era
  type Event (ShelleyDELPL era) = ShelleyDelplEvent era

  transitionRules = [delplTransition]

instance
  ( Era era,
    ToCBOR (PredicateFailure (EraRule "POOL" era)),
    ToCBOR (PredicateFailure (EraRule "DELEG" era)),
    Typeable (Script era)
  ) =>
  ToCBOR (ShelleyDelplPredFailure era)
  where
  toCBOR = \case
    (PoolFailure a) ->
      encodeListLen 2 <> toCBOR (0 :: Word8)
        <> toCBOR a
    (DelegFailure a) ->
      encodeListLen 2 <> toCBOR (1 :: Word8)
        <> toCBOR a

instance
  ( Era era,
    FromCBOR (PredicateFailure (EraRule "POOL" era)),
    FromCBOR (PredicateFailure (EraRule "DELEG" era)),
    Typeable (Script era)
  ) =>
  FromCBOR (ShelleyDelplPredFailure era)
  where
  fromCBOR =
    decodeRecordSum
      "PredicateFailure (DELPL era)"
      ( \case
          0 -> do
            a <- fromCBOR
            pure (2, PoolFailure a)
          1 -> do
            a <- fromCBOR
            pure (2, DelegFailure a)
          k -> invalidKey k
      )

delplTransition ::
  forall era.
  ( Embed (EraRule "DELEG" era) (ShelleyDELPL era),
    Environment (EraRule "DELEG" era) ~ DelegEnv era,
    State (EraRule "DELEG" era) ~ DState (Crypto era),
    Signal (EraRule "DELEG" era) ~ DCert (Crypto era),
    Embed (EraRule "POOL" era) (ShelleyDELPL era),
    Environment (EraRule "POOL" era) ~ PoolEnv era,
    State (EraRule "POOL" era) ~ PState (Crypto era),
    Signal (EraRule "POOL" era) ~ DCert (Crypto era)
  ) =>
  TransitionRule (ShelleyDELPL era)
delplTransition = do
  TRC (DelplEnv slot ptr pp acnt, d, c) <- judgmentContext
  case c of
    DCertPool (RegPool _) -> do
      ps <-
        trans @(EraRule "POOL" era) $ TRC (PoolEnv slot pp, dpsPState d, c)
      pure $ d {dpsPState = ps}
    DCertPool (RetirePool _ _) -> do
      ps <-
        trans @(EraRule "POOL" era) $ TRC (PoolEnv slot pp, dpsPState d, c)
      pure $ d {dpsPState = ps}
    DCertGenesis GenesisDelegCert {} -> do
      ds <-
        trans @(EraRule "DELEG" era) $ TRC (DelegEnv slot ptr acnt pp, dpsDState d, c)
      pure $ d {dpsDState = ds}
    DCertDeleg (RegKey _) -> do
      ds <-
        trans @(EraRule "DELEG" era) $ TRC (DelegEnv slot ptr acnt pp, dpsDState d, c)
      pure $ d {dpsDState = ds}
    DCertDeleg (DeRegKey _) -> do
      ds <-
        trans @(EraRule "DELEG" era) $ TRC (DelegEnv slot ptr acnt pp, dpsDState d, c)
      pure $ d {dpsDState = ds}
    DCertDeleg (Delegate _) -> do
      ds <-
        trans @(EraRule "DELEG" era) $ TRC (DelegEnv slot ptr acnt pp, dpsDState d, c)
      pure $ d {dpsDState = ds}
    DCertMir _ -> do
      ds <- trans @(EraRule "DELEG" era) $ TRC (DelegEnv slot ptr acnt pp, dpsDState d, c)
      pure $ d {dpsDState = ds}

instance
  ( Era era,
    STS (ShelleyPOOL era),
    PredicateFailure (EraRule "POOL" era) ~ ShelleyPoolPredFailure era
  ) =>
  Embed (ShelleyPOOL era) (ShelleyDELPL era)
  where
  wrapFailed = PoolFailure
  wrapEvent = PoolEvent

instance
  ( Era era,
    HasField "_protocolVersion" (PParams era) ProtVer,
    PredicateFailure (EraRule "DELEG" era) ~ ShelleyDelegPredFailure era
  ) =>
  Embed (ShelleyDELEG era) (ShelleyDELPL era)
  where
  wrapFailed = DelegFailure
  wrapEvent = DelegEvent
