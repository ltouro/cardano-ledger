{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Alonzo.Rules.Bbody
  ( AlonzoBBODY,
    AlonzoBbodyPredFailure (..),
    AlonzoBbodyEvent (..),
    bbodyTransition,
  )
where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.Alonzo.Era (AlonzoBBODY)
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), pointWiseExUnits)
import Cardano.Ledger.Alonzo.Tx (AlonzoTx, totExUnits)
import Cardano.Ledger.Alonzo.TxSeq (AlonzoTxSeq, txSeqTxns)
import Cardano.Ledger.Alonzo.TxWitness (AlonzoEraWitnesses (..))
import Cardano.Ledger.BHeaderView (BHeaderView (..), isOverlaySlot)
import Cardano.Ledger.BaseTypes (ShelleyBase, UnitInterval, epochInfoPure)
import Cardano.Ledger.Block (Block (..))
import Cardano.Ledger.Core
import qualified Cardano.Ledger.Era as Era
import Cardano.Ledger.Keys (DSignable, Hash, coerceKeyRole)
import Cardano.Ledger.Shelley.BlockChain (bBodySize, incrBlocks)
import Cardano.Ledger.Shelley.LedgerState (LedgerState)
import Cardano.Ledger.Shelley.Rules.Bbody
  ( BbodyEnv (..),
    ShelleyBbodyEvent (..),
    ShelleyBbodyPredFailure (..),
    ShelleyBbodyState (..),
  )
import Cardano.Ledger.Shelley.Rules.Ledgers (ShelleyLedgersEnv (..))
import Cardano.Ledger.Slot (epochInfoEpoch, epochInfoFirst)
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition
  ( Embed (..),
    STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    liftSTS,
    trans,
    (?!),
  )
import Data.Coders
import Data.Kind (Type)
import Data.Sequence (Seq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Typeable
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks (..))

-- =======================================
-- A new PredicateFailure type

data AlonzoBbodyPredFailure era
  = ShelleyInAlonzoBbodyPredFailure (ShelleyBbodyPredFailure era)
  | TooManyExUnits
      !ExUnits
      -- ^ Computed Sum of ExUnits for all plutus scripts
      !ExUnits
      -- ^ Maximum allowed by protocal parameters
  deriving (Generic)

newtype AlonzoBbodyEvent era
  = ShelleyInAlonzoEvent (ShelleyBbodyEvent era)

deriving instance
  (Era era, Show (PredicateFailure (EraRule "LEDGERS" era))) =>
  Show (AlonzoBbodyPredFailure era)

deriving instance
  (Era era, Eq (PredicateFailure (EraRule "LEDGERS" era))) =>
  Eq (AlonzoBbodyPredFailure era)

deriving anyclass instance
  (Era era, NoThunks (PredicateFailure (EraRule "LEDGERS" era))) =>
  NoThunks (AlonzoBbodyPredFailure era)

instance
  ( Typeable era,
    ToCBOR (ShelleyBbodyPredFailure era)
  ) =>
  ToCBOR (AlonzoBbodyPredFailure era)
  where
  toCBOR (ShelleyInAlonzoBbodyPredFailure x) = encode (Sum ShelleyInAlonzoBbodyPredFailure 0 !> To x)
  toCBOR (TooManyExUnits x y) = encode (Sum TooManyExUnits 1 !> To x !> To y)

instance
  ( Typeable era,
    FromCBOR (ShelleyBbodyPredFailure era) -- TODO why is there no FromCBOR for (ShelleyBbodyPredFailure era)
  ) =>
  FromCBOR (AlonzoBbodyPredFailure era)
  where
  fromCBOR = decode (Summands "AlonzoBbodyPredFail" dec)
    where
      dec 0 = SumD ShelleyInAlonzoBbodyPredFailure <! From
      dec 1 = SumD TooManyExUnits <! From <! From
      dec n = Invalid n

-- ========================================
-- The STS instance

bbodyTransition ::
  forall (someBBODY :: Type -> Type) era.
  ( -- Conditions that the Abstract someBBODY must meet
    STS (someBBODY era),
    Signal (someBBODY era) ~ Block (BHeaderView (Crypto era)) era,
    PredicateFailure (someBBODY era) ~ AlonzoBbodyPredFailure era,
    BaseM (someBBODY era) ~ ShelleyBase,
    State (someBBODY era) ~ ShelleyBbodyState era,
    Environment (someBBODY era) ~ BbodyEnv era,
    -- Conditions to be an instance of STS
    Embed (EraRule "LEDGERS" era) (someBBODY era),
    Environment (EraRule "LEDGERS" era) ~ ShelleyLedgersEnv era,
    State (EraRule "LEDGERS" era) ~ LedgerState era,
    Signal (EraRule "LEDGERS" era) ~ Seq (Tx era),
    -- Conditions to define the rule in this Era
    HasField "_d" (PParams era) UnitInterval,
    HasField "_maxBlockExUnits" (PParams era) ExUnits,
    EraSegWits era,
    AlonzoEraWitnesses era,
    Era.TxSeq era ~ AlonzoTxSeq era,
    Tx era ~ AlonzoTx era
  ) =>
  TransitionRule (someBBODY era)
bbodyTransition =
  judgmentContext
    >>= \( TRC
             ( BbodyEnv pp account,
               BbodyState ls b,
               UnserialisedBlock bh txsSeq
               )
           ) -> do
        let txs = txSeqTxns txsSeq
            actualBodySize = bBodySize txsSeq
            actualBodyHash = hashTxSeq @era txsSeq

        actualBodySize == fromIntegral (bhviewBSize bh)
          ?! ShelleyInAlonzoBbodyPredFailure
            ( WrongBlockBodySizeBBODY actualBodySize (fromIntegral $ bhviewBSize bh)
            )

        actualBodyHash == bhviewBHash bh
          ?! ShelleyInAlonzoBbodyPredFailure
            ( InvalidBodyHashBBODY @era actualBodyHash (bhviewBHash bh)
            )

        ls' <-
          trans @(EraRule "LEDGERS" era) $
            TRC (LedgersEnv (bhviewSlot bh) pp account, ls, StrictSeq.fromStrict txs)

        -- Note that this may not actually be a stake pool - it could be a
        -- genesis key delegate. However, this would only entail an overhead of
        -- 7 counts, and it's easier than differentiating here.
        --
        -- TODO move this computation inside 'incrBlocks' where it belongs. Here
        -- we make an assumption that 'incrBlocks' must enforce, better for it
        -- to be done in 'incrBlocks' where we can see that the assumption is
        -- enforced.
        let hkAsStakePool = coerceKeyRole . bhviewID $ bh
            slot = bhviewSlot bh
        firstSlotNo <- liftSTS $ do
          ei <- asks epochInfoPure
          e <- epochInfoEpoch ei slot
          epochInfoFirst ei e

        {- ∑(tx ∈ txs)(totExunits tx) ≤ maxBlockExUnits pp  -}
        let txTotal, ppMax :: ExUnits
            txTotal = foldMap totExUnits txs
            ppMax = getField @"_maxBlockExUnits" pp
        pointWiseExUnits (<=) txTotal ppMax ?! TooManyExUnits txTotal ppMax

        pure $
          BbodyState @era
            ls'
            ( incrBlocks
                (isOverlaySlot firstSlotNo (getField @"_d" pp) slot)
                hkAsStakePool
                b
            )

instance
  ( DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody),
    Embed (EraRule "LEDGERS" era) (AlonzoBBODY era),
    Environment (EraRule "LEDGERS" era) ~ ShelleyLedgersEnv era,
    State (EraRule "LEDGERS" era) ~ LedgerState era,
    Signal (EraRule "LEDGERS" era) ~ Seq (AlonzoTx era),
    AlonzoEraWitnesses era,
    Tx era ~ AlonzoTx era,
    HasField "_d" (PParams era) UnitInterval,
    HasField "_maxBlockExUnits" (PParams era) ExUnits,
    Era.TxSeq era ~ AlonzoTxSeq era,
    Tx era ~ AlonzoTx era,
    EraSegWits era
  ) =>
  STS (AlonzoBBODY era)
  where
  type
    State (AlonzoBBODY era) =
      ShelleyBbodyState era

  type
    Signal (AlonzoBBODY era) =
      (Block (BHeaderView (Crypto era)) era)

  type Environment (AlonzoBBODY era) = BbodyEnv era

  type BaseM (AlonzoBBODY era) = ShelleyBase

  type PredicateFailure (AlonzoBBODY era) = AlonzoBbodyPredFailure era
  type Event (AlonzoBBODY era) = AlonzoBbodyEvent era

  initialRules = []
  transitionRules = [bbodyTransition @AlonzoBBODY]

instance
  ( Era era,
    BaseM ledgers ~ ShelleyBase,
    ledgers ~ EraRule "LEDGERS" era,
    STS ledgers,
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody),
    Era era
  ) =>
  Embed ledgers (AlonzoBBODY era)
  where
  wrapFailed = ShelleyInAlonzoBbodyPredFailure . LedgersFailure
  wrapEvent = ShelleyInAlonzoEvent . LedgersEvent
