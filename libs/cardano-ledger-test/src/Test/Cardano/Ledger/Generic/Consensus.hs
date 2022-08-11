{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Generic Consensus examples
module Test.Cardano.Ledger.Generic.ConsensusSave where

import Cardano.Binary
import Cardano.Crypto.DSIGN as DSIGN
import Cardano.Crypto.Hash as Hash
import Cardano.Crypto.KES.Class (ContextKES)
import Cardano.Crypto.Seed as Seed
import Cardano.Crypto.VRF as VRF
import qualified Cardano.Ledger.Alonzo.PParams as AlonzoPP
import Cardano.Ledger.AuxiliaryData
import qualified Cardano.Ledger.Babbage.PParams as BabbagePP
import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Conway.PParams as ConwayPP
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Crypto as CC
import Cardano.Ledger.Era
import qualified Cardano.Ledger.Era as Era (Crypto)
import Cardano.Ledger.Keys
import Cardano.Ledger.PoolDistr
import Cardano.Ledger.SafeHash
import Cardano.Ledger.Shelley (ShelleyEra)
import Cardano.Ledger.Shelley.API
import Cardano.Ledger.Shelley.EpochBoundary
import Cardano.Ledger.Shelley.LedgerState
import Cardano.Ledger.Shelley.PParams
import qualified Cardano.Ledger.Shelley.PParams as ShelleyPP
import Cardano.Ledger.Shelley.Rules.Delegs
import Cardano.Ledger.Shelley.Rules.EraMapping ()
import Cardano.Ledger.Shelley.Rules.Ledger
import Cardano.Ledger.Shelley.Tx
import Cardano.Ledger.Shelley.UTxO
import Cardano.Protocol.TPraos.API
import Cardano.Protocol.TPraos.API (PraosCrypto)
import Cardano.Protocol.TPraos.BHeader
import Cardano.Protocol.TPraos.OCert
import Cardano.Protocol.TPraos.Rules.Prtcl
import Cardano.Protocol.TPraos.Rules.Tickn
import Cardano.Slotting.Block
import Cardano.Slotting.EpochInfo
import Cardano.Slotting.Slot
import qualified Data.ByteString as Strict
import Data.Coerce (coerce)
import Data.Default.Class
import Data.Functor.Identity (Identity (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Proxy
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time
import Data.Word (Word64, Word8)
import GHC.Records (HasField)
import Lens.Micro ((&), (.~))
import Numeric.Natural (Natural)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Shelley.Generator.Core
import Test.Cardano.Ledger.Shelley.Orphans ()
import Test.Cardano.Ledger.Shelley.Utils hiding (mkVRFKeyPair)

import Test.Cardano.Ledger.Generic.Updaters(newTx,updateTx,newTxBody)
import Test.Cardano.Ledger.Generic.Fields(TxField(..),TxBodyField(..),WitnessesField(..)) hiding (Update)
import qualified Test.Cardano.Ledger.Generic.Fields as Fields (TxBodyField(Update))
import Data.List(foldl')
import Cardano.Ledger.Val(inject)

-- ==================================================================

type KeyPairWits era = [KeyPair 'Witness (Cardano.Ledger.Era.Crypto era)]

emptyPPUpdate :: Proof era -> Core.PParamsUpdate era
emptyPPUpdate (Shelley _) = ShelleyPP.emptyPParamsUpdate
emptyPPUpdate (Allegra _) = ShelleyPP.emptyPParamsUpdate
emptyPPUpdate (Mary _) = ShelleyPP.emptyPParamsUpdate
emptyPPUpdate (Alonzo _) = AlonzoPP.emptyPParamsUpdate
emptyPPUpdate (Babbage _) = BabbagePP.emptyPParamsUpdate
emptyPPUpdate (Conway _) = ConwayPP.emptyPParamsUpdate

emptyPP :: Proof era -> Core.PParams era
emptyPP (Shelley _) = ShelleyPP.emptyPParams
emptyPP (Allegra _) = ShelleyPP.emptyPParams
emptyPP (Mary _) = ShelleyPP.emptyPParams
emptyPP (Alonzo _) = AlonzoPP.emptyPParams
emptyPP (Babbage _) = BabbagePP.emptyPParams
emptyPP (Conway _) = ConwayPP.emptyPParams

{-------------------------------------------------------------------------------
  ShelleyLedgerExamples
-------------------------------------------------------------------------------}

data ResultExamples era = ResultExamples
  { sreProof :: Proof era,
    srePParams :: Core.PParams era,
    sreProposedPPUpdates :: ProposedPPUpdates era,
    srePoolDistr :: PoolDistr (Cardano.Ledger.Era.Crypto era),
    sreNonMyopicRewards ::
      Map
        (Either Coin (Credential 'Staking (Cardano.Ledger.Era.Crypto era)))
        (Map (KeyHash 'StakePool (Cardano.Ledger.Era.Crypto era)) Coin),
    sreShelleyGenesis :: ShelleyGenesis era
  }

data LedgerExamples era = LedgerExamples
  { sleProof :: Proof era,
    sleBlock :: Block (BHeader (Era.Crypto era)) era,
    sleHashHeader :: HashHeader (Cardano.Ledger.Era.Crypto era),
    sleTx :: Core.Tx era,
    sleApplyTxError :: ApplyTxError era,
    sleRewardsCredentials :: Set (Either Coin (Credential 'Staking (Cardano.Ledger.Era.Crypto era))),
    sleResultExamples :: ResultExamples era,
    sleNewEpochState :: NewEpochState era,
    sleChainDepState :: ChainDepState (Cardano.Ledger.Era.Crypto era),
    sleTranslationContext :: TranslationContext era
  }

-- ============================================================

defaultLedgerExamples ::
  forall era.
  ( Reflect era,
    Default (StashedAVVMAddresses era),
    Default (State (Core.EraRule "PPUP" era))
  ) =>
  Proof era ->
  (Core.TxBody era -> KeyPairWits era -> Core.Witnesses era) ->
  (ShelleyTx era -> Core.Tx era) ->
  Core.Value era ->
  Core.TxBody era ->
  Core.AuxiliaryData era ->
  TranslationContext era ->
  LedgerExamples era
defaultLedgerExamples proof mkWitnesses mkAlonzoTx value txBody auxData translationContext =
  LedgerExamples
    { sleProof = proof,
      sleBlock = exampleLedgerBlock proof tx, -- (mkAlonzoTx tx),
      sleHashHeader = exampleHashHeader proof,
      sleTx = tx,
      sleApplyTxError =
        ApplyTxError
          [ case proof of
              Shelley _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
              Allegra _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
              Mary _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
              Alonzo _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
              Babbage _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
              Conway _ -> DelegsFailure $ DelegateeNotRegisteredDELEG @era (mkKeyHash 1)
          ],
      sleRewardsCredentials =
        Set.fromList
          [ Left (Coin 100),
            Right (ScriptHashObj (mkScriptHash 1)),
            Right (KeyHashObj (mkKeyHash 2))
          ],
      sleResultExamples = resultExamples,
      sleNewEpochState =
        exampleNewEpochState
          proof
          value
          undefined -- (emptyPP proof)
          undefined, -- ((emptyPP proof) {_minUTxOValue = Coin 1}),
      sleChainDepState = exampleLedgerChainDepState 1,
      sleTranslationContext = translationContext
    }
  where
    tx = exampleTx proof mkWitnesses txBody auxData

    resultExamples =
      ResultExamples
        { sreProof = proof,
          srePParams =
            ( case proof of
                Shelley _ -> def
                Allegra _ -> def
                Mary _ -> def
                Alonzo _ -> def
                Babbage _ -> def
                Conway _ -> def
            ),
          sreProposedPPUpdates = exampleProposedPParamsUpdates proof,
          srePoolDistr = examplePoolDistr,
          sreNonMyopicRewards = exampleNonMyopicRewards,
          sreShelleyGenesis = testShelleyGenesis
        }

-- ============================================

mkKeyHash :: forall c discriminator. CC.Crypto c => Int -> KeyHash discriminator c
mkKeyHash = KeyHash . mkDummyHash (Proxy @(ADDRHASH c))

mkScriptHash :: forall c. CC.Crypto c => Int -> ScriptHash c
mkScriptHash = ScriptHash . mkDummyHash (Proxy @(ADDRHASH c))

mkDummyHash :: forall h a. HashAlgorithm h => Proxy h -> Int -> Hash.Hash h a
mkDummyHash _ = coerce . hashWithSerialiser @h toCBOR

mkDummySafeHash :: forall c a. CC.Crypto c => Proxy c -> Int -> SafeHash c a
mkDummySafeHash _ =
  unsafeMakeSafeHash
    . mkDummyHash (Proxy @(HASH c))

exampleLedgerBlock ::
  forall era.
  ( Reflect era
  -- EraSegWits era
  ) =>
  Proof era ->
  Core.Tx era ->
  Block (BHeader (Era.Crypto era)) era
exampleLedgerBlock proof tx = specialize @EraSegWits proof (Block blockHeader blockBody)
  where
    keys :: AllIssuerKeys (Cardano.Ledger.Era.Crypto era) 'StakePool
    keys = exampleKeys

    (_, (hotKey, _)) = head $ hot keys
    KeyPair vKeyCold _ = cold keys

    blockHeader :: BHeader (Cardano.Ledger.Era.Crypto era)
    blockHeader = BHeader blockHeaderBody (signedKES () 0 blockHeaderBody hotKey)

    blockHeaderBody :: BHBody (Cardano.Ledger.Era.Crypto era)
    blockHeaderBody =
      BHBody
        { bheaderBlockNo = BlockNo 3,
          bheaderSlotNo = SlotNo 9,
          bheaderPrev = BlockHash (HashHeader (mkDummyHash Proxy 2)),
          bheaderVk = coerceKeyRole vKeyCold,
          bheaderVrfVk = snd $ vrf keys,
          bheaderEta = mkCertifiedVRF (mkBytes 0) (fst $ vrf keys),
          bheaderL = mkCertifiedVRF (mkBytes 1) (fst $ vrf keys),
          bsize = 2345,
          bhash = specialize @EraSegWits proof (hashTxSeq @era blockBody),
          bheaderOCert = mkOCert keys 0 (KESPeriod 0),
          bprotver = ProtVer 2 0
        }

    blockBody = specialize @EraSegWits proof (toTxSeq @era (StrictSeq.fromList [tx]))

    mkBytes :: Int -> Cardano.Ledger.BaseTypes.Seed
    mkBytes = Seed . mkDummyHash (Proxy @Blake2b_256)

exampleKeys :: forall c r. CC.Crypto c => AllIssuerKeys c r
exampleKeys =
  AllIssuerKeys
    coldKey
    (mkVRFKeyPair (Proxy @c) 1)
    [(KESPeriod 0, mkKESKeyPair (RawSeed 1 0 0 0 3))]
    (hashKey (vKey coldKey))
  where
    coldKey = mkDSIGNKeyPair 1

mkVRFKeyPair ::
  forall c.
  VRFAlgorithm (VRF c) =>
  Proxy c ->
  Word8 ->
  (Cardano.Ledger.Keys.SignKeyVRF c, Cardano.Ledger.Keys.VerKeyVRF c)
mkVRFKeyPair _ byte = (sk, VRF.deriveVerKeyVRF sk)
  where
    seed =
      Seed.mkSeedFromBytes $
        Strict.replicate
          (fromIntegral (VRF.seedSizeVRF (Proxy @(VRF c))))
          byte

    sk = VRF.genKeyVRF seed

-- | @mkKeyPair'@ from @Test.Cardano.Ledger.Shelley.Utils@ doesn't work for real
-- crypto:
-- <https://github.com/input-output-hk/cardano-ledger/issues/1770>
mkDSIGNKeyPair ::
  forall c kd.
  DSIGNAlgorithm (DSIGN c) =>
  Word8 ->
  KeyPair kd c
mkDSIGNKeyPair byte = KeyPair (VKey $ DSIGN.deriveVerKeyDSIGN sk) sk
  where
    seed =
      Seed.mkSeedFromBytes $
        Strict.replicate
          (fromIntegral (DSIGN.seedSizeDSIGN (Proxy @(DSIGN c))))
          byte

    sk = DSIGN.genKeyDSIGN seed

exampleHashHeader ::
  forall era.
  Reflect era =>
  Proof era ->
  HashHeader (Cardano.Ledger.Era.Crypto era)
exampleHashHeader proof = coerce $ mkDummyHash (Proxy @(HASH (Cardano.Ledger.Era.Crypto era))) 0

exampleProposedPParamsUpdates ::
  ( Reflect era
  ) =>
  Proof era ->
  ProposedPPUpdates era
exampleProposedPParamsUpdates proof@(Shelley _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 0)
      ((emptyPPUpdate proof) {_keyDeposit = SJust (Coin 100)})
exampleProposedPParamsUpdates proof@(Allegra _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 0)
      ((emptyPPUpdate proof) {_keyDeposit = SJust (Coin 100)})
exampleProposedPParamsUpdates proof@(Mary _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 0)
      ((emptyPPUpdate proof) {_keyDeposit = SJust (Coin 100)})
exampleProposedPParamsUpdates proof@(Alonzo _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 1)
      ((emptyPPUpdate proof) {AlonzoPP._maxBHSize = SJust 4000})
exampleProposedPParamsUpdates proof@(Babbage _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 1)
      ((emptyPPUpdate proof) {BabbagePP._maxBHSize = SJust 4000})
exampleProposedPParamsUpdates proof@(Conway _) =
  ProposedPPUpdates $
    Map.singleton
      (mkKeyHash 1)
      ((emptyPPUpdate proof) {ConwayPP._maxBHSize = SJust 4000})

exampleNonMyopicRewards ::
  forall c.
  CC.Crypto c =>
  Map
    (Either Coin (Credential 'Staking c))
    (Map (KeyHash 'StakePool c) Coin)
exampleNonMyopicRewards =
  Map.fromList
    [ (Left (Coin 100), Map.singleton (mkKeyHash 2) (Coin 3)),
      (Right (ScriptHashObj (mkScriptHash 1)), Map.empty),
      (Right (KeyHashObj (mkKeyHash 2)), Map.singleton (mkKeyHash 3) (Coin 9))
    ]

-- =====================================================================

-- | The EpochState has a field which is (PParams era). We need these
--     fields, a subset of the fields in PParams, in: startStep and createRUpd.
type UsesPP era =
  ( HasField "_d" (Core.PParams era) UnitInterval,
    HasField "_tau" (Core.PParams era) UnitInterval,
    HasField "_a0" (Core.PParams era) NonNegativeInterval,
    HasField "_rho" (Core.PParams era) UnitInterval,
    HasField "_nOpt" (Core.PParams era) Natural,
    HasField "_protocolVersion" (Core.PParams era) ProtVer
  )

-- | This is probably not a valid ledger. We don't care, we are only
-- interested in serialisation, not validation.
exampleNewEpochState ::
  forall era.
  ( Reflect era,
    Default (StashedAVVMAddresses era),
    Default (State (Core.EraRule "PPUP" era)),
    Core.EraTxOut era
  ) =>
  Proof era ->
  Core.Value era ->
  Core.PParams era ->
  Core.PParams era ->
  NewEpochState era
exampleNewEpochState proof value ppp pp =
  NewEpochState
    { nesEL = EpochNo 0,
      nesBprev = BlocksMade (Map.singleton (mkKeyHash 1) 10),
      nesBcur = BlocksMade (Map.singleton (mkKeyHash 2) 3),
      nesEs = epochState,
      nesRu = SJust rewardUpdate,
      nesPd = examplePoolDistr,
      stashedAVVMAddresses = def
    }
  where
    epochState :: EpochState era
    epochState =
      EpochState
        { esAccountState =
            AccountState
              { _treasury = Coin 10000,
                _reserves = Coin 1000
              },
          esSnapshots = emptySnapShots,
          esLState =
            LedgerState
              { lsUTxOState =
                  UTxOState
                    { _utxo =
                        UTxO $
                          Map.fromList
                            [ ( TxIn (TxId (mkDummySafeHash Proxy 1)) minBound,
                                Core.mkBasicTxOut addr value
                              )
                            ],
                      _deposited = Coin 1000,
                      _fees = Coin 1,
                      _ppups = def,
                      _stakeDistro = mempty
                    },
                lsDPState = def
              },
          esPrevPp = ppp,
          esPp = pp,
          esNonMyopic = def
        }
      where
        addr :: Addr (Cardano.Ledger.Era.Crypto era)
        addr =
          Addr
            Testnet
            (keyToCredential examplePayKey)
            (StakeRefBase (keyToCredential exampleStakeKey))

    rewardUpdate :: PulsingRewUpdate (Era.Crypto era)
    rewardUpdate = case proof of
      Shelley _ -> step
      Allegra _ -> step
      Mary _ -> step
      Alonzo _ -> step
      Babbage _ -> step
      Conway _ -> step
    step :: UsesPP era => PulsingRewUpdate (Era.Crypto era)
    step =
      ( startStep @era
          (EpochSize 432000)
          (BlocksMade (Map.singleton (mkKeyHash 1) 10))
          epochState
          (Coin 45)
          (activeSlotCoeff testGlobals)
          10
      )

keyToCredential :: CC.Crypto c => KeyPair r c -> Credential r c
keyToCredential = KeyHashObj . hashKey . vKey

examplePayKey :: CC.Crypto c => KeyPair 'Payment c
examplePayKey = mkDSIGNKeyPair 0

exampleStakeKey :: CC.Crypto c => KeyPair 'Staking c
exampleStakeKey = mkDSIGNKeyPair 1

examplePoolDistr :: forall c. PraosCrypto c => PoolDistr c
examplePoolDistr =
  PoolDistr $
    Map.fromList
      [ ( mkKeyHash 1,
          IndividualPoolStake
            1
            (hashVerKeyVRF (snd (vrf (exampleKeys @c))))
        )
      ]

exampleLedgerChainDepState :: forall c. CC.Crypto c => Word64 -> ChainDepState c
exampleLedgerChainDepState seed =
  ChainDepState
    { csProtocol =
        PrtclState
          ( Map.fromList
              [ (mkKeyHash 1, 1),
                (mkKeyHash 2, 2)
              ]
          )
          (mkNonceFromNumber seed)
          (mkNonceFromNumber seed),
      csTickn =
        TicknState
          NeutralNonce
          (mkNonceFromNumber seed),
      csLabNonce =
        mkNonceFromNumber seed
    }

-- | This is not a valid transaction. We don't care, we are only interested in
-- serialisation, not validation.
exampleTx ::
  forall era.
  ( Reflect era,
    Core.EraTx era
  ) =>
  Proof era ->
  (Core.TxBody era -> KeyPairWits era -> Core.Witnesses era) ->
  Core.TxBody era ->
  Core.AuxiliaryData era ->
  Core.Tx era
exampleTx proof mkWitnesses txBody auxData =
  genericTx proof
    [ Just (Body txBody)
    , Just (Witnesses  (mkWitnesses txBody keyPairWits))
    , Just (AuxData' [auxData])
    ]    
  where
    keyPairWits :: KeyPairWits era
    keyPairWits =
      [ asWitness examplePayKey,
        asWitness exampleStakeKey,
        asWitness $ cold (exampleKeys @(Cardano.Ledger.Era.Crypto era) @'StakePool)
      ]


exampleTxBody :: Era era => Proof era -> Core.TxBody era
exampleTxBody proof =
   genericTxBody proof
     [ Just (specialize @Core.EraTxOut proof
                (Outputs' [ Core.mkBasicTxOut (mkAddr (examplePayKey, exampleStakeKey))
                                              (inject (Coin 100000)) ]))
     , Just (Certs exampleCerts)
     , Just (Wdrls exampleWithdrawals)
     , Just (Txfee (Coin 3))
     , if (Some proof) == (Some (Shelley Mock))
          then Just (TTL (SlotNo 10)) else Nothing
     , Just (Update' (Update exampleProposedPPUpdates (EpochNo 0)))
     ]


{-
  ShelleyTxBody
    exampleTxIns
    ( StrictSeq.fromList
        [ ShelleyTxOut ( mkBasicTxOut (mkAddr (examplePayKey, exampleStakeKey)) (Coin 100000))
        ]
    )
    exampleCerts
    exampleWithdrawals
    (Coin 3)
    (SlotNo 10)
    (SJust (Update exampleProposedPPUpdates (EpochNo 0)))
    (SJust auxiliaryDataHash)
  where
    -- Dummy hash to decouple from the auxiliaryData in 'exampleTx'.
    auxiliaryDataHash :: AuxiliaryDataHash StandardCrypto
    auxiliaryDataHash =
      AuxiliaryDataHash $ mkDummySafeHash (Proxy @StandardCrypto) 30
-}


exampleCerts :: CC.Crypto c => StrictSeq (DCert c)
exampleCerts =
  StrictSeq.fromList
    [ DCertDeleg (RegKey (keyToCredential exampleStakeKey)),
      DCertPool (RegPool examplePoolParams),
      DCertMir $
        MIRCert ReservesMIR $
          StakeAddressesMIR $
            Map.fromList
              [ (keyToCredential (mkDSIGNKeyPair 2), DeltaCoin 110)
              ]
    ]

examplePoolParams :: forall c. CC.Crypto c => PoolParams c
examplePoolParams =
  PoolParams
    { _poolId = hashKey $ vKey $ cold poolKeys,
      _poolVrf = hashVerKeyVRF $ snd $ vrf poolKeys,
      _poolPledge = Coin 1,
      _poolCost = Coin 5,
      _poolMargin = unsafeBoundRational 0.1,
      _poolRAcnt = RewardAcnt Testnet (keyToCredential exampleStakeKey),
      _poolOwners = Set.singleton $ hashKey $ vKey exampleStakeKey,
      _poolRelays = StrictSeq.empty,
      _poolMD =
        SJust $
          PoolMetadata
            { _poolMDUrl = fromJust $ textToUrl "consensus.pool",
              _poolMDHash = "{}"
            }
    }
  where
    poolKeys = exampleKeys @c @'StakePool

exampleWithdrawals :: CC.Crypto c => Wdrl c
exampleWithdrawals =
  Wdrl $
    Map.fromList
      [ (_poolRAcnt examplePoolParams, Coin 100)
      ]
-- ==========================================

testShelleyGenesis = undefined


-- | Build a Tx from a list of maybe fields. The maube is usfull because sometimes we
--   only want to add a field in a particular era, so we might say something like this
-- genericTx proof
--  [Just field1
--  , if (Some proof) >= Mary Mock then Just field2 else Nothing
--  , Just field3
--  ]
genericTx:: Proof era -> [Maybe (TxField era)] -> Core.Tx era
genericTx proof xs = newTx proof (foldl' accum [] xs)
  where accum ans Nothing = ans
        accum ans (Just field) = field : ans


-- | Build a Tx from a list of maybe fields. The maube is usfull because sometimes we
--   only want to add a field in a particular era, so we might say something like this
-- genericTxBody proof
--  [Just field1
--  , if (Some proof) >= Mary Mock then Just field2 else Nothing
--  , Just field3
--  ]
genericTxBody:: Era era => Proof era -> [Maybe (TxBodyField era)] -> Core.TxBody era
genericTxBody proof xs = specialize @Core.EraTxBody proof (newTxBody proof (foldl' accum [] xs))
  where accum ans Nothing = ans
        accum ans (Just field) = field : ans