{-# LANGUAGE PatternSynonyms #-}

module Test.Cardano.Chain.Block.Gen
  ( genBlockSignature
  , genHeaderHash
  , genHeader
  , genBody
  , genProof
  , genToSign
  , genBlock
  , genBlockWithEpochSlots
  , genBoundaryValidationData
  )
where

import Cardano.Prelude

import Data.Coerce (coerce)
import Hedgehog (Gen)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Cardano.Chain.Block
  ( ABlockSignature(..)
  , Block
  , BlockSignature
  , Body
  , BoundaryValidationData(..)
  , pattern Body
  , Header
  , HeaderHash
  , Proof(..)
  , ToSign(..)
  , hashHeader
  , mkBlockExplicit
  , mkHeaderExplicit
  )
import Cardano.Chain.Delegation (mkCertificate)
import Cardano.Chain.Genesis (GenesisHash(..))
import Cardano.Chain.Slotting
  (EpochNumber(..), EpochSlots, WithEpochSlots(WithEpochSlots))
import Cardano.Chain.Ssc (SscPayload(..), SscProof(..))
import Cardano.Crypto
  ( ProtocolMagicId
  , SignTag(SignBlock)
  , noPassSafeSigner
  , safeToVerification
  , sign
  , toVerification
  )

import Test.Cardano.Chain.Common.Gen (genChainDifficulty)
import qualified Test.Cardano.Chain.Delegation.Gen as Delegation
import Test.Cardano.Chain.Slotting.Gen
  (genEpochNumber, genEpochSlots, genSlotNumber, genEpochAndSlotCount)
import Test.Cardano.Chain.UTxO.Gen (genTxPayload, genTxProof)
import qualified Test.Cardano.Chain.Update.Gen as Update
import Test.Cardano.Crypto.Gen
  ( genAbstractHash
  , genSafeSigner
  , genSigningKey
  , genTextHash
  )


genBlockSignature :: ProtocolMagicId -> EpochSlots -> Gen BlockSignature
genBlockSignature pm epochSlots =
  mkBlockSignature
    <$> genSafeSigner
    <*> genSigningKey
    <*> genEpochNumber
    <*> genToSign pm epochSlots
 where
  mkBlockSignature issuerSafeSigner delegateSK epoch toSign =
    let
      cert =
        mkCertificate pm issuerSafeSigner (toVerification delegateSK) epoch
      issuerVK = safeToVerification issuerSafeSigner
      sig      = sign pm (SignBlock issuerVK) delegateSK toSign
    in ABlockSignature cert sig

genHeaderHash :: Gen HeaderHash
genHeaderHash = coerce <$> genTextHash

genBody :: ProtocolMagicId -> Gen Body
genBody pm =
  Body
    <$> genTxPayload pm
    <*> pure SscPayload
    <*> Delegation.genPayload pm
    <*> Update.genPayload pm

genHeader :: ProtocolMagicId -> EpochSlots -> Gen Header
genHeader protocolMagicId epochSlots =
  mkHeaderExplicit'
    <$> genHeaderHash
    <*> genChainDifficulty
    <*> genSlotNumber
    <*> genBody protocolMagicId
    <*> Update.genProtocolVersion
    <*> Update.genSoftwareVersion
    <*> genSigningKey
 where
  mkHeaderExplicit'
    headerHash
    chainDifficulty
    slotNumber
    body
    protocolVersion
    softwareVersion
    signingKey =
      mkHeaderExplicit
        protocolMagicId
        headerHash
        chainDifficulty
        epochSlots
        slotNumber
        signingKey
        (mkCertificate
          protocolMagicId
          (noPassSafeSigner signingKey)
          (toVerification signingKey)
          (EpochNumber 0)
        )
        body
        protocolVersion
        softwareVersion

genProof :: ProtocolMagicId -> Gen Proof
genProof pm =
  Proof
    <$> genTxProof pm
    <*> pure SscProof
    <*> genAbstractHash (Delegation.genPayload pm)
    <*> Update.genProof pm

genToSign :: ProtocolMagicId -> EpochSlots -> Gen ToSign
genToSign pm epochSlots =
  ToSign
    <$> (mkAbstractHash <$> genHeader pm epochSlots)
    <*> genProof pm
    <*> genEpochAndSlotCount epochSlots
    <*> genChainDifficulty
    <*> Update.genProtocolVersion
    <*> Update.genSoftwareVersion
 where
  mkAbstractHash :: Header -> HeaderHash
  mkAbstractHash = hashHeader epochSlots

genBlockWithEpochSlots :: ProtocolMagicId -> Gen (WithEpochSlots Block)
genBlockWithEpochSlots pm = do
  epochSlots <- genEpochSlots
  WithEpochSlots epochSlots <$> genBlock pm epochSlots

genBlock :: ProtocolMagicId -> EpochSlots -> Gen Block
genBlock protocolMagicId epochSlots =
  mkBlockExplicit'
    <$> Update.genProtocolVersion
    <*> Update.genSoftwareVersion
    <*> genHeaderHash
    <*> genChainDifficulty
    <*> genSlotNumber
    <*> genBody protocolMagicId
    <*> genSigningKey
 where
  mkBlockExplicit'
    protocolVersion
    softwareVersion
    headerHash
    chainDifficulty
    slotNumber
    body
    signingKey =
      mkBlockExplicit
        protocolMagicId
        protocolVersion
        softwareVersion
        headerHash
        chainDifficulty
        epochSlots
        slotNumber
        signingKey
        (mkCertificate
          protocolMagicId
          (noPassSafeSigner signingKey)
          (toVerification signingKey)
          (EpochNumber 0)
        )
        body

genBoundaryValidationData :: Gen (BoundaryValidationData ())
genBoundaryValidationData = do
    (epoch, hash) <- genBVDHash
    BoundaryValidationData
      <$> pure 0
      <*> pure hash
      <*> pure epoch
      <*> genChainDifficulty
      <*> pure ()
  where
    genBVDHash = Gen.choice
      [ ((,) <$> Gen.word64 (Range.constantFrom 10 1 100)
             <*> (Right <$> genHeaderHash))
      , ((,) <$> pure 0
             <*> (Left . GenesisHash . coerce <$> genTextHash)
        )
      ]
