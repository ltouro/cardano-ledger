{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Defines reusable abstractions for testing Roundtrip properties of CBOR instances
module Data.Roundtrip
  ( roundTrip,
    roundTrip',
    roundTripWithTwiddling,
    embedTrip,
    embedTrip',
    roundTripAnn,
    roundTripAnnWithTwiddling,
    embedTripAnn,
    RoundTripResult,
  )
where

import Cardano.Binary
  ( Annotator (..),
    FromCBOR (fromCBOR),
    FullByteString (Full),
    ToCBOR (toCBOR),
  )
import Codec.CBOR.Decoding (Decoder)
import Codec.CBOR.Encoding (Encoding)
import Codec.CBOR.Read
  ( DeserialiseFailure,
    deserialiseFromBytes,
  )
import Codec.CBOR.Term (Term (..), decodeTerm, encodeTerm)
import Codec.CBOR.Write (toLazyByteString)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy as Lazy
import Data.Text (Text)
import qualified Data.Text.Lazy as T
import Test.QuickCheck (Gen, elements, shuffle)

-- | Randomly mutates a CBOR AST so that semantics are preserved.
--
-- Currently it may:
--  * change a finite length list/map/bytestring to an indefinite length one and vice versa
--  * shuffle around key-value pairs in a map
--
-- It does not yet do the following:
--  * storing a word as a larger value than necessary (e.g. storing a Word16 as a Word32)
twiddleTerm :: Term -> Gen Term
twiddleTerm (TBytes bs) = twiddleByteString bs
twiddleTerm (TBytesI bs) = twiddleByteString $ LBS.toStrict bs
twiddleTerm (TString txt) = twiddleText txt
twiddleTerm (TStringI txt) = twiddleText $ T.toStrict txt
twiddleTerm (TList tes) = twiddleList tes
twiddleTerm (TListI tes) = twiddleList tes
twiddleTerm (TMap x0) = twiddleMap x0
twiddleTerm (TMapI x0) = twiddleMap x0
twiddleTerm (TTagged wo te) = TTagged wo <$> twiddleTerm te
twiddleTerm t = pure t

twiddleEncoding :: Encoding -> Gen Encoding
twiddleEncoding enc = encodeTerm <$> twiddleTerm term
  where
    term = case deserialiseFromBytes decodeTerm $ toLazyByteString enc of
      Left err -> error $ "Failed to deserialize: " <> show err
      Right (_, x) -> x

twiddleList :: [Term] -> Gen Term
twiddleList l = do
  f <- elements [TList, TListI]
  pure $ f l

twiddleMap :: [(Term, Term)] -> Gen Term
twiddleMap m = do
  -- Elements of a map do not have to be in a specific order,
  -- so we shuffle them
  m' <- shuffle m
  f <- elements [TMap, TMapI]
  pure $ f m'

twiddleByteString :: ByteString -> Gen Term
twiddleByteString bs = do
  f <- elements [TBytes, TBytesI . fromStrict]
  pure $ f bs

twiddleText :: Text -> Gen Term
twiddleText t = do
  f <- elements [TString, TStringI . T.fromStrict]
  pure $ f t

-- =====================================================================

type RoundTripResult t = Either Codec.CBOR.Read.DeserialiseFailure (Lazy.ByteString, t)

roundTrip :: (ToCBOR t, FromCBOR t) => t -> RoundTripResult t
roundTrip s = deserialiseFromBytes fromCBOR (toLazyByteString (toCBOR s))

roundTripWithTwiddling :: (ToCBOR t, FromCBOR t) => t -> Gen (RoundTripResult t)
roundTripWithTwiddling s = do
  tw <- twiddleEncoding $ toCBOR s
  pure . deserialiseFromBytes fromCBOR $ toLazyByteString tw

roundTrip' :: (t -> Encoding) -> (forall s. Decoder s t) -> t -> RoundTripResult t
roundTrip' enc dec t = deserialiseFromBytes dec (toLazyByteString (enc t))

roundTripAnn :: (ToCBOR t, FromCBOR (Annotator t)) => t -> RoundTripResult t
roundTripAnn s =
  let bytes = toLazyByteString (toCBOR s)
   in case deserialiseFromBytes fromCBOR bytes of
        Left err -> Left err
        Right (leftover, Annotator f) -> Right (leftover, f (Full bytes))

roundTripAnnWithTwiddling ::
  ( ToCBOR t,
    FromCBOR (Annotator t)
  ) =>
  t ->
  Gen (RoundTripResult t)
roundTripAnnWithTwiddling s = do
  tw <- twiddleEncoding $ toCBOR s
  let bytes = toLazyByteString tw
  pure $ case deserialiseFromBytes fromCBOR bytes of
    Left err -> Left err
    Right (leftover, Annotator f) -> Right (leftover, f (Full bytes))

-- | Can we serialise a type, and then deserialise it as something else?
embedTrip :: (ToCBOR t, FromCBOR s) => t -> RoundTripResult s
embedTrip s = deserialiseFromBytes fromCBOR (toLazyByteString (toCBOR s))

embedTrip' :: (s -> Encoding) -> (forall x. Decoder x t) -> s -> RoundTripResult t
embedTrip' enc dec s = deserialiseFromBytes dec (toLazyByteString (enc s))

embedTripAnn :: forall s t. (ToCBOR t, FromCBOR (Annotator s)) => t -> RoundTripResult s
embedTripAnn s =
  let bytes = toLazyByteString (toCBOR s)
   in case deserialiseFromBytes fromCBOR bytes of
        Left err -> Left err
        Right (leftover, Annotator f) -> Right (leftover, f (Full bytes))
