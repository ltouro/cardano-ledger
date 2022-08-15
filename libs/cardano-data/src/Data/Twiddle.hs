module Data.Twiddle
  ( Twiddle,
    unTwiddle,
  )
where

import Cardano.Binary (Encoding, ToCBOR (..))
import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Term (Term (..), decodeTerm, encodeTerm)
import Codec.CBOR.Write (toLazyByteString)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (fromStrict)
import qualified Data.ByteString.Lazy as LBS
import Data.Text (Text)
import qualified Data.Text.Lazy as T
import Data.Typeable (Typeable)
import Test.QuickCheck (Arbitrary (..), Gen, elements, shuffle)

data Twiddle a = Twiddle !a !Encoding

instance (Arbitrary a, ToCBOR a) => Arbitrary (Twiddle a) where
  arbitrary = do
    x <- arbitrary
    enc' <- twiddleEncoding $ toCBOR x
    pure $ Twiddle x enc'

instance Typeable a => ToCBOR (Twiddle a) where
  toCBOR (Twiddle _ x) = x

instance Show a => Show (Twiddle a) where
  show (Twiddle x _) = "Twiddle " <> show x

instance Eq a => Eq (Twiddle a) where
  (Twiddle x _) == (Twiddle y _) = x == y

unTwiddle :: Twiddle a -> a
unTwiddle (Twiddle x _) = x

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
