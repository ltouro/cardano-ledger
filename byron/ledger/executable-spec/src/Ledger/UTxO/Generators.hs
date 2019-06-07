{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ledger.UTxO.Generators where

import Control.Applicative (empty)
import Data.Bitraversable (bitraverse)
import qualified Data.Map.Strict as M

import Ledger.Core hiding (Range, range)
import Ledger.UTxO

import Hedgehog (Gen, Property, Range, (===), assert, forAll, property)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Hedgehog.Internal.Gen
  (atLeast, ensure, mapGenT, runDiscardEffectT, toTree, toTreeMaybeT)
import Hedgehog.Internal.Tree (NodeT(..), TreeT(..), treeValue)
import qualified Hedgehog.Internal.Tree as Tree


--------------------------------------------------------------------------------
-- Initial TxOut generator
--------------------------------------------------------------------------------

-- | Generate a set of initial 'TxOut's from a set of 'Addr's
genInitialTxOuts :: [Addr] -> Gen [TxOut]
genInitialTxOuts = Gen.filter (not . null)
  . genTraverseSubsequence (\a -> TxOut a <$> genLovelace)

genLovelace :: Gen Lovelace
genLovelace = Lovelace . fromIntegral <$> Gen.word32 (Range.linear 1 10000)

-- | Generate a subsequence of a list of values and traverse the subsequence
--   with a generator producer
genTraverseSubsequence :: (a -> Gen b) -> [a] -> Gen [b]
genTraverseSubsequence genA as =
  mapGenT (TreeT . (interleaveTreeT . nodeValue =<<) . runTreeT) $ do
    sub <- Gen.subsequence as
    traverse (toTreeMaybeT . genA) sub

-- | Generate a list using 'genTraverseSubsequence'
genList :: Range Int -> Gen a -> Gen [a]
genList range gen = Gen.sized $ \gSize ->
  ensure (atLeast $ Range.lowerBound gSize range) $ genTraverseSubsequence
    (const gen)
    (replicate (Range.upperBound gSize range) ())

-- | Temporarily defined here until hedgehog exposes this function
interleaveTreeT :: Monad m => [TreeT m a] -> m (NodeT m [a])
interleaveTreeT = fmap Tree.interleave . traverse runTreeT


--------------------------------------------------------------------------------
-- Tx generator
--------------------------------------------------------------------------------

-- | Generate a valid transaction from a given 'UTxO'
genTxFromUTxO
  :: [Addr]
  -- ^ List of addresses to choose from as recipients of the transaction
  -- outputs.
  -> (Tx -> Lovelace)
  -- ^ Fee calculation
  -> UTxO
  -- ^ UTxO used to determine which unspent outputs can be used in the
  -- transaction.
  -> Gen Tx
genTxFromUTxO addrs txfee utxo = subtractFees txfee $ uncurry Tx <$> Gen.filter
  (not . null . fst)
  (genInputOutput
    (M.keys $ unUTxO utxo)
    (maybe 0 (unLovelace . value) . flip M.lookup (unUTxO utxo))
    (fmap (. Lovelace) $ TxOut <$> Gen.element addrs)
    (unLovelace . value)
    (\f out -> out { value = Lovelace . f . unLovelace $ value out })
  )

-- | Ensure we generate a 'Tx' which utilizes enough 'Lovelace' via its inputs
-- to cover its outputs as well as the transaction fee.
-- This function potentially removes outputs from the generated transaction
-- such that it is able to cover the transaction fee.
subtractFees :: (Tx -> Lovelace) -> Gen Tx -> Gen Tx
subtractFees txfee = fmap subtractFees'
  -- In Byron, we must disallow empty outputs in transactions in order to
  -- maintain compatability with the `cardano-sl` implementation.
  -- In order to do this, while also potentially removing some outputs from
  -- the transaction to ensure that the transaction fee is covered, we only
  -- generate transactions whose sum of outputs is greater than the
  -- transaction fee. This way, we ensure that there will always remain at
  -- least 1 'Lovelace' in the outputs.
  . Gen.filter (\tx -> sum (value <$> outputs tx) > txfee tx)
 where
  subtractFees' tx =
    tx { outputs = subFromList (txfee tx) value updateValue (outputs tx) }
  updateValue f out = out { value = f (value out) }

-- | A property to test that the entire shrink tree generated by
--   'genInputOutput' maintains the invariant that the inputs and outputs have
--   equal sums
--
--   NB: This uses small values for the list and values, because we force the
--   entire shrink tree, which can grow very large
propGenInputOutput :: Property
propGenInputOutput = property $ do
  ins <- forAll $ Gen.list (Range.linear 0 5) (Gen.integral (Range.linear 0 5))
  insOutsTree <- forAll $ toTree (genInputOutput ins id (pure id) id id)
  assert $ all (\(ins', outs) -> sum ins' == sum outs) insOutsTree

-- | Generate a subsequence of the inputs and split the value into a number of
--   outputs
--
--   The shrink tree maintains the invariant that the sum of the inputs is equal
--   to the sum of the outputs. This is generalised to any type of input where
--   we can view the contained value, and type of output where we can generate
--   the type from a value, and view and modify the contained value
genInputOutput
  :: [input]
  -- ^ List of input to take a subsequence of
  -> (input -> Integer)
  -- ^ A view of the value in the input used to preserve the invariant
  -> Gen (Integer -> output)
  -- ^ A applicative generator for an output given a value
  -> (output -> Integer)
  -- ^ A view of the value in the output used to preserve the invariant
  -> ((Integer -> Integer) -> output -> output)
  -- ^ An update function for the output value used to preserve the invariant
  -> Gen ([input], [output])
genInputOutput ins inValue genOut outValue modifyOutValue =
  mapGenT
      ( TreeT
      . (interleaveInputOutputTreeT inValue outValue modifyOutValue
          . nodeValue =<<
        )
      . runTreeT
      )
    $ do
        insTree <- toTreeMaybeT (Gen.subsequence ins)
        case treeValue (runDiscardEffectT insTree) of
          Nothing -> empty
          Just is -> (,) <$> pure insTree <*> toTreeMaybeT
            (genSplitValue
              (sum $ inValue <$> is)
              genOut
              outValue
              modifyOutValue
            )

-- | Used as part of 'genInputOutput', so see there for details of the arguments
interleaveInputOutputTreeT
  :: Monad m
  => (input -> Integer)
  -> (output -> Integer)
  -> ((Integer -> Integer) -> output -> output)
  -> (TreeT m [input], TreeT m [output])
  -> m (NodeT m ([input], [output]))
interleaveInputOutputTreeT inValue outValue modifyOutValue =
  fmap (interleaveInputOutput inValue outValue modifyOutValue)
    . bitraverse runTreeT runTreeT

-- | Used as part of 'genInputOutput', so see there for details of the arguments
interleaveInputOutput
  :: Monad m
  => (input -> Integer)
  -> (output -> Integer)
  -> ((Integer -> Integer) -> output -> output)
  -> (NodeT m [input], NodeT m [output])
  -> NodeT m ([input], [output])
interleaveInputOutput inValue outValue modifyOutValue (as, bs) =
  case nodeValue as of
    [] -> NodeT ([], []) []
    _  -> NodeT
      (nodeValue as, nodeValue bs)
      (  shrinkLeftPreserving inValue outValue modifyOutValue (as, bs)
      ++ shrinkRight inValue outValue modifyOutValue (as, bs)
      )

-- | Used as part of 'genInputOutput', so see there for details of the arguments
shrinkRight
  :: Monad m
  => (input -> Integer)
  -> (output -> Integer)
  -> ((Integer -> Integer) -> output -> output)
  -> (NodeT m [input], NodeT m [output])
  -> [TreeT m ([input], [output])]
shrinkRight inValue outValue modifyOutValue (xs, ys1) = do
  ys2 <- nodeChildren ys1
  pure . TreeT $ do
    ys3 <- runTreeT ys2
    pure $ interleaveInputOutput inValue outValue modifyOutValue (xs, ys3)

-- | Shrink the left value of a tuple, preserving the total value stored in the
--   right value
--
--   Used as part of 'genInputOutput', so see there for details of the arguments
shrinkLeftPreserving
  :: Monad m
  => (input -> Integer)
  -> (output -> Integer)
  -> ((Integer -> Integer) -> output -> output)
  -> (NodeT m [input], NodeT m [output])
  -> [TreeT m ([input], [output])]
shrinkLeftPreserving inValue outValue modifyOutValue (xs1, ys1) = do
  xs2 <- nodeChildren xs1
  pure . TreeT $ do
    xs3 <- runTreeT xs2
    let
      lost = sum (inValue <$> nodeValue xs1) - sum (inValue <$> nodeValue xs3)
      ys2  = subFromList lost outValue modifyOutValue <$> ys1
    pure $ interleaveInputOutput inValue outValue modifyOutValue (xs3, ys2)

-- | Remove total value from a list, removing from the front
subFromList
  :: (Num n, Ord n)
  => n
  -- ^ The total value to remove from the list
  -> (a -> n)
  -- ^ A view into the value contained in type @a@
  -> ((n -> n) -> a -> a)
  -- ^ A modifier for the value contained in type @a@
  -> [a]
  -- ^ The list of @a@s to remove value from
  -> [a]
subFromList n getVal modifyVal = go n
  where
  go 0  x        = x
  go _  []       = []
  go n' (x : xs) = if getVal x > n'
    then modifyVal (subtract n') x : xs
    else go (n' - getVal x) xs


-- | A property to check that `genSplitValue` does indeed preserve the input
propGenSplitValue :: Property
propGenSplitValue = property $ do
  n    <- forAll $ Gen.integral (Range.linear 1 10000)
  ints <- forAll $ genSplitValue n (pure id) id id
  sum ints === n

-- | Given an input value and functions to generate, view, and update some type
--   'a' based on that value, split the input into a number of 'a's, preserving
--   the value throughout the shrink tree
genSplitValue
  :: Integer
  -- ^ Total value to divide into outputs
  -> Gen (Integer -> a)
  -- ^ Applicative generator for an output given a value
  -> (a -> Integer)
  -- ^ A view of the value in the output used to preserve the invariant
  -> ((Integer -> Integer) -> a -> a)
  -- ^ A modifier for the value in the output used to preserve the invariant
  -> Gen [a]
genSplitValue n genA getValue modifyValue =
  mapGenT
      ( TreeT
      . (interleaveTreeTPreserving getValue modifyValue . nodeValue =<<)
      . runTreeT
      )
    $ go n []
 where
  go 0    acc = pure acc
  go left acc = do
    mTree <- toTreeMaybeT (genA <*> Gen.integral (Range.constant 1 left))
    case treeValue (runDiscardEffectT mTree) of
      Nothing -> empty
      Just a  -> go (left - getValue a) (mTree : acc)

-- | Used as part of 'genSplitValue', so see there for details of the arguments
interleaveTreeTPreserving
  :: Monad m
  => (a -> Integer)
  -> ((Integer -> Integer) -> a -> a)
  -> [TreeT m a]
  -> m (NodeT m [a])
interleaveTreeTPreserving getValue modifyValue =
  fmap (interleavePreserving getValue modifyValue) . traverse runTreeT

-- | Used as part of 'genSplitValue', so see there for details of the arguments
interleavePreserving
  :: Monad m
  => (a -> Integer)
  -> ((Integer -> Integer) -> a -> a)
  -> [NodeT m a]
  -> NodeT m [a]
interleavePreserving getValue modifyValue ts = NodeT
  (fmap nodeValue ts)
  (  dropOnePreserving getValue modifyValue ts
  ++ shrinkOnePreserving getValue modifyValue ts
  )

-- | Drop one of the outputs, preserving the invariant by moving its value to
--   the left
--
--   Used as part of 'genSplitValue', so see there for details of the arguments
dropOnePreserving
  :: Monad m
  => (a -> Integer)
  -> ((Integer -> Integer) -> a -> a)
  -> [NodeT m a]
  -> [TreeT m [a]]
dropOnePreserving getValue modifyValue ts = do
  (ws, x, y, zs) <- viewTwo ts
  let x' = modifyValue (+ getValue (nodeValue y)) <$> x
  pure . TreeT . pure $ interleavePreserving
    getValue
    modifyValue
    (ws ++ [x'] ++ zs)

-- | Shrink a value in a list, preserving the total value by moving the lost
--   value to the left
--
--   Used as part of 'genSplitValue', so see there for details of the arguments
shrinkOnePreserving
  :: Monad m
  => (a -> Integer)
  -> ((Integer -> Integer) -> a -> a)
  -> [NodeT m a]
  -> [TreeT m [a]]
shrinkOnePreserving getValue modifyValue ts = do
  (ws, x, y0, zs) <- viewTwo ts
  y1 <- nodeChildren y0
  pure . TreeT $ do
    y2 <- runTreeT y1
    let
      lost = getValue (nodeValue y0) - getValue (nodeValue y2)
      x'   = modifyValue (+ lost) <$> x
    pure $ interleavePreserving getValue modifyValue (ws ++ [x', y2] ++ zs)

-- | All the ways of choosing two consecutive values from a list
viewTwo :: [a] -> [([a], a, a, [a])]
viewTwo = \case
  []          -> []
  [      _ ]  -> []
  x : x' : xs -> ([], x, x', xs)
    : fmap (\(as, b, c, ds) -> (x : as, b, c, ds)) (viewTwo (x' : xs))
