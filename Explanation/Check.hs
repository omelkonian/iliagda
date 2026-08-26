{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Explanation.Check (violations) where

import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as T
import Explanation
import qualified MAlonzo.Code.Iliagda.Explanation as AE

violations :: Explanation -> [Text]
violations (Explanation _ sys ws qs fs) = concat
  [ [ "field lengths disagree: " <> tshow (length sys) <> " written syllables, "
      <> tshow (length qs) <> " quantities, " <> tshow nmerges <> " merges, "
      <> tshow (sum ws) <> " in words"
    | length sys /= length qs + nmerges || sum ws /= fromIntegral (length sys) ]
  , [ "locus " <> tshow i <> " out of range" | Fact i _ _ _ <- fs, i < 0 || i >= n ]
  , [ "ref " <> tshow r <> " out of range" | Fact _ _ _ (Just r) <- fs, r < 0 || r >= nf ]
  , [ "fact " <> tshow k <> " cites itself"
    | (k, Fact _ _ _ (Just r)) <- zip [0 ..] fs, r == k ]
  , [ "fact " <> tshow k <> " cites " <> tshow r <> ", which follows it"
    | (k, Fact _ _ _ (Just r)) <- zip [0 :: Integer ..] fs, r > k ]
  , [ "fact " <> tshow k <> " states " <> tshow mq <> " but its rule asserts "
      <> tshow (AE.ruleQuantity r)
    | (k, Fact _ r mq _) <- zip [0 :: Integer ..] fs, mq /= AE.ruleQuantity r ]
  , [ "text facts not in ascending locus order" | textLoci /= sort textLoci ]
  , [ "quantity fact " <> tshow k <> " at locus " <> tshow j
      <> " precedes locus " <> tshow i <> ", but nothing cites it"
    | ((k, j), (_, i)) <- zip qtyIx (drop 1 qtyIx), i < j, not (cited k) ]
  , [ "a text fact follows a quantity fact" | any isText (dropWhile isText fs) ]
  , [ "locus " <> tshow i <> ": fact " <> tshow k <> " reaffirms " <> mark a
    | (i, k, a) <- reaffirmations ]
  , [ "locus " <> tshow i <> ": last fact says " <> mark a <> " but the mark is " <> mark b
    | (i, a, b) <- disagreements ]
  ]
  where
  n  = fromIntegral (length sys)
  nf = fromIntegral (length fs)
  isText (Fact _ _ mq _) = mq == Nothing
  textLoci = [ i | f@(Fact i _ _ _) <- fs, isText f ]
  -- Quantity facts run in locus order, save that a fact may be pulled ahead of a lower
  -- locus to precede the fact that cites it. So an inversion is a violation only when
  -- nothing cites the fact that jumped.
  qtyIx = [ (k, i) | (k, f@(Fact i _ _ _)) <- zip [0 :: Integer ..] fs, not (isText f) ]
  cited k = or [ r == k | Fact _ _ _ (Just r) <- fs ]
  merges = [ j | Fact j Merge{} _ _ <- fs ]
  nmerges = length merges
  metrical i = i - fromIntegral (length [ j | j <- merges, j <= i ])
  asserted = [ (k, i, q) | (k, Fact i r mq _) <- zip [0 :: Integer ..] fs
                         , Just q <- [mq], not (isMerge r) ]
  reaffirmations =
    [ (i, k, q)
    | i <- [0 .. n - 1]
    , let chain = [ (k, q) | (k, j, q) <- asserted, j == i ]
    , ((k, q), (_, q')) <- zip (drop 1 chain) chain
    , q == q' ]
  disagreements =
    [ (i, q, qs !! fromInteger (metrical i))
    | i <- [0 .. n - 1]
    , metrical i >= 0, metrical i < fromIntegral (length qs)
    , (_, _, q) <- take 1 (reverse [ a | a@(_, j, _) <- asserted, j == i ])
    , q /= qs !! fromInteger (metrical i) ]
  isMerge = \case Merge{} -> True; _ -> False
  mark = \case Long -> "\9472"; Short -> "\183"

tshow :: Show a => a -> Text
tshow = T.pack . show
