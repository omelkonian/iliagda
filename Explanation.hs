{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Explanation where

import Data.Text (Text)

data Qty = Long | Short
  deriving (Eq, Show)

data Ground
  = Diphthong Char Char
  | LongVowel Char
  | Circumflex Char
  deriving Show

data Reach = Within | NextSyllable | NextWord
  deriving (Eq, Show)

data Position
  = DoubleConsonant Char
  | TwoConsonants Char Char Reach
  deriving Show

data Match = Whole | Stem
  deriving (Eq, Show)

data Rule
  = Unwritten Char Integer Text
  | LongByNature Ground
  | ShortByNature Char
  | ByLexicon Qty Text Match
  | R1160 Char Text
  | R1161 Char Text
  | R1162 Char Text
  | R1163 Char Text
  | Merge Text Text Bool
  | R522 Char Position
  | R1173 Qty Text Char Bool
  | R524 Qty Char Char Char Bool
  | R1168 Char Char Char
  | R1167a
  | R1167b Integer
  | R1184
  deriving Show

data Fact = Fact Integer Rule (Maybe Qty) (Maybe Integer)
  deriving Show

data Explanation = Explanation Integer [Text] [Integer] [Qty] [Fact]
  deriving Show

-- ** stable identifiers, for tallies and for the wire format

ruleName :: Rule -> Text
ruleName = \case
  Unwritten{}     -> "unwritten"
  LongByNature{}  -> "longByNature"
  ShortByNature{} -> "shortByNature"
  ByLexicon{}     -> "byLexicon"
  R1160{}         -> "1160"
  R1161{}         -> "1161"
  R1162{}         -> "1162"
  R1163{}         -> "1163"
  Merge{}         -> "merge"
  R522{}          -> "522"
  R1173{}         -> "1173"
  R524{}          -> "524"
  R1168{}         -> "1168"
  R1167a          -> "1167a"
  R1167b{}        -> "1167b"
  R1184           -> "1184"

ruleNames :: [Text]
ruleNames =
  [ "unwritten", "longByNature", "shortByNature", "byLexicon"
  , "1160", "1161", "1162", "1163"
  , "merge", "522", "1173", "524", "1168", "1167a", "1167b", "1184" ]
