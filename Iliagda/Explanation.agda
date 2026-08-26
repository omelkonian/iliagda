module Iliagda.Explanation where

open import Iliagda.Init

{-# FOREIGN GHC import qualified Explanation as E #-}

Ix Ref : Type
Ix  = ℕ
Ref = ℕ

data Qty : Type where
  long short : Qty

instance
  DecEq-Qty : DecEq Qty
  DecEq-Qty ._≟_ = λ where
    long  long  → yes refl
    long  short → no λ ()
    short long  → no λ ()
    short short → yes refl

data Ground : Type where
  diphthong  : Char → Char → Ground
  longVowel  : Char → Ground
  circumflex : Char → Ground

data Reach : Type where
  within nextSyllable nextWord : Reach

data Position : Type where
  doubleConsonant : Char → Position
  twoConsonants   : Char → Char → Reach → Position

data Match : Type where
  whole stem : Match

data Rule : Type where
  unwritten     : Char → ℕ → String → Rule
  longByNature  : Ground → Rule
  shortByNature : Char → Rule
  byLexicon     : Qty → String → Match → Rule
  [1160]        : Char → String → Rule
  [1161]        : Char → String → Rule
  [1162]        : Char → String → Rule
  [1163]        : Char → String → Rule
  merge         : String → String → Bool → Rule
  [522]         : Char → Position → Rule
  [1173]        : Qty → String → Char → Bool → Rule
  [524]         : Qty → Char → Char → Char → Bool → Rule
  [1168]        : Char → Char → Char → Rule
  [1167/1a]     : Rule
  [1167/1b]     : ℕ → Rule
  [1184]        : Rule

quantity : Rule → Maybe Qty
quantity = λ where
  (unwritten _ _ _)  → nothing
  (longByNature _)   → just long
  (shortByNature _)  → just short
  (byLexicon q _ _)  → just q
  ([1160] _ _)       → just short
  ([1161] _ _)       → just long
  ([1162] _ _)       → just short
  ([1163] _ _)       → just short
  (merge _ _ _)      → just long
  ([522] _ _)        → just long
  ([1173] q _ _ _)   → just q
  ([524] q _ _ _ _)  → just q
  ([1168] _ _ _)     → just long
  [1167/1a]          → just long
  ([1167/1b] _)      → just long
  [1184]             → just long

record Fact : Type where
  constructor fact
  field
    locus : Ix
    rule  : Rule
    qty   : Maybe Qty
    ref   : Maybe Ref
open Fact public

mkFact : Ix → Rule → Maybe Ref → Fact
mkFact i r = fact i r (quantity r)

record Explanation : Type where
  constructor explanation
  field
    parses     : ℕ
    syllables  : List String
    words      : List ℕ
    quantities : List Qty
    facts      : List Fact

{-# COMPILE GHC Qty         = data E.Qty         (E.Long | E.Short) #-}
{-# COMPILE GHC Ground      = data E.Ground      (E.Diphthong | E.LongVowel | E.Circumflex) #-}
{-# COMPILE GHC Reach       = data E.Reach       (E.Within | E.NextSyllable | E.NextWord) #-}
{-# COMPILE GHC Position    = data E.Position    (E.DoubleConsonant | E.TwoConsonants) #-}
{-# COMPILE GHC Match       = data E.Match       (E.Whole | E.Stem) #-}
{-# COMPILE GHC Rule        = data E.Rule        (E.Unwritten | E.LongByNature | E.ShortByNature | E.ByLexicon | E.R1160 | E.R1161 | E.R1162 | E.R1163 | E.Merge | E.R522 | E.R1173 | E.R524 | E.R1168 | E.R1167a | E.R1167b | E.R1184) #-}
{-# COMPILE GHC Fact        = data E.Fact        (E.Fact) #-}
{-# COMPILE GHC Explanation = data E.Explanation (E.Explanation) #-}
{-# COMPILE GHC quantity as ruleQuantity #-}
