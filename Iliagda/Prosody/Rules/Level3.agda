{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level3 where

open import Iliagda.Init hiding (∅)
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

-- ** LEVEL 3: syllable context

-- (522)
-- We have to look at the next syllable for "vowel before".
-- (523)
-- We might also need to look at the next word
-- (in the case of the final syllable of a word).

data Context : Type where
  ∅     : Context
  inner : Syllable → Context
  outer : Syllable → Context

variable ctx ctx′ : Context

data StartsWithDoubleConsonant : Letters → Type where
  doubleConsonant :
    ∙ l ≢ Ζ
    ∙ DoubleConsonant l
      ──────────────────────────────────
      StartsWithDoubleConsonant (l ∷ ls)

data StartsWithTwoConsonants : Letters → Type where
  twoConsonants :
    ∙ (l , l′) ≢ (Σ , κ)
    ∙ Consonant l
    ∙ Consonant l′
      ─────────────────────────────────────
      StartsWithTwoConsonants (l ∷ l′ ∷ ls)

Mute Liquid Nasal : Letter → Type
Mute   = _∈ [ Β ⨾ β ⨾ Γ ⨾ γ ⨾ Δ ⨾ δ ⨾ Θ ⨾ θ ⨾ Κ ⨾ κ ⨾ Π ⨾ π ⨾ Τ ⨾ τ ⨾ Φ ⨾ φ ⨾ Χ ⨾ χ ]
Liquid = _∈ [ Λ ⨾ ƛ ⨾ Ρ ⨾ ρ ⨾ Ῥ ⨾ ῥ ]
Nasal  = _∈ [ Μ ⨾ μ ⨾ Ν ⨾ ν ]

data MuteThenLiquid : Letters → Type where
  muteLiquid :
    ∙ Mute l
    ∙ Liquid l′ ⊎ Nasal l′
      ────────────────────────────
      MuteThenLiquid (l ∷ l′ ∷ ls)

data StartsWithVowel : Letters → Type where
  vowel :
    Vowel l
    ────────────────────────
    StartsWithVowel (l ∷ ls)

!_ : Quantity → Quantity
!_ = λ{ ─ → ·; · → ─ }

-- TODO: consider commas, full stops, etc.

toLetters : Context → Letters
toLetters = λ where
  ∅          → []
  (inner sy) → toList sy
  (outer sy) → toList sy

FollowedByInner : (Q : Letters → Type) {P : Letter → Type} {ls : Letters} →
  Any P ls → Type
FollowedByInner Q = λ where
  (here {xs = sys} _) → Q sys
  (there p) → FollowedByInner Q p

module QuantityRules (⋯ : Flat Quantity × Context) (let mq , next = ⋯) where

  FollowedBy FollowedByOuter : (Q : Letters → Type) {P : Letter → Type} {ls : Letters} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = sys} _) → Q (sys ++ toLetters next)
    (there p) → FollowedBy Q p
  FollowedByOuter Q = λ where
    (here {xs = []} _) → Q (toLetters next)
    (here {xs = _ ∷ _} _) → ⊥
    (there p) → FollowedByOuter Q p

  data _~∗_ : Syllable → Quantity → Type where

    -- long by position
    [522] :
      (v∈ : Any Vowel sy) →
      -- ∙ ¬ [526/1167.2] ... (lexicon-based)
      ∙ FollowedBy (StartsWithDoubleConsonant ∪¹ StartsWithTwoConsonants) v∈
        ────────────────────────────────────────────────────────────────────
        sy ~∗ ─

    -- (572)
    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ mq ≡ single ─
      ∙ LastAny v∈
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ q

    -- mutes followed by liquids within the same word make a short syllable
    -- either long or short according to the needs of the verse
    -- (a.k.a. *common* syllable)
    [524] :
      (v∈ : Any Vowel sy) →
      ∙ mq ≡ single ·
      ∙ FollowedByInner MuteThenLiquid v∈
      ⊎ FollowedByOuter MuteThenLiquid v∈
        ─────────────────────────────────
        sy ~∗ q

  _≁∗_ = λ x y → ¬ (x ~∗ y)

  data _~?_ : Syllable → Flat Quantity → Type where

    ambiguous :
      (∀ q → sy ≁∗ q)
      ───────────────
      sy ~? none

    ambivalent :
      ∙ sy ~∗ ─
      ∙ sy ~∗ ·
        ─────────
        sy ~? all

    certain :
      ∙ sy ~∗ q
      ∙ sy ≁∗ (! q)
        ──────────────
        sy ~? single q

open QuantityRules public
  using ()
  renaming (_~∗_ to _⊢_~∗_; _≁∗_ to _⊢_≁∗_; _~?_ to _⊢_~?_)

instance
  Complies-Sy-MQ : (Syllable × Flat Quantity × Context) -compliesWith- Flat Quantity
  Complies-Sy-MQ ._~_ (sy , mq , ctx) = (mq , ctx) ⊢ sy ~?_

inContext : Words n → Quantities n
          → Vec (Syllable × Flat Quantity × Context) n
inContext []       _  = []
inContext (w ∷ ws) qs = go (unword w) (V.take _ qs) (next ws)
                   V.++ inContext ws (V.drop _ qs)
  where
  next : Words n → Context
  next []      = ∅
  next (w ∷ _) = outer $ firstSyllable w

  go : Syllables n
      → Quantities n
      → Context
      → Vec (Syllable × Flat Quantity × Context) n
  go = λ where
    [] _ _ → []
    [ sy ] [ mq ] nxt → [ sy , mq , nxt ]
    (sy ∷ sys@(sy′ ∷ _)) (mq ∷ mqs) nxt → (sy , mq , inner sy′) ∷ go sys mqs nxt

_~³_ : Words n × Quantities n → Quantities n → Type
(ws , qs) ~³ qs′ = VPointwise _~_ (inContext ws qs) qs′
