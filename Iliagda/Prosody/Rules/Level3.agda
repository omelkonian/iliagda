{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level3 where

open import Iliagda.Init hiding (∅)
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

SynezizedOrDipthong : Syllable → Type
SynezizedOrDipthong sy = vowels sy ≥ 2

-- NB: separation of concerns between Level1~Synezesis
_~ˢʸⁿ_ : Syllable → Quantity → Type
sy ~ˢʸⁿ q =
  if ¿ SynezizedOrDipthong sy ¿ᵇ then
    (q ≡ ─)
  else
    (sy ~ q)

-- ** LEVEL 3: syllable context
-- TODO: find counter-example that demonstrates Level2~>3 dependency.

-- data LastAny {xs : List A} {P : A → Type} : Any P xs → Type where
--   isLastAny : (p : P x) → LastAny (here {xs = []} p)
LastAny : ∀ {xs : List A} {P : A → Type} → Any P xs → Type
LastAny = λ where
  (here {xs = xs} _) → xs ≡ []
  (there p)          → LastAny p

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

Letters = List Letter

variable ls ls′ : Letters

data StartsWithDoubleConsonant : Letters → Type where
  doubleConsonant :
    DoubleConsonant l
    ──────────────────────────────────
    StartsWithDoubleConsonant (l ∷ ls)

data StartsWithTwoConsonants : Letters → Type where
  twoConsonants :
    ∙ Consonant l
    ∙ Consonant l′
      ─────────────────────────────────────
      StartsWithTwoConsonants (l ∷ l′ ∷ ls)

Mute Liquid Nasal : Letter → Type
Mute   = _∈ [ π ⨾ β ⨾ φ ⨾ κ ⨾ γ ⨾ χ ⨾ τ ⨾ δ ⨾ θ ]
Liquid = _∈ [ ƛ ⨾ ρ ]
Nasal  = _∈ [ μ ⨾ ν ]

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

module QuantityRules (next : Context) where

  FollowedBy : (Q : Letters → Type) {P : Letter → Type} {ls : Letters} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = sys} _) → Q (sys ++ toLetters next)
    (there p) → FollowedBy Q p

  -- [522]
  data _↝_ : Syllable → Quantity → Type where

    longByPosition :
      (v∈ : Any Vowel sy) →
      -- ∙ ¬ [526/1167.2] ... (lexicon-based)
      ∙ FollowedBy (StartsWithDoubleConsonant ∪₁ StartsWithTwoConsonants) v∈
        ────────────────────────────────────────────────────────────────────
        sy ↝ ─

  data _~∗_ : Syllable → Quantity → Type where

    [522] :
      sy ↝ q
      -- ∙ ¬ [1173] sy -- "regularly"
      ───────
      sy ~∗ q

    -- (572)
    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ LastAny v∈
      ∙ sy ~ˢʸⁿ ─
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ ·

    -- mutes followed by liquids within the same word make a short syllable
    -- either long or short according to the needs of the verse
    -- (a.k.a. *common* syllable)
    [524] :
      (v∈ : Any Vowel sy) →
      ∙ sy ~ˢʸⁿ ·
      ∙ FollowedByInner MuteThenLiquid v∈
        ─────────────────────────────────
        sy ~∗ q

    {- TODO: apparent exception 526/1167.2, lexicon-based -}
    {- TODO: 1175, lexicon-based -}

  _≁∗_ = λ x y →  ¬ (x ~∗ y)

  data _~?_ : Syllable → Maybe Quantity → Type where

    ambiguous :
      (∀ q → sy ≁∗ q)
      ───────────────
      sy ~? nothing

    ambivalent :
      ∙ sy ~∗ ─
      ∙ sy ~∗ ·
        ─────────────
        sy ~? nothing

    certain :
      ∙ sy ~∗ q
      ∙ sy ≁∗ (! q)
        ────────────
        sy ~? just q

  ─Syllable = _~? just ─
  ·Syllable = _~? just ·

open QuantityRules
  renaming ( _↝_ to _⊢_↝_
           ; _~∗_ to _⊢_~∗_; _≁∗_ to _⊢_≁∗_
           ; _~?_ to _⊢_~?_
           )

instance
  Complies-Sy-MQ : (Syllable × Context) -compliesWith- Maybe Quantity
  Complies-Sy-MQ ._~_ (sy , ctx) mq = ctx ⊢ sy ~? mq

firstSyllable : Word n → Syllable
firstSyllable (word (sy ∷ _)) = sy

_~³_ : Words n → Quantities n → Type
_~³_ = VPointwise _~_ ∘ inContext
  module _ where
  inContext : Words n → Vec (Syllable × Context) n
  inContext [] = []
  inContext (w ∷ ws) = go (unword w) (next ws) V.++ inContext ws
    where
    next : Words n → Context
    next []      = ∅
    next (w ∷ _) = outer $ firstSyllable w

    go : Syllables n → Context → Vec (Syllable × Context) n
    go = λ where
      [] _ → []
      [ sy ] nxt → [ sy , nxt ]
      (sy ∷ sys@(sy′ ∷ _)) nxt → (sy , inner sy′) ∷ go sys nxt
