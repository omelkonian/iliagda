{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level3 where

open import Iliagda.Init hiding (∅)
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

SynizizedOrDipthong : Syllable → Type
SynizizedOrDipthong sy = vowels sy ≥ 2

-- NB: separation of concerns between Level1~Synizesis
--     a.k.a. "by nature after synizesis"
data _~ˢʸⁿ_ : Syllable → Quantity → Type where
  synLong :
    SynizizedOrDipthong sy
    ──────────────────────
    sy ~ˢʸⁿ ─

  ¬synLong :
    ∙ ¬ SynizizedOrDipthong sy
    ∙ sy ~ q
      ────────────────────────
      sy ~ˢʸⁿ q

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

module QuantityRules (next : Context) where

  FollowedBy FollowedByOuter : (Q : Letters → Type) {P : Letter → Type} {ls : Letters} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = sys} _) → Q (sys ++ toLetters next)
    (there p) → FollowedBy Q p
  FollowedByOuter Q = λ where
    (here {xs = []} _) → Q (toLetters next)
    (here {xs = _ ∷ _} _) → ⊥
    (there p) → FollowedByOuter Q p

{- -- ** Liberal restricting
-}

  data _~∗_ : Syllable → Quantity → Type where

    -- long by position
    [522] :
      (v∈ : Any Vowel sy) →
      -- ∙ ¬ [526/1167.2] ... (lexicon-based)
      ∙ FollowedBy (StartsWithDoubleConsonant ∪₁ StartsWithTwoConsonants) v∈
        ────────────────────────────────────────────────────────────────────
        sy ~∗ ─

    -- (572)
    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ LastAny v∈
      ∙ sy ~ˢʸⁿ ─
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ q

    -- mutes followed by liquids within the same word make a short syllable
    -- either long or short according to the needs of the verse
    -- (a.k.a. *common* syllable)
    [524] :
      (v∈ : Any Vowel sy) →
      ∙ sy ~ˢʸⁿ ·
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

{- ** Simultaneous restricting/relaxing

  data _~?′_ : Syllable → Flat Quantity → Type where

    -- long by position
    [522] :
      ∀ (v∈ : Any Vowel sy) →
      -- -- ∙ ¬ [526/1167.2] ... (lexicon-based)
      ∙ FollowedBy (StartsWithDoubleConsonant ∪₁ StartsWithTwoConsonants) v∈
        ────────────────────────────────────────────────────────────────────
        sy ~?′ single ─

    -- (572)
    [1173] :
      ∀ (v∈ : Any Vowel sy) →
      ∙ LastAny v∈
      ∙ sy ~ˢʸⁿ ─
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~?′ all

    -- mutes followed by liquids within the same word make a short syllable
    -- either long or short according to the needs of the verse
    -- (a.k.a. *common* syllable)
    [524] :
      ∀ (v∈ : Any Vowel sy) →
      ∙ sy ~ˢʸⁿ ·
      ∙ FollowedByInner MuteThenLiquid v∈
        ─────────────────────────────────
        sy ~?′ all

  data _~?_ : Syllable → Flat Quantity → Type where

    fromBelow : sy ~?′ mq → sy ~? mq
     -- ∙ ¬ [526/1167.2] ... (lexicon-based)

    {- TODO: apparent exception 526/1167.2, lexicon-based -}
    {- TODO: 1175, lexicon-based -}

    default :
      (∀ {mq} → ¬ sy ~?′ mq)
      ──────────────────────
      sy ~? none

    -- ** ALTERNATIVE: thread Level1 through Level3
    -- defaultByNature :
    --   ∙ (∀ {mq} → ¬ sy ~?′ mq)
    --   ∙ sy ~¹ mq
    --     ──────────────────────
    --     sy ~? mq

-}

{- -- ** Restrict before Relax

  module _ (sy : Syllable) where

    data RestrictByPosition : Type where

      [522] :
        ∀ (v∈ : Any Vowel sy) →
        -- -- ∙ ¬ [526/1167.2] ... (lexicon-based)
        ∙ FollowedBy (StartsWithDoubleConsonant ∪₁ StartsWithTwoConsonants) v∈
          ────────────────────────────────────────────────────────────────────
          RestrictByPosition


    data RelaxByPosition : Type where

      [1173] :
        ∀ (v∈ : Any Vowel sy) →
        ∙ LastAny v∈
        ∙ sy ~ˢʸⁿ ─
        ∙ FollowedBy StartsWithVowel v∈
          ─────────────────────────────
          RelaxByPosition

      [524] :
        ∀ (v∈ : Any Vowel sy) →
        ∙ sy ~ˢʸⁿ ·
        ∙ FollowedByInner MuteThenLiquid v∈
          ─────────────────────────────────
          RelaxByPosition

  data _~?′_ : Syllable → Flat Quantity → Type where

    single :
      RestrictByPosition sy
      ─────────────────────
      sy ~?′ single ─

    all :
      ∙ ¬ RestrictByPosition sy
      ∙ RelaxByPosition sy
        ───────────────────────
        sy ~?′ all

    none :
      ∙ ¬ RestrictByPosition sy
      ∙ ¬ RelaxByPosition sy
        ───────────────────────
        sy ~?′ none

  data _~?_ : Syllable → Flat Quantity → Type where

    fromBelow : sy ~?′ mq → sy ~? mq
     -- ∙ ¬ [526/1167.2] ... (lexicon-based)

    {- TODO: apparent exception 526/1167.2, lexicon-based -}
    {- TODO: 1175, lexicon-based -}

    default :
      (∀ {mq} → ¬ sy ~?′ mq)
      ──────────────────────
      sy ~? none

    -- ** ALTERNATIVE: thread Level1 through Level3
    -- defaultByNature :
    --   ∙ (∀ {mq} → ¬ sy ~?′ mq)
    --   ∙ sy ~¹ mq
    --     ──────────────────────
    --     sy ~? mq
-}

  ─Syllable = _~? single ─
  ·Syllable = _~? single ·

open QuantityRules
  renaming ( _~∗_ to _⊢_~∗_; _≁∗_ to _⊢_≁∗_
           ; _~?_ to _⊢_~?_
           )
  -- renaming (_~?′_ to _⊢_~?′_; _~?_ to _⊢_~?_)

instance
  Complies-Sy-MQ : (Syllable × Context) -compliesWith- Flat Quantity
  Complies-Sy-MQ ._~_ (sy , ctx) mq = ctx ⊢ sy ~? mq

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
