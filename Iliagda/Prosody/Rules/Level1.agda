{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level1 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core

-- ** LEVEL 1: inherent quantities

open import Relation.Unary public
  using () renaming (Decidable to Decidable¹)

filter⁺ : ∀ {P : A → Type} → Decidable¹ P → List⁺ A → List A
filter⁺ P? = L.filter P? ∘ toList

vowels : Syllable → ℕ
vowels = length ∘ filter⁺ {P = Vowel} dec¹

instance
  Sy-Q : Syllable -compliesWith- Quantity
  Sy-Q ._~_ = _~′_
    module ∣Sy-Q∣ where
    -- PRECONDITIONS : no synezesis has taken place
    data _~′_ : Syllable → Quantity → Type where

      longByNature :
        ( Any× Diphthong sy
        ⊎ Any ─Vowel sy
        ⊎ Any HasCircumflex sy )
        ────────────────────────
        sy ~′ ─

      shortByNature :
        ∀ (v∈ : Any ·Vowel sy) →
        ∙ vowels sy ≡ 1
          ─────────────
          sy ~′ ·

  Sy-MQ : Syllable -compliesWith- Flat Quantity
  Sy-MQ ._~_ = _~′_
    module ∣Sy-MQ∣ where
    data _~′_ : Syllable → Flat Quantity → Type where

      byNature :
        sy ~ q
        ──────────────
        sy ~′ single q

      doubtful :
        NonDerivable {B = Quantity} sy
        ──────────────────────────────
        sy ~′ none

module ∣Sys-Qs∣ where
  data _~′_ : Syllables n → Quantities n → Type where

    [] :
      ────────────────────────
      [] ~′ []

    _∷_ :
      ∙ sy ~ mq
      ∙ sys ~′ mqs
        ────────────────────────
        (sy ∷ sys) ~′ (mq ∷ mqs)

instance
  Sys-Qs : Syllables n -compliesWith- Quantities n
  Sys-Qs ._~_ = ∣Sys-Qs∣._~′_
