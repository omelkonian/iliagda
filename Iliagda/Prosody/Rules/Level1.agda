module Iliagda.Prosody.Rules.Level1 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core

-- ** LEVEL 1: inherent quantities

Syllables = Vec Syllable

instance
  Sy-Q : Syllable -compliesWith- Quantity
  Sy-Q ._~_ = _~′_
    where
    data _~′_ : Syllable → Quantity → Type where

      longByNature :
        ( Any× Diphthong sy
        ⊎ Any ─Vowel sy
        ⊎ Any HasCircumflex sy )
        ────────────────────────
        sy ~′ ─

      shortByNature :
        ∀ (v∈ : Any ·Vowel sy) →
        ∙ ¬ Any× Diphthong sy
          ───────────────────
          sy ~′ ·

  Sy-MQ : Syllable -compliesWith- Maybe Quantity
  Sy-MQ ._~_ = _~′_
    where
    data _~′_ : Syllable → Maybe Quantity → Type where

      byNature :
        sy ~ q
        ────────────
        sy ~′ just q

      doubtful :
        sy ≁ q
        ─────────────
        sy ~′ nothing

  Sys-Qs : Syllables n -compliesWith- Quantities n
  Sys-Qs ._~_ = _~′_
    where
    data _~′_ : Syllables n → Quantities n → Type where

      [] :
        ────────────────────────
        [] ~′ []

      _∷_ :
        ∙ sy ~ mq
        ∙ sys ~′ mqs
          ────────────────────────
          (sy ∷ sys) ~′ (mq ∷ mqs)
