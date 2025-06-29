module Iliagda.Prosody.Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology

import Data.Maybe as M

private
  first = L.head
  last  = L.last

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = M.Any.Any Vowel ∘ first
LastVowel  = M.Any.Any Vowel ∘ last

{-
FirstVowel = λ where
  [] → ⊥
  (l ∷ _) → Vowel l
LastVowel ls = case L.reverse ls of λ where
  [] → ⊥
  (l ∷ _) → Vowel l
-}

data _-synizizes*-_ : List Syllable → List Syllable → Type

private
  _~_ = _-synizizes*-_

  _⁀_ = _++_



{-
data _-synizizes₁-_ where
  _∷_ : ∀ {sys sys′} →
    ∀ sy →
    ∙ sys ~ sys′
      ───────────────────────────────────
      (sy ∷ sys) ~ (sy ∷ sys′)

  ∺ : ∀ {sys} →
    ∙ LastVowel sy × FirstVowel sy′
      ─────────────────────────────────
      (sy ∷ sy′ ∷ []) ~ (sy ⁀ sy′ ∷ [])

  _∷ʳ_ : ∀ {sys sys′} →
    ∀ sy →
    ∙ sys ~ sys′
      ───────────────────────────────────
      (sys ∷ʳ sy) ~ (sys′ ∷ʳ sy)

-- OR alternatively,
xs = Any× Synizible xs
map× : Any× P xs → List A


-- Design decisions:
--    (1) reflexive? NO
--    (2) allow recursive/iterative synizesis? NO
data _-synizizes+-_ where
  [] :
    sys ~₁ sys′
    sys ~+ sys′

  _ :
    sys  ~₁ sys′
    sys″ ~+ sys‴
    sys ++ sys″ ~+ sys′ ++ sys‴
-}

-- Design decisions:
--    (1) reflexive? YES
--    (2) allow recursive/iterative synizesis? NO
data _-synizizes*-_ where

  [] :
    ───────
    [] ~ []

  _∷_ : ∀ {sys sys′} →
    ∀ sy →
    ∙ sys ~ sys′
      ────────────────────────
      (sy ∷ sys) ~ (sy ∷ sys′)

  _∺_ : ∀ {sys sys′} →
    ∙ LastVowel sy × FirstVowel sy′
    ∙ sys ~ sys′
      ────────────────────────────────────
      (sy ∷ sy′ ∷ sys) ~ (sy ⁀ sy′ ∷ sys′)

{- ** IF WE WANT "minimal synizesis"

penalty : xs ~ ys → ℕ
penalty = λ where
  (_ ∺ tail) → 1 + penalty tail
  (_ ∺ tail) → 1 + penalty tail

xs ~⁺ ys = ∃ λ (pr : xs ~ ys) → penantly pr > 0

data _-synizizes-_ : List Syllable → List Syllable → Type

  base :
      ──────────────────────
      [ x , y ] ~ [ x <> y ]

  stepˡ :
    xs ~ ys
    ──────────────────────
    * ++ xs ~ * ++ ys

  stepʳ :
    xs ~ ys
    ──────────────────────
    xs ++ * ~ ys ++ *

  trans :
    xs ~ ys
    zs ~ ws
    ───────────────────
    xs ++ zs ~ ys ++ ws
-}

{- ** decision procedures

        ∙ (sys) → [[(sys′ , mqs′)]]
        ∙ (sys , mqs) → [[(sys′ , mqs′)]]
  |sys| - |sys′| = cost
        ∙ (sys , mqs) ~synizise~ (sys′ , mqs′)

-}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
