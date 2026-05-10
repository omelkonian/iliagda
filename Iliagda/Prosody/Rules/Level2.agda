{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level2 where

open import Iliagda.Init
open import Prelude.Vectors

open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

-- TODO: how does apostrophe interact with syllables?
-- i.e. re-index by-construction or not??

-- ** LEVEL 2: lexical structure

CircumflexPenult : Pred₀ (Word (2 + n))
CircumflexPenult (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = Any HasCircumflex penult

circumflexPenult? : (w : Word (2 + n)) → Dec (CircumflexPenult w)
circumflexPenult? (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = dec

-- (547) final αι/oι are counted short *only* for accent
FinalDiphthong : Pred₀ (Letter × Letter)
FinalDiphthong = _∈
  ( (α , ι)
  ∷ (α , ὶ)
  ∷ (ο , ι)
  ∷ (ο , ῖ)
  ∷ (ο , ἰ)
  ∷ (ο , ὶ)
  ∷ (ο , ί)
  ∷ []
  )

-- (1164) exception rules

EndsInFinalDiphthong : Syllables n → Type
EndsInFinalDiphthong = InUlt (Any× FinalDiphthong)

-- (575) exception rules
EndsInApostrophe : Syllables n → Type
EndsInApostrophe = InUlt (Last⁺ (_≡ ᾽))

HasAccentSy : Syllable → Type
HasAccentSy = Any HasAccent ∘ toList

SingleAccents : Syllables n → Type
SingleAccents = LastThree (  Affinely HasAccentSy
                          ∩¹ All (Affinely⁺ HasAccent)
                          )

data _~%′_ : Syllables n → Op₁ (Quantities n) → Type where

  -- The vowel of the ultima in every word
  -- having the circumflex on the penult is short (545).
  [1160] :
    InPenult (Any HasCircumflex) sys
    ────────────────────────────────
    sys ~%′ (_≔ₙ single ·)

  -- If a long penult has the acute accent,
  -- then the ultima must be long also.
  [1161] :
    -- ** add context if you want LEVEL 3
    -- ∙ toList ult ⊢ penult ↝ ─
    InPenult ((_~ ─) ∩¹ Any HasAcute) sys
    ─────────────────────────────────────
    sys ~%′ (_≔ₙ single ─)

  -- If the ultima is short and the penult has the acute accent,
  -- then the penult must be short also.
  [1162] :
    -- ** add context if you want LEVEL 3
    -- ∙ ctx ⊢ ult ↝ ·
    ∙ InUlt (_~ ·) sys
    ∙ InPenult ( (_≁ ─) -- NB: to avoid clash with [1161]
               ∩¹ Any HasAcute
               ) sys
      ────────────────────────
      sys ~%′ (_≔ₙ₋₁ single ·)

  -- If the antepenult has the accent,
  -- the vowel of the ultima must be short (544).
  [1163] :
    InAntepenult (Any HasAccent) sys
    ────────────────────────────────
    sys ~%′ (_≔ₙ single ·)

unsyllables : Syllables n → Letters
unsyllables = L.concat ∘ map toList ∘ toList

IsCompound : Syllables n → Type
IsCompound sys = unsyllables sys ∈
  [ [ ο ⨾ ὔ ⨾ τ ⨾ ε ]
  ⨾ [ μ ⨾ ή ⨾ τ ⨾ ε ]
  ⨾ [ ο ⨾ ὔ ⨾ τ ⨾ ι ⨾ ς ]
  ⨾ [ μ ⨾ ή ⨾ τ ⨾ ι ⨾ ς ]
  ⨾ [ ἥ ⨾ δ ⨾ ε ]
  ⨾ [ ο ⨾ ἵ ⨾ δ ⨾ ε ]
  ⨾ [ α ⨾ ἵ ⨾ δ ⨾ ε ]
  ⨾ [ τ ⨾ ο ⨾ ύ ⨾ σ ⨾ δ ⨾ ε ]
  ⨾ [ τ ⨾ ά ⨾ σ ⨾ δ ⨾ ε ]
  -- INCOMPLETE: add as needed
  ]

data ApparentException : Syllables n → Type where
  [1165] : IsCompound sys → ApparentException sys

data _~%_ : Syllables n → Op₁ (Quantities n) → Type where

  [1164] :
    EndsInFinalDiphthong sys
    ────────────────────────
    sys ~% id

  [574] :
    ApparentException sys
    ─────────────────────
    sys ~% id

  -- (575/583) Elision has taken place.
  [575] :
    EndsInApostrophe sys
    ────────────────────
    sys ~% id

  fromBelow : ∀ {f} →
    ∙ ¬ EndsInFinalDiphthong sys
    ∙ ¬ ApparentException sys
    ∙ ¬ EndsInApostrophe sys
    ∙ SingleAccents sys
    ∙ sys ~%′ f
      ───────────────────────────
      sys ~% f

  noop :
    ∙ (¬ SingleAccents sys)
    ⊎ (∀ {f} → ¬ sys ~%′ f)
      ─────────────────────────────────
      sys ~% id

data _~ʷ_ : Word n → Quantities n → Type where

  𝟙-then-𝟚 : ∀ {f} → let sys = unword w in
    ∙ sys ~ mqs
    ∙ sys ~% f
      ───────────────
      w ~ʷ f mqs

instance
  Complies-W-MQs : Word n -compliesWith- Quantities n
  Complies-W-MQs ._~_ = _~ʷ_

data _~²_ : Words n → Quantities n → Type where

  [] :
    ────────
    [] ~² []

  _∷_ : ∀ {w : Word n}
          {mqs : Quantities n}
          {ws : Words n′}
          {mqs′ : Quantities n′}
          {mqs₀ : Quantities (n + n′)}
          ⦃ _ : mqs₀ ≡ mqs V.++ mqs′ ⦄ →

    ∙ w ~ʷ mqs
    ∙ ws ~² mqs′
      ────────────────
      (w ∷ ws) ~² mqs₀
