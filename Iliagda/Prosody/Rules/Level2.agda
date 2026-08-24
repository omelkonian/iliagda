{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level2 where

open import Iliagda.Init
open import Prelude.Vectors

open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Lexicon

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
FinalDiphthong (l , l′)
  = (fst-α l × snd-ι l′)  -- αι
  ⊎ (fst-ο l × snd-ι l′)  -- οι

-- (1164) exception rules

EndsInFinalDiphthong : Syllables n → Type
EndsInFinalDiphthong = InUlt (Last× FinalDiphthong)

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

IsCompound : Syllables n → Type
IsCompound sys = unsyllables sys ∈
  [ [ ο ⨾ ὔ ⨾ τ ⨾ ε ]
  ⨾ [ μ ⨾ ή ⨾ τ ⨾ ε ]
  ⨾ [ ο ⨾ ὔ ⨾ τ ⨾ ι ⨾ ς ]
  ⨾ [ μ ⨾ ή ⨾ τ ⨾ ι ⨾ ς ]
  ⨾ [ ἥ ⨾ δ ⨾ ε ]
  ⨾ [ ἤ ⨾ τ ⨾ ε ]
  ⨾ [ ο ⨾ ἵ ⨾ δ ⨾ ε ]
  ⨾ [ δ ⨾ ᾽ ⨾ ο ⨾ ἵ ⨾ δ ⨾ ε ]
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

record LexHit {n} (sys : Syllables n) : Type where
  constructor lexHit
  field
    entry   : Entry
    ix      : Fin n
    found   : lexLookup (unsyllables sys) ≡ just entry
    atLocus : locusIx (locusOf (entry .mode)) n ≡ just ix
    gap     : NonDerivable {B = Quantity} (V.lookup sys ix)
open LexHit public

data _~L_ : Syllables n → Op₁ (Quantities n) → Type where

  byLexicon : (h : LexHit sys) → sys ~L (V._[ h .ix ]≔ single (h .entry .qty))

  noLex :
    ¬ LexHit sys
    ────────────
    sys ~L id

data _~ʷ_ : Word n → Quantities n → Type where

  𝟙-then-L-then-𝟚 : ∀ {lex f} → let sys = unword w in
    ∙ sys ~ mqs
    ∙ sys ~L lex
    ∙ sys ~% f
      ─────────────────
      w ~ʷ f (lex mqs)

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
