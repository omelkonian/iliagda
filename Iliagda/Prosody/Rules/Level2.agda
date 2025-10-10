module Iliagda.Prosody.Rules.Level2 where

open import Iliagda.Init
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

data _~↓↓ʷ_ : Word n → Quantities n → Type where

  base :
    unword w ~ mqs
    ──────────────────────
    w ~↓↓ʷ mqs

private variable x : A

data VLast (P : A → Type) : Vec A (suc n) → Type where
  here :
    P x
    ─────────────
    VLast P [ x ]

  there : ∀ {xs : Vec A (suc n)} →
    VLast P xs
    ────────────────
    VLast P (x ∷ xs)

_∶⋯_ : Vec A (suc n) → A → Type
xs ∶⋯ x = VLast (_≡ x) xs

V-init : Vec A (suc n) → Vec A n
V-init = λ where
  (x ∷ []) → []
  (x ∷ xs@(_ ∷ _)) → x ∷ V-init xs

_∶⋯_∣_ : Vec A (2 + n) → A → A → Type
xs ∶⋯ penult ∣ ult
  = (xs ∶⋯ ult)
  × (V-init xs ∶⋯ penult)

_∶⋯_∣_∣_ : Vec A (3 + n) → A → A → A → Type
xs ∶⋯ antepenult ∣ penult ∣ ult
  = (xs ∶⋯ ult)
  × (V-init xs ∶⋯ penult)
  × (V-init (V-init xs) ∶⋯ antepenult)

variable antepenult : Syllable

_≔ₙ_ : Quantities (1 + n) → Quantity → Quantities (1 + n)
_≔ₙ_ {n = n} mqs q = mqs V.[ lastIndex ]≔ just q
  where lastIndex = Fi.fromℕ n

_≔ₙ₋₁_ : Quantities (2 + n) → Quantity → Quantities (2 + n)
_≔ₙ₋₁_ {n = n} mqs q = mqs V.[ penultIndex ]≔ just q
  where penultIndex = Fi.inject₁ $ Fi.fromℕ n

infix 10 _≔ₙ_ _≔ₙ₋₁_

data _~↓ʷ_ : Word n → Quantities n → Type where

  -- The vowel of the ultima in every word
  -- having the circumflex on the penult is short (545).
  [1160] :
    ∙ unword w ∶⋯ penult ∣ ult
    ∙ Any HasCircumflex penult
    ∙ w ~↓↓ʷ mqs
      ────────────────────────
      w ~↓ʷ (mqs ≔ₙ ·)

  -- If a long penult has the acute accent,
  -- then the ultima must be long also.
  [1161] :
    ∙ unword w ∶⋯ penult ∣ ult
    -- ** add context if you want LEVEL 3
    -- ∙ toList ult ⊢ penult ↝ ─
    ∙ penult ~ ─
    ∙ Any HasAcute penult
    ∙ w ~↓↓ʷ mqs
      ────────────────────────
      w ~↓ʷ (mqs ≔ₙ ─)

  -- If the ultima is short and the penult has the acute accent,
  -- then the penult must be short also.
  [1162] :
    ∙ unword w ∶⋯ penult ∣ ult
    -- ** add context if you want LEVEL 3
    -- ∙ ctx ⊢ ult ↝ ·
    ∙ ult ~ ·
    ∙ Any HasAcute penult
    ∙ w ~↓↓ʷ mqs
      ────────────────────────
      w ~↓ʷ (mqs ≔ₙ₋₁ ·)

  -- If the antepenult has the accent,
  -- the vowel of the ultima must be short (544).
  [1163] :
    ∙ unword w ∶⋯ antepenult ∣ penult ∣ ult
    ∙ Any HasAccent antepenult -- NB: it will always be acute
      ─────────────────────────────────────
      w ~↓ʷ (mqs ≔ₙ ·)

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
data EndsInFinalDiphthong : Word n → Type where
  finalDiphthong :
    ∙ unword w ∶⋯ ult
    ∙ Any× FinalDiphthong ult
      ───────────────────────
      EndsInFinalDiphthong w

Last⁺ : (A → Type) → List⁺ A → Type
Last⁺ P = VLast P ∘ L.NE.toVec

-- (575) exception rules
data EndsInApostrophe : Word n → Type where
  elision :
    ∙ unword w ∶⋯ ult
    ∙ Last⁺ (_≡ ᾽) ult
      ──────────────────
      EndsInApostrophe w

data _~ʷ_ : Word n → Quantities n → Type where

  [1164] :
    ∙ EndsInFinalDiphthong w
    ∙ w ~↓↓ʷ mqs
      ──────────────────────
      w ~ʷ mqs

{- ** TODO: lexicon-based
  [1165/574] :
    ∙ ApparentException w
    ∙ w ~↓↓ʷ mqs
      ──────────────────
      w ~ʷ mqs
-}

  -- (575/583) Elision has taken place.
  [575] :
    ∙ EndsInApostrophe w
    ∙ w ~↓↓ʷ mqs -- NB: or reindex?
      ──────────────────────
      w ~ʷ mqs

  fromBelow :
    ∙ ¬ EndsInFinalDiphthong w
    -- ∙ ¬ ApparentException w
    ∙ ¬ EndsInApostrophe w
    ∙ w ~↓ʷ mqs
      ────────────────────────
      w ~ʷ mqs

instance
  Complies-W-MQs : Word n -compliesWith- Quantities n
  Complies-W-MQs ._~_ = _~ʷ_
