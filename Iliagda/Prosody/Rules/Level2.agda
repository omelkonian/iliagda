{-# OPTIONS --safe #-}
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
data EndsInFinalDiphthong : Syllables n → Type where
  finalDiphthong :
    ∙ sys ∶⋯ ult
    ∙ Any× FinalDiphthong ult
      ────────────────────────
      EndsInFinalDiphthong sys

Last⁺ : (A → Type) → List⁺ A → Type
Last⁺ P = VLast P ∘ L.NE.toVec

-- (575) exception rules
data EndsInApostrophe : Syllables n → Type where
  elision :
    ∙ sys ∶⋯ ult
    ∙ Last⁺ (_≡ ᾽) ult
      ────────────────────
      EndsInApostrophe sys

module _ (P : A → Type) where
  Single : List A → Type
  Single xs = ∀ (p q : Any P xs) → L.Any.index p ≡ L.Any.index q

  Single⁺ : List⁺ A → Type
  Single⁺ = Single ∘ toList

Letters = List Letter

lastThree : Vec A n → List A
lastThree = L.reverse ∘ L.take 3 ∘ V.toList ∘ V.reverse

lastThreeSys : Syllables n → Letters
lastThreeSys = concatMap toList ∘ lastThree

SingleAccents : Syllables n → Type
SingleAccents = Single HasAccent ∘ lastThreeSys

open import Algebra using (Op₁)

data _~%′_ : Syllables n → Op₁ (Quantities n) → Type where

  -- The vowel of the ultima in every word
  -- having the circumflex on the penult is short (545).
  [1160] :
    ∙ sys ∶⋯ penult ∣ ult
    ∙ Any HasCircumflex penult
      ────────────────────────
      sys ~%′ (_≔ₙ ·)

  -- If a long penult has the acute accent,
  -- then the ultima must be long also.
  [1161] :
    ∙ sys ∶⋯ penult ∣ ult
    -- ** add context if you want LEVEL 3
    -- ∙ toList ult ⊢ penult ↝ ─
    ∙ penult ~ ─
    ∙ Any HasAcute penult
      ───────────────────
      sys ~%′ (_≔ₙ ─)

  -- If the ultima is short and the penult has the acute accent,
  -- then the penult must be short also.
  [1162] :
    ∙ sys ∶⋯ penult ∣ ult
    -- ** add context if you want LEVEL 3
    -- ∙ ctx ⊢ ult ↝ ·
    ∙ penult ≁ ─ -- NB: to avoid clash with [1161]
    ∙ ult ~ ·
    ∙ Any HasAcute penult
      ───────────────────
      sys ~%′ (_≔ₙ₋₁ ·)

  -- If the antepenult has the accent,
  -- the vowel of the ultima must be short (544).
  [1163] :
    ∙ sys ∶⋯ antepenult ∣ penult ∣ ult
    ∙ Any HasAccent antepenult -- NB: it will always be acute
      ────────────────────────────────
      sys ~%′ (_≔ₙ ─)

data _~%_ : Syllables n → Op₁ (Quantities n) → Type where

  [1164] :
    EndsInFinalDiphthong sys
    ────────────────────────
    sys ~% id

{- ** TODO: lexicon-based
  [1165/574] :
    ApparentException sys
    ──────────────────
    sys ~% id
-}

  -- (575/583) Elision has taken place.
  [575] :
    EndsInApostrophe sys
    ────────────────────
    sys ~% id

  fromBelow : ∀ {f} →
    ∙ ¬ EndsInFinalDiphthong sys
    -- ∙ ¬ ApparentException sys
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


-- -}
-- -}
-- -}
-- -}
