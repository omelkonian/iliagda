{-# OPTIONS --safe #-}
module Iliagda.Prosody.Core where

open import Iliagda.Init
open import Iliagda.Morphology

data Quantity : Type where
  · {- short -} : Quantity
  ─ {- long  -} : Quantity

Quantities : ℕ → Type
Quantities = Vec (Maybe Quantity)

data Foot : (n : ℕ) {- syllables -} → Vec Quantity n → Type where
  ─·· {- dactyl -} : Foot 3 (─ ∷ · ∷ · ∷ [])
  ──  {- sponde -} : Foot 2 (─ ∷ ─ ∷ [])
∃∃Foot = ∃ (∃ ∘ Foot)

Feet = List ∃∃Foot

data Meter : ℕ {- syllables -} → ℕ {- feet -} → Type where
  mkPM : (fs : Feet) → Meter (∑₁ fs) (length fs)

Hexameter : ℕ {- syllables -} → Type
Hexameter n = Meter n 6

unmkPM : Meter n m → Feet
unmkPM (mkPM fs) = fs

∑₁≡0 : ∀ {P : Pred₀ ℕ} {ps : List (∃ P)} →
  ∑₁ ps ≡ 0 →
  All ((_≡ 0) ∘ proj₁) ps
∑₁≡0 {ps = []} _ = []
∑₁≡0 {ps = _ ∷ _} eq = Nat.m+n≡0⇒m≡0 _ eq ∷ ∑₁≡0 (Nat.m+n≡0⇒n≡0 _ eq)

Meter-sum≡ : (meter : Meter n m) → n ≡ ∑₁ (unmkPM meter)
Meter-sum≡ (mkPM _) = refl

Meter-length≡ : (meter : Meter n m) → m ≡ length (unmkPM meter)
Meter-length≡ (mkPM _) = refl

Foot≢0 : ∀ {qs} → ¬ Foot 0 qs
Foot≢0 ()

emptyFeet′ : (fs : Feet) → All ((_≡ 0) ∘ proj₁) fs → fs ≡ []
emptyFeet′ [] [] = refl
emptyFeet′ ((.0 , _ , f) ∷ _) (refl ∷ _) = ⊥-elim $ Foot≢0 f

emptyFeet : (fs : Feet) → ∑₁ fs ≡ 0 → fs ≡ []
emptyFeet fs sum0 = emptyFeet′ fs (∑₁≡0 sum0)

IsEmptyMeter : Pred₀ (Meter n m)
IsEmptyMeter (mkPM fs) = fs ≡ []

IsEmptyMeter⇒≡0 : (pm : Meter n m) → IsEmptyMeter pm → n ≡ 0 × m ≡ 0
IsEmptyMeter⇒≡0 (mkPM .[]) refl = refl , refl

emptyMeter-n′ : (pm : Meter n m) → n ≡ 0 → IsEmptyMeter pm
emptyMeter-n′ (mkPM fs) = emptyFeet fs

emptyMeter-m′ : (pm : Meter n m) → m ≡ 0 → IsEmptyMeter pm
emptyMeter-m′ (mkPM []) refl = refl

emptyMeter-n : (pm : Meter 0 m) → IsEmptyMeter pm
emptyMeter-n = flip emptyMeter-n′ refl

emptyMeter-m : (pm : Meter n 0) → IsEmptyMeter pm
emptyMeter-m = flip emptyMeter-m′ refl

emptyMeter : (pm : Meter 0 0) → IsEmptyMeter pm
emptyMeter = flip emptyMeter-n′ refl

Hex≢0 : ¬ Hexameter 0
Hex≢0 hm
  with unmkPM hm | Meter-length≡ hm | ∑₁≡0 {ps = unmkPM hm} (sym $ Meter-sum≡ hm)
... | (.0 , _ , ()) ∷ _ | _ | refl ∷ _

Hex>0 : Hexameter n → n > 0
Hex>0 {zero} hm = ⊥-elim $ Hex≢0 hm
Hex>0 {suc n} hm = s≤s z≤n

variable
  q q′ : Quantity
  qs qs′ : Vec Quantity n
  mq mq′ mq″ : Maybe Quantity
  mqs mqs′ : Quantities n
  pm  : Meter n m
  pm′ : Meter n′ m′
  meter meter′ : Hexameter n

infixr 5 _∷ᵖᵐ_
_∷ᵖᵐ_ : Foot n qs → Meter n′ m′ → Meter (n + n′) (1 + m′)
f ∷ᵖᵐ (mkPM fs) = mkPM ((-, -, f) ∷ fs)

-- ** basic rules

-- (519)
─Vowel ·Vowel Doubtful HasCircumflex : Pred₀ Letter
-- INCOMPLETE: add as needed
─Vowel = _∈ [ η ⨾ ῆ ⨾ ἣ ⨾ ἡ ⨾ ή ⨾ ὴ ⨾ ω ⨾ ώ ⨾ ῶ ]
-- INCOMPLETE: add as needed
·Vowel = _∈ [ ε ⨾ έ ⨾ ἔ ⨾ ὲ ⨾ ἑ ⨾ ἐ ⨾ ο ⨾ ὸ ]
Doubtful      = (¬_ ∘ ─Vowel) ∩¹ (¬_ ∘ ·Vowel)
-- INCOMPLETE: add as needed
HasCircumflex = _∈ [ ῆ ⨾ ῖ ⨾ ῦ ⨾ ὗ ⨾ ᾶ ⨾ ῶ ]

-- (518)
DoubleConsonant : Pred₀ Letter
DoubleConsonant = _∈ [ Ζ ⨾ ζ ⨾ Ξ ⨾ ξ ⨾ Ψ ⨾ ψ ]

-- (504)
Diphthong : Pred₀ (Letter × Letter)
Diphthong = _∈
-- INCOMPLETE: add as needed
  ( (α , ι)
  ∷ (α , ὶ)
  ∷ (α , υ)
  ∷ (α , ὐ)
  ∷ (ε , ι)
  ∷ (ε , ί)
  ∷ (ε , ὶ)
  ∷ (ε , υ)
  ∷ (ε , ῦ)
  ∷ (η , υ)
  ∷ (ο , ι)
  ∷ (ο , ῖ)
  ∷ (ο , ἰ)
  ∷ (ο , ὶ)
  ∷ (ο , υ)
  ∷ (ο , ὐ)
  ∷ (ο , ὺ)
  ∷ (ο , ὗ)
  ∷ (υ , ι)
  ∷ (υ , ὶ)
  ∷ (ω , υ)
  ∷ []
  )

VowelBeforeDoubleConsonant : Pred₀ (Letter × Letter)
VowelBeforeDoubleConsonant (v , c) = Vowel v × DoubleConsonant c

VowelBeforeTwoConsonants : Pred₀ (Letter × Letter × Letter)
VowelBeforeTwoConsonants (v , c , c′) = Vowel v × Consonant c × Consonant c′

{-
-- ** example words

w7 : Words _
w7 =
  ( word [ [ Ἀ ] ⨾ [ τ ⨾ ρ ⨾ ε ] ⨾ [ ΐ ] ⨾ [ δ ⨾ η ⨾ ς ] ]
  ∷ word [ [ τ ⨾ ε ] ]
  ∷ word [ [ ἄ ] ⨾ [ ν ⨾ α ⨾ ξ ] ]
  ∷ word [ [ ἀ ⨾ ν ] ⨾ [ δ ⨾ ρ ⨾ ῶ ⨾ ν ] ]
  ∷ word [ [ κ ⨾ α ⨾ ὶ ] ]
  ∷ word [ [ δ ⨾ ῖ ] ⨾ [ ο ⨾ ς ] ]
  ∷ word [ [ Ἀ ] ⨾ [ χ ⨾ ι ⨾ ƛ ] ⨾ [ ƛ ⨾ ε ⨾ ύ ⨾ ς ] ]
  ∷ []
  )
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
