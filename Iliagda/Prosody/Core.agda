{-# OPTIONS --safe #-}
module Iliagda.Prosody.Core where

open import Iliagda.Init
open import Iliagda.Morphology

data Quantity : Type where
  · {- short -} : Quantity
  ─ {- long  -} : Quantity

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

feet-qs : (fs : Feet) → Vec Quantity (∑₁ fs)
feet-qs [] = []
feet-qs ((_ , qs , _) ∷ fs) = qs V.++ feet-qs fs

meter-qs : Meter n m → Vec Quantity n
meter-qs (mkPM fs) = feet-qs fs

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
  pm  pm′ : Meter n m
  hm  hm′ : Hexameter n

infixr 5 _∷ᵖᵐ_
_∷ᵖᵐ_ : Foot n qs → Meter n′ m′ → Meter (n + n′) (1 + m′)
f ∷ᵖᵐ (mkPM fs) = mkPM ((-, -, f) ∷ fs)

-- ** basic rules

-- (519)
─Vowel ·Vowel Doubtful : Pred₀ Letter
-- INCOMPLETE: add as needed
─Vowel = _∈ [ η ⨾ ῆ ⨾ ῇ ⨾ ῃ ⨾ ἠ ⨾ ἡ ⨾ ἢ ⨾ ἣ ⨾ ἤ ⨾ ἦ ⨾ ἥ ⨾ Ἥ ⨾ ή ⨾ ὴ ⨾ ᾔ ]
          ◇ [ ω ⨾ ὠ ⨾ ὣ ⨾ ὤ ⨾ ὥ ⨾ ὦ ⨾ ᾤ ⨾ ᾧ ⨾ ώ ⨾ ὼ ⨾ ῶ ⨾ ῳ ⨾ ῴ ⨾ ῷ ]
-- INCOMPLETE: add as needed
·Vowel = _∈ [ ε ⨾ ἐ ⨾ ἑ ⨾ ἔ ⨾ ἕ ⨾ έ ⨾ ὲ ]
          ◇ [ ο ⨾ Ο ⨾ ὀ ⨾ Ὀ ⨾ ὁ ⨾ ὃ ⨾ ὄ ⨾ ὅ ⨾ ό ⨾ ὸ ]
Doubtful = (¬_ ∘ ─Vowel) ∩¹ (¬_ ∘ ·Vowel)

-- (534)
HasAccent HasAcute HasGrave HasCircumflex : Pred₀ Letter
HasAccent = HasAcute ∪₁ HasGrave ∪₁ HasCircumflex
-- INCOMPLETE: add as needed
HasCircumflex = _∈ [ ῆ ⨾ ῇ ⨾ ἶ ⨾ ῖ ⨾ ῦ ⨾ ὗ ⨾ ὖ ⨾ ᾶ ⨾ ᾷ ]
                 ◇ [ ῶ ⨾ ὦ ⨾ ᾧ ⨾ ῷ ]
-- INCOMPLETE: add as needed
HasAcute = _∈ [ Ἄ ⨾ ἄ ⨾ ά ]
            ◇ [ έ ⨾ ἔ ⨾ ἕ ]
            ◇ [ ἤ ⨾ ή ⨾ ἥ ⨾  Ἥ ⨾ ᾔ ]
            ◇ [ ί ⨾ ἴ ⨾ Ἴ ⨾ ΐ ]
            ◇ [ ὄ ⨾ ὅ ⨾ ό ]
            ◇ [ ὔ ⨾ ὕ ⨾ ύ ⨾ ΰ ]
            ◇ [ ὤ ⨾ ὥ ⨾ ᾤ ⨾ ώ ⨾ ῴ ]
-- INCOMPLETE: add as needed
HasGrave = _∈ [ ἂ ⨾ ὰ ]
            ◇ [ ὲ ]
            ◇ [ ἢ ⨾ ἣ ⨾ ὴ ]
            ◇ [ ὶ ⨾ ἳ ⨾ ῒ ]
            ◇ [ ὸ ⨾ ὃ ]
            ◇ [ ὺ ]
            ◇ [ ὣ ⨾ ὼ ]

-- (518)
DoubleConsonant : Pred₀ Letter
DoubleConsonant = _∈ [ Ζ ⨾ ζ ⨾ Ξ ⨾ ξ ⨾ Ψ ⨾ ψ ]

-- (504)
Diphthong : Pred₀ (Letter × Letter)
Diphthong = _∈
-- TODO: refactor (better/complete)
-- INCOMPLETE: add as needed
  ( (α , ι)
  ∷ (α , ὶ)
  ∷ (α , ί)
  ∷ (ε , ι)
  ∷ (ε , ί)
  ∷ (ε , ὶ)
  ∷ (ε , ἰ)
  ∷ (η , υ)
  ∷ (ο , ι)
  ∷ (ο , ῖ)
  ∷ (ο , ἰ)
  ∷ (ο , ὶ)
  ∷ (ο , ί)
  ∷ (ο , ἱ)
  ∷ (ο , υ)
  ∷ (ο , ὐ)
  ∷ (ο , ὺ)
  ∷ (ο , ὗ)
  ∷ (ο , ὕ)
  ∷ (ο , ῦ)
  ∷ (ο , ύ)
  ∷ (υ , ι)
  ∷ (υ , ὶ)
  ∷ (υ , ἱ)
  ∷ (ω , υ)
  ∷ []
  )

VowelBeforeDoubleConsonant : Pred₀ (Letter × Letter)
VowelBeforeDoubleConsonant (v , c) = Vowel v × DoubleConsonant c

VowelBeforeTwoConsonants : Pred₀ (Letter × Letter × Letter)
VowelBeforeTwoConsonants (v , c , c′) = Vowel v × Consonant c × Consonant c′

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
