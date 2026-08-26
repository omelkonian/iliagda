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
─Vowel = _∈ [ η ⨾ Ἠ ⨾ ἠ ⨾ Ἤ ⨾ ἤ ⨾ ᾔ ⨾ ἢ ⨾ ἦ ⨾ ᾖ ⨾ ᾐ ⨾ Ἡ ⨾ ἡ ⨾ Ἥ ⨾ ἥ ⨾ ᾕ ⨾ ἣ ⨾ ἧ ⨾ ᾗ ⨾ ή ⨾ ῄ ⨾ ὴ ⨾ ῂ ⨾ ῆ ⨾ ῇ ⨾ ῃ ]
          ◇ [ ω ⨾ Ὠ ⨾ ὠ ⨾ Ὤ ⨾ ὤ ⨾ ᾤ ⨾ ὢ ⨾ Ὦ ⨾ ὦ ⨾ ᾦ ⨾ ᾠ ⨾ ὡ ⨾ ὥ ⨾ ὣ ⨾ Ὧ ⨾ ὧ ⨾ ᾧ ⨾ ώ ⨾ ῴ ⨾ ὼ ⨾ ῶ ⨾ ῷ ⨾ ῳ ]
          ◇ [ ᾳ ]
·Vowel = _∈ [ Ε ⨾ ε ⨾ Ἐ ⨾ ἐ ⨾ Ἔ ⨾ ἔ ⨾ Ἑ ⨾ ἑ ⨾ Ἕ ⨾ ἕ ⨾ ἓ ⨾ έ ⨾ ὲ ]
          ◇ [ Ο ⨾ ο ⨾ Ὀ ⨾ ὀ ⨾ Ὄ ⨾ ὄ ⨾ ὁ ⨾ ὅ ⨾ ὃ ⨾ ό ⨾ ὸ ]
          ◇ [ Ᾰ ⨾ ᾰ ⨾ Ῐ ⨾ ῐ ⨾ Ῠ ⨾ ῠ ]
Doubtful = (¬_ ∘ ─Vowel) ∩¹ (¬_ ∘ ·Vowel)

-- (534)
HasAccent HasAcute HasGrave HasCircumflex : Pred₀ Letter
HasAccent = HasAcute ∪¹ HasGrave ∪¹ HasCircumflex
HasCircumflex = _∈ [ ᾶ ⨾ ᾷ ⨾ Ἆ ⨾ ἆ ]
                 ◇ [ ῆ ⨾ ῇ ⨾ ἦ ⨾ ᾖ ⨾ ἧ ⨾ ᾗ ]
                 ◇ [ ῖ ⨾ ἶ ⨾ Ἶ ⨾ ἷ ⨾ ῗ ]
                 ◇ [ ῦ ⨾ ὖ ⨾ ὗ ]
                 ◇ [ ῶ ⨾ ῷ ⨾ ὦ ⨾ Ὦ ⨾ ᾦ ⨾ ὧ ⨾ Ὧ ⨾ ᾧ ]
HasAcute = _∈ [ ά ⨾ Ἄ ⨾ ἄ ⨾ Ἅ ⨾ ἅ ]
            ◇ [ έ ⨾ Ἔ ⨾ ἔ ⨾ Ἕ ⨾ ἕ ]
            ◇ [ ή ⨾ Ἤ ⨾ ἤ ⨾ ᾔ ⨾ Ἥ ⨾ ἥ ⨾ ᾕ ⨾ ῄ ]
            ◇ [ ί ⨾ Ἴ ⨾ ἴ ⨾ ἵ ⨾ ΐ ]
            ◇ [ ό ⨾ Ὄ ⨾ ὄ ⨾ ὅ ]
            ◇ [ ύ ⨾ ὔ ⨾ Ὕ ⨾ ὕ ⨾ ΰ ]
            ◇ [ ώ ⨾ Ὤ ⨾ ὤ ⨾ ὥ ⨾ ᾤ ⨾ ῴ ]
HasGrave = _∈ [ ὰ ⨾ ἂ ⨾ ἃ ]
            ◇ [ ὲ ⨾ ἓ ]
            ◇ [ ὴ ⨾ ἢ ⨾ ἣ ⨾ ῂ ]
            ◇ [ ὶ ⨾ ἲ ⨾ ἳ ⨾ ῒ ]
            ◇ [ ὸ ⨾ ὃ ]
            ◇ [ ὺ ⨾ ὓ ⨾ ῢ ]
            ◇ [ ὼ ⨾ ὢ ⨾ ὣ ]

-- (518)
DoubleConsonant : Pred₀ Letter
DoubleConsonant = _∈ [ Ζ ⨾ ζ ⨾ Ξ ⨾ ξ ⨾ Ψ ⨾ ψ ]
-- TODO (optimization): remove Z instead of the a-posteriori treatment in Lvl3

-- (504)
-- Diphthong V1 (fst): plain (no breathing/accent), since in Greek typography
-- the breathing/accent of a word-initial diphthong falls on V2.
fst-α fst-ε fst-η fst-ο fst-υ fst-ω : Pred₀ Letter
fst-α = _∈ [ α ⨾ Α ]
fst-ε = _∈ [ ε ⨾ Ε ]
fst-η = _∈ [ η ]
fst-ο = _∈ [ ο ⨾ Ο ]
fst-υ = _∈ [ υ ]
fst-ω = _∈ [ ω ]

-- Diphthong V2 (snd): any lowercase ι- or υ-form *without* diaeresis.
-- (Capitals omitted: word-initial caps like Αἰ-, Εὐ-, Οἰ- have V2 lowercase.)
snd-ι snd-υ : Pred₀ Letter
snd-ι = _∈ [ ι ⨾ ἰ ⨾ ἴ ⨾ ἲ ⨾ ἶ ⨾ ἱ ⨾ ἵ ⨾ ἳ ⨾ ἷ ⨾ ί ⨾ ὶ ⨾ ῖ ]
snd-υ = _∈ [ υ ⨾ ὐ ⨾ ὔ ⨾ ὖ ⨾ ὑ ⨾ ὕ ⨾ ὓ ⨾ ὗ ⨾ ύ ⨾ ὺ ⨾ ῦ ]

Diphthong : Pred₀ (Letter × Letter)
Diphthong (l , l′)
  = (fst-α l × snd-ι l′)  -- αι
  ⊎ (fst-α l × snd-υ l′)  -- αυ
  ⊎ (fst-ε l × snd-ι l′)  -- ει
  ⊎ (fst-ε l × snd-υ l′)  -- ευ
  ⊎ (fst-η l × snd-υ l′)  -- ηυ
  ⊎ (fst-ο l × snd-ι l′)  -- οι
  ⊎ (fst-ο l × snd-υ l′)  -- ου
  ⊎ (fst-υ l × snd-ι l′)  -- υι
  ⊎ (fst-ω l × snd-υ l′)  -- ωυ
