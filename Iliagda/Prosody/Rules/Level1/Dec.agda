-- {-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level1.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

open ∣Sy-Q∣; open ∣Sy-MQ∣; open ∣Sys-Qs∣

noInj₁ : ¬ A → A ⊎ B → B
noInj₁ ¬a = λ where
  (inj₁ a) → ⊥-elim $ ¬a a
  (inj₂ b) → b

module _
  {P Q R : A → Type}
  (R? : Decidable¹ R)
  (P⇒R : P ⊆¹ R)
  (Q⇒R : Q ⊆¹ R)
  where

  find-∩ :
    (xs : List A) →
    length (L.filter R? xs) ≡ 1 →
    (p∈ : Any P xs) →
    (q∈ : Any Q xs) →
    Any (P ∩¹ Q) xs
  find-∩ (x ∷ xs) R1 p∈ q∈
    with R? x
  ... | yes rx
    = here (px , qx)
    where
    -- length (filter R? xs) ≡ 0
    len≡0 = sym $ Nat.suc-injective R1

    p∉ : ¬ Any P xs
    p∉ p∈
      using r∈ ← L.Any.map P⇒R p∈
      = Nat.<⇒≢ (L.filter-some R? r∈) len≡0

    q∉ : ¬ Any Q xs
    q∉ q∈
      using r∈ ← L.Any.map Q⇒R q∈
      = Nat.<⇒≢ (L.filter-some R? r∈) len≡0

    px : P x
    px with ⟫ p∈
    ... | ⟫ here px = px
    ... | ⟫ there p∈ = ⊥-elim $ p∉ p∈

    qx : Q x
    qx with ⟫ q∈
    ... | ⟫ here qx = qx
    ... | ⟫ there q∈ = ⊥-elim $ q∉ q∈

  ... | no ¬rx
    = there
    $ find-∩ xs R1 ≪p∈ ≪q∈
    where
    ≪p∈ : Any P xs
    ≪p∈ with ⟫ p∈
    ... | ⟫ here  px = ⊥-elim $ ¬rx (P⇒R px)
    ... | ⟫ there p∈ = p∈

    ≪q∈ : Any Q xs
    ≪q∈ with ⟫ q∈
    ... | ⟫ here  qx = ⊥-elim $ ¬rx (Q⇒R qx)
    ... | ⟫ there q∈ = q∈

postulate
  ·Vowel⇒Vowel : ·Vowel ⊆¹ Vowel
  ─Vowel⇒Vowel : ─Vowel ⊆¹ Vowel
  Circ⇒Vowel : HasCircumflex ⊆¹ Vowel
  ¬·cVowel : ¬ (·Vowel l × HasCircumflex l)
  ¬·─Vowel : ¬ (·Vowel l × ─Vowel l)
  ∣Dipthong∣>1 : Any× Diphthong sy → vowels sy > 1

¬bothByNature : ¬ ((sy ~ ─) × (sy ~ ·))
¬bothByNature {sy = sy} (longByNature long , shortByNature ·v∈ v1)
  with long
... | inj₁ di =
  let 1<1 = subst (_> 1) v1 (∣Dipthong∣>1 di) in
  Nat.<-irrefl refl 1<1
... | inj₂ (inj₁ ─v∈) =
  let _ , ·v , ─v = L.Any.satisfied
                  $ find-∩ dec¹ ·Vowel⇒Vowel ─Vowel⇒Vowel (toList sy) v1 ·v∈ ─v∈
  in ¬·─Vowel (·v , ─v)
... | inj₂ (inj₂ cv∈) =
  let _ , ·v , cv = L.Any.satisfied
                  $ find-∩ dec¹ ·Vowel⇒Vowel Circ⇒Vowel (toList sy) v1 ·v∈ cv∈
  in ¬·cVowel (·v , cv)

theQuantity₁? :
  (sy : Syllable) →
    (∃ λ (q : Quantity) →
        (sy ~ q)
      × (∀ {q′} → sy ~ q′ → q′ ≡ q))
  ⊎ NonDerivable {B = Quantity} sy
theQuantity₁? sy
  with ¿ Any× Diphthong sy
       ⊎ Any ─Vowel sy
       ⊎ Any HasCircumflex sy ¿
... | yes long =
  let ~─ = longByNature long in
  inj₁ $ ─
       , ~─
       , λ where (longByNature _) → refl
                 ~·@(shortByNature _ _) → ⊥-elim $ ¬bothByNature (~─ , ~·)
... | no ¬long
  with ¿ Any ·Vowel sy
       × vowels sy ≡ 1 ¿
... | no ¬h
  = inj₂ λ where _ (longByNature long) → ¬long long
                 _ (shortByNature ·v∈ v1) → ¬h (·v∈ , v1)
... | yes (·v∈ , v1) =
  let ~· = shortByNature ·v∈ v1 in
  inj₁ $ ·
       , ~·
       , λ where ~─@(longByNature _) → ⊥-elim $ ¬bothByNature (~─ , ~·)
                 (shortByNature _ _) → refl

theQuantity₁ :
  (sy : Syllable) →
  ∃ λ (mq : Maybe Quantity) →
      (sy ~ mq)
    × (∀ {mq′} → sy ~ mq′ → mq′ ≡ mq)
theQuantity₁ sy
  with theQuantity₁? sy
... | inj₁ (q , sy~q , complete-q)
  = just q , byNature sy~q , λ where
    (byNature sy~q) → cong just (complete-q sy~q)
    (doubtful sy≁) → ⊥-elim $ sy≁ q sy~q
... | inj₂ sy≁
  = nothing
  , doubtful sy≁
  , λ where (byNature sy~q) → ⊥-elim $ sy≁ _ sy~q
            (doubtful sy≁) → refl

theQuantities₁ :
  (sys : Syllables n) →
  ∃ λ (mqs : Quantities n) →
      (sys ~ mqs)
    × (∀ {mqs′} → sys ~ mqs′ → mqs′ ≡ mqs)
theQuantities₁ [] = [] , [] , (λ where [] → refl)
theQuantities₁ {n = suc n} (sy ∷ sys) =
  let
    mq , sy~mq , complete-mq = theQuantity₁ sy
    mqs , sys~mqs , complete-mqs = theQuantities₁ {n = n} sys
  in
    mq ∷ mqs
  , sy~mq ∷ sys~mqs
  , λ where (sy~ ∷ sys~) → cong₂ _∷_ (complete-mq sy~) (complete-mqs sys~)
