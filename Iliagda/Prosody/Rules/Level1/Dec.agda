{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level1.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

open ∣Sy-Q∣; open ∣Sy-MQ∣; open ∣Sys-Qs∣

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

private
  pattern 𝟘 = here refl
  pattern ↠_ x = there x

¬circ×acu : HasCircumflex l → HasAcute l → ⊥
¬circ×acu = λ where
  𝟘 → auto
  (↠ 𝟘) → auto
  (↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto

·Vowel⇒Vowel : ·Vowel ⊆¹ Vowel
·Vowel⇒Vowel = λ where
  𝟘 → auto
  (↠ 𝟘) → auto
  (↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto

─Vowel⇒Vowel : ─Vowel ⊆¹ Vowel
─Vowel⇒Vowel = λ where
  𝟘 → auto
  (↠ 𝟘) → auto
  (↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto

fst-α⇒Vowel : fst-α ⊆¹ Vowel
fst-α⇒Vowel 𝟘 = auto
fst-α⇒Vowel (↠ 𝟘) = auto

fst-ε⇒Vowel : fst-ε ⊆¹ Vowel
fst-ε⇒Vowel 𝟘 = auto
fst-ε⇒Vowel (↠ 𝟘) = auto

fst-η⇒Vowel : fst-η ⊆¹ Vowel
fst-η⇒Vowel 𝟘 = auto

fst-ο⇒Vowel : fst-ο ⊆¹ Vowel
fst-ο⇒Vowel 𝟘 = auto
fst-ο⇒Vowel (↠ 𝟘) = auto

fst-υ⇒Vowel : fst-υ ⊆¹ Vowel
fst-υ⇒Vowel 𝟘 = auto

fst-ω⇒Vowel : fst-ω ⊆¹ Vowel
fst-ω⇒Vowel 𝟘 = auto

snd-ι⇒Vowel : snd-ι ⊆¹ Vowel
snd-ι⇒Vowel 𝟘 = auto
snd-ι⇒Vowel (↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-ι⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto

snd-υ⇒Vowel : snd-υ ⊆¹ Vowel
snd-υ⇒Vowel 𝟘 = auto
snd-υ⇒Vowel (↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto
snd-υ⇒Vowel (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) = auto

Di⇒Vowel : Diphthong (l , l′) → Vowel l × Vowel l′
Di⇒Vowel = λ where
  (inj₁ (a , i))                                          → fst-α⇒Vowel a , snd-ι⇒Vowel i
  (inj₂ (inj₁ (a , u)))                                   → fst-α⇒Vowel a , snd-υ⇒Vowel u
  (inj₂ (inj₂ (inj₁ (e , i))))                            → fst-ε⇒Vowel e , snd-ι⇒Vowel i
  (inj₂ (inj₂ (inj₂ (inj₁ (e , u)))))                     → fst-ε⇒Vowel e , snd-υ⇒Vowel u
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (h , u))))))              → fst-η⇒Vowel h , snd-υ⇒Vowel u
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (o , i)))))))       → fst-ο⇒Vowel o , snd-ι⇒Vowel i
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (o , u))))))))→ fst-ο⇒Vowel o , snd-υ⇒Vowel u
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (u , i))))))))) → fst-υ⇒Vowel u , snd-ι⇒Vowel i
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (w , u))))))))) → fst-ω⇒Vowel w , snd-υ⇒Vowel u

Circ⇒Vowel : HasCircumflex ⊆¹ Vowel
Circ⇒Vowel = λ where
  𝟘 → auto
  (↠ 𝟘) → auto
  (↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto

Circ⇒¬·Vowel : HasCircumflex ⊆¹ ¬_ ∘ ·Vowel
Circ⇒¬·Vowel = λ where
  𝟘 → auto
  (↠ 𝟘) → auto
  (↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘) → auto

¬·cVowel : ¬ (·Vowel l × HasCircumflex l)
¬·cVowel (s , c) = Circ⇒¬·Vowel c s

¬·─Vowel : ¬ (·Vowel l × ─Vowel l)
¬·─Vowel = λ where
  (𝟘 , p) → contradict p
  (↠ 𝟘 , p) → contradict p
  (↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p
  (↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ ↠ 𝟘 , p) → contradict p

onlyVowels : List Letter → List Letter
onlyVowels = L.filter Vowel?

♯vowels : List Letter → ℕ
♯vowels = length ∘ onlyVowels

module _ {l ls} where

  onlyVowels∷ : onlyVowels (l ∷ ls) ≡ onlyVowels [ l ] ++ onlyVowels ls
  onlyVowels∷ = L.filter-++ Vowel? [ l ] ls

  vowels∷ : vowels (l ∷ ls) ≡ vowels [ l ] + ♯vowels ls
  vowels∷ =
    let open ≡-Reasoning in
    begin
      vowels (l ∷ ls)
    ≡⟨⟩
      length (onlyVowels (l ∷ ls))
    ≡⟨ cong length onlyVowels∷ ⟩
      length (onlyVowels [ l ] ++ onlyVowels ls)
    ≡⟨ L.length-++ (onlyVowels [ l ]) ⟩
      length (onlyVowels [ l ]) + length (onlyVowels ls)
    ≡⟨⟩
      vowels [ l ] + ♯vowels ls
    ∎

vowelsDi : (l , l′) ∈ pairs (toList sy) → vowels sy ≥ vowels [ l ⨾ l′ ]
vowelsDi {sy = [ _ ]} ()
vowelsDi {sy = l ∷ l′ ∷ ls} 𝟘 =
  let open Nat.≤-Reasoning in
  begin
    vowels [ l ⨾ l′ ]
  ≡⟨ vowels∷ {l} ⟩
    vowels [ l ] + vowels [ l′ ]
  ≤⟨ Nat.m≤m+n _ _ ⟩
    vowels [ l ] + vowels [ l′ ] + ♯vowels ls
  ≡⟨ Nat.+-assoc (vowels [ l ]) _ _ ⟩
    vowels [ l ] + (vowels [ l′ ] + ♯vowels ls)
  ≡˘⟨ cong (_ +_) $ vowels∷ {l′} ⟩
    vowels [ l ] + vowels (l′ ∷ ls)
  ≡˘⟨ vowels∷ {l} ⟩
    vowels (l ∷ l′ ∷ ls)
  ∎
vowelsDi {l}{l′}{sy = l↓ ∷ ls@(_ ∷ _)} (↠ p) =
  let open Nat.≤-Reasoning in
  begin
    vowels [ l ⨾ l′ ]
  ≤⟨ vowelsDi p ⟩
    ♯vowels ls
  ≤⟨ Nat.m≤n+m _ _ ⟩
    vowels [ l↓ ] + ♯vowels ls
  ≡˘⟨ vowels∷ {l↓} ⟩
    vowels (l↓ ∷ ls)
  ∎

Di-vowels≡2 : Diphthong (l , l′) → vowels [ l ⨾ l′ ] ≡ 2
Di-vowels≡2 {l}{l′} di =
  let
    vl , vl′ = Di⇒Vowel di
    open ≡-Reasoning
  in
  begin
    vowels [ l ⨾ l′ ]
  ≡⟨ cong length $ L.filter-accept Vowel? vl ⟩
    1 + vowels [ l′ ]
  ≡⟨ cong (suc ∘ length) $ L.filter-accept Vowel? vl′ ⟩
    2
  ∎

∣Dipthong∣>1 : Any× Diphthong sy → vowels sy > 1
∣Dipthong∣>1 {sy} di∈ =
  let (l , l′) , di∈ , di = satisfied′ di∈
  in subst (_ ≥_) (Di-vowels≡2 di) (vowelsDi di∈)

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

𝟙-theQuantity? :
  (sy : Syllable) →
    (∃ λ (q : Quantity) →
        (sy ~ q)
      × (∀ {q′} → sy ~ q′ → q′ ≡ q))
  ⊎ NonDerivable {B = Quantity} sy
𝟙-theQuantity? sy
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

_~₁?_ : ∀ (sy : Syllable) (q : Quantity) → Dec (sy ~ q)
sy ~₁? q
  with 𝟙-theQuantity? sy
... | inj₂ sy≁   = no λ sy~q → sy≁ _ sy~q
... | inj₁ (q′ , sy~q′ , unique-q′)
  with q ≟ q′
... | yes refl = yes sy~q′
... | no  q≢   = no λ sy~q → q≢ (unique-q′ sy~q)

𝟙-theQuantity :
  (sy : Syllable) →
  ∃ λ (mq : Flat Quantity) →
      (sy ~ mq)
    × (∀ {mq′} → sy ~ mq′ → mq′ ≡ mq)
𝟙-theQuantity sy
  with 𝟙-theQuantity? sy
... | inj₁ (q , sy~q , complete-q)
  = single q , byNature sy~q , λ where
    (byNature sy~q) → cong single (complete-q sy~q)
    (doubtful sy≁) → ⊥-elim $ sy≁ q sy~q
... | inj₂ sy≁
  = none
  , doubtful sy≁
  , λ where (byNature sy~q) → ⊥-elim $ sy≁ _ sy~q
            (doubtful sy≁) → refl

𝟙-theQuantities :
  (sys : Syllables n) →
  ∃ λ (mqs : Quantities n) →
      (sys ~ mqs)
    × (∀ {mqs′} → sys ~ mqs′ → mqs′ ≡ mqs)
𝟙-theQuantities [] = [] , [] , (λ where [] → refl)
𝟙-theQuantities {n = suc n} (sy ∷ sys) =
  let
    mq , sy~mq , complete-mq = 𝟙-theQuantity sy
    mqs , sys~mqs , complete-mqs = 𝟙-theQuantities {n = n} sys
  in
    mq ∷ mqs
  , sy~mq ∷ sys~mqs
  , λ where (sy~ ∷ sys~) → cong₂ _∷_ (complete-mq sy~) (complete-mqs sys~)
