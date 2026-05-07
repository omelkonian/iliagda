{-# OPTIONS --safe #-}
module Prelude.Vectors where

open import Iliagda.Init

private variable
  x y z : A
  xs : Vec A n
  P Q R : A → Type

_≔ₙ_ : Vec A (1 + n) → A → Vec A (1 + n)
_≔ₙ_ {n = n} xs = xs V.[ lastIndex ]≔_
  where lastIndex = Fi.fromℕ n

_≔ₙ₋₁_ : Vec A (2 + n) → A → Vec A (2 + n)
_≔ₙ₋₁_ {n = n} xs = xs V.[ penultIndex ]≔_
  where penultIndex = Fi.inject₁ $ Fi.fromℕ n

_≔ₙ⟨_⟩_ : Vec A n → n > 0 → A → Vec A n
_≔ₙ⟨_⟩_ {n = suc n} xs _ = xs ≔ₙ_

infix 10 _≔ₙ_ _≔ₙ₋₁_ _≔ₙ⟨_⟩_

module _ (P : A → Type) where
  data InUlt : Vec A n → Type where
    here  : P x → InUlt [ x ]
    there : InUlt xs → InUlt (x ∷ xs)

  data InPenult : Vec A n → Type where
    here  : P x → InPenult [ x ⨾ y ]
    there : InPenult xs → InPenult (x ∷ xs)

  data InAntepenult : Vec A n → Type where
    here  : P x → InAntepenult [ x ⨾ y ⨾ z ]
    there : InAntepenult xs → InAntepenult (x ∷ xs)

module _ (f : P ⊆¹ Q) where
  InUlt-map : InUlt P xs → InUlt Q xs
  InUlt-map = λ where
    (here p) → here (f p)
    (there ps) → there (InUlt-map ps)

  InPenult-map : InPenult P xs → InPenult Q xs
  InPenult-map = λ where
    (here p) → here (f p)
    (there ps) → there (InPenult-map ps)

  InAntepenult-map : InAntepenult P xs → InAntepenult Q xs
  InAntepenult-map = λ where
    (here p) → here (f p)
    (there ps) → there (InAntepenult-map ps)

InUlt-elim : ¬ InUlt (const ⊥) xs
InUlt-elim (there ps) = InUlt-elim ps

InPenult-elim : ¬ InPenult (const ⊥) xs
InPenult-elim (there ps) = InPenult-elim ps

InAntepenult-elim : ¬ InAntepenult (const ⊥) xs
InAntepenult-elim (there ps) = InAntepenult-elim ps

module _ (¬P : P ⊆¹ const ⊥) where
  ¬InUlt : ¬ InUlt P xs
  ¬InUlt = InUlt-elim ∘ InUlt-map ¬P

  ¬InPenult : ¬ InPenult P xs
  ¬InPenult = InPenult-elim ∘ InPenult-map ¬P

  ¬InAntepenult : ¬ InAntepenult P xs
  ¬InAntepenult = InAntepenult-elim ∘ InAntepenult-map ¬P

module _ ⦃ _ : P ⁇¹ ⦄ where instance
  Dec-InUlt : InUlt P xs ⁇
  Dec-InUlt {xs = xs} .dec
    with xs
  ... | [] = no λ ()
  ... | [ x ] = mapDec here (λ where (here p) → p) ¿ P x ¿
  ... | _ ∷ xs@(_ ∷ _) = mapDec there (λ where (there p) → p) ¿ InUlt P xs ¿

  Dec-InPenult : InPenult P xs ⁇
  Dec-InPenult {xs = xs} .dec
    with xs
  ... | [] = no λ ()
  ... | [ _ ] = no λ where (there ())
  ... | [ x ⨾ y ] = mapDec here (λ where (here p) → p; (there (there ()))) ¿ P x ¿
  ... | _ ∷ xs@(_ ∷ (_ ∷ _)) = mapDec there (λ where (there p) → p) ¿ InPenult P xs ¿

  Dec-InAntepenult : InAntepenult P xs ⁇
  Dec-InAntepenult {xs = xs} .dec
    with xs
  ... | [] = no λ ()
  ... | [ _ ] = no λ where (there ())
  ... | [ _ ⨾ _ ] = no λ where (there (there ()))
  ... | [ x ⨾ y ⨾ z ] =
    mapDec here (λ where (here p) → p; (there (there (there ())))) ¿ P x ¿
  ... | _ ∷ xs@(_ ∷ (_ ∷ (_ ∷ _))) =
    mapDec there (λ where (there p) → p) ¿ InAntepenult P xs ¿

data LastThree (P : List A → Type) : Vec A n → Type where
  here₀ : LastThree P []
  here₁ : P [ x ] → LastThree P [ x ]
  here₂ : P [ x ⨾ y ] → LastThree P [ x ⨾ y ]
  here₃ : P [ x ⨾ y ⨾ z ] → LastThree P [ x ⨾ y ⨾ z ]
  there : {xs : Vec A (3 + n)} → LastThree P xs → LastThree P (x ∷ xs)

module _ {P Q : List A → Type} (f : P ⊆¹ Q) where
  LastThree-map : LastThree P xs → LastThree Q xs
  LastThree-map = λ where
    here₀ → here₀
    (here₁ p) → here₁ (f p)
    (here₂ p) → here₂ (f p)
    (here₃ p) → here₃ (f p)
    (there ps) → there (LastThree-map ps)

module _ {P Q : List A → Type} where
  LastThree-∩⁻ : LastThree (P ∩¹ Q) xs → LastThree P xs × LastThree Q xs
  LastThree-∩⁻ pq = LastThree-map proj₁ pq , LastThree-map proj₂ pq

  LastThree-∩⁻ˡ : LastThree (P ∩¹ Q) xs → LastThree P xs
  LastThree-∩⁻ˡ = proj₁ ∘ LastThree-∩⁻

  LastThree-∩⁻ʳ : LastThree (P ∩¹ Q) xs → LastThree Q xs
  LastThree-∩⁻ʳ = proj₂ ∘ LastThree-∩⁻

module _ {P : List A → Type} ⦃ _ : P ⁇¹ ⦄ where instance
  Dec-LastThree : LastThree P xs ⁇
  Dec-LastThree {xs = xs} .dec
    with xs
  ... | [] = yes here₀
  ... | [ x ] = mapDec here₁ (λ where (here₁ p) → p) ¿ P [ x ] ¿
  ... | [ x ⨾ y ] = mapDec here₂ (λ where (here₂ p) → p) ¿ P [ x ⨾ y ] ¿
  ... | [ x ⨾ y ⨾ z ] = mapDec here₃ (λ where (here₃ p) → p) ¿ P [ x ⨾ y ⨾ z ] ¿
  ... | _ ∷ xs@(_ ∷ (_ ∷ (_ ∷ _)))
    = mapDec there (λ where (there p) → p)
      ¿ LastThree P xs ¿

None : (A → Type) → List A → Type
None P = All (¬_ ∘ P)

data Affinely (P : A → Type) : List A → Type where
  []   : Affinely P []
  _∷_  : ∀ {xs} → P x → None P xs → Affinely P (x ∷ xs)
  _¬∷_ : ∀ {xs} → ¬ P x → Affinely P xs → Affinely P (x ∷ xs)

Affinely⁺ : (A → Type) → List⁺ A → Type
Affinely⁺ P = Affinely P ∘ toList

module _ ⦃ _ : P ⁇¹ ⦄ where instance
  Dec-Affinely : Affinely P ⁇¹
  Dec-Affinely {x = xs} .dec
    with xs
  ... | [] = yes []
  ... | x ∷ xs
    with ¿ P x ¿
  ... | yes px
    = mapDec (px ∷_) (λ where (_ ∷ ¬pxs) → ¬pxs; (¬px ¬∷ _) → ⊥-elim $ ¬px px)
      ¿ None P xs ¿
  ... | no ¬px
    = mapDec (¬px ¬∷_) (λ where (_ ¬∷ pxs) → pxs; (px ∷ _) → ⊥-elim $ ¬px px)
      ¿ Affinely P xs ¿

None⇒Affinely : None P ⊆¹ Affinely P
None⇒Affinely = λ where
  [] → []
  (¬p ∷ ¬ps) → ¬p ¬∷ None⇒Affinely ¬ps

Affinely-uncons : ∀ {xs} → Affinely P (x ∷ xs) → Affinely P xs
Affinely-uncons = λ where
  (p ∷ ¬ps) → None⇒Affinely ¬ps
  (_ ¬∷ ps) → ps

None⇒¬Ult : None P (toList xs) → ¬ InUlt P xs
None⇒¬Ult {xs = _ ∷ _} (¬p ∷ ¬ps) = λ where
  (here p)  → ¬p p
  (there u) → None⇒¬Ult ¬ps u

None⇒¬Penult : None P (toList xs) → ¬ InPenult P xs
None⇒¬Penult {xs = _ ∷ _} (¬p ∷ ¬ps) = λ where
  (here p)  → ¬p p
  (there u) → None⇒¬Penult ¬ps u

None⇒¬Antepenult : None P (toList xs) → ¬ InAntepenult P xs
None⇒¬Antepenult {xs = _ ∷ _} (¬p ∷ ¬ps) = λ where
  (here p)  → ¬p p
  (there u) → None⇒¬Antepenult ¬ps u

module _
  (Q⇒P : Q ⊆¹ P)
  (R⇒P : R ⊆¹ P)
  (¬Q×R : ∀ {x} → Q x → R x → ⊥)
  where

  AffinelyP⇒¬Q×R : ¬ (Affinely P ∩¹ Any Q ∩¹ Any R) x
  AffinelyP⇒¬Q×R = λ where
    ((_ ∷ _) , here q , here r) → ¬Q×R q r
    ((_ ∷ 0p) , there q , _) → L.All.All¬⇒¬Any 0p $ L.Any.map Q⇒P q
    ((_ ∷ 0p) , _ , there r) → L.All.All¬⇒¬Any 0p $ L.Any.map R⇒P r
    ((¬p ¬∷ _) , here q , _) → ¬p $ Q⇒P q
    ((¬p ¬∷ _) , _ , here r) → ¬p $ R⇒P r
    ((_ ¬∷ 1p) , there q , there r) → AffinelyP⇒¬Q×R (1p , q , r)

Affinely⇒¬[Ult×Penult] : {xs : Vec A n} →
  Affinely P (toList xs) →
  ¬ (InUlt P xs × InPenult P xs)
Affinely⇒¬[Ult×Penult] {xs = []} [] (() , _)
Affinely⇒¬[Ult×Penult] {xs = _ ∷ _} = λ where
  (_ ∷ _) (here _ , there ())
  (_ ∷ ¬ps) (there u , _) → None⇒¬Ult ¬ps u
  (¬p ¬∷ _) (there _ , here p) → ¬p p
  (_ ¬∷ aff) (there u , there pu) → Affinely⇒¬[Ult×Penult] aff (u , pu)

Affinely⇒¬[Penult×Antepenult] : {xs : Vec A n} →
  Affinely P (toList xs) →
  ¬ (InPenult P xs × InAntepenult P xs)
Affinely⇒¬[Penult×Antepenult] {xs = []} [] (() , _)
Affinely⇒¬[Penult×Antepenult] {xs = _ ∷ _} = λ where
  (_ ∷ _) (here _ , there (there ()))
  (_ ∷ ¬ps) (there u , _) → None⇒¬Penult ¬ps u
  (_ ¬∷ _) (here _ , there (there ()))
  (¬p ¬∷ _) (there _ , here p) → ¬p p
  (_ ¬∷ aff) (there u , there pu) → Affinely⇒¬[Penult×Antepenult] aff (u , pu)

InPenult-∩⁺ :
  ∙ InPenult P xs
  ∙ InPenult Q xs
    ────────────────────
    InPenult (P ∩¹ Q) xs
InPenult-∩⁺ = λ where
  (here p) (here q) → here (p , q)
  (here _) (there (there ()))
  (there (there ())) (here _)
  (there p) (there q) → there (InPenult-∩⁺ p q)

3All⇒Penult : {xs : Vec A n} →
  ∙ LastThree (All P) xs
  ∙ InPenult Q xs
    ────────────────────
    InPenult (P ∩¹ Q) xs
3All⇒Penult = λ where
  (here₁ _) (there ())
  (here₂ (p ∷ _)) (here q) → here (p , q)
  (here₂ _) (there (there ()))
  (here₃ (_ ∷ p ∷ _)) (there (here q)) → there (here (p , q))
  (here₃ _) (there (there (there ())))
  (there p) (there q) → there (3All⇒Penult p q)

3Affinely⇒¬[Ult×Penult] : {xs : Vec A n} →
  LastThree (Affinely P) xs →
  ¬ (InUlt P xs × InPenult P xs)
3Affinely⇒¬[Ult×Penult] = λ where
  here₀ (() , _)
  (here₁ _) (_ , there ())
  (here₂ aff) (u , pu) → Affinely⇒¬[Ult×Penult] aff (u , pu)
  (here₃ aff) (u , pu) → Affinely⇒¬[Ult×Penult] aff (u , pu)
  (there l) (there u , there pu) → 3Affinely⇒¬[Ult×Penult] l (u , pu)

3Affinely⇒¬[Penult×Antepenult] : {xs : Vec A n} →
  LastThree (Affinely P) xs →
  ¬ (InPenult P xs × InAntepenult P xs)
3Affinely⇒¬[Penult×Antepenult] = λ where
  here₀ (() , _)
  (here₁ _) (_ , there ())
  (here₂ aff) (u , pu) → Affinely⇒¬[Penult×Antepenult] aff (u , pu)
  (here₃ aff) (u , pu) → Affinely⇒¬[Penult×Antepenult] aff (u , pu)
  (there l) (there u , there pu) → 3Affinely⇒¬[Penult×Antepenult] l (u , pu)

data Last (P : A → Type) : List A → Type where
  here  : P x → Last P [ x ]
  there : ∀ {xs} → Last P xs → Last P (x ∷ xs)

module _ ⦃ _ : P ⁇¹ ⦄ where instance
  Dec-Last : Last P ⁇¹
  Dec-Last {x = xs} .dec
    with xs
  ... | [] = no λ ()
  ... | [ x ] = mapDec here (λ where (here p) → p) ¿ P x ¿
  ... | _ ∷ xs@(_ ∷ _) = mapDec there (λ where (there p) → p) ¿ Last P xs ¿

Last⁺ : (A → Type) → List⁺ A → Type
Last⁺ P = Last P ∘ toList
