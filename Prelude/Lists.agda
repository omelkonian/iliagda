{-# OPTIONS --safe #-}
module Prelude.Lists where

open import Class.Prelude hiding ([_])
open L using (mapMaybe)
open Nat using (ℕ; _∸_)
open import Data.Nat.ListAction using (sum)
open import Relation.Unary using () renaming (_⊆_ to _⊆¹_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to anyMap)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; mapMaybe⁺)
open import Data.Maybe.Relation.Unary.Any using (just)

open import Class.Anyable
open import Class.ToList
open import Class.Bifunctor

-- ** list notation

pattern [_] x = x ∷ []
pattern [_⨾_] x y = x ∷ [ y ]
pattern [_⨾_⨾_] x y z = x ∷ [ y ⨾ z ]
pattern [_⨾_⨾_⨾_] x y z w = x ∷ [ y ⨾ z ⨾ w ]
pattern [_⨾_⨾_⨾_⨾_] x y z w q = x ∷ [ y ⨾ z ⨾ w ⨾ q ]
pattern [_⨾_⨾_⨾_⨾_⨾_] x y z w q r = x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s = x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t = x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v = x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e f =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ⨾ f ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e f g =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ⨾ f ⨾ g ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e f g h =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ⨾ f ⨾ g ⨾ h ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e f g h i =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ⨾ f ⨾ g ⨾ h ⨾ i ]
pattern [_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_⨾_] x y z w q r s t v p o u k l m n b c d e f g h i j =
  x ∷ [ y ⨾ z ⨾ w ⨾ q ⨾ r ⨾ s ⨾ t ⨾ v ⨾ p ⨾ o ⨾ u ⨾ k ⨾ l ⨾ m ⨾ n ⨾ b ⨾ c ⨾ d ⨾ e ⨾ f ⨾ g ⨾ h ⨾ i ⨾ j ]

-- ** sums

∑₁ : ∀ {X : ℕ → Type ℓ} → List (∃ X) → ℕ
∑₁ = sum ∘ map proj₁

-- ** pairs

pairs : List A → List (A × A)
pairs = λ where
  (x ∷ y ∷ xs) → (x , y) ∷ pairs (y ∷ xs)
  _            → []

private
  Pred₀ : Type → Type₁
  Pred₀ A = A → Type

Any× : Pred₀ (A × A) → Pred₀ (List⁺ A)
Any× P = Any P ∘ pairs ∘ toList

triples : List A → List (A × A × A)
triples = map (map₁ proj₁) ∘ pairs ∘ pairs

Any×₃ : Pred₀ (A × A × A) → Pred₀ (List⁺ A)
Any×₃ P = Any P ∘ triples ∘ toList

-- -- ** mapMaybe

private variable
  xs ys : List A

module _ (f : A → Maybe B) where

  mapMaybe-++ : ∀ xs ys → mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  mapMaybe-++ []       ys = refl
  mapMaybe-++ (x ∷ xs) ys with f x
  ... | just _  = cong (_ ∷_) (mapMaybe-++ xs ys)
  ... | nothing = mapMaybe-++ xs ys

  -- ** mapMaybe⁻

  ≡just⇒MAny :
      f x ≡ just y
    → (x ≡_) ⊆¹ Any (_≡_ y) ∘ f
  ≡just⇒MAny eq refl = subst (Any (_ ≡_)) (sym eq) (just refl)

  ∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
  ∈-mapMaybe⁺ x∈ eq
    = mapMaybe⁺ _ _
    $ map⁺
    $ anyMap (≡just⇒MAny eq) x∈

  ∈-mapMaybe⁻ : y ∈ mapMaybe f xs
              → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
  ∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
    with f x in fx≡
  ... | nothing = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈)
  ... | just y′
    with y∈
  ... | here refl = x , here refl , fx≡
  ... | there y∈′ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈′)

-- ** membership

satisfied′ : ∀ {A : Type} {P : A → Type} {xs : List A}
  → Any P xs
  → ∃ λ x → x ∈ xs × P x
satisfied′ = λ where
  (here px)   → _ , here refl , px
  (there pxs) → let x , x∈ , px = satisfied′ pxs
                in  x , there x∈ , px

-- ** begins/ends with some sequence of predicates

CheckList : List (A → Type) → List A → Type
CheckList (P ∷ Ps) (x ∷ xs) = P x × CheckList Ps xs
CheckList (_ ∷ _)  []       = ⊥
CheckList []       _        = ⊤

module _ (Ps : List (A → Type)) where
  BeginsWith EndsWith : List A → Type
  BeginsWith xs = CheckList Ps $ L.take (length Ps) xs
  EndsWith   xs = CheckList Ps $ L.drop (length xs ∸ length Ps) xs

private variable Ps : List (A → Type)

CheckList? : All Decidable¹ Ps → Decidable¹ (CheckList Ps)
CheckList? [] _ = yes tt
CheckList? (_ ∷ _) [] = no λ ()
CheckList? (P? ∷ Ps?) (x ∷ xs)
  with P? x
... | no ¬px = no $ ¬px ∘ proj₁
... | yes px
  with CheckList? Ps? xs
... | no ¬pxs = no $ ¬pxs ∘ proj₂
... | yes pxs = yes (px , pxs)

BeginsWith? : All Decidable¹ Ps → Decidable¹ (BeginsWith Ps)
BeginsWith? Ps? _ = CheckList? Ps? _

EndsWith? : All Decidable¹ Ps → Decidable¹ (EndsWith Ps)
EndsWith? Ps? _ = CheckList? Ps? _
