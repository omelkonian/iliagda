{-# OPTIONS --safe #-}
module Prelude.Lists where

open import Agda.Primitive using () renaming (Set to Type)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Level using (Level)
open import Function using (_∘_; _$_)
open import Data.Product using (_×_; _,_; ∃; proj₁)
open import Data.Nat using (ℕ)
open import Data.Nat.ListAction using (sum)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map; mapMaybe; _++_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Unary using () renaming (_⊆_ to _⊆¹_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to anyMap)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; mapMaybe⁺)
open import Data.Maybe.Relation.Unary.Any using (just)

open import Class.Anyable
open import Class.ToList
open import Class.Bifunctor

private
  Pred₀ : Type → Type₁
  Pred₀ A = A → Type

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

-- ** sums

private variable
  ℓ : Level
  A B : Type

∑₁ : ∀ {X : ℕ → Type ℓ} → List (∃ X) → ℕ
∑₁ = sum ∘ map proj₁

-- ** pairs

pairs : List A → List (A × A)
pairs = λ where
  (x ∷ y ∷ xs) → (x , y) ∷ pairs (y ∷ xs)
  _            → []

Any× : Pred₀ (A × A) → Pred₀ (List⁺ A)
Any× P = Any P ∘ pairs ∘ toList

triples : List A → List (A × A × A)
triples = map (map₁ proj₁) ∘ pairs ∘ pairs

Any×₃ : Pred₀ (A × A × A) → Pred₀ (List⁺ A)
Any×₃ P = Any P ∘ triples ∘ toList

-- -- ** mapMaybe

private variable
  x x′ y : A
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
