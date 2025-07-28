{-# OPTIONS --safe #-}
module Iliagda.Init where

open import Agda.Primitive public
  using () renaming (Set to Type; Setω to Typeω)
open import Level public
  using (Level; 0ℓ) renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
open import Function public
  using (id; _∘_; _∘′_; _∘₂_; _$_; _$′_; const; flip; it; case_of_; _on_; _∋_)

open import Data.Empty public
  using (⊥; ⊥-elim)
open import Data.Unit public
  using (⊤; tt)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Product public
  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; -,_; curry; uncurry)

module 𝔹 where
  open import Data.Bool public
  open import Data.Bool.Properties public
  open import Data.Bool.ListAction public
open 𝔹 public
  using (Bool; true; false; if_then_else_)

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Data.Nat.ListAction public
open Nat public
  using ( ℕ; zero; suc; _+_
        ; _≤_; _≥_; _<_; _>_; z≤n; s≤s
        )

module May where
  open import Data.Maybe public
  open import Data.Maybe.Properties public
  module All where
    open import Data.Maybe.Relation.Unary.All public
    open import Data.Maybe.Relation.Unary.All.Properties public
  module Any where
    open import Data.Maybe.Relation.Unary.Any public

open May public
  using (Maybe; just; nothing; maybe; fromMaybe; Is-nothing; Is-just)
open May.All public
  using (just; nothing)
open May.Any public
  using (just)

module Fi where
  open import Data.Fin public
  open import Data.Fin.Properties public
open Fi public
  using (Fin) renaming (suc to fsuc)

module L where
  open import Data.List public
  open import Data.List.Properties public
  module All where
    open import Data.List.Relation.Unary.All public
    open import Data.List.Relation.Unary.All.Properties public
  module Any where
    open import Data.List.Relation.Unary.Any public
    open import Data.List.Relation.Unary.Any.Properties public
  module Mem where
    open import Data.List.Membership.Propositional public
    open import Data.List.Membership.Propositional.Properties public
  module NE where
    open import Data.List.NonEmpty public
    open import Data.List.NonEmpty.Properties public
open L public
  using (List; []; _∷_; _∷ʳ_; length; map; mapMaybe; concat; concatMap; _++_)
open L.NE public
  using (List⁺; _∷_; head; last; _⁺∷ʳ_; _⁺++⁺_) renaming (length to length⁺)
open L.All public
  using ([]; _∷_)
open L.Any public
  using (here; there)
open L.Mem public

module V where
  open import Data.Vec public
  open import Data.Vec.Properties public
  module Mem where
    open import Data.Vec.Membership.Propositional public
    open import Data.Vec.Membership.Propositional.Properties public
  module PW where
    open import Data.Vec.Relation.Binary.Pointwise.Inductive public

open V public
  using (Vec; []; _∷_)
open V.PW public
  using ([]; _∷_)
  renaming (Pointwise to VPointwise)

open import Relation.Nullary public
  using (¬_)
open import Relation.Nullary.Decidable.Core public
  using (Dec; yes; no; ⌊_⌋; ¬?) renaming (map′ to mapDec)
open import Relation.Unary public
  using (Pred) renaming (_∪_ to _∪₁_; _∩_ to _∩¹_; _⊆_ to _⊆¹_)
open import Relation.Binary public
  using (Rel)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; _≢_; sym; trans; cong; subst; module ≡-Reasoning)

Pred₀ : Type → Type₁
Pred₀ A = A → Type

Rel₀ : Type → Type₁
Rel₀ A = A → A → Type

open import Class.Functor public
open import Class.Bifunctor public
open import Class.DecEq public
open import Class.DecEq.WithK public
open import Class.Decidable public
open import Class.Semigroup public
open import Class.Monoid public
  renaming (ε to ∅)
open import Class.Anyable public
open import Class.Allable public
open import Class.ToList public
open import Class.FromList public
open import Class.ToN public
open import Class.FromN public

open import Tactic.Defaults public
open import Tactic.Derive.DecEq public

variable
  ℓ ℓ′ ℓ″ : Level
  X Y A B C : Type
  n n′ m m′ : ℕ

-- ** singleton types

data Is {A : Type ℓ} : A → Type ℓ where
  ⟫_ : (x : A) → Is x
infix -100 ⟫_

-- ** utilities from omelkonian/formal-prelude

open import Prelude.Lists public
open import Prelude.InferenceRules public
