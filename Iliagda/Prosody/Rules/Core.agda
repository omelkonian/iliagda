{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Core where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis

-- A complies with B
record _-compliesWith-_ (A B : Type) : Type₁ where
  infix 0 _~_
  field _~_ : A → B → Type
  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_

  NonDerivable NonDerivable∃ : A → Type
  NonDerivable  a = ∀ b → a ≁ b
  NonDerivable∃ a = ¬ ∃ λ b → a ~ b

  NonDerivable′ NonDerivable∃′ : B → Type
  NonDerivable′  b = ∀ a → a ≁ b
  NonDerivable∃′ b = ¬ ∃ λ a → a ~ b

  NonDerivable∃⇒ : ∀ {a} → NonDerivable∃ a → NonDerivable a
  NonDerivable∃⇒ ∄b b a~b = ∄b (b , a~b)

  NonDerivable∃′⇒ : ∀ {b} → NonDerivable∃′ b → NonDerivable′ b
  NonDerivable∃′⇒ ∄a a a~b = ∄a (a , a~b)

open _-compliesWith-_ ⦃ ... ⦄ public

-- ** quantity knowledge

data Flat (A : Type) : Type where
  single : A → Flat A
  none   : Flat A
  all    : Flat A

Quantities : ℕ → Type
Quantities = Vec (Flat Quantity)

variable
  mq mq′ mq″ : Flat Quantity
  mqs mqs′ : Quantities n

synezize : ∀ {sys : Syllables n} {sys′ : Syllables n′}
  (syn : sys -synezizes*- sys′) →
  Quantities n →
  Quantities n′
synezize = λ where
  []        mqs           → mqs
  (_ ∷ syn) (mq ∷ mqs)    → mq ∷ synezize syn mqs
  (_ ∺ syn) (_ ∷ _ ∷ mqs) → single ─ ∷ synezize syn mqs


-- _⊔_ _⊓_ : DecEq A  Op₂ (Flat A)
-- _⊔_ = λ where
--   (single x) (single y) → single ?
-- _⊓_ = λ where

-- isFlatLattice : IsLattice _⊔_ _⊓_
-- isFlatLattice = ...

-- ** enumerations

record Enumeration (_~_ : A → B → Type) : Type where
  field
    allBs    : A → List B
    sound    : ∀ {a b} → b ∈ allBs a → a ~ b
    complete : ∀ {a b} → a ~ b → b ∈ allBs a
open Enumeration public
