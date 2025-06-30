module Iliagda.Prosody.Core where

open import Iliagda.Init
open import Iliagda.Morphology

data Quantity : Type where
  · {- short -} : Quantity
  ─ {- long  -} : Quantity
unquoteDecl DecEq-Quantity = DERIVE DecEq [ quote Quantity , DecEq-Quantity ]

data Foot : (n : ℕ) {- syllables -} → Vec Quantity n → Type where
  ─·· {- dactyl -} : Foot 3 (─ ∷ · ∷ · ∷ [])
  ──  {- sponde -} : Foot 2 (─ ∷ ─ ∷ [])
unquoteDecl DecEq-Foot = DERIVE DecEq [ quote Foot , DecEq-Foot ]
∃∃Foot = ∃ (∃ ∘ Foot)

Feet = List ∃∃Foot

data Meter : ℕ {- syllables -} → ℕ {- feet -} → Type where
  mkPM : (fs : Feet) → Meter (∑₁ fs) (length fs)

Hexameter : ℕ {- syllables -} → Type
Hexameter n = Meter n 6

variable
  q q′ : Quantity
  qs qs′ : Vec Quantity n
  mq mq′ mq″ : Maybe Quantity
  mqs mqs′ : Vec (Maybe Quantity) n
  pm  : Meter n m
  pm′ : Meter n′ m′
  meter meter′ : Hexameter n

_∷ᵖᵐ_ : Foot n qs → Meter n′ m′ → Meter (n + n′) (1 + m′)
f ∷ᵖᵐ (mkPM fs) = mkPM ((-, -, f) ∷ fs)
