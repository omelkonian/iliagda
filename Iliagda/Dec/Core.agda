-- {-# OPTIONS --safe #-}
module Iliagda.Dec.Core where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core

-- ** decidable equality
-- unquoteDecl DecEq-Letter = derive-DecEq [ quote Letter , DecEq-Letter ]
unquoteDecl DecEq-Quantity = derive-DecEq [ quote Quantity , DecEq-Quantity ]
-- unquoteDecl DecEq-Foot = derive-DecEq [ quote Foot , DecEq-Foot ]
instance
  DecEq-Foot : DecEq (Foot n qs)
  DecEq-Foot ._≟_ = λ where
    ──  ──  → yes refl
    ─·· ─·· → yes refl

open import Data.Char using (Char)

toChar : Letter → Char
toChar = λ where
  Ἀ → 'Ἀ'
  Ἄ → 'Ἄ'
  α → 'α'
  ἄ → 'ἄ'
  ὰ → 'ὰ'
  ά → 'ά'
  ε → 'ε'
  έ → 'έ'
  ἔ → 'ἔ'
  η → 'η'
  ῆ → 'ῆ'
  ἣ → 'ἣ'
  ι → 'ι'
  ί → 'ί'
  ἰ → 'ἰ'
  ῖ → 'ῖ'
  ϊ → 'ϊ'
  ΐ → 'ΐ'
  ο → 'ο'
  υ → 'υ'
  ὐ → 'ὐ'
  ω → 'ω'
  Γ → 'Γ'
  γ → 'γ'
  Δ → 'Δ'
  δ → 'δ'
  Ζ → 'Ζ'
  ζ → 'ζ'
  Θ → 'Θ'
  θ → 'θ'
  Κ → 'Κ'
  κ → 'κ'
  Λ → 'Λ'
  ƛ → 'ƛ'
  Μ → 'Μ'
  μ → 'μ'
  Ν → 'Ν'
  ν → 'ν'
  Ξ → 'Ξ'
  ξ → 'ξ'
  Π → 'Π'
  π → 'π'
  Ρ → 'Ρ'
  ρ → 'ρ'
  Σ → 'Σ'
  σ → 'σ'
  ς → 'ς'
  Τ → 'Τ'
  τ → 'τ'
  Φ → 'Φ'
  φ → 'φ'
  Χ → 'Χ'
  χ → 'χ'
  Ψ → 'Ψ'
  ψ → 'ψ'

_≈_ : Letter → Letter → Type
l ≈ l′ = toChar l ≡ toChar l′

open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

-- postulate
≈-sound : l ≈ l′ → l ≡ l′
≈-sound _ = trustMe

instance
  DecEq-Letter : DecEq Letter
  DecEq-Letter ._≟_ x y
    with toChar x ≟ toChar y
  ... | yes eq = yes (≈-sound eq)
  ... | no ¬eq = no  λ where refl → ¬eq refl
