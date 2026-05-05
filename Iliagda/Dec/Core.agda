{-# OPTIONS --safe #-}
module Iliagda.Dec.Core where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core

-- ** decidable equality
unquoteDecl DecEq-Quantity = derive-DecEq [ quote Quantity , DecEq-Quantity ]
unquoteDecl DecEq-Foot = derive-DecEq [ quote Foot , DecEq-Foot ]

-- INCOMPLETE: add as needed
toChar : Letter → Char
toChar = λ where
  Ἀ → 'Ἀ'
  Ἄ → 'Ἄ'
  α → 'α'
  ἀ → 'ἀ'
  ἁ → 'ἁ'
  ἂ → 'ἂ'
  ἄ → 'ἄ'
  ὰ → 'ὰ'
  ά → 'ά'
  ᾶ → 'ᾶ'
  ᾷ → 'ᾷ'
  ε → 'ε'
  ἐ → 'ἐ'
  ἑ → 'ἑ'
  ἔ → 'ἔ'
  ἕ → 'ἕ'
  έ → 'έ'
  ὲ → 'ὲ'
  η → 'η'
  ῆ → 'ῆ'
  ῇ → 'ῇ'
  ῃ → 'ῃ'
  ἠ → 'ἠ'
  ἡ → 'ἡ'
  ἢ → 'ἢ'
  ἣ → 'ἣ'
  ἤ → 'ἤ'
  ἦ → 'ἦ'
  ἥ → 'ἥ'
  Ἥ → 'Ἥ'
  ή → 'ή'
  ὴ → 'ὴ'
  ᾔ → 'ᾔ'
  ι → 'ι'
  ί → 'ί'
  ὶ → 'ὶ'
  ἰ → 'ἰ'
  ἱ → 'ἱ'
  ἳ → 'ἳ'
  ἴ → 'ἴ'
  ἶ → 'ἶ'
  Ἴ → 'Ἴ'
  ῖ → 'ῖ'
  ϊ → 'ϊ'
  ΐ → 'ΐ'
  ῒ → 'ῒ'
  ο → 'ο'
  Ο → 'Ο'
  ὀ → 'ὀ'
  Ὀ → 'Ὀ'
  ὁ → 'ὁ'
  ὃ → 'ὃ'
  ὄ → 'ὄ'
  ὅ → 'ὅ'
  ό → 'ό'
  ὸ → 'ὸ'
  υ → 'υ'
  ὐ → 'ὐ'
  ὑ → 'ὑ'
  ὔ → 'ὔ'
  ὖ → 'ὖ'
  ὕ → 'ὕ'
  ὗ → 'ὗ'
  ὺ → 'ὺ'
  ύ → 'ύ'
  ῦ → 'ῦ'
  ϋ → 'ϋ'
  ΰ → 'ΰ'
  ω → 'ω'
  ὠ → 'ὠ'
  ὣ → 'ὣ'
  ὤ → 'ὤ'
  ὥ → 'ὥ'
  ὦ → 'ὦ'
  ᾤ → 'ᾤ'
  ᾧ → 'ᾧ'
  ώ → 'ώ'
  ὼ → 'ὼ'
  ῶ → 'ῶ'
  ῳ → 'ῳ'
  ῴ → 'ῴ'
  ῷ → 'ῷ'
  ὡ → 'ὡ'
  Β → 'Β'
  β → 'β'
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
  ῥ → 'ῥ'
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
  ᾽ → '᾽'

-- INCOMPLETE: add as needed
toChar-inj : Injective _≡_ _≡_ toChar
toChar-inj {Ἀ} {Ἀ} refl = refl
toChar-inj {Ἄ} {Ἄ} refl = refl
toChar-inj {α} {α} refl = refl
toChar-inj {ἀ} {ἀ} refl = refl
toChar-inj {ἁ} {ἁ} refl = refl
toChar-inj {ἂ} {ἂ} refl = refl
toChar-inj {ἄ} {ἄ} refl = refl
toChar-inj {ὰ} {ὰ} refl = refl
toChar-inj {ά} {ά} refl = refl
toChar-inj {ᾶ} {ᾶ} refl = refl
toChar-inj {ᾷ} {ᾷ} refl = refl
toChar-inj {ε} {ε} refl = refl
toChar-inj {ἐ} {ἐ} refl = refl
toChar-inj {ἑ} {ἑ} refl = refl
toChar-inj {ἔ} {ἔ} refl = refl
toChar-inj {ἕ} {ἕ} refl = refl
toChar-inj {έ} {έ} refl = refl
toChar-inj {ὲ} {ὲ} refl = refl
toChar-inj {η} {η} refl = refl
toChar-inj {ῆ} {ῆ} refl = refl
toChar-inj {ῇ} {ῇ} refl = refl
toChar-inj {ῃ} {ῃ} refl = refl
toChar-inj {ἠ} {ἠ} refl = refl
toChar-inj {ἡ} {ἡ} refl = refl
toChar-inj {ἢ} {ἢ} refl = refl
toChar-inj {ἣ} {ἣ} refl = refl
toChar-inj {ἤ} {ἤ} refl = refl
toChar-inj {ἦ} {ἦ} refl = refl
toChar-inj {ἥ} {ἥ} refl = refl
toChar-inj {Ἥ} {Ἥ} refl = refl
toChar-inj {ή} {ή} refl = refl
toChar-inj {ὴ} {ὴ} refl = refl
toChar-inj {ᾔ} {ᾔ} refl = refl
toChar-inj {ι} {ι} refl = refl
toChar-inj {ί} {ί} refl = refl
toChar-inj {ὶ} {ὶ} refl = refl
toChar-inj {ἰ} {ἰ} refl = refl
toChar-inj {ἱ} {ἱ} refl = refl
toChar-inj {ἳ} {ἳ} refl = refl
toChar-inj {ἴ} {ἴ} refl = refl
toChar-inj {ἶ} {ἶ} refl = refl
toChar-inj {Ἴ} {Ἴ} refl = refl
toChar-inj {ῖ} {ῖ} refl = refl
toChar-inj {ϊ} {ϊ} refl = refl
toChar-inj {ΐ} {ΐ} refl = refl
toChar-inj {ῒ} {ῒ} refl = refl
toChar-inj {ο} {ο} refl = refl
toChar-inj {Ο} {Ο} refl = refl
toChar-inj {ὀ} {ὀ} refl = refl
toChar-inj {Ὀ} {Ὀ} refl = refl
toChar-inj {ὁ} {ὁ} refl = refl
toChar-inj {ὃ} {ὃ} refl = refl
toChar-inj {ὄ} {ὄ} refl = refl
toChar-inj {ὅ} {ὅ} refl = refl
toChar-inj {ό} {ό} refl = refl
toChar-inj {ὸ} {ὸ} refl = refl
toChar-inj {υ} {υ} refl = refl
toChar-inj {ὐ} {ὐ} refl = refl
toChar-inj {ὑ} {ὑ} refl = refl
toChar-inj {ὔ} {ὔ} refl = refl
toChar-inj {ὖ} {ὖ} refl = refl
toChar-inj {ὕ} {ὕ} refl = refl
toChar-inj {ὗ} {ὗ} refl = refl
toChar-inj {ὺ} {ὺ} refl = refl
toChar-inj {ύ} {ύ} refl = refl
toChar-inj {ῦ} {ῦ} refl = refl
toChar-inj {ϋ} {ϋ} refl = refl
toChar-inj {ΰ} {ΰ} refl = refl
toChar-inj {ω} {ω} refl = refl
toChar-inj {ὠ} {ὠ} refl = refl
toChar-inj {ὣ} {ὣ} refl = refl
toChar-inj {ὤ} {ὤ} refl = refl
toChar-inj {ὥ} {ὥ} refl = refl
toChar-inj {ὦ} {ὦ} refl = refl
toChar-inj {ᾤ} {ᾤ} refl = refl
toChar-inj {ᾧ} {ᾧ} refl = refl
toChar-inj {ώ} {ώ} refl = refl
toChar-inj {ὼ} {ὼ} refl = refl
toChar-inj {ῶ} {ῶ} refl = refl
toChar-inj {ῳ} {ῳ} refl = refl
toChar-inj {ῴ} {ῴ} refl = refl
toChar-inj {ῷ} {ῷ} refl = refl
toChar-inj {ὡ} {ὡ} refl = refl
toChar-inj {Β} {Β} refl = refl
toChar-inj {β} {β} refl = refl
toChar-inj {Γ} {Γ} refl = refl
toChar-inj {γ} {γ} refl = refl
toChar-inj {Δ} {Δ} refl = refl
toChar-inj {δ} {δ} refl = refl
toChar-inj {Ζ} {Ζ} refl = refl
toChar-inj {ζ} {ζ} refl = refl
toChar-inj {Θ} {Θ} refl = refl
toChar-inj {θ} {θ} refl = refl
toChar-inj {Κ} {Κ} refl = refl
toChar-inj {κ} {κ} refl = refl
toChar-inj {Λ} {Λ} refl = refl
toChar-inj {ƛ} {ƛ} refl = refl
toChar-inj {Μ} {Μ} refl = refl
toChar-inj {μ} {μ} refl = refl
toChar-inj {Ν} {Ν} refl = refl
toChar-inj {ν} {ν} refl = refl
toChar-inj {Ξ} {Ξ} refl = refl
toChar-inj {ξ} {ξ} refl = refl
toChar-inj {Π} {Π} refl = refl
toChar-inj {π} {π} refl = refl
toChar-inj {Ρ} {Ρ} refl = refl
toChar-inj {ρ} {ρ} refl = refl
toChar-inj {ῥ} {ῥ} refl = refl
toChar-inj {Σ} {Σ} refl = refl
toChar-inj {σ} {σ} refl = refl
toChar-inj {ς} {ς} refl = refl
toChar-inj {Τ} {Τ} refl = refl
toChar-inj {τ} {τ} refl = refl
toChar-inj {Φ} {Φ} refl = refl
toChar-inj {φ} {φ} refl = refl
toChar-inj {Χ} {Χ} refl = refl
toChar-inj {χ} {χ} refl = refl
toChar-inj {Ψ} {Ψ} refl = refl
toChar-inj {ψ} {ψ} refl = refl
toChar-inj {᾽} {᾽} refl = refl

instance
  DecEq-Letter : DecEq Letter
  DecEq-Letter ._≟_ _ _ = mapDec toChar-inj (cong toChar) $ _ ≟ _
