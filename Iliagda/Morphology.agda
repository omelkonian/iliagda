{-# OPTIONS --safe #-}
module Iliagda.Morphology where

open import Iliagda.Init

-- INCOMPLETE: add as needed
data Letter : Type where
  -- vowels
  Ἀ Ἄ α ἀ ἄ ὰ ά ᾶ
   ε έ ἔ ὲ ἑ ἐ
   η ῆ ἣ ἡ ή ὴ
   ι ί ὶ ἰ ῖ ϊ ΐ
   ο ὸ
   υ ὐ ὺ ῦ ύ ὗ
   ω ώ ῶ
  -- consonants
   Β β Γ γ Δ δ Ζ ζ Θ θ Κ κ Λ ƛ Μ μ Ν ν Ξ ξ
   Π π Ρ ρ Σ σ ς Τ τ Φ φ Χ χ Ψ ψ
   : Letter

Consonant Vowel : Pred₀ Letter
Consonant = _∈
  ( Β ∷ β ∷ Γ ∷ γ ∷ Δ ∷ δ ∷ Ζ ∷ ζ
  ∷ Θ ∷ θ ∷ Κ ∷ κ ∷ Λ ∷ ƛ ∷ Μ ∷ μ ∷ Ν ∷ ν
  ∷ Ξ ∷ ξ ∷ Π ∷ π ∷ Ρ ∷ ρ ∷ Σ ∷ σ ∷ ς
  ∷ Τ ∷ τ ∷ Φ ∷ φ ∷ Χ ∷ χ ∷ Ψ ∷ ψ ∷ [])
Vowel = ¬_ ∘ Consonant

-- TODO: syllabification
Syllable = List⁺ Letter

data Word : ℕ {- syllables -} → Type where
  word : {_ : auto∶ n ≢ 0} → Vec Syllable n → Word n
∃Word = ∃ Word

_ : Word 3
_ = word ([ μ ⨾ ῆ ]  ∷ ([ ν ⨾ ι ⨾ ν ] ∷ ([ δ ⨾ ε ] ∷ [])))

unword : Word n → Vec Syllable n
unword (word sys) = sys

data Words : ℕ → Type where
  []  : Words 0
  _∷_ : Word n → Words n′ → Words (n + n′)

unwords : Words n → Vec Syllable n
unwords = λ where
  [] → []
  (w ∷ ws) → unword w V.++ unwords ws

Verse = List ∃Word

_ : Verse
_ =
  [ -, word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
  ⨾ -, word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
  ⨾ -, word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
  ⨾ -, word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
  ⨾ -, word [ [ Ἀ ] ⨾ [ χ ⨾ ι ] ⨾ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]
  ]

variable
  l l′ : Letter
  sy sy′ sy″ penult penult′ ult ult′ : Syllable
  sys sys′ sys″ : Vec Syllable n
  w  w′ : Word n
  ws ws′ : Words n
  v v′ : Verse
