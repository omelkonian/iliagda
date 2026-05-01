{-# OPTIONS --safe #-}
module Iliagda.Morphology where

open import Iliagda.Init
open import Agda.Builtin.Char

-- INCOMPLETE: add as needed
data Letter : Type where
  -- ** vowels
  Ἀ Ἄ α ἀ ἁ ἂ ἄ ὰ ά ᾶ ᾷ
   ε ἐ ἑ ἔ ἕ έ ὲ
   η ῆ ῇ ῃ ἠ ἡ ἢ ἣ ἤ ἦ ἥ Ἥ ή ὴ ᾔ
   ι ί ὶ ἰ ἱ ἳ ἴ ἶ Ἴ ῖ ϊ ΐ ῒ
   ο Ο ὀ Ὀ ὁ ὃ ὄ ὅ ό ὸ
   υ ὐ ὑ ὔ ὖ ὕ ὗ ὺ ύ ῦ ϋ ΰ
   ω ὠ ὣ ὤ ὥ ὦ ᾤ ᾧ ώ ὼ ῶ ῳ ῴ ῷ
  -- ** consonants
   Β β Γ γ Δ δ Ζ ζ Θ θ Κ κ Λ ƛ Μ μ Ν ν Ξ ξ
   Π π Ρ ρ ῥ Σ σ ς Τ τ Φ φ Χ χ Ψ ψ
  -- ** special symbols
   ᾽ -- apostrophe
   : Letter

Letters = List Letter

Consonant Vowel Apostrophe : Pred₀ Letter
Consonant = _∈
  ( Β ∷ β ∷ Γ ∷ γ ∷ Δ ∷ δ ∷ Ζ ∷ ζ
  ∷ Θ ∷ θ ∷ Κ ∷ κ ∷ Λ ∷ ƛ ∷ Μ ∷ μ ∷ Ν ∷ ν
  ∷ Ξ ∷ ξ ∷ Π ∷ π ∷ Ρ ∷ ρ ∷ ῥ ∷ Σ ∷ σ ∷ ς
  ∷ Τ ∷ τ ∷ Φ ∷ φ ∷ Χ ∷ χ ∷ Ψ ∷ ψ ∷ [])
Vowel = _∈
  -- INCOMPLETE: add as needed
  ( Ἀ ∷ Ἄ ∷ α ∷ ἀ ∷ ἁ ∷ ἂ ∷ ἄ ∷ ὰ ∷ ά ∷ ᾶ ∷ ᾷ
  ∷ ε ∷ ἐ ∷ ἑ ∷ ἔ ∷ ἕ ∷ έ ∷ ὲ
  ∷ η ∷ ῆ ∷ ῇ ∷ ῃ ∷ ἠ ∷ ἡ ∷ ἢ ∷ ἣ ∷ ἤ ∷ ἦ ∷ ἥ ∷ Ἥ ∷ ή ∷ ὴ ∷ ᾔ
  ∷ ι ∷ ί ∷ ὶ ∷ ἰ ∷ ἱ ∷ ἳ ∷ ἴ ∷ ἶ ∷ Ἴ ∷ ῖ ∷ ϊ ∷ ΐ ∷ ῒ
  ∷ ο ∷ Ο ∷ ὀ ∷ Ὀ ∷ ὁ ∷ ὃ ∷ ὄ ∷ ὅ ∷ ό ∷ ὸ
  ∷ υ ∷ ὐ ∷ ὑ ∷ ὔ ∷ ὖ ∷ ὕ ∷ ὗ ∷ ὺ ∷ ύ ∷ ῦ ∷ ϋ ∷ ΰ
  ∷ ω ∷ ὠ ∷ ὣ ∷ ὤ ∷ ὥ ∷ ὦ ∷ ᾤ ∷ ᾧ ∷ ώ ∷ ὼ ∷ ῶ ∷ ῳ ∷ ῴ ∷ ῷ ∷ [])
Apostrophe = _≡ ᾽

-- TODO: syllabification
Syllable = List⁺ Letter

Syllables = Vec Syllable

data Word : ℕ {- syllables -} → Type where
  word : {_ : auto∶ n ≢ 0} → Syllables n → Word n
∃Word = ∃ Word

_ : Word 3
_ = word ([ μ ⨾ ῆ ]  ∷ ([ ν ⨾ ι ⨾ ν ] ∷ ([ δ ⨾ ε ] ∷ [])))

unword : Word n → Syllables n
unword (word sys) = sys

data Words : ℕ → Type where
  []  : Words 0
  _∷_ : Word n → Words n′ → Words (n + n′)

unwords : Words n → Syllables n
unwords = λ where
  [] → []
  (w ∷ ws) → unword w V.++ unwords ws

Verse : {ℕ} → Type
Verse {n} = Words n

Verses : Type
Verses = List (∃ λ n → Verse {n})

_ : Verse
_ = word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
  ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
  ∷ word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
  ∷ word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
  ∷ word [ [ Ἀ ] ⨾ [ χ ⨾ ι ] ⨾ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]
  ∷ []

variable
  l l′ : Letter
  ls ls′ : Letters
  sy sy′ sy″ penult penult′ ult ult′ : Syllable
  sys sys′ sys″ : Syllables n
  w  w′ : Word n
  ws ws′ : Words n
  v v′ : Verse
  vs vs′ : Verses
