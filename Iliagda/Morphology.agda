{-# OPTIONS --safe #-}
module Iliagda.Morphology where

open import Iliagda.Init
open import Agda.Builtin.Char

-- ** letters

data Letter : Type where
  -- ** vowels
  Α α Ἀ ἀ Ἄ ἄ ἂ Ἆ ἆ Ἁ ἁ Ἅ ἅ ἃ ά ὰ ᾶ ᾷ ᾳ Ᾰ ᾰ
   Ε ε Ἐ ἐ Ἔ ἔ Ἑ ἑ Ἕ ἕ ἓ έ ὲ
   η Ἠ ἠ Ἤ ἤ ᾔ ἢ ἦ ᾖ ᾐ Ἡ ἡ Ἥ ἥ ᾕ ἣ ἧ ᾗ ή ῄ ὴ ῂ ῆ ῇ ῃ
   ι Ἰ ἰ Ἴ ἴ ἲ Ἶ ἶ Ἱ ἱ ἵ ἳ ἷ ί ὶ ῖ ϊ ΐ ῒ ῗ Ῐ ῐ
   Ο ο Ὀ ὀ Ὄ ὄ ὁ ὅ ὃ ό ὸ
   υ ὐ ὔ ὖ Ὑ ὑ Ὕ ὕ ὓ ὗ ύ ὺ ῦ ϋ ΰ ῢ Ῠ ῠ
   ω Ὠ ὠ Ὤ ὤ ᾤ ὢ Ὦ ὦ ᾦ ᾠ ὡ ὥ ὣ Ὧ ὧ ᾧ ώ ῴ ὼ ῶ ῷ ῳ
  -- ** consonants
   Β β Γ γ Δ δ Ζ ζ Θ θ Κ κ Λ ƛ Μ μ Ν ν Ξ ξ
   Π π Ρ ρ Ῥ ῥ Σ σ ς Τ τ Φ φ Χ χ Ψ ψ
  -- ** special symbols
   ᾽ -- apostrophe
   ϝ -- digamma
   : Letter

Letters = List Letter

Consonant Vowel Apostrophe Digamma HasDiaeresis : Pred₀ Letter
Consonant = _∈
  ( Β ∷ β ∷ Γ ∷ γ ∷ Δ ∷ δ ∷ Ζ ∷ ζ
  ∷ Θ ∷ θ ∷ Κ ∷ κ ∷ Λ ∷ ƛ ∷ Μ ∷ μ ∷ Ν ∷ ν
  ∷ Ξ ∷ ξ ∷ Π ∷ π ∷ Ρ ∷ ρ ∷ Ῥ ∷ ῥ ∷ Σ ∷ σ ∷ ς
  ∷ Τ ∷ τ ∷ Φ ∷ φ ∷ Χ ∷ χ ∷ Ψ ∷ ψ
  ∷ ϝ -- digamma
  ∷ [])
Vowel = _∈
  ( Α ∷ α ∷ Ἀ ∷ ἀ ∷ Ἄ ∷ ἄ ∷ ἂ ∷ Ἆ ∷ ἆ ∷ Ἁ ∷ ἁ ∷ Ἅ ∷ ἅ ∷ ἃ ∷ ά ∷ ὰ ∷ ᾶ ∷ ᾷ ∷ ᾳ ∷ Ᾰ ∷ ᾰ
  ∷ Ε ∷ ε ∷ Ἐ ∷ ἐ ∷ Ἔ ∷ ἔ ∷ Ἑ ∷ ἑ ∷ Ἕ ∷ ἕ ∷ ἓ ∷ έ ∷ ὲ
  ∷ η ∷ Ἠ ∷ ἠ ∷ Ἤ ∷ ἤ ∷ ᾔ ∷ ἢ ∷ ἦ ∷ ᾖ ∷ ᾐ ∷ Ἡ ∷ ἡ ∷ Ἥ ∷ ἥ ∷ ᾕ ∷ ἣ ∷ ἧ ∷ ᾗ ∷ ή ∷ ῄ ∷ ὴ ∷ ῂ ∷ ῆ ∷ ῇ ∷ ῃ
  ∷ ι ∷ Ἰ ∷ ἰ ∷ Ἴ ∷ ἴ ∷ ἲ ∷ Ἶ ∷ ἶ ∷ Ἱ ∷ ἱ ∷ ἵ ∷ ἳ ∷ ἷ ∷ ί ∷ ὶ ∷ ῖ ∷ ϊ ∷ ΐ ∷ ῒ ∷ ῗ ∷ Ῐ ∷ ῐ
  ∷ Ο ∷ ο ∷ Ὀ ∷ ὀ ∷ Ὄ ∷ ὄ ∷ ὁ ∷ ὅ ∷ ὃ ∷ ό ∷ ὸ
  ∷ υ ∷ ὐ ∷ ὔ ∷ ὖ ∷ Ὑ ∷ ὑ ∷ Ὕ ∷ ὕ ∷ ὓ ∷ ὗ ∷ ύ ∷ ὺ ∷ ῦ ∷ ϋ ∷ ΰ ∷ ῢ ∷ Ῠ ∷ ῠ
  ∷ ω ∷ Ὠ ∷ ὠ ∷ Ὤ ∷ ὤ ∷ ᾤ ∷ ὢ ∷ Ὦ ∷ ὦ ∷ ᾦ ∷ ᾠ ∷ ὡ ∷ ὥ ∷ ὣ ∷ Ὧ ∷ ὧ ∷ ᾧ ∷ ώ ∷ ῴ ∷ ὼ ∷ ῶ ∷ ῷ ∷ ῳ
  ∷ [])
Apostrophe = _≡ ᾽
Digamma    = _≡ ϝ
HasDiaeresis = _∈
  ( ϊ ∷ ΐ ∷ ῒ ∷ ῗ
  ∷ ϋ ∷ ΰ ∷ ῢ
  ∷ [])
  -- NB: not to be confused with the metrical *diaeresis* of [1167/1b] (foot boundary)

-- ** syllables

Syllable  = List⁺ Letter
Syllables = Vec Syllable

-- ** words

data Word : ℕ {- syllables -} → Type where
  word : {_ : auto∶ n ≢ 0} → Syllables n → Word n
∃Word = ∃ Word

unword : Word n → Syllables n
unword (word sys) = sys

data Words : ℕ → Type where
  []  : Words 0
  _∷_ : Word n → Words n′ → Words (n + n′)

unwords : Words n → Syllables n
unwords = λ where
  [] → []
  (w ∷ ws) → unword w V.++ unwords ws

-- ** verses

Verse : {ℕ} → Type
Verse {n} = Words n

Verses : Type
Verses = List (∃ λ n → Verse {n})

variable
  l l′ : Letter
  ls ls′ : Letters
  sy sy′ sy″ ult ult′ penult penult′ antepenult antepenult′ : Syllable
  sys sys′ sys″ : Syllables n
  w  w′ : Word n
  ws ws′ : Words n
  v v′ : Verse
  vs vs′ : Verses
