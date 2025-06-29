module Iliagda.Core where

open import Iliagda.Init

-- INCOMPLETE: ADD AS NEEDED
data Letter : Type where
  -- vowels
  α ἄ ὰ ά Ἀ
   ε έ ἔ
   ῆ ἣ η
   ι ϊ ί ῖ
   ο
   ὐ υ
   ω : Letter
  -- consonants
  γ δ θ κ ƛ μ ν Π ρ ς χ : Letter
-- Letter = Vowel ⊎ Consonant
unquoteDecl DecEq-Letter = DERIVE DecEq [ quote Letter , DecEq-Letter ]

Vowel Consonant : Pred₀ Letter
Vowel = _∈
  ( α ∷ ἄ ∷ ὰ ∷ ά ∷ Ἀ
  ∷ ε ∷ έ ∷ ἔ
  ∷ ῆ ∷ ἣ ∷ η
  ∷ ι ∷ ϊ ∷ ί ∷ ῖ
  ∷ ο
  ∷ ὐ ∷ υ
  ∷ ω
  ∷ []
  )
Consonant = _∈ [ γ ⨾ δ ⨾ θ ⨾ κ ⨾ ƛ ⨾ μ ⨾ ν ⨾ Π ⨾ ρ ⨾ ς ⨾ χ ]
-- Consonant = ¬_ ∘ Vowel

-- NB: loose definition of a syllable for now
-- TODO? proper inductive definition of words/syllables
Syllable = List Letter
-- Syllable = List⁺ Letter
