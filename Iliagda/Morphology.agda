module Iliagda.Morphology where

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
-- Syllable = List Letter
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
  sys  : Vec Syllable n
  sys′ : Vec Syllable n′
  w  : Word n
  w′ : Word n′
  ws  : Words n
  ws′ : Words n′
  v v′ : Verse
