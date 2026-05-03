module Iliagda.ToHaskell where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Rules.Dec
open import Iliagda.Show

RawLetter   = Char
RawSyllable = List RawLetter
RawWord     = List RawSyllable
RawVerse    = List RawWord

postulate ERROR : List Char → A
{-# COMPILE GHC ERROR = \_ s -> error s #-}

IMPOSSIBLE : String → A
IMPOSSIBLE = ERROR ∘ primStringToList
  where open import Agda.Builtin.String

-- nonEmpty : List A → List⁺ A
-- nonEmpty = λ where
--   [] → IMPOSSIBLE
--   (x ∷ xs) → x ∷ xs

mkLetter : RawLetter → Letter
mkLetter = λ where
  'Ἀ' → Ἀ
  'Ἄ' → Ἄ; 'α' → α; 'ἀ' → ἀ; 'ἁ' → ἁ; 'ἂ' → ἂ; 'ἄ' → ἄ; 'ὰ' → ὰ; 'ά' → ά; 'ᾶ' → ᾶ; 'ᾷ' → ᾷ
  'ε' → ε; 'ἐ' → ἐ; 'ἑ' → ἑ; 'ἔ' → ἔ; 'ἕ' → ἕ; 'έ' → έ; 'ὲ' → ὲ
  'η' → η; 'ῆ' → ῆ; 'ῇ' → ῇ; 'ῃ' → ῃ; 'ἠ' → ἠ; 'ἡ' → ἡ; 'ἢ' → ἢ; 'ἣ' → ἣ; 'ἤ' → ἤ; 'ἦ' → ἦ; 'ἥ' → ἥ; 'Ἥ' → Ἥ; 'ή' → ή; 'ὴ' → ὴ; 'ᾔ' → ᾔ
  'ι' → ι; 'ί' → ί; 'ὶ' → ὶ; 'ἰ' → ἰ; 'ἱ' → ἱ; 'ἳ' → ἳ; 'ἴ' → ἴ; 'ἶ' → ἶ; 'Ἴ' → Ἴ; 'ῖ' → ῖ; 'ϊ' → ϊ; 'ΐ' → ΐ; 'ῒ' → ῒ
  'ο' → ο; 'Ο' → Ο; 'ὀ' → ὀ; 'Ὀ' → Ὀ; 'ὁ' → ὁ; 'ὃ' → ὃ; 'ὄ' → ὄ; 'ὅ' → ὅ; 'ό' → ό; 'ὸ' → ὸ
  'υ' → υ; 'ὐ' → ὐ; 'ὑ' → ὑ; 'ὔ' → ὔ; 'ὖ' → ὖ; 'ὕ' → ὕ; 'ὗ' → ὗ; 'ὺ' → ὺ; 'ύ' → ύ; 'ῦ' → ῦ; 'ϋ' → ϋ; 'ΰ' → ΰ
  'ω' → ω; 'ὠ' → ὠ; 'ὣ' → ὣ; 'ὤ' → ὤ; 'ὥ' → ὥ; 'ὦ' → ὦ; 'ᾤ' → ᾤ; 'ᾧ' → ᾧ; 'ώ' → ώ; 'ὼ' → ὼ; 'ῶ' → ῶ; 'ῳ' → ῳ; 'ῴ' → ῴ; 'ῷ' → ῷ
  'Β' → Β; 'β' → β; 'Γ' → Γ; 'γ' → γ; 'Δ' → Δ; 'δ' → δ; 'Ζ' → Ζ; 'ζ' → ζ; 'Θ' → Θ; 'θ' → θ; 'Κ' → Κ; 'κ' → κ; 'Λ' → Λ; 'ƛ' → ƛ; 'Μ' → Μ; 'μ' → μ; 'Ν' → Ν; 'ν' → ν; 'Ξ' → Ξ; 'ξ' → ξ
  'Π' → Π; 'π' → π; 'Ρ' → Ρ; 'ρ' → ρ; 'ῥ' → ῥ; 'Σ' → Σ; 'σ' → σ; 'ς' → ς; 'Τ' → Τ; 'τ' → τ; 'Φ' → Φ; 'φ' → φ; 'Χ' → Χ; 'χ' → χ; 'Ψ' → Ψ; 'ψ' → ψ
  '᾽' → ᾽
  c   → IMPOSSIBLE ("mkLetter: " ◇ show c)

mkSyllable : RawSyllable → Syllable
mkSyllable = λ where
  [] → IMPOSSIBLE "mkSyllable"
  (c ∷ cs) → mkLetter c ∷ map mkLetter cs

mkSyllables : List RawSyllable → ∃ (Vec Syllable)
mkSyllables = λ where
  [] → -, []
  (sy ∷ sys) → -, mkSyllable sy ∷ mkSyllables sys .proj₂

mkWord : RawWord → ∃ Word
mkWord = λ where
  [] → IMPOSSIBLE "mkWord"
  sys@(_ ∷ _) → -, word (mkSyllables sys .proj₂)

mkVerse : RawVerse → ∃ Words
mkVerse = λ where
  [] → -, []
  (w ∷ ws) → -, mkWord w .proj₂ ∷ mkVerse ws .proj₂

checkVerse : RawVerse → String
checkVerse = show ∘ allDerivations ∘ proj₂ ∘ mkVerse
{-# COMPILE GHC checkVerse as checkVerse #-}
