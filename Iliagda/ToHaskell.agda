module Iliagda.ToHaskell where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules
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

mkLetter : RawLetter → Letter
mkLetter = λ where
  'Α' → Α; 'α' → α
  'Ἀ' → Ἀ; 'ἀ' → ἀ
  'Ἄ' → Ἄ; 'ἄ' → ἄ; 'ἂ' → ἂ
  'Ἆ' → Ἆ; 'ἆ' → ἆ
  'Ἁ' → Ἁ; 'ἁ' → ἁ
  'Ἅ' → Ἅ; 'ἅ' → ἅ; 'ἃ' → ἃ
  'ά' → ά; 'ὰ' → ὰ; 'ᾶ' → ᾶ; 'ᾷ' → ᾷ; 'ᾳ' → ᾳ
  'ᾰ' → ᾰ
  'Β' → Β; 'β' → β
  'Γ' → Γ; 'γ' → γ
  'Δ' → Δ; 'δ' → δ
  'Ε' → Ε; 'ε' → ε
  'Ἐ' → Ἐ; 'ἐ' → ἐ
  'Ἔ' → Ἔ; 'ἔ' → ἔ
  'Ἑ' → Ἑ; 'ἑ' → ἑ
  'Ἕ' → Ἕ; 'ἕ' → ἕ; 'ἓ' → ἓ
  'έ' → έ; 'ὲ' → ὲ
  'Ζ' → Ζ; 'ζ' → ζ
  'η' → η
  'Ἠ' → Ἠ; 'ἠ' → ἠ
  'Ἤ' → Ἤ; 'ἤ' → ἤ; 'ᾔ' → ᾔ; 'ἢ' → ἢ; 'ἦ' → ἦ; 'ᾖ' → ᾖ; 'ᾐ' → ᾐ
  'Ἡ' → Ἡ; 'ἡ' → ἡ
  'Ἥ' → Ἥ; 'ἥ' → ἥ; 'ᾕ' → ᾕ; 'ἣ' → ἣ; 'ἧ' → ἧ; 'ᾗ' → ᾗ
  'ή' → ή; 'ῄ' → ῄ; 'ὴ' → ὴ; 'ῂ' → ῂ; 'ῆ' → ῆ; 'ῇ' → ῇ; 'ῃ' → ῃ
  'Θ' → Θ; 'θ' → θ
  'ι' → ι
  'Ἰ' → Ἰ; 'ἰ' → ἰ
  'Ἴ' → Ἴ; 'ἴ' → ἴ; 'ἲ' → ἲ
  'Ἶ' → Ἶ; 'ἶ' → ἶ
  'Ἱ' → Ἱ; 'ἱ' → ἱ
  'ἵ' → ἵ; 'ἳ' → ἳ; 'ἷ' → ἷ
  'ί' → ί; 'ὶ' → ὶ; 'ῖ' → ῖ; 'ϊ' → ϊ; 'ΐ' → ΐ; 'ῒ' → ῒ; 'ῗ' → ῗ
  'Κ' → Κ; 'κ' → κ
  'Λ' → Λ; 'λ' → ƛ
  'Μ' → Μ; 'μ' → μ
  'Ν' → Ν; 'ν' → ν
  'Ξ' → Ξ; 'ξ' → ξ
  'Ο' → Ο; 'ο' → ο
  'Ὀ' → Ὀ; 'ὀ' → ὀ
  'Ὄ' → Ὄ; 'ὄ' → ὄ
  'ὁ' → ὁ; 'ὅ' → ὅ; 'ὃ' → ὃ; 'ό' → ό; 'ὸ' → ὸ
  'Π' → Π; 'π' → π
  'Ρ' → Ρ; 'ρ' → ρ
  'Ῥ' → Ῥ; 'ῥ' → ῥ
  'Σ' → Σ; 'σ' → σ; 'ς' → ς
  'Τ' → Τ; 'τ' → τ
  'υ' → υ
  'ὐ' → ὐ; 'ὔ' → ὔ; 'ὖ' → ὖ
  'Ὑ' → Ὑ; 'ὑ' → ὑ
  'Ὕ' → Ὕ; 'ὕ' → ὕ; 'ὓ' → ὓ; 'ὗ' → ὗ
  'ύ' → ύ; 'ὺ' → ὺ; 'ῦ' → ῦ; 'ϋ' → ϋ; 'ΰ' → ΰ; 'ῢ' → ῢ
  'Φ' → Φ; 'φ' → φ
  'Χ' → Χ; 'χ' → χ
  'Ψ' → Ψ; 'ψ' → ψ
  'ω' → ω
  'Ὠ' → Ὠ; 'ὠ' → ὠ
  'Ὤ' → Ὤ; 'ὤ' → ὤ; 'ᾤ' → ᾤ; 'ὢ' → ὢ
  'Ὦ' → Ὦ; 'ὦ' → ὦ; 'ᾦ' → ᾦ; 'ᾠ' → ᾠ
  'ὡ' → ὡ; 'ὥ' → ὥ; 'ὣ' → ὣ
  'Ὧ' → Ὧ; 'ὧ' → ὧ; 'ᾧ' → ᾧ
  'ώ' → ώ; 'ῴ' → ῴ; 'ὼ' → ὼ; 'ῶ' → ῶ; 'ῷ' → ῷ; 'ῳ' → ῳ
  '᾽' → ᾽
  'ϝ' → ϝ
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

module _ (v : RawVerse) (let _ , ws = mkVerse v) where

  RawDerivations = List (List String)

  private
    groupDerivations′ : Derivations ws → List (Feet × List String)
    groupDerivations′ [] = []
    groupDerivations′ ((_ , hm , p) ∷ ds)
      using i ← unmkPM hm
      using s ← show p
      using ids ← groupDerivations′ ds
      with ¿ i ∈ map proj₁ ids ¿
    ... | no _
      = (i , [ s ]) ∷ ids
    ... | yes i∈
      with _ , y∈ , refl ← ∈-map⁻ proj₁ i∈
      with _ , as ← L.Any.lookup y∈
      = y∈ ∷= (i , s ∷ as)

    groupDerivations : Derivations ws → RawDerivations
    groupDerivations = map proj₂ ∘ groupDerivations′

  checkVerse checkVerseMin : RawDerivations
  checkVerse    = groupDerivations $ allDerivations ws
  checkVerseMin = groupDerivations $ allDerivationsMin ws

  open ∣Complies-Ws-HM∣
  open ∣Complies-MQs-HM∣

  debugVerse explainVerse : String
  debugVerse    =
    let
      mqs1 , _ , _ = 𝟙-theQuantities (unwords ws)
      mqs2 , _ , _ = 𝟚-theQuantities ws
      mqs3 , _ , _ = 𝟛-theQuantities ws

      `ws = show (unwords ws)
      ns = map Str.length (Str.words `ws)
      `mqs1 = map show (toList mqs1)
      `mqs2 = map show (toList mqs2)
      `mqs3 = map show (toList mqs3)
      `mqs23 = map show (toList $ mqs2 ⊗ mqs3)
    in
      `ws ◇ "\n"
      ◇ spaces (map (uncurry pad) $ L.zip `mqs1 ns) ◇ " --𝟙 \n"
      ◇ spaces (map (uncurry pad) $ L.zip `mqs2 ns) ◇ " --𝟚 \n"
      ◇ spaces (map (uncurry pad) $ L.zip `mqs3 ns) ◇ " --𝟛 \n"
      ◇ spaces (map (uncurry pad) $ L.zip `mqs23 ns) ◇ " --𝟚⊗3\n"
  explainVerse
    with allDerivationsMin ws
  ... | [] = IMPOSSIBLE "Cannot explain non-derivable verse"
  ... | (_ , _ , d@(_≫⟨_⟩≫_≫_ _ syn _ (reify {qs = qs} _ _))) ∷ _
    =
    let
      ws′  = synizizeWords ws syn
      `ws′ = map show (toList $ unwords ws′)
      es   = explain d
      `es  = spaced (toList es)
      ns   = map Str.length (Str.words `es)
      `qs  = map show (toList qs)
    in
      spaces (map (uncurry pad) $ L.zip `ws′ ns) ◇ "\n"
    ◇ spaces (map (uncurry pad) $ L.zip `qs ns) ◇ "\n"
    ◇ `es ◇ "\n"
{-# COMPILE GHC checkVerse    as checkVerse #-}
{-# COMPILE GHC checkVerseMin as checkVerseMin #-}
{-# COMPILE GHC debugVerse    as debugVerse #-}
{-# COMPILE GHC explainVerse  as explainVerse #-}
