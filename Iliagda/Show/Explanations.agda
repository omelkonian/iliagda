{-# OPTIONS --safe #-}
module Iliagda.Show.Explanations where

open import Iliagda.Init hiding (∅); open import Prelude.Vectors
open import Iliagda.Morphology
open import Iliagda.Prosody
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules

data Explanation : Type where

  -- _⨾_ : Explanation → Explanation → Explanation

  ？
  -- Level 1
    byNature
  -- Level 2
    -- [522]
    [522]dc [522]cc
    [1173]
    [524]
  -- Level 3
    [1160]
    [1161]
    [1162]
    [1163]

    : Explanation

  ambivalent
    : Explanation → Explanation → Explanation

  -- Level4

  mkLastLong
    ⁀
    [1168]
    [1167/1a]
    [1167/1b]
    : Explanation

Explanations : ℕ → Type
Explanations = Vec Explanation

open ∣Sys-Qs∣
explain1 : {sys : Syllables n} {mqs : Quantities n} → sys ~ mqs → Explanations n
explain1 [] = []
explain1 (p ∷ ps) = explain11 p ∷ explain1 ps
  where
  open ∣Sy-MQ∣
  explain11 : sy ~ mq → Explanation
  explain11 = λ where
    (byNature _) → byNature
    (doubtful _) → ？

explain2 : {ws : Words n} → ws ~² mqs → Explanations n
explain2 = λ where
  [] → []
  (p ∷ ps) → explain21 p V.++ explain2 ps
 where
  explain21 : {w : Word n} → w ~ʷ mqs → Explanations n
  explain21 (𝟙-then-𝟚 p1 p2)
    with p2
  ... | [1164] _ = explain1 p1
  ... | [574] _ = explain1 p1
  ... | [575] _ = explain1 p1
  ... | noop _ = explain1 p1
  ... | fromBelow _ _ _ _ p2
    with p2
  ... | [1160] _ = explain1 p1 ≔ₙ [1160]
  ... | [1161] _ = explain1 p1 ≔ₙ [1161]
  ... | [1162] _ _ = explain1 p1 ≔ₙ₋₁ [1162]
  ... | [1163] _ = explain1 p1 ≔ₙ [1163]

module _ {ctx} (let open QuantityRules ctx) where

  FollowedBy-∪⁻ : ∀ {P Q R} (l∈ : Any P ls) →
    FollowedBy (Q ∪¹ R) l∈ → FollowedBy Q l∈ ⊎ FollowedBy R l∈
  FollowedBy-∪⁻ = λ where
    (here _)   → id
    (there l∈) → FollowedBy-∪⁻ l∈

explain31 : (sy , mq , ctx) ~ mq′ → Explanation
explain31 {mq = mq} = λ where
  (ambiguous _) → ？
  (ambivalent p q) → ambivalent (explain311 p) (explain311 q)
  (certain p _) → explain311 p
 where
  open QuantityRules
  explain311 : (mq , ctx) ⊢ sy ~∗ q → Explanation
  explain311 = λ where
    ([522] v∈ p) → case FollowedBy-∪⁻ v∈ p of λ where
      (inj₁ _) → [522]dc
      (inj₂ _) → [522]cc
    ([1173] _ _ _ _) → [1173]
    ([524] _ _ _) → [524]

open ∣Complies-Ws-HM∣

module _
  ⦃ _ : A -compliesWith- B ⦄
  (explain~ : ∀ {a : A} {b : B} → a ~ b → Explanation)
  where

  explain-VPointwise : ∀ {as : Vec A n} {bs : Vec B n} →
    VPointwise _~_ as bs → Explanations n
  explain-VPointwise = λ where
    [] → []
    (p ∷ ps) → explain~ p ∷ explain-VPointwise ps

explain3 : {ws : Words n} → (ws , mqs₂) ~³ mqs₃ → Explanations n
explain3 = explain-VPointwise explain31

open ∣Complies-MQs-HM∣

explain4m : {ws : Words n} {mqs : Vec Quantity n} {m : Meter n m} →
  (ws , mqs) ~ m → Explanations n
explain4m = λ where
  [] → []
  (sponde p) → ？ ∷ ？ ∷ explain4m p
  (dactyl p) → ？ ∷ ？ ∷ ？ ∷ explain4m p
  ([1168] _ _ p) → [1168] ∷ V.tail (explain4m p)
  ([1167/1a] p) → [1167/1a] ∷ V.tail (explain4m p)
-- {-
  ([1167/1b] _ p) → ？ ∷ [1167/1b] ∷ explain4m p
-- -}

explain4 : {ws : Words n} {mqs : Quantities n} {hm : Hexameter n} →
  (ws , mqs) ~ hm → Explanations n
explain4 {hm = hm} (reify _ p) = explain4m p ≔ₙ⟨ Hex>0 hm ⟩ mkLastLong

explainSyn : {sys′ : Syllables n′} → sys -synizizes*- sys′ → Explanations n′
explainSyn = λ where
  [] → []
  (_ ∷ p) → ？ ∷ explainSyn p
  (_ ∺ p) → ⁀ ∷ explainSyn p

-- Re-align explanations of the original syllables (e.g. from level 2)
-- to the post-synizesis syllables, analogously to `synizize`.
synizizeExplanations : {sys : Syllables n} {sys′ : Syllables n′} →
  sys -synizizes*- sys′ → Explanations n → Explanations n′
synizizeExplanations = λ where
  []        es           → es
  (_ ∷ syn) (e ∷ es)     → e ∷ synizizeExplanations syn es
  (_ ∺ syn) (_ ∷ _ ∷ es) → ？ ∷ synizizeExplanations syn es

syn≥ : {sys : Syllables n} {sys′ : Syllables n′} →
  sys -synizizes*- sys′ → n ≥ n′
syn≥ = λ where
  [] → Nat.≤-refl
  (_ ∷ p) → s≤s (syn≥ p)
  (_ ∺ p) → Nat.m≤n⇒m≤1+n $ s≤s (syn≥ p)

infixl 4 _⊕_
_⊕_ : Op₂ Explanation
_⊕_ = λ where
  p ？ → p
  _ q → q

⊞ : n ≥ n′
  → Explanations n
  → Explanations n′
  → Explanations n′
  → Explanations n′
  → Explanations n′
⊞ n> _ [] [] [] = []
⊞ (s≤s n>) (x ∷ p2) (y ∷ syn) (z ∷ p3) (w ∷ p4)
  = (x ⊕ y ⊕ z ⊕ w) ∷ ⊞ n> p2 syn p3 p4

explain : {hm : Hexameter n′} → ws ~ hm → Explanations n′
explain (_≫⟨_⟩≫_≫_ {ws = ws} p2 syn p3 p4) = let ws′ = synizizeWords ws syn in
  ⊞ Nat.≤-refl (synizizeExplanations syn (explain2 p2))
               (explainSyn syn) (explain3 {ws = ws′} p3) (explain4 p4)

open import Iliagda.Show.Core
open import Iliagda.Show.Prosody

instance
  Show-Explanation : Show Explanation
  Show-Explanation .show = λ where
    ？ → "byMeter"
    byNature → "byNature"
    [522]dc → "[522]dc"
    [522]cc → "[522]cc"
    [1173] → "[1173]"
    [524] → "[524]"
    [1160] → "[1160]"
    [1161] → "[1161]"
    [1162] → "[1162]"
    [1163] → "[1163]"
    (ambivalent p q) → let `p = show p; `q = show q in
      if `p == `q then
        `p
      else
        `p ◇ "+" ◇ `q
    mkLastLong → "mkLastLong"
    ⁀ → "⁀"
    [1168] → "[1168]"
    [1167/1a] → "[1167/1a]"
    [1167/1b] → "[1167/1b]"

-- ** hyperlinks to the Agda identifier corresponding to each rule

private
  baseURL lvl1URL lvl2URL lvl3URL lvl4URL synURL : String
  baseURL = "https://omelkonian.github.io/iliagda/"
  lvl1URL = baseURL ◇ "Iliagda.Prosody.Rules.Level1.html#"
  lvl2URL = baseURL ◇ "Iliagda.Prosody.Rules.Level2.html#"
  lvl3URL = baseURL ◇ "Iliagda.Prosody.Rules.Level3.html#"
  lvl4URL = baseURL ◇ "Iliagda.Prosody.Rules.Level4.html#"
  synURL  = baseURL ◇ "Iliagda.Prosody.Synizesis.html#"

byNatureURL : Quantity → String
byNatureURL = λ where
  ─ → lvl1URL ◇ "∣Sy-Q∣._~′_.longByNature"
  · → lvl1URL ◇ "∣Sy-Q∣._~′_.shortByNature"

ruleURL : Explanation → String
ruleURL = λ where
  ？                → lvl4URL ◇ "_ˢ~ᵐ_"
  byNature          → lvl1URL ◇ "∣Sy-MQ∣._~′_.byNature"
  [522]dc           → lvl3URL ◇ "QuantityRules._~∗_.[522]"
  [522]cc           → lvl3URL ◇ "QuantityRules._~∗_.[522]"
  [1173]            → lvl3URL ◇ "QuantityRules._~∗_.[1173]"
  [524]             → lvl3URL ◇ "QuantityRules._~∗_.[524]"
  [1160]            → lvl2URL ◇ "_~%25′_.[1160]"
  [1161]            → lvl2URL ◇ "_~%25′_.[1161]"
  [1162]            → lvl2URL ◇ "_~%25′_.[1162]"
  [1163]            → lvl2URL ◇ "_~%25′_.[1163]"
  (ambivalent _ _)  → lvl3URL ◇ "QuantityRules._~?_.ambivalent"
  mkLastLong        → lvl4URL ◇ "∣Complies-MQs-HM∣._~′_.reify"
  ⁀                 → synURL ◇ "_-synizizes*-_._∺_"
  [1168]            → lvl4URL ◇ "_ˢ~ᵐ_.[1168]"
  [1167/1a]         → lvl4URL ◇ "_ˢ~ᵐ_.[1167/1a]"
  [1167/1b]         → lvl4URL ◇ "_ˢ~ᵐ_.[1167/1b]"

-- markdown hyperlink: mdLink "caesura" url ≈ [caesura](url)
mdLink : String → String → String
mdLink txt url = "[" ◇ txt ◇ "](" ◇ url ◇ ")"

-- ** logical explanations: natural-deduction derivations with horizontal bars

private
  -- a rectangular block of text, to be composed 2-dimensionally
  Block : Type
  Block = List String

  blockWidth : Block → ℕ
  blockWidth = L.foldr (Nat._⊔_ ∘ Str.length) 0

  center : ℕ → String → String
  center n s =
    let d = n ∸ Str.length s; l = Nat.⌊_/2⌋ d
    in Str.replicate l ' ' ◇ s ◇ Str.replicate (d ∸ l) ' '

  -- horizontal composition, bottom-aligned (premises sit on the bar)
  _┆_ : Op₂ Block
  [] ┆ ys = ys
  xs ┆ [] = xs
  xs ┆ ys = L.zipWith (λ a b → a ◇ "   " ◇ b) (padBlock xs) (padBlock ys)
    where
    h = length xs Nat.⊔ length ys
    padBlock : Op₁ Block
    padBlock zs = let w = blockWidth zs in
      L.replicate (h ∸ length zs) (Str.replicate w ' ') ++ map (center w) zs

  -- premises above a horizontal bar (annotated with the rule name),
  -- conclusion below
  infer : List Block → String → String → Block
  infer prems rule concl =
    let top = L.foldr _┆_ [] prems
        w   = blockWidth top Nat.⊔ Str.length concl
    in map (center w) top
    ++ ((Str.replicate w '─' ◇ " " ◇ rule) ∷ [ center w concl ])

  _⊢~_ : String → Quantity → String
  s ⊢~ q = s ◇ " ~ " ◇ show q

  byNaturePremise : String → Quantity → String
  byNaturePremise s = λ where
    ─ → s ◇ " contains a diphthong, a naturally-long vowel (η/ω), or a circumflex"
    · → "the only vowel of " ◇ s ◇ " is naturally short (ε/ο or short α/ι/υ)"

  byNatureName : Quantity → String
  byNatureName = λ where
    ─ → "longByNature"
    · → "shortByNature"

nd : String → Quantity → Explanation → Block
nd s q = λ where
  ？ → infer [ [ "the meter requires " ◇ show q ◇ " here" ] ]
    "byMeter" (s ⊢~ q)
  byNature → infer [ [ byNaturePremise s q ] ]
    (byNatureName q) (s ⊢~ q)
  [522]dc → infer [ [ "the vowel of " ◇ s ◇ " is followed by a double consonant (ζ/ξ/ψ)" ] ]
    "[522]" (s ⊢~ ─)
  [522]cc → infer [ [ "the vowel of " ◇ s ◇ " is followed by two consonants" ] ]
    "[522]" (s ⊢~ ─)
  [1173] → infer ( [ s ◇ " ends in a long vowel/diphthong" ]
                 ∷ [ [ "the next word begins with a vowel" ] ] )
    "[1173]" (s ⊢~ q)
  [524] → infer ( [ "the short vowel of " ◇ s ◇ " is followed by a mute, then a liquid/nasal" ]
                ∷ [ [ "the meter requires " ◇ show q ] ] )
    "[524]" (s ⊢~ q)
  [1160] → infer ( [ "the penult of the word bears a circumflex" ]
                 ∷ [ [ s ◇ " is the ultima" ] ] )
    "[1160]" (s ⊢~ ·)
  [1161] → infer ( [ "the long penult of the word bears an acute" ]
                 ∷ [ [ s ◇ " is the ultima" ] ] )
    "[1161]" (s ⊢~ ─)
  [1162] → infer ( [ "the ultima of the word is short" ]
                 ∷ [ [ s ◇ " (the penult) bears an acute" ] ] )
    "[1162]" (s ⊢~ ·)
  [1163] → infer ( [ "the antepenult of the word is accented" ]
                 ∷ [ [ s ◇ " is the ultima" ] ] )
    "[1163]" (s ⊢~ ·)
  (ambivalent e₁ e₂) → infer (nd s (─) e₁ ∷ [ nd s (·) e₂ ])
    "ambivalent" (s ⊢~ q)
  mkLastLong → infer [ [ s ◇ " is the last syllable of the verse (pause)" ] ]
    "[1184]" (s ⊢~ ─)
  ⁀ → infer [ [ "two vowel sounds merge into one: " ◇ s ] ]
    "synizesis" (s ⊢~ ─)
  [1168] → infer ( [ s ⊢~ · ]
                 ∷ ( [ s ◇ " ends in vowel+consonant" ]
                 ∷ ( [ "the next word begins with a vowel" ]
                 ∷ [ [ s ◇ " stands in thesis (the ictus)" ] ] ) ) )
    "[1168]" (s ⊢~ ─)
  [1167/1a] → infer ( [ s ⊢~ · ]
                    ∷ [ [ "the word ends inside the foot (caesura)" ] ] )
    "[1167/1a]" (s ⊢~ ─)
  [1167/1b] → infer ( [ s ⊢~ · ]
                    ∷ [ [ "the word-end coincides with the foot-end (diaeresis)" ] ] )
    "[1167/1b]" (s ⊢~ ─)

-- ** natural-language explanations: textbook-style prose with hyperlinked rules

private
  quantityWord : Quantity → String
  quantityWord = λ where
    ─ → "long"
    · → "short"

nlExplain : Quantity → Explanation → String
nlExplain q = λ where
  ？ → "no rule fixes its quantity, so it is read "
    ◇ quantityWord q ◇ " as the " ◇ mdLink "meter" (ruleURL ？) ◇ " requires."
  byNature → "it is " ◇ mdLink (quantityWord q ◇ " by nature") (byNatureURL q)
    ◇ (case q of λ where
        ─ → " — it contains a diphthong, a naturally-long vowel (η/ω), or a circumflex."
        · → " — its only vowel is naturally short (ε, ο, or short α/ι/υ).")
  [522]dc → "it is " ◇ mdLink "long by position" (ruleURL [522]dc)
    ◇ " — its vowel is followed by a double consonant (ζ, ξ, ψ)."
  [522]cc → "it is " ◇ mdLink "long by position" (ruleURL [522]cc)
    ◇ " — its vowel is followed by two consonants."
  [1173] → "its long final vowel/diphthong stands before a word beginning with a vowel, so it "
    ◇ mdLink "may be shortened" (ruleURL [1173])
    ◇ " (epic correption) — here it is read " ◇ quantityWord q ◇ "."
  [524] → "it is a " ◇ mdLink "common syllable" (ruleURL [524])
    ◇ " — its short vowel is followed by a mute and then a liquid or nasal,"
    ◇ " so the verse may treat it either way; here it is read " ◇ quantityWord q ◇ "."
  [1160] → "the penult of its word bears a circumflex, so this ultima "
    ◇ mdLink "must be short" (ruleURL [1160]) ◇ "."
  [1161] → "the long penult of its word bears an acute, so this ultima "
    ◇ mdLink "must be long" (ruleURL [1161]) ◇ "."
  [1162] → "this penult bears an acute while the ultima is short, so it "
    ◇ mdLink "must be short" (ruleURL [1162]) ◇ "."
  [1163] → "its word is accented on the antepenult, so this ultima "
    ◇ mdLink "must be short" (ruleURL [1163]) ◇ "."
  e@(ambivalent e₁ e₂) →
    if show e₁ == show e₂ then
      nlExplain q e₁
    else
      "it is " ◇ mdLink "ambivalent" (ruleURL e)
      ◇ " — read long, " ◇ nlExplain (─) e₁
      ◇ " Read short, " ◇ nlExplain (·) e₂
      ◇ " The meter selects " ◇ quantityWord q ◇ "."
  mkLastLong → "it is the " ◇ mdLink "last syllable of the verse" (ruleURL mkLastLong)
    ◇ ", which is always counted long due to the pause at the end of the line."
  ⁀ → "it arose by " ◇ mdLink "synizesis" (ruleURL ⁀)
    ◇ " — two adjacent vowels merged and are pronounced together as one long syllable."
  [1168] → "although short, it is " ◇ mdLink "lengthened in thesis" (ruleURL [1168])
    ◇ " — it ends in a consonant and carries the beat of the foot,"
    ◇ " even though the next word begins with a vowel."
  [1167/1a] → "although short, it is counted long — the word ends inside the foot,"
    ◇ " i.e. at a " ◇ mdLink "caesura" (ruleURL [1167/1a])
    ◇ ", and the pause makes up for the missing length."
  [1167/1b] → "although short, it is counted long — the word ends together with the foot,"
    ◇ " i.e. at a " ◇ mdLink "diaeresis" (ruleURL [1167/1b])
    ◇ ", and the pause makes up for the missing length."

-- ** whole-verse renderings, syllable by syllable

SyllableExplanation : Type
SyllableExplanation = Syllable × Quantity × Explanation

explainLogical explainTextual : List SyllableExplanation → String
explainLogical = Str.unlines ∘ L.concatMap
  (λ where (sy , q , e) → nd (show sy) q e ∷ʳ "")
explainTextual = Str.unlines ∘ map
  (λ where (sy , q , e) → "- **" ◇ show sy ◇ "** (" ◇ show q ◇ "): " ◇ nlExplain q e)

-- -}
-- -}
-- -}
