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
  ... | [575] _ = explain1 p1
  ... | noop _ = explain1 p1
  ... | fromBelow _ _ _ p2
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


explain31 : (sy , ctx) ~ mq → Explanation
explain31 = λ where
  (ambiguous _) → ？
  (ambivalent p q) → ambivalent (explain311 p) (explain311 q)
  (certain p _) → explain311 p
 where
  open QuantityRules
  explain311 : ctx ⊢ sy ~∗ q → Explanation
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

explain3 : {ws : Words n} → ws ~³ mqs → Explanations n
explain3 = explain-VPointwise explain31

open ∣Complies-MQs-HM∣

explain4m : {ws : Words n} {mqs : Vec Quantity n} {m : Meter n m} →
  (ws , mqs) ~ m → Explanations n
explain4m = λ where
  [] → []
  (sponde p) → ？ ∷ ？ ∷ explain4m p
  (dactyl p) → ？ ∷ ？ ∷ ？ ∷ explain4m p
  ([1168] _ _ p) → [1168] ∷ V.tail (explain4m p)

explain4 : {ws : Words n} {mqs : Quantities n} {hm : Hexameter n} →
  (ws , mqs) ~ hm → Explanations n
explain4 {hm = hm} (reify _ p) = explain4m p ≔ₙ⟨ Hex>0 hm ⟩ mkLastLong

explainSyn : {sys′ : Syllables n′} → sys -synizizes*- sys′ → Explanations n′
explainSyn = λ where
  [] → []
  (_ ∷ p) → ？ ∷ explainSyn p
  (_ ∺ p) → ⁀ ∷ explainSyn p

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
  ⊞ (syn≥ syn) (explain2 p2) (explainSyn syn) (explain3 {ws = ws′} p3) (explain4 p4)

open import Iliagda.Show.Core

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

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
