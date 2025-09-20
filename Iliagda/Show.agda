{-# OPTIONS --safe #-}
module Iliagda.Show where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody

open Nat

pad : String → ℕ → String
pad s n = let ∣s∣ = Str.length s in
  if ∣s∣ Nat.<ᵇ n then
    s ◇ fromList (L.replicate (n ∸ ∣s∣) ' ')
  else
    s

merge spaces lines : List String → String
merge  = Str.intersperse ""
spaces = Str.intersperse " "
lines  = ("\n" ◇_) ∘ Str.intersperse "\n\n"

merged spaced lined : ⦃ Show A ⦄ → List A → String
merged = merge ∘ map show
spaced = spaces ∘ map show
lined  = lines ∘ map show

padded : ⦃ Show A ⦄ → ⦃ Show B ⦄ → List A → List B → String
padded xs ys =
  let
    `xs = map show xs
    ns  = map Str.length `xs
  in
    spaces `xs ◇ "\n"
  ◇ spaces (map (uncurry pad) $ L.zip (map show ys) ns )

instance
  Show-Quantity = Show Quantity ∋ λ where .show → λ where
    · → "·"
    ─ → "─"

  {- INCOMPLETE: add as needed -}
  Show-Letter = Show Letter ∋ λ where .show → λ where
    Ἀ → "Ἀ"
    Ἄ → "Ἄ"
    α → "α"
    ἀ → "ἀ"
    ἄ → "ἄ"
    ὰ → "ὰ"
    ά → "ά"
    ᾶ → "ᾶ"
    ε → "ε"
    έ → "έ"
    ἔ → "ἔ"
    ὲ → "ὲ"
    ἑ → "ἑ"
    ἐ → "ἐ"
    η → "η"
    ῆ → "ῆ"
    ἣ → "ἣ"
    ἡ → "ἡ"
    ή → "ή"
    ὴ → "ὴ"
    ἠ → "ἠ"
    ἦ → "ἦ"
    ι → "ι"
    ί → "ί"
    ὶ → "ὶ"
    ἰ → "ἰ"
    ῖ → "ῖ"
    ϊ → "ϊ"
    ΐ → "ΐ"
    ἱ → "ἱ"
    ο → "ο"
    ὸ → "ὸ"
    ό → "ό"
    ὃ → "ὃ"
    ὄ → "ὄ"
    ὀ → "ὀ"
    υ → "υ"
    ὐ → "ὐ"
    ὺ → "ὺ"
    ῦ → "ῦ"
    ύ → "ύ"
    ὗ → "ὗ"
    ὕ → "ὕ"
    ω → "ω"
    ώ → "ώ"
    ῶ → "ῶ"
    ῳ → "ῳ"
    Β → "Β"
    β → "β"
    Γ → "Γ"
    γ → "γ"
    Δ → "Δ"
    δ → "δ"
    Ζ → "Ζ"
    ζ → "ζ"
    Θ → "Θ"
    θ → "θ"
    Κ → "Κ"
    κ → "κ"
    Λ → "Λ"
    ƛ → "ƛ"
    Μ → "Μ"
    μ → "μ"
    Ν → "Ν"
    ν → "ν"
    Ξ → "Ξ"
    ξ → "ξ"
    Π → "Π"
    π → "π"
    Ρ → "Ρ"
    ρ → "ρ"
    Σ → "Σ"
    σ → "σ"
    ς → "ς"
    Τ → "Τ"
    τ → "τ"
    Φ → "Φ"
    φ → "φ"
    Χ → "Χ"
    χ → "χ"
    Ψ → "Ψ"
    ψ → "ψ"

  Show-Sy = Show Syllable ∋ λ where
    .show → merged ∘ toList

  Show-Sys : Show (Vec Syllable n)
  Show-Sys .show = spaced ∘ toList

  Show-SQs : Show (Vec Syllable n × Vec Quantity n)
  Show-SQs .show (sys , qs) = padded (toList sys) (toList qs)

$sy : Syllable
$sy = [ ν ⨾ ι ⨾ ν ]

$sys : Vec Syllable _
$sys = [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]

ex : Vec Syllable _
   × Vec Quantity _
ex = [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
   , [ ─         ⨾ ─         ⨾ ─     ⨾ ·     ⨾ ·         ⨾ ─ ]

instance
  Show-Syn : Show (sys -synezizes*- sys′)
  Show-Syn .show = λ where
    [] → ""
    (sy ∷ syn) → show sy ◇ " " ◇ show syn
    (_∺_ {sy = sy} {sy′ = sy′} _ syn) → show sy ◇ "⁀" ◇ show sy′ ◇ " " ◇ show syn

instance
  Show-mq : Show (Maybe Quantity)
  Show-mq .show = λ where
    nothing  → "*"
    (just q) → show q

  Show-mqs : Show (Quantities n)
  Show-mqs .show = spaced ∘ toList

-- ** explanations

-- OPTION: set to `true` to show rule explanations below derivations
SHOW_RULES = false

showRules-ws : ∀ {ws : Words n} {mqs : Quantities n} → (ws ~ mqs) → String
showRules-ws {mqs = mqs} _ = "~ʷˢ {mqs= " ◇ show mqs ◇ "}"

showRules-mqs : ∀ {mqs : Quantities n} {hm : Hexameter n} → (mqs ~ hm) → String
showRules-mqs (reify {qs = qs} _ qs~hm) = "reify {qs= " ◇ spaced (toList qs) ◇ "}"

showRules : (ws ~ hm) → String
showRules = λ where
  (fromBelow (ws~mqs ~∘~ mqs~hm)) →
    "fromBelow\n  → " ◇ showRules-ws ws~mqs ◇ "\n  → " ◇ showRules-mqs mqs~hm
  ([586] _ ws~mqs _ syn~hm) →
    "[586]\n  → " ◇ showRules-ws ws~mqs ◇ "\n  → " ◇ showRules-mqs syn~hm

showIf : ⦃ Show A ⦄ → Bool → A → String
showIf b a = if b then show a else ""

-- ** derivations

instance
  Show-Ws-HM : Show (ws ~ hm)
  Show-Ws-HM {ws = ws} {hm = hm} .show ws~hm = (case ws~hm of λ where
    (fromBelow (_ ~∘~ _)) →
      show (unwords ws , meter-qs hm)
    ([586] {sys′ = sys′} syn _ _ _) →
      let
        `syn = show syn
        ns   = map Str.length (Str.words `syn)
        qs   = meter-qs hm
        `qs  = map show (toList qs)
      in
        `syn ◇ "\n"
      ◇ spaces (map (uncurry pad) $ L.zip `qs ns))
    ◇ showIf SHOW_RULES ("\n  ⊣ " ◇ showRules ws~hm)

  Show-∃ : ∀ {P : A → Type} → ⦃ Show¹ P ⦄ → Show (∃ λ a → P a)
  Show-∃ .show (_ , p) = show p

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
