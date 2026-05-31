{-# OPTIONS --safe #-}
module Iliagda.Show.Prosody where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules
open import Iliagda.Show.Core

instance
  Show-Quantity = Show Quantity ∋ λ where .show → λ where
    · → "·"
    ─ → "─"

  Show-Letter = Show Letter ∋ λ where
    .show l → fromList [ toChar l ]

  Show-Sy = Show Syllable ∋ λ where
    .show → merged ∘ toList

  Show-Sys : Show (Syllables n)
  Show-Sys .show = spaced ∘ toList

  Show-Syn : Show (sys -synizizes*- sys′)
  Show-Syn .show = λ where
    [] → ""
    (sy ∷ syn) → show sy ◇ " " ◇ show syn
    (_∺_ {sy = sy} {sy′ = sy′} _ syn) → show sy ◇ "⁀" ◇ show sy′ ◇ " " ◇ show syn

  Show-mq : Show (Flat Quantity)
  Show-mq .show = λ where
    none → "?"
    all → "*"
    (single q) → show q

  Show-mqs : Show (Quantities n)
  Show-mqs .show = spaced ∘ toList

-- ** derivations

open import Iliagda.Prosody.Rules.Level1.Dec
open ∣Complies-Ws-HM∣

instance
  Show-Ws-HM : Show (ws ~ hm)
  Show-Ws-HM {ws = ws} {hm = hm} .show
    (_≫⟨_⟩≫_≫_ {mqs₂ = mqs₂} {mqs₃ = mqs₃} _ syn _ _) =
    let
      `syn = show syn
      ns   = map Str.length (Str.words `syn)
      qs   = meter-qs hm
      `qs  = map show (toList qs)
      mqs₁  = 𝟙-theQuantities (unwords ws) .proj₁
      `mqs₁ = map show (toList $ synizize syn mqs₁)
      `mqs₂ = map show (toList $ synizize syn mqs₂)
      `mqs₃ = map show (toList mqs₃)
      `mqs₄ = map show (toList $ synizize syn mqs₂ ⊗ mqs₃)
    in
      `syn ◇ "\n"
    ◇ spaces (map (uncurry pad) $ L.zip `mqs₁ ns) ◇ " --𝟙 \n"
    ◇ spaces (map (uncurry pad) $ L.zip `mqs₂ ns) ◇ " --𝟚 \n"
    ◇ spaces (map (uncurry pad) $ L.zip `mqs₃ ns) ◇ " --𝟛 \n"
    ◇ spaces (map (uncurry pad) $ L.zip `mqs₄ ns) ◇ " --𝟚⊗𝟛 \n"

  Show-Derivations : Show (Derivations ws)
  -- Show-Derivations .show = lined
  Show-Derivations {ws = ws} .show = λ where
    [] → "\n" ◇ show (unwords ws) ◇ "\n∅"
    ds → lined ds
