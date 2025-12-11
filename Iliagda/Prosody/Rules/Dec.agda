-- ** decision procedures
-- {-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Dec where

open import Iliagda.Init
  hiding (n′)
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
  hiding (hm′)
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules

open import Iliagda.Prosody.Rules.Level2
open import Iliagda.Prosody.Rules.Level3
open import Iliagda.Prosody.Rules.Level23 using (_⊗_)

open import Iliagda.Prosody.Rules.Level1.Dec
-- open import Iliagda.Prosody.Rules.Level2.Dec
-- open import Iliagda.Prosody.Rules.Level3.Dec
-- open import Iliagda.Prosody.Synezesis.Dec

theQuantities₁ :
  (w : Word n) →
  ∃ λ (mqs : Quantities n) →
      (w ~ mqs)
    × (∀ {mqs′} → w ~ mqs′ → mqs′ ≡ mqs)
theQuantities₁ w
  = {!!}

theQuantities :
  (ws : Words n) →
  ∃ λ (mqs : Quantities n) →
      (ws ~² mqs)
    × (∀ {mqs′} → ws ~² mqs′ → mqs′ ≡ mqs)
theQuantities [] = [] , [] , λ where [] → refl
theQuantities (w ∷ ws)
  = let
      mqs  , w~mqs  , complete-mqs  = theQuantities₁ w
      mqs′ , ws~mqs′ , complete-mqs′ = theQuantities ws
    in
      (mqs V.++ mqs′)
      , (w~mqs ∷ ws~mqs′)
      , λ where (_∷_ ⦃ refl ⦄ w~mqs ws~mqs′) →
                     cong₂ V._++_ (complete-mqs  w~mqs) (complete-mqs′ ws~mqs′)

𝟛-theQuantities :
  (ws : Words n) →
  ∃ λ (mqs : Quantities n) →
      (ws ~³ mqs)
    × (∀ {mqs′} → ws ~³ mqs′ → mqs′ ≡ mqs)
𝟛-theQuantities = {!!}

allSynezeses′ : ∀ (sys : Syllables n) →
  ∃ λ (n×syss : List (∃ λ n′ → Syllables n′)) →
      (∀ {n′ sys′} → (n′ , sys′) ∈ n×syss → sys -synezizes*- sys′)
    × (∀ {n′ sys′} → sys -synezizes*- sys′ → (n′ , sys′) ∈ n×syss)
allSynezeses′ {n} sys
  = {!!}

allHexameters :
  (mqs : Quantities n) →
  ∃ λ (hms : List (Hexameter n)) →
      (∀ {hm} → hm ∈ hms → mqs ~ hm)
    × (∀ {hm} → mqs ~ hm → hm ∈ hms)
allHexameters = {!!}

open ∣Complies-Ws-HM∣

allMeterDerivations :
  (ws : Words n) →
  ∃ λ (ds : List (∃ Hexameter)) →
      (∀ {n′} {hm} → (n′ , hm) ∈ ds → ws ~ hm)
    × (∀ {n′} {hm} → ws ~ hm → (n′ , hm) ∈ ds)
allMeterDerivations ws
  using mqs , ws~mqs , complete-mqs ← theQuantities ws
  using n×syss , sound-syss , complete-syss ← allSynezeses′ (unwords ws)
  = ds , sound-ds , complete-ds
  where
  mkDerivation : ∀ {n′}{sys′} → (n′ , sys′) ∈ n×syss → List (∃ Hexameter)
  mkDerivation x∈
    using syn  ← sound-syss x∈
    using ws′  ← synezizeWords ws syn
    using mqs′ , _ , _ ← 𝟛-theQuantities ws′
    using mqs⊗ ← synezize syn mqs ⊗ mqs′
    using hms , _ , _ ← allHexameters mqs⊗
    = map -,_ hms

  ds : List (∃ Hexameter)
  ds = concat $ mapWith∈ n×syss mkDerivation

  sound-ds : ∀ {n′} {hm} → (n′ , hm) ∈ ds → ws ~ hm
  sound-ds {n′}{hm} x∈
    with ys , y∈ , x∈ys ← satisfied′ $ ∈-concat⁻ (mapWith∈ n×syss mkDerivation) x∈
    with z , z∈ , refl ← L.Any.mapWith∈⁻ n×syss mkDerivation y∈
    using syn ← sound-syss z∈
    using ws′ ← synezizeWords ws syn
    using mqs′ , ws′~mqs′ , _ ← 𝟛-theQuantities ws′
    using mqs⊗ ← synezize syn mqs ⊗ mqs′
    with hms , sound-hms , _ ← allHexameters mqs⊗
    with hm , hm∈ , refl ← ∈-map⁻ -,_ x∈ys
    = ws~mqs ≫⟨ syn ⟩≫ ws′~mqs′ ≫ sound-hms hm∈

  complete-ds : ∀ {n′} {hm} → ws ~ hm → (n′ , hm) ∈ ds
  complete-ds {n′}{hm}
    (_≫⟨_⟩≫_≫_ {ws = ws} {mqs = mqs} {sys′ = sys′} {mqs′ = mqs′↓}
               ws~ syn ws′~ ~hm)
    using x∈ ← complete-syss syn
    using syn′ ← sound-syss x∈
    = L.Any.concat⁺
    $ L.Any.mapWith∈⁺ mkDerivation
    $ -, x∈ , QED
    where
    QED : (n′ , hm) ∈ mkDerivation x∈
    QED
      using ws′ ← synezizeWords ws syn′
      with mqs′ , ws′~mqs′ , complete-mqs′ ← 𝟛-theQuantities ws′
      using mqs⊗ ← synezize syn′ mqs ⊗ mqs′
      using hms , _ , complete-hms ← allHexameters mqs⊗
      rewrite sym (complete-mqs ws~)
      = ∈-map⁺ (n′ ,_) {xs = hms} (complete-hms ~hm′)
      where

      ~~hm : synezize syn mqs ⊗ mqs′↓ ~ hm
      ~~hm = ~hm

      mqs′≡ : mqs′↓ ≡ mqs′
      mqs′≡ rewrite uniqueSyn syn′ syn = complete-mqs′ ws′~

      ~hm1 : synezize syn mqs ⊗ mqs′ ~ hm
      ~hm1 = subst (λ ◆ → synezize syn mqs ⊗ ◆ ~ hm) mqs′≡ ~~hm

      ~hm′ : synezize syn′ mqs ⊗ mqs′ ~ hm
      ~hm′ rewrite uniqueSyn syn′ syn = ~hm1

Derivation : Words n → Type
Derivation ws = ∃ λ n′ → ∃ λ (hm : Hexameter n′) → ws ~ hm

Derivations : Words n → Type
Derivations ws = List (Derivation ws)

allDerivations : (ws : Words n) → Derivations ws
allDerivations ws = let ds , sound-ds , _ = allMeterDerivations ws in
   mapWith∈ ds (λ d∈ → -, -, sound-ds d∈)


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
