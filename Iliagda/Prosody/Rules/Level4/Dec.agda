{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level4.Dec where

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
open import Iliagda.Prosody.Rules.Level2.Dec
open import Iliagda.Prosody.Rules.Level3.Dec
open import Iliagda.Prosody.Synizesis.Dec

private
  pattern 𝟘 = here refl
  pattern 𝟙 = there 𝟘

allPMs :
  (qs : Vec Quantity n) →
  ∃ λ (pms : List (∃ λ m → Meter n m)) →
      (∀ {m} {pm : Meter n m} → (m , pm) ∈ pms → qs ~ pm)
    × (∀ {m} {pm : Meter n m} → qs ~ pm → (m , pm) ∈ pms)
allPMs [] = [ 0 , mkPM [] ]
          , (λ where 𝟘 → [])
          , (λ where [] → 𝟘)
allPMs (_ ∷ []) = [] , (λ ()) , (λ ())
allPMs (· ∷ _ ∷ qs) = [] , (λ ()) , (λ ())
allPMs (─ ∷ · ∷ []) = [] , (λ ()) , (λ ())
allPMs (─ ∷ · ∷ ─ ∷ _) = [] , (λ ()) , (λ ())
allPMs (─ ∷ ─ ∷ qs)
  with pms , sound-pms , complete-pms ← allPMs qs
  = QED
  where
  f = λ (m , pm) → 1 + m , (── ∷ᵖᵐ pm)

  sou : _
  sou pm∈
    with _ , pm∈ , refl ← ∈-map⁻ f pm∈
    = sponde (sound-pms pm∈)

  com : _
  com (sponde p) = ∈-map⁺ f (complete-pms p)

  QED : _
  QED = map f pms , sou , com
allPMs (─ ∷ · ∷ · ∷ qs)
  with pms , sound-pms , complete-pms ← allPMs qs
  = QED
  where
  f = λ (m , pm) → 1 + m , (─·· ∷ᵖᵐ pm)

  sou : _
  sou pm∈
    with _ , pm∈ , refl ← ∈-map⁻ f pm∈
    = dactyl (sound-pms pm∈)

  com : _
  com (dactyl p) = ∈-map⁺ f (complete-pms p)

  QED : _
  QED = map f pms , sou , com

allMasks :
  (mqs : Quantities n) →
  ∃ λ (qss : List (Vec Quantity n)) →
      (∀ {qs} → qs ∈ qss → mqs -masks*- qs)
    × (∀ {qs} → mqs -masks*- qs → qs ∈ qss)
allMasks [] = [ [] ]
            , (λ where 𝟘 → [])
            , (λ where [] → 𝟘)
allMasks (mq ∷ mqs)
  with qss , sound-qss , complete-qss ← allMasks mqs
  with mq
... | single q
  = QED
  where
  sou : _
  sou qs∈
    with qs , qs∈ , refl ← ∈-map⁻ (q ∷_) qs∈
    = single ∷ sound-qss qs∈

  com : _
  com (single ∷ p) = ∈-map⁺ (q ∷_) (complete-qss p)

  QED : _
  QED = map (q ∷_) qss , sou , com
... | none
  = QED
  where
  qssF = map (λ qs → [ (─ ∷ qs) ⨾ (· ∷ qs) ]) qss
  qss′ = concat qssF

  sou : _
  sou qs∈
    with ∃qss ← ∈-concat⁻ qssF qs∈
    with ∃qss′ ← L.Any.map⁻ ∃qss
    with qs′ , qs∈′ , ∈qss ← satisfied′ ∃qss′
    with ∈qss
  ... | 𝟘 = none ∷ sound-qss qs∈′
  ... | 𝟙 = none ∷ sound-qss qs∈′

  com : _
  com (none {x = q} ∷ p)
    = ∈-concat⁺ {xss = qssF}
    $ L.Any.map⁺
    $ L.Any.map (λ where refl → P⇒Q) (complete-qss p)
    where
    P⇒Q : _
    P⇒Q with ⟫ q
    ... | ⟫ ─ = 𝟘
    ... | ⟫ · = 𝟙

  QED : _
  QED = qss′ , sou , com
... | all
  = QED
  where
  qssF = map (λ qs → [ (─ ∷ qs) ⨾ (· ∷ qs) ]) qss
  qss′ = concat qssF

  sou : _
  sou qs∈
    with ∃qss ← ∈-concat⁻ qssF qs∈
    with ∃qss′ ← L.Any.map⁻ ∃qss
    with qs′ , qs∈′ , ∈qss ← satisfied′ ∃qss′
    with ∈qss
  ... | 𝟘 = all ∷ sound-qss qs∈′
  ... | 𝟙 = all ∷ sound-qss qs∈′

  com : _
  com (all {x = q} ∷ p)
    = ∈-concat⁺ {xss = qssF}
    $ L.Any.map⁺
    $ L.Any.map (λ where refl → P⇒Q) (complete-qss p)
    where
    P⇒Q : _
    P⇒Q with ⟫ q
    ... | ⟫ ─ = 𝟘
    ... | ⟫ · = 𝟙

  QED : _
  QED = qss′ , sou , com

onlyHexameters :
  List (∃ $ Meter n) → List (Hexameter n)
onlyHexameters = L.mapMaybe onlyHexameter
  module _ where
  onlyHexameter : ∃ (Meter n) → Maybe (Meter n 6)
  onlyHexameter (m , pm) with m ≟ 6
  ... | yes refl = just pm
  ... | no  _    = nothing

open ∣Complies-MQs-HM∣

allHexameters :
  (mqs : Quantities n) →
  ∃ λ (hms : List (Hexameter n)) →
      (∀ {hm} → hm ∈ hms → mqs ~ hm)
    × (∀ {hm} → mqs ~ hm → hm ∈ hms)
allHexameters {0} mqs = [] , (λ ()) , λ where
  (reify {hm = hm} msk p) → ⊥-elim $ Hex≢0 hm
allHexameters {n@(suc _)} mqs
  with n>0 ← n > 0
           ∋ s≤s z≤n
  with qss , sound-qss , complete-qss ← allMasks mqs
  = concatMap sols qss
  , sou
  , com
  where
  sols : Vec Quantity n → List (Hexameter n)
  sols qs =
    let qs─ = mkLastLong {n = n} (s≤s z≤n) qs
        pms , _ = allPMs qs─
    in onlyHexameters pms

  sou : ∀ {hm} → hm ∈ concatMap sols qss → mqs ~ hm
  sou {hm} hm∈
    with qs , qs∈ , hm∈ ← satisfied′ $ ∈-concatMap⁻ sols {xs = qss} hm∈
    with pms , sound-pms , complete-pms ← allPMs (mkLastLong {n = n} (s≤s z≤n) qs)
    with (m , hm) , hm∈ , hm≡ ← ∈-mapMaybe⁻ (onlyHexameter {n}) {xs = pms} hm∈
    with 6 ← m
    with refl ← hm≡
    = reify (sound-qss qs∈) (sound-pms hm∈)

  com : ∀ {hm} → mqs ~ hm → hm ∈ concatMap sols qss
  com {hm} (reify {qs = qs} msk hm~) =
    let pms , sound-pms , complete-pms = allPMs (mkLastLong {n = n} (s≤s z≤n) qs) in
    ∈-concatMap⁺ sols {xs = qss}
        (L.Any.map
          (λ where refl → ∈-mapMaybe⁺ (onlyHexameter {n}) {xs = pms} (complete-pms hm~) refl)
          (complete-qss msk))

open ∣Complies-Ws-HM∣

allMeterDerivations :
  (ws : Words n) →
  ∃ λ (ds : List (∃ Hexameter)) →
      (∀ {n′} {hm} → (n′ , hm) ∈ ds → ws ~ hm)
    × (∀ {n′} {hm} → ws ~ hm → (n′ , hm) ∈ ds)
allMeterDerivations ws
  using mqs , ws~mqs , complete-mqs ← 𝟚-theQuantities ws
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

allDerivations : (ws : Words n) → Derivations ws
allDerivations ws = let ds , sound-ds , _ = allMeterDerivations ws in
   mapWith∈ ds (λ d∈ → -, -, sound-ds d∈)

NonEmpty : List A → Type
NonEmpty = λ where
  [] → ⊥
  (_ ∷ _) → ⊤

instance
  Dec-NonEmpty : NonEmpty {A} ⁇¹
  Dec-NonEmpty {x = xs} .dec
    with xs
  ... | []    = no λ ()
  ... | _ ∷ _ = yes tt

Derivable : Words n → Type
Derivable = NonEmpty ∘ allDerivations
