{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level4.Dec where

open import Relation.Nullary.Decidable using (_×-dec_)

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

private
  -- Measure-based termination of `allPMs` due to [1168] rule.
  measure : Vec Quantity n → ℕ
  measure = λ where
    (─ ∷ qs) → 1 + measure qs
    (· ∷ qs) → 2 + measure qs
    [] → 0

allPMs :
  ∀ (ws : Words n) (qs : Vec Quantity n) {m} → measure qs ≡ m →
  ∃ λ (pms : List (∃ λ m → Meter n m)) →
      (∀ {m} {pm : Meter n m} → (m , pm) ∈ pms → ws , qs ~ pm)
    × (∀ {m} {pm : Meter n m} → ws , qs ~ pm → (m , pm) ∈ pms)
allPMs ws′ [] _
  = [ 0 , mkPM [] ]
  , (λ where 𝟘 → subst (λ ◆ → ◆ , [] ˢ~ᵐ mkPM []) (sym $ emptyWords ws′) [])
  , (λ where [] → 𝟘)
allPMs _ [ q ] _
  = [] , (λ ()) , λ ()
allPMs _ [ ─ ⨾ · ] _
  = [] , (λ ()) , λ ()
allPMs _ (─ ∷ · ∷ ─ ∷ _) _
  = [] , (λ ()) , λ ()
allPMs ws′ (─ ∷ ─ ∷ qs) refl
  -- ** sponde
  using ws ← dropSys 2 ws′
  with pms , sound-pms , complete-pms ← allPMs ws qs refl
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
allPMs ws′ (─ ∷ · ∷ · ∷ qs) refl
  -- ** dactyl
  using ws ← dropSys 3 ws′
  with pms , sound-pms , complete-pms ← allPMs ws qs refl
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
allPMs ws′ (· ∷ qs@(_ ∷ _)) {.suc (.suc m)} refl
  with IH ← allPMs ws′ (─ ∷ qs) {suc m} refl
  using sy , sy′ , tt ← firstSys 2 ws′
  with ¿ SingleSyllable ws′ ¿
... | no ¬single
  = [] , (λ ()) , λ where ([1168] _ _ _) → ⊥-elim $ ¬single singleSy
... | yes (singleSy {sy = sy} {ws = ws})
  using sy′ ← firstSy ws
  with EndsWith? [ Vowel? ⨾ Consonant? ] (toList sy)
 ×-dec BeginsWith? [ Vowel? ] (toList sy′)
... | no ¬pq
  = [] , (λ ()) , λ where ([1168] p q _) → ⊥-elim $ ¬pq (p , q)
... | yes (p , q)
  with pms , sound-pms , complete-pms ← IH
  = pms , ([1168] p q ∘ sound-pms)
        , λ where ([1168] _ _ H) → complete-pms H

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
  (smqs : Words n × Quantities n) →
  ∃ λ (hms : List (Hexameter n)) →
      (∀ {hm} → hm ∈ hms → smqs ~ hm)
    × (∀ {hm} → smqs ~ hm → hm ∈ hms)
allHexameters {0} _ = [] , (λ ()) , λ where
  (reify {hm = hm} msk p) → ⊥-elim $ Hex≢0 hm
allHexameters {n@(suc _)} smqs@(sys , mqs)
  with n>0 ← n > 0
           ∋ s≤s z≤n
  using mqs─ ← mkLastLong {n = n} n>0 mqs
  with qss , sound-qss , complete-qss ← allMasks mqs─
  = concatMap sols qss
  , sou
  , com
  where
  sols : Vec Quantity n → List (Hexameter n)
  sols qs =
    let pms , _ = allPMs sys qs refl
    in onlyHexameters pms

  sou : ∀ {hm} → hm ∈ concatMap sols qss → smqs ~ hm
  sou {hm} hm∈
    with qs , qs∈ , hm∈ ← satisfied′ $ ∈-concatMap⁻ sols {xs = qss} hm∈
    with pms , sound-pms , complete-pms ← allPMs sys qs refl
    with (m , hm) , hm∈ , hm≡ ← ∈-mapMaybe⁻ (onlyHexameter {n}) {xs = pms} hm∈
    with 6 ← m
    with refl ← hm≡
    = reify (sound-qss qs∈) (sound-pms hm∈)

  com : ∀ {hm} → smqs ~ hm → hm ∈ concatMap sols qss
  com {hm} (reify {qs = qs} msk hm~) =
    let pms , sound-pms , complete-pms = allPMs sys qs refl in
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
    using hms , _ , _ ← allHexameters (ws′ , mqs⊗)
    = map -,_ hms

  ds : List (∃ Hexameter)
  ds = concat $ mapWith∈ n×syss mkDerivation

  sound-ds : ∀ {n′} {hm} → (n′ , hm) ∈ ds → ws ~ hm
  sound-ds {n′}{hm} x∈
    with _ , y∈ , x∈ys ← satisfied′ $ ∈-concat⁻ (mapWith∈ n×syss mkDerivation) x∈
    with _ , z∈ , refl ← L.Any.mapWith∈⁻ n×syss mkDerivation y∈
    using syn ← sound-syss z∈
    using ws′ ← synezizeWords ws syn
    using mqs′ , ws′~mqs′ , _ ← 𝟛-theQuantities ws′
    using mqs⊗ ← synezize syn mqs ⊗ mqs′
    with hms , sound-hms , _ ← allHexameters (ws′ , mqs⊗)
    with hm , hm∈ , refl ← ∈-map⁻ -,_ x∈ys
    = ws~mqs ≫⟨ syn ⟩≫ ws′~mqs′ ≫ sound-hms hm∈

  complete-ds : ∀ {n′} {hm} → ws ~ hm → (n′ , hm) ∈ ds
  complete-ds {n′}{hm}
    (_≫⟨_⟩≫_≫_ {mqs = mqs} {mqs′ = mqs′↓} {ws = ws} {sys′ = sys′}
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
      using hms , _ , complete-hms ← allHexameters (ws′ , mqs⊗)
      rewrite sym (complete-mqs ws~)
      = ∈-map⁺ (n′ ,_) {xs = hms} (complete-hms ~hm′)
      where
      ~hm′ : ws′ , synezize syn′ mqs ⊗ mqs′ ~ hm
      ~hm′ rewrite uniqueSyn syn′ syn | sym (complete-mqs′ ws′~) = ~hm

allDerivations : (ws : Words n) → Derivations ws
allDerivations ws = let ds , sound-ds , _ = allMeterDerivations ws in
   mapWith∈ ds (λ d∈ → -, -, sound-ds d∈)

mkDerivations : Verses → List ∃Derivations
mkDerivations = map λ (_ , v) → -, -, allDerivations v

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

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
