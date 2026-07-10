{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level4.Dec where

open import Relation.Nullary.Decidable using (_×-dec_)

open import Iliagda.Init; open import Prelude.Vectors
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
  hiding (hm′)
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules

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
allPMs ws [] _
  = [ 0 , mkPM [] ]
  , (λ where 𝟘 → subst (λ ◆ → ◆ , [] ˢ~ᵐ mkPM []) (sym $ emptyWords ws) [])
  , (λ where [] → 𝟘)
allPMs _ [ q ] _
  = [] , (λ ()) , λ where ([1167/1a] ())

{-
allPMs ws [ ─ ⨾ · ] _
  = [] , (λ ()) , λ ()
allPMs ws (─ ∷ · ∷ ─ ∷ _) _
  = [] , (λ ()) , λ ()
-- -}
-- {-
allPMs ws [ ─ ⨾ · ] _
  with ¿ Split 2 ws ¿
... | no ¬sp
  = [] , (λ ()) , λ where ([1167/1b] sp _) → ⊥-elim $ ¬sp sp
... | yes sp
  using ws′ ← dropSys 2 ws
  using ws′≡ ← emptyWords ws′
  = pms
  , (λ where 𝟘 → [1167/1b] sp $ subst (λ ◆ → ◆ , [] ~ mkPM []) (sym ws′≡) [])
  , com
  where
  pms = [ -, mkPM [ -, -, ── ] ]

  com : ∀ {m} {pm : Meter 2 m} → ws , [ ─ ⨾ · ] ˢ~ᵐ pm → (m , pm) ∈ pms
  com ([1167/1b] sp p)
    rewrite ws′≡
    with [] ← p
    = 𝟘

allPMs ws (─ ∷ · ∷ ─ ∷ qs) {.suc (.suc (.suc (.suc m)))} refl
  using ws′ ← dropSys 2 ws
  with IH ← allPMs ws′ (─ ∷ qs) {suc m} refl
  with ¿ Split 2 ws ¿
... | no ¬sp
  = [] , (λ ()) , λ where ([1167/1b] sp _) → ⊥-elim $ ¬sp sp
... | yes sp
  -- ** sponde by diairesis
  with pms , sound-pms , complete-pms ← IH
  = QED
  where
  f = λ (m , pm) → 1 + m , (── ∷ᵖᵐ pm)

  sou : _
  sou pm∈
    with _ , pm∈ , refl ← ∈-map⁻ f pm∈
    = [1167/1b] sp (sound-pms pm∈)

  com : _
  com ([1167/1b] _ p) = ∈-map⁺ f (complete-pms p)

  QED : _
  QED = map f pms , sou , com
-- -}
allPMs ws (─ ∷ ─ ∷ qs) refl
  -- ** sponde
  using ws′ ← dropSys 2 ws
  with pms , sound-pms , complete-pms ← allPMs ws′ qs refl
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

allPMs ws (─ ∷ · ∷ · ∷ qs) refl

  -- ** sponde by diairesis
  using dws′ ← dropSys 2 ws
  with go── ← allPMs dws′ (· ∷ qs)

  -- ** dactyl
  using ws′ ← dropSys 3 ws
  with go─·· ← allPMs ws′ qs
  with pms , sound-pms , complete-pms ← go─·· refl
-- {-
  with ¿ Split 2 ws ¿
... | yes sp
  using dpms , sound-dpms , complete-dpms ← go── refl

  = QED
  where
  f  = λ (m , pm) → 1 + m , (─·· ∷ᵖᵐ pm)
  df = λ (m , pm) → 1 + m , (──  ∷ᵖᵐ pm)

  sou : _
  sou pm∈
    with ∈-++⁻ (map f pms) pm∈
  ... | inj₁ pm∈
    with _ , pm∈ , refl ← ∈-map⁻ f pm∈
    = dactyl (sound-pms pm∈)
  ... | inj₂ pm∈
    with _ , pm∈ , refl ← ∈-map⁻ df pm∈
    = [1167/1b] sp (sound-dpms pm∈)

  com : _
  com (dactyl p)      = ∈-++⁺ˡ $ ∈-map⁺ f (complete-pms p)
  com ([1167/1b] _ p) = ∈-++⁺ʳ _ $ ∈-map⁺ df (complete-dpms p)

  QED : _
  QED = map f pms ++ map df dpms , sou , com
... | no ¬sp
-- -}
  = QED
  where
  f = λ (m , pm) → 1 + m , (─·· ∷ᵖᵐ pm)

  sou : _
  sou pm∈
    with _ , pm∈ , refl ← ∈-map⁻ f pm∈
    = dactyl (sound-pms pm∈)

  com : _
  com (dactyl p) = ∈-map⁺ f (complete-pms p)
-- {-
  com ([1167/1b] sp _) = ⊥-elim $ ¬sp sp
-- -}

  QED : _
  QED = map f pms , sou , com

allPMs ws (· ∷ qs@(_ ∷ _)) {.suc (.suc m)} refl
  with IH ← allPMs ws (─ ∷ qs) {suc m} refl
  using sy , sy′ , tt ← firstSys 2 ws
  with ¿ SingleSyllable ws ¿
... | no ¬single
  = [] , (λ ()) , λ where
  ([1168] _ _ _) → ⊥-elim $ ¬single singleSy
  ([1167/1a] _) → ⊥-elim $ ¬single singleSy
... | yes (singleSy {sy = sy} {ws = ws})
  using sy′ ← firstSy ws
  with EndsWith? [ Vowel? ⨾ Consonant? ] (toList sy)
 ×-dec BeginsWith? [ Vowel? ] (toList sy′)
... | yes (p , q)
  with pms , sound-pms , complete-pms ← IH
  = pms , ([1168] p q ∘ sound-pms) , λ where
  ([1168] _ _ H) → complete-pms H
  ([1167/1a] H) → complete-pms H
... | no ¬1168
  with pms , sound-pms , complete-pms ← IH
  = pms , ([1167/1a] ∘ sound-pms) , λ where
  ([1168] p q _) → ⊥-elim $ ¬1168 (p , q)
  ([1167/1a] H) → complete-pms H

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
  using mqs─ ← mqs ≔ₙ⟨ n>0 ⟩ single ─
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
    ∈-concatMap⁺ sols {xs = qss} $
      L.Any.map
        (λ where refl → ∈-mapMaybe⁺ (onlyHexameter {n}) (complete-pms hm~) refl)
        (complete-qss msk)

open ∣Complies-Ws-HM∣

open import Iliagda.Prosody.Rules.Level1.Dec
open import Iliagda.Prosody.Rules.Level2.Dec
open import Iliagda.Prosody.Rules.Level3.Dec
open import Iliagda.Prosody.Synizesis.Dec

module _ (n′ : ℕ) where
  Derivation⟨_⟩ Derivations⟨_⟩ : Words n → Type
  Derivation⟨_⟩  ws = ∃ λ (hm : Hexameter n′) → ws ~ hm
  Derivations⟨_⟩ = List ∘ Derivation⟨_⟩

  allMeterDerivations⟨_⟩ :
    (ws : Words n) →
    ∃ λ (ds : List (Hexameter n′)) →
        (∀ {hm} → hm ∈ ds → ws ~ hm)
      × (∀ {hm} → ws ~ hm → hm ∈ ds)
  allMeterDerivations⟨_⟩ ws
    using mqs₂ , ws~mqs₂ , complete-mqs₂ ← 𝟚-theQuantities ws
    using syss , sound-syss , complete-syss ← allSynizeses (unwords ws) n′
    = ds , sound-ds , complete-ds
    where
    mkDerivation : ∀ {sys′} → sys′ ∈ syss → List (Hexameter n′)
    mkDerivation x∈
      using syn  ← sound-syss x∈
      using ws′  ← synizizeWords ws syn
      using mqs₂′ ← synizize syn mqs₂
      using mqs₃ , _ , _ ← 𝟛-theQuantities ws′ mqs₂′
      using hms , _ , _ ← allHexameters (ws′ , mqs₂′ ⊗ mqs₃)
      = hms

    ds : List (Hexameter n′)
    ds = concat $ mapWith∈ syss mkDerivation

    sound-ds : ∀ {hm} → hm ∈ ds → ws ~ hm
    sound-ds {hm} x∈
      with _ , y∈ , hm∈ ← satisfied′ $ ∈-concat⁻ (mapWith∈ syss mkDerivation) x∈
      with _ , z∈ , refl ← L.Any.mapWith∈⁻ syss mkDerivation y∈
      using syn ← sound-syss z∈
      using ws′ ← synizizeWords ws syn
      using mqs₂′ ← synizize syn mqs₂
      using mqs₃ , ws′~mqs₃ , _ ← 𝟛-theQuantities ws′ mqs₂′
      with hms , sound-hms , _ ← allHexameters (ws′ , mqs₂′ ⊗ mqs₃)
      = ws~mqs₂ ≫⟨ syn ⟩≫ ws′~mqs₃ ≫ sound-hms hm∈

    complete-ds : ∀ {hm} → ws ~ hm → hm ∈ ds
    complete-ds {hm}
      (_≫⟨_⟩≫_≫_ {mqs₂ = mqs₂} {mqs₃ = mqs₃↓} {ws = ws} {sys′ = sys′} ws~ syn ws′~ ~hm)
      using x∈ ← complete-syss syn
      using syn′ ← sound-syss x∈
      = L.Any.concat⁺
      $ L.Any.mapWith∈⁺ mkDerivation
      $ -, x∈ , QED
      where

      QED : hm ∈ mkDerivation x∈
      QED
        using ws′ ← synizizeWords ws syn
        using mqs₂′ ← synizize syn mqs₂
        using mqs₃ , ws′~mqs₃ , complete-mqs₃ ← 𝟛-theQuantities ws′ mqs₂′
        using hms , _ , complete-hms ← allHexameters (ws′ , mqs₂′ ⊗ mqs₃)
        with hm∈ ← complete-hms $ subst (λ ◆ → _ , (_ ⊗ ◆) ~ _) (complete-mqs₃ ws′~) ~hm
        rewrite uniqueSyn syn′ syn | complete-mqs₂ ws~
        = hm∈

  allDerivations⟨_⟩ : (ws : Words n) → Derivations⟨_⟩ ws
  allDerivations⟨_⟩ ws = let ds , sound-ds , _ = allMeterDerivations⟨_⟩ ws in
    mapWith∈ ds (-,_ ∘ sound-ds)

-- ** minimal synizesis

private
  WhichSynizeses   = Bool
  MinimalSynizeses = true
  AllSynizeses     = false

allDerivations′ : WhichSynizeses → (ws : Words n) → Derivations ws
allDerivations′ {n = n} minimal? ws = go (suc n)
  where
  go : ℕ → Derivations ws
  go 0 = []
  go (suc n′)
    with ⋯ ← go n′
    with allDerivations⟨ n′ ⟩ ws
  ... | []         = ⋯
  ... | ds@(_ ∷ _) = map -,_ ds ◇ (if minimal? then [] else ⋯)

allDerivations allDerivationsMin : (ws : Words n) → Derivations ws
allDerivations    = allDerivations′ AllSynizeses
allDerivationsMin = allDerivations′ MinimalSynizeses

-- ** derivability

isNonDerivable : Words n → Bool
isNonDerivable ws = length (allDerivationsMin ws) == 0

-- -}
-- -}
-- -}
