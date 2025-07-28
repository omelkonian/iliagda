-- ** decision procedures
{-# OPTIONS --safe #-}
module Iliagda.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody

-- ** synezesis
instance
  Dec-syn : (sys -synizizes*- sys′) ⁇
  Dec-syn {sys = []} {sys′ = []} .dec = yes []
  Dec-syn {sys = []} {sys′ = _ ∷ _} .dec = no λ ()
  Dec-syn {sys = _ ∷ _} {sys′ = []} .dec = no λ ()
  Dec-syn {sys = sy ∷ sys} {sys′ = sy′ ∷ sys′} .dec
    with sy ≟ sy′
  ... | yes refl
    =  mapDec (_ ∷_) uncons ¿ sys -synizizes*- sys′ ¿
  ... | no sy≢
    with sys
  ... | []
    = no λ where (_ ∷ _) → ⊥-elim $ sy≢ refl
  ... | sy↓ ∷ sys
    = mapDec
      (λ (lv , syn , eq) → (lv ∺ syn) ⦃ eq ⦄)
      (λ where ((lv ∺ syn) ⦃ eq ⦄) → lv , syn , eq
               (_ ∷ _) → ⊥-elim $ sy≢ refl)
       ¿ (LastVowel sy × FirstVowel sy↓)
       × (sys -synizizes*- sys′)
       × (sy′ ≡ sy ⁀ sy↓)
       ¿


-- ** VPointwise
instance
  Dec-VPointwise : ∀ {_~_ : X → Y → Type ℓ} {xs : Vec X n} {ys : Vec Y n} →
    ⦃ _~_ ⁇² ⦄ → VPointwise _~_ xs ys ⁇
  Dec-VPointwise .dec = VP.decidable dec² _ _
    where import Data.Vec.Relation.Binary.Pointwise.Inductive as VP

-- ** Subsumes
module _ ⦃ _ : DecEq X ⦄ where instance
  Dec-masks : ∀ {mx : Maybe X}{y} → (mx -masks- y) ⁇
  Dec-masks {mx = mx} {y = y} .dec
    with mx
  ... | nothing = yes mask
  ... | just x  = mapDec (λ where refl → refl) (λ where refl → refl) (x ≟ y)

_ : (nothing ∷ just ─ ∷ nothing ∷ []) -masks*-
    (q       ∷ ─      ∷ q       ∷ [])
_ = auto

-- ** Complies-with
instance
  Dec-Complies-Sy-MQ : _~_ {A = Syllable} {B = Maybe Quantity} ⁇²
  Dec-Complies-Sy-MQ {x = sy}{mq} .dec
    with ¿ ─Syllable sy ¿ | ¿ ·Syllable sy ¿ | mq
  ... | yes ─sy | _ | just ─
    = yes $ long ─sy
  ... | _ | yes ·sy | just ·
    = yes $ short ·sy
  ... | no ¬─sy | no ¬·sy | nothing
    = yes $ ambiguous ¬─sy ¬·sy
  ... | _ | no ¬·sy | just ·
    = no λ where (short ·sy) → ¬·sy ·sy
  ... | no ¬─sy | _ | just ─
    = no λ where (long ─sy) → ¬─sy ─sy
  ... | yes ─sy | _ | nothing
    = no λ where (ambiguous ¬─sy _) → ¬─sy ─sy
  ... | _ | yes ·sy | nothing
    = no λ where (ambiguous _ ¬·sy) → ¬·sy ·sy

_ : _~_ {A = Vec Syllable n} {B = Vec (Maybe Quantity) n} ⁇²
_ = it

--
toList-length : ∀ {A : Type} (xs : Vec A n) →
  length (V.toList xs) ≡ n
toList-length = λ where
  [] → refl
  (_ ∷ xs) → cong suc (toList-length xs)

toList-inj : ∀ {A : Type} (xs ys : Vec A n) →
  V.toList xs ≡ V.toList ys → xs ≡ ys
toList-inj []       []       refl = refl
toList-inj (_ ∷ xs) (_ ∷ ys) eq
  with refl , eq ← L.∷-injective eq
  = cong (_ ∷_) (toList-inj xs ys eq)
--

𝔑 = List Quantity

normQuantities : Vec Quantity n → 𝔑
normQuantities = V.toList

normFoot : Foot n qs → 𝔑
normFoot {qs = qs} _ = normQuantities qs

norm∃Foot : ∃∃Foot → 𝔑
norm∃Foot (_ , qs , _) = normQuantities qs

normMeter : Meter n m → 𝔑
normMeter (mkPM fs) = L.concatMap norm∃Foot fs

normMeter≡ : (pm : Meter n m) → length (normMeter pm) ≡ n
normMeter≡ (mkPM []) = refl
normMeter≡ (mkPM ((n , qs , f) ∷ fs)) =
  let open ≡-Reasoning in
  begin
    length (L.concatMap norm∃Foot ((n , qs , f) ∷ fs))
  ≡⟨⟩
    length (V.toList qs ++ concatMap norm∃Foot fs)
  ≡⟨ L.length-++ (V.toList qs) ⟩
    length (V.toList qs) + length (concatMap norm∃Foot fs)
  ≡⟨ cong (_+ _) $ toList-length qs ⟩
    n + length (concatMap norm∃Foot fs)
  ≡⟨ cong (λ ◆ → _ + ◆) $ normMeter≡ (mkPM fs) ⟩
    n + ∑₁ fs
  ≡⟨⟩
    ∑₁ ((n , qs , f) ∷ fs)
  ∎

_norm~_ : Vec Quantity n → Meter n m → Type
qs norm~ pm = normQuantities qs ≡ normMeter pm

toList∘subst∘fromList : ∀ {A : Type} (xs : List A) (eq : length xs ≡ n′) →
  ( V.toList
  $ subst (Vec A) eq
  $ V.fromList xs
  )
  ≡ xs
toList∘subst∘fromList xs refl = V.toList∘fromList xs

private _~~_ = _ˢ~ᵐ_

~-sound : qs norm~ pm → qs ~~ pm
~-sound {qs = qs} {pm = mkPM []} p
  = QED
  where
  qs≡ : qs ≡ []
  qs≡ with ⟫ [] ← ⟫ qs = refl

  QED : qs ~~ mkPM []
  QED = subst (_~~ _) (sym qs≡) []
~-sound {qs = qs} {pm = mkPM ((_ , _ , ──) ∷ fs)} p
  with IH ← (λ qs′ → ~-sound {qs = qs′} {pm = mkPM fs})
  = subst (_~~ _) (sym qs≡)
  $ sponde (IH _qs′ p′)
  where
  _qs′ : Vec Quantity (∑₁ fs)
  _qs′ =
    ( subst (Vec Quantity) (normMeter≡ (mkPM fs))
    $ V.fromList
    $ normMeter (mkPM fs)
    )

  p′ : V.toList _qs′ ≡ normMeter (mkPM fs)
  p′ = let open ≡-Reasoning in
    begin
      V.toList _qs′
    ≡⟨⟩
      ( V.toList
      $ subst (Vec Quantity) (normMeter≡ (mkPM fs))
      $ V.fromList
      $ normMeter (mkPM fs)
      )
    ≡⟨ toList∘subst∘fromList (normMeter $ mkPM fs) (normMeter≡ (mkPM fs)) ⟩
      normMeter (mkPM fs)
    ∎

  qs≡ : qs ≡ ─ ∷ ─ ∷ _qs′
  qs≡ = let open ≡-Reasoning in
    toList-inj _ _ $
    begin
      V.toList qs
    ≡⟨ p ⟩
      ─ ∷ ─ ∷ normMeter (mkPM fs)
    ≡˘⟨ cong (λ ◆ → ─ ∷ ─ ∷ ◆) p′ ⟩
      ─ ∷ ─ ∷ V.toList _qs′
    ≡⟨⟩
      V.toList (─ ∷ ─ ∷ _qs′)
    ∎
~-sound {qs = qs} {pm = mkPM ((_ , _ , ─··) ∷ fs)} p
  with IH ← (λ qs′ → ~-sound {qs = qs′} {pm = mkPM fs})
  = subst (_~~ _) (sym qs≡)
  $ dactyl (IH _qs′ p′)
  where
  _qs′ : Vec Quantity (∑₁ fs)
  _qs′ =
    ( subst (Vec Quantity) (normMeter≡ (mkPM fs))
    $ V.fromList
    $ normMeter (mkPM fs)
    )

  p′ : V.toList _qs′ ≡ normMeter (mkPM fs)
  p′ = let open ≡-Reasoning in
    begin
      V.toList _qs′
    ≡⟨⟩
      ( V.toList
      $ subst (Vec Quantity) (normMeter≡ (mkPM fs))
      $ V.fromList
      $ normMeter (mkPM fs)
      )
    ≡⟨ toList∘subst∘fromList (normMeter $ mkPM fs) (normMeter≡ (mkPM fs)) ⟩
      normMeter (mkPM fs)
    ∎

  qs≡ : qs ≡ ─ ∷ · ∷ · ∷ _qs′
  qs≡ = let open ≡-Reasoning in
    toList-inj _ _ $
    begin
      V.toList qs
    ≡⟨ p ⟩
      ─ ∷ · ∷ · ∷ normMeter (mkPM fs)
    ≡˘⟨ cong (λ ◆ → ─ ∷ · ∷ · ∷ ◆) p′ ⟩
      ─ ∷ · ∷ · ∷ V.toList _qs′
    ≡⟨⟩
      V.toList (─ ∷ · ∷ · ∷ _qs′)
    ∎

~-complete : qs ~~ pm → qs norm~ pm
~-complete [] = refl
~-complete (sponde {pm = mkPM _} IH)
  = cong (λ ◆ → ─ ∷ ─ ∷ ◆)
  $ ~-complete IH
~-complete (dactyl {pm = mkPM _} IH)
  = cong (λ ◆ → ─ ∷ · ∷ · ∷ ◆)
  $ ~-complete IH

instance
  Dec-Complies-Qs-PM : _~_ {A = Vec Quantity n} {B = Meter n m} ⁇²
  Dec-Complies-Qs-PM {x = qs} {pm} .dec
    with ¿ qs norm~ pm ¿
  ... | yes p = yes (~-sound p)
  ... | no ¬p = no  (¬p ∘ ~-complete)

allPMs :
  (qs : Vec Quantity n) →
  ∃ λ (pms : List (∃ λ m → Meter n m)) →
      (∀ {m} {pm : Meter n m} → (m , pm) ∈ pms → qs ~ pm)
    × (∀ {m} {pm : Meter n m} → qs ~ pm → (m , pm) ∈ pms)
allPMs [] = [ 0 , mkPM [] ]
          , (λ where (here refl) → [])
          , (λ where [] → here refl)
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

derivable? : ∀ {n} {qs : Vec Quantity n} → Dec $
  ∃ λ m → ∃ λ (pm : Meter n m) → qs ~ pm
derivable? {n} {qs}
  with pms , sound-pms , complete-pms ← allPMs qs
  with pms
... | []           = no λ (m , pm , pm~) → case complete-pms pm~ of λ ()
... | (m , pm) ∷ _ = yes (m , pm , sound-pms (here refl))

-- nonDerivable? : ∀ {n} {qs : Vec Quantity n} → Dec $
--   ∀ m (pm : Meter n m) → qs ≁ pm
-- nonDerivable? {n} {qs}
--   with derivable? {n} {qs}
-- ... | yes (m , pm , pm~) = no λ pm≁ → pm≁ m pm pm~
-- ... | no ∄pm = yes λ m pm pm~ → ∄pm (m , pm , pm~)

nonDerivable? : ∀ {n} {qs : Vec Quantity n} → Dec $
  ¬ (∃ λ m → ∃ λ (pm : Meter n m) → qs ~ pm)
nonDerivable? {n} {qs} = ¬? (derivable? {n} {qs})

{-
instance
  Dec-NonDerivable-Qs-PM : NonDerivable {A = Vec Quantity n} {B = Meter n m} ⁇¹
  Dec-NonDerivable-Qs-PM {m = m} {x = qs} .dec
    with pms , sound-pms , complete-pms ← allPMs qs
    with pms
  ... | [] = yes λ _ pm~ → case complete-pms pm~ of λ ()
  ... | (m , pm) ∷ _ = no λ pm≁ → pm≁ {!pm!} {!!}
-}

{-
record {A B : Type} (P : A → Type)
  CharacterizesPred
  : Type where
  field
    allPred  : List A
    sound    : ∀ {a} → a ∈ allPred → P a
    complete : ∀ {a} → P a → a ∈ allPred

record {A B : Type} (R : A → B → Type)
  CharacterizesRel
  : Type where
  field
    allRel   : A → List B
    sound    : ∀ {a b} → b ∈ allRel a → R a b
    complete : ∀ {a b} → R a b → b ∈ allRel a
-}

satisfied′ : ∀ {A : Type} {P : A → Type} {xs : List A}
  → Any P xs
  → ∃ λ x → x ∈ xs × P x
satisfied′ = λ where
  (here px)   → -, here refl , px
  (there pxs) → let x , x∈ , px = satisfied′ pxs
                in  x , there x∈ , px

allMasks :
  (mqs : Vec (Maybe Quantity) n) →
  ∃ λ (qss : List (Vec Quantity n)) →
      (∀ {qs} → qs ∈ qss → mqs -masks*- qs)
    × (∀ {qs} → mqs -masks*- qs → qs ∈ qss)
allMasks [] = [ [] ]
            , (λ where (here refl) → [])
            , (λ where [] → here refl)
allMasks (mq ∷ mqs)
  with qss , sound-qss , complete-qss ← allMasks mqs
  with mq
... | just q
  = QED
  where
  sou : _
  sou qs∈
    with qs , qs∈ , refl ← ∈-map⁻ (q ∷_) qs∈
    = refl ∷ sound-qss qs∈

  com : _
  com (refl ∷ p) = ∈-map⁺ (q ∷_) (complete-qss p)

  QED : _
  QED = map (q ∷_) qss , sou , com
... | nothing
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
  ... | here refl         = mask ∷ sound-qss qs∈′
  ... | there (here refl) = mask ∷ sound-qss qs∈′

  com : _
  com (mask {x = q} ∷ p)
    = ∈-concat⁺ {xss = qssF}
    $ L.Any.map⁺
    $ L.Any.map (λ where refl → P⇒Q) (complete-qss p)
    where
    P⇒Q : _
    P⇒Q with ⟫ q
    ... | ⟫ ─ = here refl
    ... | ⟫ · = there $′ here refl

  QED : _
  QED = qss′ , sou , com

instance
  Dec-Complies-MQs-PM : _~_ {A = Vec (Maybe Quantity) n} {B = Hexameter n} ⁇²
  Dec-Complies-MQs-PM {n} {x = mqs} {pm} .dec
    with qss , sound-qss , complete-qss ← allMasks mqs
    with ¿ Any (λ qs → mkLastLong {n} (Hex>0 pm) qs ~ pm) qss ¿
  ... | yes ∃x =
    let qs , qs∈ , pm~ = satisfied′ ∃x
        msk = sound-qss qs∈
    in yes (reify msk pm~)
  ... | no ∄x
    = no λ where
      (reify msk pm~) →
        ∄x (L.Any.map (λ where refl → pm~) (complete-qss msk))

onlyHexameters :
  List (∃ $ Meter n) → List (Hexameter n)
onlyHexameters = L.mapMaybe onlyHexameter
  module _ where
  onlyHexameter : ∃ (Meter n) → Maybe (Meter n 6)
  onlyHexameter (m , pm) with m ≟ 6
  ... | yes refl = just pm
  ... | no  _    = nothing

allHexameters :
  (mqs : Vec (Maybe Quantity) n) →
  ∃ λ (pms : List (Hexameter n)) →
      (∀ {pm} → pm ∈ pms → mqs ~ pm)
    × (∀ {pm} → mqs ~ pm → pm ∈ pms)
allHexameters {0} mqs = [] , (λ ()) , λ where
  (reify {pm = pm} msk p) → ⊥-elim $ Hex≢0 pm
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

  sou : ∀ {pm} → pm ∈ concatMap sols qss → mqs ~ pm
  sou {pm} pm∈
    with qs , qs∈ , pm∈ ← satisfied′ $ ∈-concatMap⁻ sols {xs = qss} pm∈
    with pms , sound-pms , complete-pms ← allPMs (mkLastLong {n = n} (s≤s z≤n) qs)
    with (m , pm) , pm∈ , pm≡ ← ∈-mapMaybe⁻ (onlyHexameter {n}) {xs = pms} pm∈
    with 6 ← m
    with refl ← pm≡
    = reify (sound-qss qs∈) (sound-pms pm∈)

  com : ∀ {pm} → mqs ~ pm → pm ∈ concatMap sols qss
  com {pm} (reify {qs = qs} msk pm~) =
    let pms , sound-pms , complete-pms = allPMs (mkLastLong {n = n} (s≤s z≤n) qs) in
    ∈-concatMap⁺ sols {xs = qss}
        (L.Any.map
          (λ where refl → ∈-mapMaybe⁺ (onlyHexameter {n}) {xs = pms} (complete-pms pm~) refl)
          (complete-qss msk))

derivableM? : ∀ {n} (mqs : Vec (Maybe Quantity) n) → Dec $
  ∃ λ (pm : Hexameter n) → mqs ~ pm
derivableM? {n} mqs
  with pms , sound-pms , complete-pms ← allHexameters mqs
  with pms
... | []     = no λ (pm , pm~) → case complete-pms pm~ of λ ()
... | pm ∷ _ = yes (pm , sound-pms (here refl))

nonDerivableM? : ∀ {n} (mqs : Vec (Maybe Quantity) n) → Dec $
  ¬ (∃ λ (pm : Hexameter n) → mqs ~ pm)
nonDerivableM? {n} mqs = ¬? (derivableM? {n} mqs)

instance
  Dec-NonDerivable-MQs-PM : NonDerivable {A = Vec (Maybe Quantity) n} {B = Hexameter n} ⁇¹
  Dec-NonDerivable-MQs-PM {n} {x = mqs} .dec
    with nonDerivableM? mqs
  ... | yes ∄pm = yes λ pm pm~ → ∄pm (pm , pm~)
  ... | no  ∃pm = no λ pm≁ → ∃pm (uncurry pm≁)
