-- ** decision procedures
{-# OPTIONS --safe #-}
module Iliagda.Dec2 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody

pattern 𝟘 = here refl
pattern 𝟙 = there 𝟘
pattern 𝟚 = there 𝟙
pattern 𝟛 = there 𝟚

-- ** synezesis
instance
  Dec-syn : (sys -synezizes*- sys′) ⁇
  Dec-syn {sys = []} {sys′ = []} .dec = yes []
  Dec-syn {sys = []} {sys′ = _ ∷ _} .dec = no λ ()
  Dec-syn {sys = _ ∷ _} {sys′ = []} .dec = no λ ()
  Dec-syn {sys = sy ∷ sys} {sys′ = sy′ ∷ sys′} .dec
    with sy ≟ sy′
  ... | yes refl
    =  mapDec (_ ∷_) uncons ¿ sys -synezizes*- sys′ ¿
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
       × (sys -synezizes*- sys′)
       × (sy′ ≡ sy ⁀ sy↓)
       ¿

-- ** VPointwise
instance
  Dec-VPointwise : ∀ {_~_ : X → Y → Type ℓ} {xs : Vec X n} {ys : Vec Y n} →
    ⦃ _~_ ⁇² ⦄ → VPointwise _~_ xs ys ⁇
  Dec-VPointwise .dec = V.PW.decidable dec² _ _

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
  Dec-Complies-Sy-MQ : _~_ {A = Syllable × Context} {B = Maybe Quantity} ⁇²
  Dec-Complies-Sy-MQ {x = sy , ctx}{mq} .dec
    with ¿ ─Syllable ctx sy ¿ | ¿ ·Syllable ctx sy ¿ | mq
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

_ : _~_ {A = Vec Syllable n × Context} {B = Quantities n} ⁇²
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

derivable? : ∀ {n} {qs : Vec Quantity n} → Dec $
  ∃ λ m → ∃ λ (pm : Meter n m) → qs ~ pm
derivable? {n} {qs}
  with pms , sound-pms , complete-pms ← allPMs qs
  with pms
... | []           = no λ (m , pm , pm~) → case complete-pms pm~ of λ ()
... | (m , pm) ∷ _ = yes (m , pm , sound-pms 𝟘)

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
  ... | 𝟘 = mask ∷ sound-qss qs∈′
  ... | 𝟙 = mask ∷ sound-qss qs∈′

  com : _
  com (mask {x = q} ∷ p)
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

instance
  Dec-Complies-MQs-PM : _~_ {A = Quantities n} {B = Hexameter n} ⁇²
  Dec-Complies-MQs-PM {n} {x = mqs} {hm} .dec
    with qss , sound-qss , complete-qss ← allMasks mqs
    with ¿ Any (λ qs → mkLastLong {n} (Hex>0 hm) qs ~ hm) qss ¿
  ... | yes ∃x =
    let qs , qs∈ , hm~ = satisfied′ ∃x
        msk = sound-qss qs∈
    in yes (reify msk hm~)
  ... | no ∄x
    = no λ where
      (reify msk hm~) →
        ∄x (L.Any.map (λ where refl → hm~) (complete-qss msk))

onlyHexameters :
  List (∃ $ Meter n) → List (Hexameter n)
onlyHexameters = L.mapMaybe onlyHexameter
  module _ where
  onlyHexameter : ∃ (Meter n) → Maybe (Meter n 6)
  onlyHexameter (m , pm) with m ≟ 6
  ... | yes refl = just pm
  ... | no  _    = nothing

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

derivableM? : ∀ {n} (mqs : Quantities n) → Dec $
  ∃ λ (hm : Hexameter n) → mqs ~ hm
derivableM? {n} mqs
  with hms , sound-hms , complete-hms ← allHexameters mqs
  with hms
... | []     = no λ (hm , hm~) → case complete-hms hm~ of λ ()
... | hm ∷ _ = yes (hm , sound-hms 𝟘)

nonDerivableM? : ∀ {n} (mqs : Quantities n) → Dec $
  ¬ (∃ λ (hm : Hexameter n) → mqs ~ hm)
nonDerivableM? {n} mqs = ¬? (derivableM? {n} mqs)

instance
  Dec-NonDerivable-MQs-PM : NonDerivable {A = Quantities n} {B = Hexameter n} ⁇¹
  Dec-NonDerivable-MQs-PM {n} {x = mqs} .dec
    with nonDerivableM? mqs
  ... | yes ∄hm = yes λ hm hm~ → ∄hm (hm , hm~)
  ... | no  ∃hm = no λ hm≁ → ∃hm (uncurry hm≁)

lookup-updateAt≡ : ∀ {A : Type} {xs : Vec A n} {x : A} (i : Fin n) →
  V.lookup xs i ≡ x → xs ≡ xs V.[ i ]≔ x
lookup-updateAt≡ {xs = _ ∷ _} Fi.zero refl = refl
lookup-updateAt≡ {xs = _ ∷ _} (fsuc i) eq = cong (_ ∷_) (lookup-updateAt≡ i eq)

[1160]˘ :
  (mqs : Quantities n) (w : Word n) →
  ∃ λ (mqss : List (Quantities n)) →
      (∀ {mqs′} → mqs′ ∈ mqss → mqs ≡ [1160] {n = n} w mqs′)
    × (∀ {mqs′} → mqs ≡ [1160] {n = n} w mqs′ → mqs′ ∈ mqss)
[1160]˘ {n} mqs w
  with n
... | 0 = [ mqs ] , (λ where 𝟘 → refl) , (λ where refl → 𝟘)
... | 1 = [ mqs ] , (λ where 𝟘 → refl) , (λ where refl → 𝟘)
... | n@(suc n-1@(suc _))
  with n>1 ← (n > 1) ∋ s≤s (s≤s z≤n)
  with circumflexPenult? w
... | no _ = [ mqs ] , (λ where 𝟘 → refl) , (λ where refl → 𝟘)
... | yes cp
  using i ← Fi.fromℕ n-1
  with V.lookup mqs i in i≡
... | nothing
  = [] , (λ ()) , (λ {mqs′} mqs≡ → contradict $ let open ≡-Reasoning in
    begin
      nothing
    ≡˘⟨ i≡ ⟩
      V.lookup mqs i
    ≡⟨ cong (flip V.lookup i) mqs≡ ⟩
      V.lookup (mqs′ V.[ i ]≔ just ·) i
    ≡⟨ V.lookup∘updateAt i mqs′ ⟩
      just ·
    ∎
    )
... | just ─
  = [] , (λ ()) , (λ {mqs′} mqs≡ → contradict $ let open ≡-Reasoning in
    begin
      just ─
    ≡˘⟨ i≡ ⟩
      V.lookup mqs i
    ≡⟨ cong (flip V.lookup i) mqs≡ ⟩
      V.lookup (mqs′ V.[ i ]≔ just ·) i
    ≡⟨ V.lookup∘updateAt i mqs′ ⟩
      just ·
    ∎
    )
... | just ·
  = QED
  where
  set = mqs V.[ i ]≔_

  mqss = [ set nothing ⨾ set (just ─) ⨾ set (just ·) ]

  sou : _
  sou =
    let
      sou′ = λ mq → let open ≡-Reasoning in
        begin
          mqs
        ≡⟨ lookup-updateAt≡ i i≡ ⟩
          mqs V.[ i ]≔ just ·
        ≡˘⟨ V.[]≔-idempotent mqs i ⟩
          (mqs V.[ i ]≔ mq) V.[ i ]≔ just ·
        ≡⟨⟩
          set mq V.[ i ]≔ just ·
        ∎
    in
    λ where
      𝟘 → sou′ nothing
      𝟙 → sou′ (just ─)
      𝟚 → sou′ (just ·)
      (there (there (there ())))
      -- cannot comment this out, deep Agda bug?

  com : _
  com {mqs′} eq
    with V.lookup mqs′ i in i≡
  ... | nothing
    = here let open ≡-Reasoning in
      begin
        mqs′
      ≡⟨ lookup-updateAt≡ {xs = mqs′} i i≡ ⟩
        mqs′ V.[ i ]≔ nothing
      ≡˘⟨ V.[]≔-idempotent mqs′ i ⟩
        mqs′ V.[ i ]≔ (just ·) V.[ i ]≔ nothing
      ≡˘⟨ cong (V._[ i ]≔ _) eq ⟩
        mqs V.[ i ]≔ nothing
      ≡⟨⟩
        set nothing
      ∎
  ... | just ─
    = there $ here let open ≡-Reasoning in
      begin
        mqs′
      ≡⟨ lookup-updateAt≡ {xs = mqs′} i i≡ ⟩
        mqs′ V.[ i ]≔ just ─
      ≡˘⟨ V.[]≔-idempotent mqs′ i ⟩
        mqs′ V.[ i ]≔ (just ·) V.[ i ]≔ just ─
      ≡˘⟨ cong (V._[ i ]≔ _) eq ⟩
        mqs V.[ i ]≔ just ─
      ≡⟨⟩
        set (just ─)
      ∎
  ... | just ·
    = there $ there $ here let open ≡-Reasoning in
      begin
        mqs′
      ≡⟨ lookup-updateAt≡ {xs = mqs′} i i≡ ⟩
        mqs′ V.[ i ]≔ just ·
      ≡˘⟨ V.[]≔-idempotent mqs′ i ⟩
        mqs′ V.[ i ]≔ (just ·) V.[ i ]≔ just ·
      ≡˘⟨ cong (V._[ i ]≔ _) eq ⟩
        mqs V.[ i ]≔ just ·
      ≡⟨⟩
        set (just ·)
      ∎

  QED : _
  QED = mqss , sou , com

instance
  Dec-Complies-W-MQs : _~_ {A = Word n × Context} {B = Quantities n} ⁇²
  Dec-Complies-W-MQs {n} {x = w , ctx} {mqs} .dec
    with mqss , sound-mqss , complete-mqss ← [1160]˘ mqs w
    with ¿ Any (λ mqs′ → (unword w , ctx) ~ mqs′) mqss ¿
  ... | yes ∃x
    with mqs′ , mqs∈ , w~ ← satisfied′ ∃x
    with refl ← sound-mqss mqs∈
    = yes (base w~)
  ... | no ∄x = no λ where
    (base w~) → ∄x (L.Any.map (λ where refl → w~) $ complete-mqss refl)

  Dec-Complies-Ws-MQs : _~_ {A = Words n} {B = Quantities n} ⁇²
  Dec-Complies-Ws-MQs {n} {x = []} {[]} .dec = yes []
  Dec-Complies-Ws-MQs {.(n + n′)} {x = _∷_ {n = n} {n′ = n′} w ws} {mqs₀} .dec
    using mqs , mqs′ , mqs≡ ← V.splitAt n mqs₀
    using nextSy ← L.head $ toList $ unwords ws
    using wctx   ← maybe firstConsonants [] nextSy
    with ¿ (w , wctx) ~ʷ mqs ¿ | ¿ ws ~ mqs′ ¿
    -- AGDA BUG: interaction breaks in these subterms!!!
  ... | yes h₁ | yes h₂ = yes (_∷_ ⦃ mqs≡ ⦄ h₁ h₂)
  ... | no ¬h₁ | _      = no λ where
    (_∷_ {mqs = `mqs} {mqs′ = `mqs′} ⦃ `mqs≡ ⦄ h₁ _) →
      ¬h₁ $
      subst (_ ~ʷ_) (V.++-injectiveˡ `mqs mqs (trans (sym `mqs≡) mqs≡))
      h₁
  ... | _      | no ¬h₂ = no λ where
    (_∷_ {mqs = `mqs} {mqs′ = `mqs′} ⦃ `mqs≡ ⦄ _ h₂) →
      ¬h₂ $
      subst (_ ~ʷˢ_) (V.++-injectiveʳ `mqs mqs (trans (sym `mqs≡) mqs≡))
      h₂

theQuantity₀ :
  (sy : Syllable) (ctx : Context) →
  ∃ λ (mq : Maybe Quantity) →
      (∀ {mq′} → mq′ ≡ mq → (sy , ctx) ~ mq′)
    × (∀ {mq′} → (sy , ctx) ~ mq′ → mq′ ≡ mq)
theQuantity₀ sy ctx
  with ¿ ─Syllable ctx sy ¿ | ¿ ·Syllable ctx sy ¿
... | yes ─sy | yes (¬─sy , _)
  = ⊥-elim $ ¬─sy ─sy
... | yes ─sy | no ¬·sy
  = just ─
  , (λ where refl → long ─sy)
  , λ where (long _) → refl
            (short ·sy) → ⊥-elim $ ¬·sy ·sy
            (ambiguous ¬─sy _) → ⊥-elim $ ¬─sy ─sy
... | no ¬─sy | yes ·sy
  = just ·
  , (λ where refl → short ·sy)
  , λ where (short _) → refl
            (long ─sy) → ⊥-elim $ ¬─sy ─sy
            (ambiguous _ ¬·sy) → ⊥-elim $ ¬·sy ·sy
... | no ¬─sy | no ¬·sy
  = nothing
  , (λ where refl → ambiguous ¬─sy ¬·sy)
  , λ where (ambiguous _ _) → refl
            (long ─sy) → ⊥-elim $ ¬─sy ─sy
            (short ·sy) → ⊥-elim $ ¬·sy ·sy

Dec-Complies-Sy-MQ′ : _~_ {A = Syllable × Context} {B = Maybe Quantity} ⁇²
Dec-Complies-Sy-MQ′ {x = sy , ctx}{mq′} .dec
  with mq , sound-mq , complete-mq ← theQuantity₀ sy ctx
  with mq′ ≟ mq
... | yes mq≡ = yes $ sound-mq mq≡
... | no  mq≢ = no λ sy~mq → ⊥-elim (mq≢ $ complete-mq sy~mq)

theQuantities₀∗ :
  (sys : Vec Syllable n) (ctx : Context) →
  ∃ λ (mqs : Quantities n) →
      (∀ {mqs′} → mqs′ ≡ mqs → (sys , ctx) ~ mqs′)
    × (∀ {mqs′} → (sys , ctx) ~ mqs′ → mqs′ ≡ mqs)
theQuantities₀∗ [] ctx
  = [] , (λ where refl → []) , (λ where [] → refl)
theQuantities₀∗ [ sy ] ctx
  with mq , sound-mq , complete-mq ← theQuantity₀ sy ctx
  = [ mq ]
  , (λ where refl → sound-mq refl ∷ [])
  , λ where (sy~mq ∷ []) → cong (_∷ []) (complete-mq sy~mq)
theQuantities₀∗ (sy ∷ sys@(sy′ ∷ _)) ctx
  with mqs , sound-mqs , complete-mqs ← theQuantities₀∗ sys ctx
  with mq  , sound-mq  , complete-mq  ← theQuantity₀ sy (firstConsonants sy′)
  = mq ∷ mqs
  , (λ where refl → sound-mq refl ∷ sound-mqs refl)
  , λ where (sy~mq ∷ sys~mqs) → cong₂ _∷_ (complete-mq sy~mq) (complete-mqs sys~mqs)

theQuantities₁ :
  (w : Word n) (wctx : Context) →
  ∃ λ (mqs : Quantities n) →
      (∀ {mqs′} → mqs′ ≡ mqs → (w , wctx) ~ mqs′)
    × (∀ {mqs′} → (w , wctx) ~ mqs′ → mqs′ ≡ mqs)
theQuantities₁ w wctx
  with mqs , sound-mqs , complete-mqs ← theQuantities₀∗ (unword w) wctx
  = [1160] w mqs
  , (λ where refl → base (sound-mqs refl))
  , λ where (base sys~mqs) → cong ([1160] w) (complete-mqs sys~mqs)

theQuantities :
  (ws : Words n) →
  ∃ λ (mqs : Quantities n) →
      (∀ {mqs′} → mqs′ ≡ mqs → ws ~ mqs′)
    × (∀ {mqs′} → ws ~ mqs′ → mqs′ ≡ mqs)
theQuantities [] = [] , (λ where refl → []) , λ where [] → refl
theQuantities (w ∷ ws)
  = let
      nextSy : Maybe Syllable
      nextSy = L.head $ toList $ unwords ws

      wctx   = maybe firstConsonants [] nextSy

      mqs  , sound-mqs  , complete-mqs  = theQuantities₁ w wctx
      mqs′ , sound-mqs′ , complete-mqs′ = theQuantities ws
    in
      (mqs V.++ mqs′)
      , (λ where refl → sound-mqs refl ∷ sound-mqs′ refl)
      , λ where (_∷_ ⦃ refl ⦄ w~mqs ws~mqs′) →
                     cong₂ V._++_ (complete-mqs  w~mqs) (complete-mqs′ ws~mqs′)

allSynezeses : ∀ (sys : Vec Syllable n) n′ →
  ∃ λ (syss : List (Vec Syllable n′)) →
      (∀ {sys′} → sys′ ∈ syss → sys -synezizes*- sys′)
    × (∀ {sys′} → sys -synezizes*- sys′ → sys′ ∈ syss)

-- n′ = 0
allSynezeses [] 0 = [ [] ] , (λ where 𝟘 → []) , λ where [] → 𝟘
allSynezeses [] (suc _) = [] , (λ ()) , λ ()

-- n′ = 1
allSynezeses [ sy ] 0 = [] , (λ ()) , λ ()
allSynezeses [ sy ] 1 = [ [ sy ] ] , (λ where 𝟘 → _ ∷ []) , λ where (_ ∷ []) → 𝟘
allSynezeses [ sy ] (suc (suc _)) = [] , (λ ()) , λ where (_ ∷ ())

-- n′ > 1
allSynezeses (sy ∷ sys@(sy′ ∷ _)) 0
  = [] , (λ ()) , λ ()
allSynezeses (sy ∷ sys@(sy′ ∷ sys′)) n′@(suc n′-1)
  with ¿ LastVowel sy × FirstVowel sy′ ¿
... | yes vv

  -- DON'T DO THE SYNIZESIS
  using syss , sound-syss , complete-syss ← allSynezeses sys n′-1

  -- DO DO THE SYNIZESIS
  using syss′ , sound-syss′ , complete-syss′ ← allSynezeses sys′ n′-1

  using sysˡ ← map (sy ∷_) syss
  using sysʳ ← map ((sy ⁀ sy′) ∷_) syss′
  = sysˡ ++ sysʳ
  , (λ syn∈ → case ∈-++⁻ sysˡ syn∈ of λ where
       (inj₁ syn∈ˡ) → let syn′ , syn′∈ , sys≡ = ∈-map⁻ (sy ∷_) syn∈ˡ
                       in subst (_ -synezizes*-_) (sym sys≡) (sy ∷ sound-syss syn′∈)
       (inj₂ syn∈ʳ) → let syn′ , syn′∈ , sys≡ = ∈-map⁻ ((sy ⁀ sy′) ∷_) syn∈ʳ
                       in subst (_ -synezizes*-_) (sym sys≡) (vv ∺ sound-syss′ syn′∈)
    )
  , λ where (sy ∷ p) → ∈-++⁺ˡ (∈-map⁺ (sy ∷_) (complete-syss p))
            ((vv ∺ p) ⦃ refl ⦄) → ∈-++⁺ʳ sysˡ (∈-map⁺ ((sy ⁀ sy′) ∷_) (complete-syss′ p))
... | no ¬vv
  using syss , sound-syss , complete-syss ← allSynezeses sys n′-1
  = map (sy ∷_) syss
  , (λ syn∈ → let syn′ , syn′∈ , sys≡ = ∈-map⁻ (sy ∷_) syn∈
               in subst (_ -synezizes*-_) (sym sys≡) (sy ∷ sound-syss syn′∈))
  , λ where (sy ∷ p) → ∈-map⁺ (sy ∷_) (complete-syss p)
            (vv ∺ _) → ⊥-elim $ ¬vv vv

uniqueSyn : (p q : sys -synezizes*- sys′) → p ≡ q
uniqueSyn [] [] = refl
uniqueSyn (sy ∷ p) (.sy ∷ q) = cong (sy ∷_) (uniqueSyn p q)
uniqueSyn (sy ∷ _) ((_ ∺ _) ⦃ eq ⦄) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn ((_ ∺ _) ⦃ eq ⦄) (sy ∷ _) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn ((_ ∺ p) ⦃ refl ⦄) ((_ ∺ q) ⦃ refl ⦄) = cong (_ ∺_) $ uniqueSyn p q

Derivation : Words n → Type
Derivation ws = ∃ λ n′ → ∃ λ (hm : Hexameter n′) → ws ~ hm

-- record Derivation (ws : Words n) : Type where
--   field
--     {n′}   : ℕ
--     hm     : Hexameter n′
--     .ws~hm : ws ~ hm

Derivations : Words n → Type
Derivations ws = List (Derivation ws)

{- OPTION 2: using theQuantities/allSynezeses′/allHexameters -}

syn⇒≤ : ∀ {sys : Vec Syllable n} {sys′ : Vec Syllable n′}
  → sys -synezizes*- sys′
  → n ≥ n′
syn⇒≤ = λ where
  []      → z≤n
  (_ ∷ p) → s≤s $ syn⇒≤ p
  (_ ∺ p) → Nat.m≤n⇒m≤1+n $ s≤s $ syn⇒≤ p

Syllables = Vec Syllable

record _-synezizes+-′_ (sys : Syllables n) (sys′ : Syllables n′) : Type where
  constructor _⊣_
  field
    syn   : sys -synezizes*- sys′
    .syn+ : n ≢ n′
    -- .syn+ : n > n′
    -- .syn+ : sys ≢ sys′
    -- .syn+ : penalty syn > 0

allSynezeses′ : ∀ (sys : Syllables n) →
  ∃ λ (n×syss : List (∃ λ n′ → Syllables n′)) →
      (∀ {n′ sys′} → (n′ , sys′) ∈ n×syss → sys -synezizes+-′ sys′)
    × (∀ {n′ sys′} → sys -synezizes+-′ sys′ → (n′ , sys′) ∈ n×syss)
allSynezeses′ {n} sys
  = n×syss , sou , com
 where
 ns′    = L.downFrom n
 mk     = (λ n′ → map (n′ ,_) $ allSynezeses sys n′ .proj₁)
 n×syss = concatMap mk ns′

 sou : ∀ {n′ sys′} → (n′ , sys′) ∈ n×syss → sys -synezizes+-′ sys′
 sou {n′}{sys′} n×sys∈
   using syss , sound-syss , _ ← allSynezeses sys n′
   = sound-syss sys∈ ⊣ {!!}
   where
   sys∈ : sys′ ∈ syss
   sys∈ with p ← ∈-concatMap⁻ mk {ns′} n×sys∈
   -- ... | here p
   --   with sys , sys∈ , refl ← ∈-map⁻ (_ ,_) p
   --   = sys∈
   -- ... | there n∈
   --   with _ , _ , p ← L.Any.applyDownFrom⁻ id n∈
   --   with sys , sys∈ , refl ← ∈-map⁻ (_ ,_) p
     -- = sys∈
     = {!!}

 com : ∀ {n′ sys′} → sys -synezizes+-′ sys′ → (n′ , sys′) ∈ n×syss
 com {n′} {sys′} (syn ⊣ _)
   using syss , _ , complete-syss ← allSynezeses sys n′
   = ∈-concatMap⁺ mk
   $ L.Any.map (λ where refl → ∈-map⁺ (_ ,_) (complete-syss syn)) n∈
   where
   n∈ : n′ ∈ ns′
   n∈
     = ∈-downFrom⁺ {!syn⁺⇒< syn!}
   --   with Nat.m≤n⇒m<n∨m≡n $ syn⇒≤ syn
   -- ... | inj₁ n′<n
   --   = there (∈-downFrom⁺ n′<n)
   -- ... | inj₂ refl
   --   = here refl

{-
allMeterDerivations :
  (ws : Words n) →
  ∃ λ (ds : Derivations ws) →
    (∀ {d : Derivation ws} → d ∈ ds)
allMeterDerivations {n} ws
  using mqs , sound-mqs , complete-mqs ← theQuantities ws
  using ws~mqs ← sound-mqs refl
  using n×syss , sound-syss , complete-syss ← allSynezeses′ (unwords ws)
  = ds , complete-ds
  where
  mkDerivation : (n′ , sys′) ∈ n×syss → Derivations ws
  mkDerivation {n′}{sys′} n×sys∈
    with hms , sound-hms , complete-hms ← allHexameters mqs
    with n ≟ n′
  ... | yes refl
    = ds
    where
    ds : Derivations ws
    ds = mapWith∈ hms λ hm∈ → -, -, fromBelow (ws~mqs ~∘~ sound-hms hm∈)
  ... | no  n≢
    using syn ← sound-syss n×sys∈
    using mqs′ ← synezize syn mqs
    with hms′ , sound-hms′ , complete-hms′ ← allHexameters mqs′
    = mapWith∈ hms′ λ {hm} hm∈ → -, -, [586] syn ws~mqs mqs≁ (sound-hms′ hm∈)
    where
    mqs≁ : NonDerivable mqs
    mqs≁ hm′ mqs~hm′ = {!complete-hms mqs~hm′!}

  ds : Derivations ws
  ds = concat $ mapWith∈ n×syss mkDerivation

  complete-ds : ∀ {d : Derivation ws} → d ∈ ds
  complete-ds = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
