-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Iliagda.Prosody.Rules.Level2.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level1.Dec
open import Iliagda.Prosody.Rules.Level2

instance
  Dec-VLast : ∀ {P : A → Type} → ⦃ P ⁇¹ ⦄ → VLast P {n = n} ⁇¹
  Dec-VLast {P = P} {x = [ x ]} .dec
    = mapDec here (λ where (here p) → p) ¿ P x ¿
  Dec-VLast {P = P} {x = x ∷ xs@(_ ∷ _)} .dec
    = mapDec there (λ where (there p) → p) ¿ VLast P xs ¿

theUlt :
  (sys : Vec Syllable (1 + n)) →
  (∃ λ (ult : Syllable) →
      sys ∶⋯ ult
    × (∀ {ult′} → sys ∶⋯ ult′ → ult′ ≡ ult))
theUlt [ sy ] = sy , here refl , λ where (here refl) → refl
theUlt (_ ∷ sys@(_ ∷ _)) =
  let ult , ult∈ , unique-ult = theUlt sys
   in ult , there ult∈ , λ where (there ult∈′) → unique-ult ult∈′

thePenult :
  (sys : Vec Syllable (2 + n)) → let sys-1 = V-init sys in
  (∃ λ (penult : Syllable) →
      sys-1 ∶⋯ penult
    × (∀ {penult′} → sys-1 ∶⋯ penult′ → penult′ ≡ penult))
thePenult _ = theUlt _

theAntepenult :
  (sys : Vec Syllable (3 + n)) → let sys-2 = V-init (V-init sys) in
  (∃ λ (antepenult : Syllable) →
      sys-2 ∶⋯ antepenult
    × (∀ {antepenult′} → sys-2 ∶⋯ antepenult′ → antepenult′ ≡ antepenult))
theAntepenult _ = theUlt _

instance
  Dec-EndsFDi : EndsInFinalDiphthong {n = n} ⁇¹
  Dec-EndsFDi {n = 0} .dec = no λ ()
  Dec-EndsFDi {n = suc n} {x = sys} .dec
    using ult , ult∈ , unique-ult ← theUlt sys
    with ¿ Any× FinalDiphthong ult ¿
  ... | yes fdi = yes (finalDiphthong ult∈ fdi)
  ... | no ¬fdi = no λ where
    (finalDiphthong ult∈ fdi) →
      ¬fdi (subst (Any× _) (unique-ult ult∈) fdi)

  Dec-EndsApo : EndsInApostrophe {n = n} ⁇¹
  Dec-EndsApo {n = 0} .dec = no λ ()
  Dec-EndsApo {n = suc n} {x = sys} .dec
    using ult , ult∈ , unique-ult ← theUlt sys
    with ¿ Last⁺ (_≡ ᾽) ult ¿
  ... | yes apo = yes (elision ult∈ apo)
  ... | no ¬apo = no λ where
    (elision ult∈ apo) →
      ¬apo (subst (Last⁺ _) (unique-ult ult∈) apo)

open import Algebra using (Op₁)

circ⇒acc : HasCircumflex l → HasAccent l
circ⇒acc = inj₂ ∘ inj₂

private
  pattern 𝟘 = here refl
  pattern 𝟙 = there 𝟘
  pattern 𝟚 = there 𝟙
  pattern 𝟛 = there 𝟚
  pattern 𝟜 = there 𝟛
  pattern 𝟝 = there 𝟜

¬circ×acu : HasCircumflex l → HasAcute l → ⊥
¬circ×acu = λ where
  𝟘 → auto
  𝟙 → auto
  𝟚 → auto
  𝟛 → auto
  𝟜 → auto
  𝟝 → auto

_~?_ : ∀ (sy : Syllable) (q : Quantity) → Dec (sy ~ q)
sy ~? q
  with 𝟙-theQuantity? sy
... | inj₂ sy≁
  = no λ sy~q → sy≁ _ sy~q
... | inj₁ (q′ , sy~q′ , unique-q′)
  with q ≟ q′
... | yes refl = yes sy~q′
... | no q≢    = no λ sy~q → q≢ (unique-q′ sy~q)

open L.Any using (index; lookup)

instance
  Dec-Single : ∀ {P : A → Type} → ⦃ P ⁇¹ ⦄ → Single P ⁇¹
  Dec-Single {P = P} {x = xs} .dec
    with xs
  ... | [] = yes λ ()
  ... | x ∷ xs
    with ¿ P x ¿
  ... | yes px
    = QED
    where
    QED : _
    QED
      with ¿ Any P xs ¿
    ... | no ∄p = yes λ where
      (there ∃p) _ → ⊥-elim $ ∄p ∃p
      _ (there ∃p) → ⊥-elim $ ∄p ∃p
      (here _) (here _) → refl
    ... | yes ∃p = no λ sp → contradict $ sp (here px) (there ∃p)
  ... | no ¬px
    with ¿ Single P xs ¿
  ... | yes sp = yes λ where
      (here px) _ → ⊥-elim $ ¬px px
      _ (here px) → ⊥-elim $ ¬px px
      (there ∃p) (there ∃p′) → cong fsuc $ sp ∃p ∃p′
  ... | no ¬sp = no λ sp →
    ¬sp λ ∃p ∃p′ → Fi.suc-injective $ sp (there ∃p) (there ∃p′)

∈-lookup′ : ∀ {P : A → Type} {xs : List A} (i : Any P xs) → lookup i ∈ xs
∈-lookup′ = λ where
  (here px) → here refl
  (there i) → there (∈-lookup′ i)

lookup⇒ : ∀ {P Q : A → Type} {xs : List A} (x∈ : Any P xs) → let x = L.Any.lookup x∈ in
  Q x → Any Q xs
lookup⇒ x∈ Qx = L.Any.map (λ where refl → Qx) $ ∈-lookup′ x∈


import Data.Vec.Relation.Unary.Any.Properties as VAny

Any-ult⇒lastThree : ∀ {P : Letter → Type} →
  let ult , _ = theUlt sys in
  Any P ult
  ────────────────────────
  Any P (lastThreeSys sys)
Any-ult⇒lastThree {sys = sys} {P = P} p
  using ult , ult∈ , unique-ult ← theUlt sys
  -- = QED
  = L.Any.concatMap⁺ toList {xs = lastThree sys}
  $ QED
  where
  QED : _
  QED
    with x ∷ sys′ ← V.reverse sys
    = {!p!}
    -- where
    -- pz : Any P z
    -- pz = subst (Any P) (sym $ unique-ult {z} {!!}) p

Any-antepenult⇒lastThree : ∀ {P : Letter → Type} →
  let antepenult , _ = theAntepenult sys in
  Any P antepenult
  ────────────────────────
  Any P (lastThreeSys sys)
Any-antepenult⇒lastThree {sys = sys} {P = P} p
  using antepenult , antepenult∈ , unique-antepenult ← theAntepenult sys
  = L.Any.concatMap⁺ toList {xs = lastThree sys}
  $ QED
  where
  QED : _
  QED
    with sys˘ ← V.reverse sys
    -- with ult ∷ penult ∷ antepenult′ ∷ _ ← V.reverse sys
    with sys˘@(ult ∷ penult ∷ antepenult′ ∷ _) ← sys˘
    -- with ult ∷ penult ∷ antepenult′ ∷ _ ← V.toList sys˘
    -- with _ ∷ _ ∷ _ ∷ [] ← lastThree sys
    = {!pz!}
    -- where
    -- pz : Any P z
    -- pz = subst (Any P) (sym $ unique-antepenult {z} {!!}) p

{-
theF′? :
  (sys : Syllables n) →
  SingleAccents sys →
    (∃ λ (f : Op₁ (Quantities n)) →
         (sys ~%′ f)
       × (∀ {f′} → sys ~%′ f′ → f′ ≡ f))
  ⊎ (∀ {f} → ¬ sys ~%′ f)
theF′? [] _ = inj₂ λ ()
theF′? (_ ∷ []) _ = inj₂ λ ()
theF′? sys@(_ ∷ (_ ∷ [])) sacc
  = {!!}
theF′? {n = n} sys@(_ ∷ (_ ∷ (_ ∷ _))) sacc
  using ult , ult∈ , unique-ult ← theUlt sys
  using penult , penult∈ , unique-penult ← thePenult sys
  using antepenult , antepenult∈ , unique-antepenult ← theAntepenult sys

  with ¿ Any HasAccent penult ¿
... | yes accPenult
  = QED
  where
  ¬accAntepenult : ¬ Any HasAccent antepenult
  ¬accAntepenult accAntepenult
    = i≢ $ sacc x∈ y∈
    where
    x∈ : Any HasAccent (lastThreeSys sys)
    x∈ = Any-antipenult⇒lastThree accAntepenult
    -- accAntepenult

    y∈ : Any HasAccent (lastThreeSys sys)
    y∈ = {!!}
    -- accPenult

    i≢ : index x∈ ≢ index y∈
    i≢ = {!!}

  QED : (∃ λ (f : Op₁ (Quantities n)) →
           (sys ~%′ f)
           × (∀ {f′} → sys ~%′ f′ → f′ ≡ f))
      ⊎ (∀ {f} → ¬ sys ~%′ f)
  QED
    using l ← L.Any.lookup accPenult
    with ¿ HasCircumflex l ¿
  ... | yes circPenult
    = inj₁
    $ (_≔ₙ ·) , [1160] (ult∈ , penult∈) (lookup⇒ accPenult circPenult) , λ where
    ([1160] _ _) → refl
    ([1161] _ _ acuPenult) → ⊥-elim $ ¬circ×acu circPenult {!unique-ult , L.Any.lookup-result acuPenult!}
    ([1162] _ _ _ acuPenult) → ⊥-elim $ {!!}
    ([1163] _ accAntepenult) → ⊥-elim $ {!!}
  ... | no ¬circPenult
    with ¿ HasAcute l ¿
  ... | no ¬acuPenult
    = inj₂ $ λ where
    ([1160] _ circPenult) → ¬circPenult {!circPenult!} -- circPenult
    ([1161] _ _ acuPenult) → ¬acuPenult {!!} -- acuPenult
    ([1162] _ _ _ acuPenult) → ¬acuPenult {!!} -- acuPenult
    ([1163] _ accAntepenult) → {!!} -- ¬accAntepenult accAntepenult
  ... | yes acuPenult
    with penult ~? ─
  ... | yes longPenult
    = inj₁
    $ (_≔ₙ ─)
    , [1161] (ult∈ , penult∈) longPenult (lookup⇒ accPenult acuPenult)
    , λ where
      ([1160] _ circPenult) → ⊥-elim $ ¬circ×acu {!!}{-circPenult-} acuPenult
      ([1161] _ _ _) → refl
      ([1162] _ ¬longPenult _ _) → ⊥-elim $ {!!} -- ¬longPenult longPenult
      ([1163] _ accAntepenult) → ⊥-elim $ {!!} -- ¬accAntepenult accAntepenult
  ... | no ¬longPenult
    with ult ~? ·
  ... | yes shortUlt
    = inj₁
    $ (_≔ₙ₋₁ ·)
    , [1162] (ult∈ , penult∈) ¬longPenult shortUlt (lookup⇒ accPenult acuPenult)
    , λ where
      ([1160] _ circPenult) → ⊥-elim $ {!!} -- ¬circ×acu circPenult acuPenult
      ([1161] _ longPenult _) → ⊥-elim $ {!!} -- ¬longPenult longPenult
      ([1162] _ _ _ _) → refl
      ([1163] _ accAntepenult) → ⊥-elim $ {!!} -- ¬accAntepenult accAntepenult
  ... | no ¬shortUlt
    = inj₂ λ where
    ([1160] _ circPenult) → {!!} -- ¬circ×acu circPenult acuPenult
    ([1161] _ longPenult _) → ¬longPenult {!!} -- longPenult
    ([1162] _ _ shortUlt _) → ¬shortUlt {!!} -- shortUlt
    ([1163] _ accAntepenult) → {!!} -- ¬accAntepenult accAntepenult
... | no ¬accPenult
  with ¿ Any HasAccent antepenult ¿
... | no ¬accAntepenult
  = inj₂ λ where
    ([1160] _ circPenult) → ¬accPenult {!!} -- (circ⇒acc circPenult)
    ([1161] _ _ accPenult) → ¬accPenult {!!} -- accPenult
    ([1162] _ _ _ accPenult) → ¬accPenult {!!} -- accPenult
    ([1163] _ accAntepenult) → ¬accAntepenult {!!} -- accAntepenult
... | yes accAntepenult
  = inj₁
  $ (_≔ₙ ─) , [1163] (ult∈ , penult∈ , antepenult∈) accAntepenult , λ where
    ([1160] _ circPenult) → ⊥-elim $ {!!}
    ([1161] _ _ accPenult) → ⊥-elim $ {!!}
    ([1162] _ _ _ accPenult) → ⊥-elim $ {!!}
    ([1163] _ _ ) → refl

{-
theF :
  (sys : Syllables n) →
  ∃ λ (f : Op₁ (Quantities n)) →
      (sys ~% f)
    × (∀ {f′} → sys ~% f′ → f′ ≡ f)
theF sys
  -- do the exceptions hold?
  with ¿ EndsInFinalDiphthong sys ¿
... | yes fdi
  -- exception [1164], straight to Level 1
  = id , [1164] fdi , λ where
    ([1164] _) → refl
    ([575] _) → refl
    (fromBelow ¬fdi _ _ _) → ⊥-elim $ ¬fdi fdi
    (noop _) → refl
... | no ¬fdi
  with ¿ EndsInApostrophe sys ¿
... | yes apo
  -- exception [575], straight to Level 1
  = id , [575] apo , λ where
    ([1164] _) → refl
    ([575] _) → refl
    (fromBelow _ ¬apo _ _) → ⊥-elim $ ¬apo apo
    (noop _) → refl
... | no ¬apo
  with ¿ SingleAccents sys ¿
... | no ¬sacc
  = id , noop (inj₁ ¬sacc) , λ where
    ([1164] _) → refl
    ([575] _) → refl
    (fromBelow _ _ sacc _) → ⊥-elim $ ¬sacc sacc
    (noop _) → refl
... | yes sacc
  with theF′? sys sacc
... | inj₂ sys≁
  = id , noop (inj₂ sys≁) , λ where
    ([1164] _) → refl
    ([575] _) → refl
    (fromBelow _ _ _ sys~) → ⊥-elim $ sys≁ sys~
    (noop _) → refl
... | inj₁ (f , sys~ , unique-f)
  = f
  , fromBelow ¬fdi ¬apo sacc sys~
  , λ where
    ([1164] fdi) → ⊥-elim $ ¬fdi fdi
    ([575] apo) → ⊥-elim $ ¬apo apo
    (noop (inj₁ ¬sacc)) → ⊥-elim $ ¬sacc sacc
    (noop (inj₂ sys≁)) → ⊥-elim $ sys≁ sys~
    (fromBelow _ _ _ sys~′) → unique-f sys~′

𝟚-theQuantities₁ :
  (w : Word n) →
  ∃ λ (mqs : Quantities n) →
      (w ~ʷ mqs)
    × (∀ {mqs′} → w ~ʷ mqs′ → mqs′ ≡ mqs)
𝟚-theQuantities₁ w
  using sys ← unword w
  using mqs , mqs~ , unique-mqs ← 𝟙-theQuantities sys
  using f , f~ , unique-f ← theF sys
  = f mqs
  , 𝟙-then-𝟚 mqs~ f~
  , λ where (𝟙-then-𝟚 mqs~ f~) → cong₂ id (unique-f f~) (unique-mqs mqs~)

𝟚-theQuantities :
  (ws : Words n) →
  ∃ λ (mqs : Quantities n) →
      (ws ~² mqs)
    × (∀ {mqs′} → ws ~² mqs′ → mqs′ ≡ mqs)
𝟚-theQuantities [] = [] , [] , λ where [] → refl
𝟚-theQuantities (w ∷ ws)
  = let
      mqs  , w~mqs  , complete-mqs  = 𝟚-theQuantities₁ w
      mqs′ , ws~mqs′ , complete-mqs′ = 𝟚-theQuantities ws
    in
      (mqs V.++ mqs′)
      , (w~mqs ∷ ws~mqs′)
      , λ where (_∷_ ⦃ refl ⦄ w~mqs ws~mqs′) →
                     cong₂ V._++_ (complete-mqs  w~mqs) (complete-mqs′ ws~mqs′)

-- -}
-- -}
-- -}
-- -}
-- -}
