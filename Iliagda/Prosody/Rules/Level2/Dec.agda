{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level2.Dec where

open import Iliagda.Init
open import Prelude.Vectors

open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level1.Dec
open import Iliagda.Prosody.Rules.Level2

instance
  Dec-~₁ : _~_ {Syllable}{Quantity} ⁇²
  Dec-~₁ .dec = _ ~₁? _

acu⇒acc : HasAcute l → HasAccent l
acu⇒acc = inj₁
grv⇒acc : HasGrave l → HasAccent l
grv⇒acc = inj₂ ∘ inj₁
circ⇒acc : HasCircumflex l → HasAccent l
circ⇒acc = inj₂ ∘ inj₂

singleAccentSy : ¬ (Affinely⁺ HasAccent ∩¹ Any HasCircumflex ∩¹ Any HasAcute) sy
singleAccentSy = AffinelyP⇒¬Q×R circ⇒acc acu⇒acc ¬circ×acu

module _ (sacc : SingleAccents sys) where

  1160#1161/2 : ∀ {P} →
    ¬ ( InPenult (Any HasCircumflex) sys
      × InPenult (P ∩¹ Any HasAcute) sys
      )
  1160#1161/2 (circPu , lacuPu)
    using acuPu ← InPenult-map proj₂ lacuPu
    = ¬InPenult singleAccentSy pu
    where
    pu : InPenult (Affinely⁺ HasAccent ∩¹ Any HasCircumflex ∩¹ Any HasAcute) sys
    pu = 3All⇒Penult (LastThree-map proj₂ sacc)
       $ InPenult-∩⁺ circPu acuPu

  1160#1163 :
    ¬ ( InPenult (Any HasCircumflex) sys
      × InAntepenult (Any HasAccent) sys
      )
  1160#1163 (circPu , accApu)
    = 3Affinely⇒¬[Penult×Antepenult] (LastThree-map proj₁ sacc) (accPu , accApu)
    where
    accPu : InPenult (Any HasAccent) sys
    accPu = InPenult-map (L.Any.map circ⇒acc) circPu

  1161#1162 :
    ¬ ( InPenult ((_~ ─) ∩¹ Any HasAcute) sys
      × InPenult ((_≁ ─) ∩¹ Any HasAcute) sys
      )
  1161#1162 (p , q)
    using l  ← InPenult-map proj₁ p
    using ¬l ← InPenult-map proj₁ q
    = ¬InPenult (λ (p , ¬p) → ¬p p)
    $ InPenult-∩⁺ l ¬l

  1161/2#1163 : ∀ {P} →
    ¬ ( InPenult (P ∩¹ Any HasAcute) sys
      × InAntepenult (Any HasAccent) sys
      )
  1161/2#1163 (lacuPu , accApu)
    using acuPu ← InPenult-map proj₂ lacuPu
    = 3Affinely⇒¬[Penult×Antepenult] (LastThree-map proj₁ sacc) (accPu , accApu)
    where
    accPu : InPenult (Any HasAccent) sys
    accPu = InPenult-map (L.Any.map acu⇒acc) acuPu

theF′? :
  (sys : Syllables n) →
  SingleAccents sys →
    (∃ λ (f : Op₁ (Quantities n)) →
         (sys ~%′ f)
       × (∀ {f′} → sys ~%′ f′ → f′ ≡ f))
  ⊎ (∀ {f} → ¬ sys ~%′ f)
theF′? [] _ = inj₂ λ ()
theF′? [ _ ] _ = inj₂ λ where
  ([1160] (there ()))
  ([1161] (there ()))
  ([1163] (there ()))
theF′? sys@([ _ ⨾ _ ]) sacc
  with sacc , ∀sacc ← LastThree-∩⁻ sacc
  with ¿ InPenult (Any HasCircumflex) sys ¿
... | yes circPu
  = inj₁ $ -, [1160] circPu , λ where
  ([1160] _) → refl
  ([1161] lacuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , lacuPu)
  ([1162] _ lacuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , lacuPu)
  ([1163] (there (there ())))
... | no ¬circPu
  with ¿ InPenult ((_~ ─) ∩¹ Any HasAcute) sys ¿
... | yes lacuPu
  = inj₁ $ -, [1161] lacuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] _) → refl
  ([1162] _ ≁lacuPu) → ⊥-elim $ 1161#1162 sacc (lacuPu , ≁lacuPu)
  ([1163] (there (there ())))
... | no ¬lacuPu
  with ¿ InUlt (_~ ·) sys × InPenult ((_≁ ─) ∩¹ Any HasAcute) sys ¿
... | yes (sult , ≁lacuPu)
  = inj₁ $ -, [1162] sult ≁lacuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lacuPu) → ⊥-elim $ ¬lacuPu lacuPu
  ([1162] _ _) → refl
  ([1163] (there (there ())))
... | no ¬≁lacuPu
  = inj₂ λ where
  ([1160] circPu) → ¬circPu circPu
  ([1161] lacuPu) → ¬lacuPu lacuPu
  ([1162] sult ≁lacuPu) → ¬≁lacuPu (sult , ≁lacuPu)
  ([1163] (there (there ())))
theF′? {n = n} sys@(_ ∷ (_ ∷ (_ ∷ _))) sacc
  with sacc , ∀sacc ← LastThree-∩⁻ sacc
  with ¿ InPenult (Any HasCircumflex) sys ¿
... | yes circPu
  = inj₁ $ -, [1160] circPu , λ where
  ([1160] _) → refl
  ([1161] lacuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , lacuPu)
  ([1162] _ lacuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , lacuPu)
  ([1163] accApu) → ⊥-elim $ 1160#1163 sacc (circPu , accApu)
... | no ¬circPu
  with ¿ InPenult ((_~ ─) ∩¹ Any HasAcute) sys ¿
... | yes lacuPu
  = inj₁ $ -, [1161] lacuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] _) → refl
  ([1162] _ ≁lacuPu) → ⊥-elim $ 1161#1162 sacc (lacuPu , ≁lacuPu)
  ([1163] accApu) → ⊥-elim $ 1161/2#1163 sacc (lacuPu , accApu)
... | no ¬lacuPu
  with ¿ InUlt (_~ ·) sys × InPenult ((_≁ ─) ∩¹ Any HasAcute) sys ¿
... | yes (sult , ≁lacuPu)
  = inj₁ $ -, [1162] sult ≁lacuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lacuPu) → ⊥-elim $ ¬lacuPu lacuPu
  ([1162] _ _) → refl
  ([1163] accApu) → ⊥-elim $ 1161/2#1163 sacc (≁lacuPu , accApu)
... | no ¬≁lacuPu
  with ¿ InAntepenult (Any HasAccent) sys ¿
... | yes accApu
  = inj₁ $ -, [1163] accApu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lacuPu) → ⊥-elim $ ¬lacuPu lacuPu
  ([1162] sult ≁lacuPu) → ⊥-elim $ ¬≁lacuPu (sult , ≁lacuPu)
  ([1163] accApu) → refl
... | no ¬accApu
  = inj₂ λ where
  ([1160] circPu) → ¬circPu circPu
  ([1161] lacuPu) → ¬lacuPu lacuPu
  ([1162] sult ≁lacuPu) → ¬≁lacuPu (sult , ≁lacuPu)
  ([1163] accApu) → ¬accApu accApu

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
-- -}
-- -}
