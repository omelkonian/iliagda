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
open import Iliagda.Lexicon
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

instance
  Dec-ApparentException : ApparentException {n} ⁇¹
  Dec-ApparentException {x = sys} .dec =
    mapDec [1165] (λ where ([1165] p) → p) ¿ IsCompound sys ¿

module _ (sacc : SingleAccents sys) where

  1160#1161/2 : ¬ (InPenult (Any HasCircumflex) sys × InPenult (Any HasAcute) sys)
  1160#1161/2 (circPu , acuPu)
    = ¬InPenult singleAccentSy pu
    where
    pu : InPenult (Affinely⁺ HasAccent ∩¹ Any HasCircumflex ∩¹ Any HasAcute) sys
    pu = 3All⇒Penult (LastThree-map proj₂ sacc)
       $ InPenult-∩⁺ circPu acuPu

  1160#1163 : ¬ (InPenult (Any HasCircumflex) sys × InAntepenult (Any HasAccent) sys)
  1160#1163 (circPu , accApu)
    = 3Affinely⇒¬[Penult×Antepenult] (LastThree-map proj₁ sacc) (accPu , accApu)
    where
    accPu : InPenult (Any HasAccent) sys
    accPu = InPenult-map (L.Any.map circ⇒acc) circPu

  1161/2#1163 : ¬ (InPenult (Any HasAcute) sys × InAntepenult (Any HasAccent) sys)
  1161/2#1163 (acuPu , accApu)
    = 3Affinely⇒¬[Penult×Antepenult] (LastThree-map proj₁ sacc) (accPu , accApu)
    where
    accPu : InPenult (Any HasAccent) sys
    accPu = InPenult-map (L.Any.map acu⇒acc) acuPu

1161#1162 : ¬ (InPenult (_≡ single ─) mqs × InPenult (_≢ single ─) mqs)
1161#1162 (p , q)
  = ¬InPenult (λ (p , ¬p) → ¬p p)
  $ InPenult-∩⁺ p q

theF′? :
  (mqs : Quantities n) (sys : Syllables n) →
  SingleAccents sys →
    (∃ λ (f : Op₁ (Quantities n)) →
         (mqs ⊨ sys ~%′ f)
       × (∀ {f′} → mqs ⊨ sys ~%′ f′ → f′ ≡ f))
  ⊎ (∀ {f} → ¬ (mqs ⊨ sys ~%′ f))
theF′? _ [] _ = inj₂ λ ()
theF′? _ [ _ ] _ = inj₂ λ where
  ([1160] (there ()))
  ([1161] (there ()) _)
  ([1163] (there ()))
theF′? mqs sys@([ _ ⨾ _ ]) sacc
  with sacc , ∀sacc ← LastThree-∩⁻ sacc
  with ¿ InPenult (Any HasCircumflex) sys ¿
... | yes circPu
  = inj₁ $ -, [1160] circPu , λ where
  ([1160] _) → refl
  ([1161] _ acuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , acuPu)
  ([1162] _ _ acuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , acuPu)
  ([1163] (there (there ())))
... | no ¬circPu
  with ¿ InPenult (_≡ single ─) mqs × InPenult (Any HasAcute) sys ¿
... | yes (lPu , acuPu)
  = inj₁ $ -, [1161] lPu acuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] _ _) → refl
  ([1162] _ ≁lPu _) → ⊥-elim $ 1161#1162 (lPu , ≁lPu)
  ([1163] (there (there ())))
... | no ¬lacuPu
  with ¿ InUlt (_≡ single ·) mqs
     × InPenult (_≢ single ─) mqs
     × InPenult (Any HasAcute) sys ¿
... | yes (sult , ≁lPu , acuPu)
  = inj₁ $ -, [1162] sult ≁lPu acuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lPu acuPu) → ⊥-elim $ ¬lacuPu (lPu , acuPu)
  ([1162] _ _ _) → refl
  ([1163] (there (there ())))
... | no ¬≁lacuPu
  = inj₂ λ where
  ([1160] circPu) → ¬circPu circPu
  ([1161] lPu acuPu) → ¬lacuPu (lPu , acuPu)
  ([1162] sult ≁lPu acuPu) → ¬≁lacuPu (sult , ≁lPu , acuPu)
  ([1163] (there (there ())))
theF′? {n = n} mqs sys@(_ ∷ (_ ∷ (_ ∷ _))) sacc
  with sacc , ∀sacc ← LastThree-∩⁻ sacc
  with ¿ InPenult (Any HasCircumflex) sys ¿
... | yes circPu
  = inj₁ $ -, [1160] circPu , λ where
  ([1160] _) → refl
  ([1161] _ acuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , acuPu)
  ([1162] _ _ acuPu) → ⊥-elim $ 1160#1161/2 sacc (circPu , acuPu)
  ([1163] accApu) → ⊥-elim $ 1160#1163 sacc (circPu , accApu)
... | no ¬circPu
  with ¿ InPenult (_≡ single ─) mqs × InPenult (Any HasAcute) sys ¿
... | yes (lPu , acuPu)
  = inj₁ $ -, [1161] lPu acuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] _ _) → refl
  ([1162] _ ≁lPu _) → ⊥-elim $ 1161#1162 (lPu , ≁lPu)
  ([1163] accApu) → ⊥-elim $ 1161/2#1163 sacc (acuPu , accApu)
... | no ¬lacuPu
  with ¿ InUlt (_≡ single ·) mqs
     × InPenult (_≢ single ─) mqs
     × InPenult (Any HasAcute) sys ¿
... | yes (sult , ≁lPu , acuPu)
  = inj₁ $ -, [1162] sult ≁lPu acuPu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lPu acuPu) → ⊥-elim $ ¬lacuPu (lPu , acuPu)
  ([1162] _ _ _) → refl
  ([1163] accApu) → ⊥-elim $ 1161/2#1163 sacc (acuPu , accApu)
... | no ¬≁lacuPu
  with ¿ InAntepenult (Any HasAccent) sys ¿
... | yes accApu
  = inj₁ $ -, [1163] accApu , λ where
  ([1160] circPu) → ⊥-elim $ ¬circPu circPu
  ([1161] lPu acuPu) → ⊥-elim $ ¬lacuPu (lPu , acuPu)
  ([1162] sult ≁lPu acuPu) → ⊥-elim $ ¬≁lacuPu (sult , ≁lPu , acuPu)
  ([1163] accApu) → refl
... | no ¬accApu
  = inj₂ λ where
  ([1160] circPu) → ¬circPu circPu
  ([1161] lPu acuPu) → ¬lacuPu (lPu , acuPu)
  ([1162] sult ≁lPu acuPu) → ¬≁lacuPu (sult , ≁lPu , acuPu)
  ([1163] accApu) → ¬accApu accApu

theF :
  (mqs : Quantities n) (sys : Syllables n) →
  ∃ λ (f : Op₁ (Quantities n)) →
      (mqs ⊨ sys ~% f)
    × (∀ {f′} → mqs ⊨ sys ~% f′ → f′ ≡ f)
theF mqs sys
  -- do the exceptions hold?
  with ¿ EndsInFinalDiphthong sys ¿
... | yes fdi
  -- exception [1164], straight to Level 1
  = id , [1164] fdi , λ where
    ([1164] _) → refl
    ([574] _) → refl
    ([575] _) → refl
    (fromBelow ¬fdi _ _ _ _) → ⊥-elim $ ¬fdi fdi
    (noop _) → refl
... | no ¬fdi
  with ¿ ApparentException sys ¿
... | yes ae
  = id , [574] ae , λ where
    ([1164] _) → refl
    ([574] _) → refl
    ([575] _) → refl
    (fromBelow _ ¬ae _ _ _) → ⊥-elim $ ¬ae ae
    (noop _) → refl
... | no ¬ae
  with ¿ EndsInApostrophe sys ¿
... | yes apo
  -- exception [575], straight to Level 1
  = id , [575] apo , λ where
    ([1164] _) → refl
    ([574] _) → refl
    ([575] _) → refl
    (fromBelow _ _ ¬apo _ _) → ⊥-elim $ ¬apo apo
    (noop _) → refl
... | no ¬apo
  with ¿ SingleAccents sys ¿
... | no ¬sacc
  = id , noop (inj₁ ¬sacc) , λ where
    ([1164] _) → refl
    ([574] _) → refl
    ([575] _) → refl
    (fromBelow _ _ _ sacc _) → ⊥-elim $ ¬sacc sacc
    (noop _) → refl
... | yes sacc
  with theF′? mqs sys sacc
... | inj₂ sys≁
  = id , noop (inj₂ sys≁) , λ where
    ([1164] _) → refl
    ([574] _) → refl
    ([575] _) → refl
    (fromBelow _ _ _ _ sys~) → ⊥-elim $ sys≁ sys~
    (noop _) → refl
... | inj₁ (f , sys~ , unique-f)
  = f
  , fromBelow ¬fdi ¬ae ¬apo sacc sys~
  , λ where
    ([1164] fdi) → ⊥-elim $ ¬fdi fdi
    ([574] ae) → ⊥-elim $ ¬ae ae
    ([575] apo) → ⊥-elim $ ¬apo apo
    (noop (inj₁ ¬sacc)) → ⊥-elim $ ¬sacc sacc
    (noop (inj₂ sys≁)) → ⊥-elim $ sys≁ sys~
    (fromBelow _ _ _ _ sys~′) → unique-f sys~′

nonDerivable? : (sy : Syllable) → Dec (NonDerivable {B = Quantity} sy)
nonDerivable? sy with 𝟙-theQuantity? sy
... | inj₁ (q , sy~q , _) = no λ nd → nd q sy~q
... | inj₂ nd = yes nd

lex? : (sys : Syllables n) → Dec (LexHit sys)
lex? {n} sys = go (lexLookup (unsyllables sys)) refl
  where
  go : (m : Maybe Entry) → lexLookup (unsyllables sys) ≡ m → Dec (LexHit sys)
  go nothing eqL = no λ where
    (lexHit _ _ eqL′ _) → case trans (sym eqL) eqL′ of λ ()
  go (just e) eqL = go′ (locusIx (locusOf (e .mode)) n) refl
    where
    go′ : (mi : Maybe (Fin n)) → locusIx (locusOf (e .mode)) n ≡ mi → Dec (LexHit sys)
    go′ nothing eqI = no λ where
      (lexHit _ _ eqL′ eqI′) →
        case May.just-injective (trans (sym eqL) eqL′) of λ where
          refl → case trans (sym eqI) eqI′ of λ ()
    go′ (just i) eqI = yes (lexHit e i eqL eqI)

lexUnique : {sys : Syllables n} (h h′ : LexHit sys) →
  (V._[ h′ .ix ]≔ single (h′ .entry .qty)) ≡ (V._[ h .ix ]≔ single (h .entry .qty))
lexUnique (lexHit _ _ eqL eqI) (lexHit _ _ eqL′ eqI′)
  with refl ← May.just-injective (trans (sym eqL) eqL′)
  with refl ← May.just-injective (trans (sym eqI) eqI′)
  = refl

theL :
  (sys : Syllables n) →
  ∃ λ (lex : Op₁ (Quantities n)) →
      (sys ~L lex)
    × (∀ {lex′} → sys ~L lex′ → lex′ ≡ lex)
theL sys with lex? sys
... | yes h
  = -, lexHit h , λ where
    (lexHit h′) → lexUnique h h′
    (lexMiss ¬h) → ⊥-elim $ ¬h h
... | no ¬h
  = id , lexMiss ¬h , λ where
    (lexHit h′) → ⊥-elim $ ¬h h′
    (lexMiss _) → refl

𝟚-theQuantities₁ :
  (w : Word n) →
  ∃ λ (mqs : Quantities n) →
      (w ~ʷ mqs)
    × (∀ {mqs′} → w ~ʷ mqs′ → mqs′ ≡ mqs)
𝟚-theQuantities₁ w
  using sys ← unword w
  using mqs , mqs~ , unique-mqs ← 𝟙-theQuantities sys
  using f , f~ , unique-lex ← theL sys
  using g , g~ , unique-f ← theF (f mqs) sys
  = g (f mqs)
  , 𝟙-then-L-then-𝟚 mqs~ f~ g~
  , λ where
    (𝟙-then-L-then-𝟚 {g = g′} mqs~′ f~′ g~′) →
      let eqv = cong₂ id (unique-lex f~′) (unique-mqs mqs~′) in
      cong₂ id (unique-f (subst (λ ◆ → ◆ ⊨ sys ~% g′) eqv g~′)) eqv

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
