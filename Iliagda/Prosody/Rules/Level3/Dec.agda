{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level3.Dec where

open import Relation.Nullary.Decidable using (_×-dec_; _⊎-dec_)

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level1.Dec
open import Iliagda.Prosody.Rules.Level3

-- ** StartsWith predicates

StartsWithDoubleConsonant? : (ls : Letters) → Dec (StartsWithDoubleConsonant ls)
StartsWithDoubleConsonant? []       = no λ ()
StartsWithDoubleConsonant? (l ∷ ls) =
  mapDec doubleConsonant (λ where (doubleConsonant dc) → dc) ¿ DoubleConsonant l ¿

StartsWithTwoConsonants? : (ls : Letters) → Dec (StartsWithTwoConsonants ls)
StartsWithTwoConsonants? []            = no λ ()
StartsWithTwoConsonants? (_ ∷ [])      = no λ ()
StartsWithTwoConsonants? (l ∷ l′ ∷ ls)
  with ¿ Consonant l ¿ | ¿ Consonant l′ ¿
... | yes cl | yes cl′ = yes (twoConsonants cl cl′)
... | no ¬cl | _       = no λ where (twoConsonants cl _)  → ¬cl  cl
... | _      | no ¬cl′ = no λ where (twoConsonants _  cl′) → ¬cl′ cl′

StartsWithVowel? : (ls : Letters) → Dec (StartsWithVowel ls)
StartsWithVowel? []       = no λ ()
StartsWithVowel? (l ∷ ls) =
  mapDec vowel (λ where (vowel v) → v) ¿ Vowel l ¿

MuteThenLiquid? : (ls : Letters) → Dec (MuteThenLiquid ls)
MuteThenLiquid? []            = no λ ()
MuteThenLiquid? (_ ∷ [])      = no λ ()
MuteThenLiquid? (l ∷ l′ ∷ ls)
  with ¿ Mute l ¿ | ¿ Liquid l′ ⊎ Nasal l′ ¿
... | yes ml | yes ln = yes (muteLiquid ml ln)
... | no ¬ml | _      = no λ where (muteLiquid ml _)  → ¬ml ml
... | _      | no ¬ln = no λ where (muteLiquid _  ln) → ¬ln ln

private variable
  Q : Letters → Type

-- ** LastAny decidability

dec-LastAny : (v∈ : Any Vowel ls) → Dec (LastAny v∈)
dec-LastAny (here {xs = []}    _)  = yes refl
dec-LastAny (here {xs = _ ∷ _} _)  = no λ ()
dec-LastAny (there v∈)             = dec-LastAny v∈

-- ** FollowedBy / FollowedByInner existentials (parameterised by context)

module _ (⋯ : Flat Quantity × Context) (let fq , next = ⋯) where
  open QuantityRules ⋯

  -- ∃ vowel position s.t. FollowedBy Q holds
  ∃-vowel-followedBy :
    (Q? : ∀ ls → Dec (Q ls)) →
    (ls : Letters) →
    Dec (∃ λ (v∈ : Any Vowel ls) → FollowedBy Q v∈)
  ∃-vowel-followedBy Q? [] = no λ ()
  ∃-vowel-followedBy Q? (l ∷ ls)
    with ¿ Vowel l ¿
  ... | yes vl
    with Q? (ls ++ toLetters next)
  ... | yes q  = yes (here vl , q)
  ... | no  ¬q
    with ∃-vowel-followedBy Q? ls
  ... | yes (v∈ , q) = yes (there v∈ , q)
  ... | no  ¬∃       = no λ where (here _ , q)   → ¬q q ; (there v∈ , q) → ¬∃ (v∈ , q)
  ∃-vowel-followedBy Q? (l ∷ ls) | no ¬vl
    with ∃-vowel-followedBy Q? ls
  ... | yes (v∈ , q) = yes (there v∈ , q)
  ... | no  ¬∃       = no λ where (here vl , _) → ¬vl vl ; (there v∈ , q) → ¬∃ (v∈ , q)

  -- ∃ last vowel position s.t. FollowedBy Q holds
  -- (LastAny means the vowel is the final letter of the syllable)
  ∃-lastVowel-followedBy :
    (Q? : ∀ ls → Dec (Q ls)) →
    (ls : Letters) →
    Dec (∃ λ (v∈ : Any Vowel ls) → LastAny v∈ × FollowedBy Q v∈)
  ∃-lastVowel-followedBy Q? [] = no λ ()
  ∃-lastVowel-followedBy Q? (l ∷ [])
    with ¿ Vowel l ¿ | Q? ([] ++ toLetters next)
  ... | yes vl | yes q = yes (here vl , refl , q)
  ... | yes _  | no ¬q = no λ where (here _ , refl , q) → ¬q q ; (there () , _)
  ... | no ¬vl | _     = no λ where (here vl , _) → ¬vl vl ; (there () , _)
  ∃-lastVowel-followedBy Q? (l ∷ ls@(_ ∷ _))
    with ∃-lastVowel-followedBy Q? ls
  ... | yes (v∈ , la , q) = yes (there v∈ , la , q)
  ... | no  ¬∃            = no λ where (here {xs = _ ∷ _} _ , () , _) ; (there v∈ , la , q) → ¬∃ (v∈ , la , q)

  ∃-vowel-followedByOuter :
    (Q? : ∀ ls → Dec (Q ls)) →
    (ls : Letters) →
    Dec (∃ λ (v∈ : Any Vowel ls) → FollowedByOuter Q v∈)
  ∃-vowel-followedByOuter Q? [] = no λ ()
  ∃-vowel-followedByOuter Q? (l ∷ ls)
    with ¿ Vowel l ¿
  ... | yes vl
    with ls ≟ [] ×-dec Q? (toLetters next)
  ... | yes (refl , q) = yes (here vl , q)
  ... | no ¬q
    with ∃-vowel-followedByOuter Q? ls
  ... | yes (v∈ , q) = yes (there v∈ , q)
  ... | no  ¬∃       = no λ where
    (here {xs = []} _ , q) → ¬q (refl , q); (there v∈ , q) → ¬∃ (v∈ , q)
  ∃-vowel-followedByOuter Q? (l ∷ ls) | no ¬vl
    with ∃-vowel-followedByOuter Q? ls
  ... | yes (v∈ , q) = yes (there v∈ , q)
  ... | no  ¬∃       = no λ where
    (here vl , _) → ¬vl vl ; (there v∈ , q) → ¬∃ (v∈ , q)

-- ∃ vowel position s.t. FollowedByInner Q holds (no context needed)
∃-vowel-followedByInner :
  (Q? : ∀ ls → Dec (Q ls)) →
  (ls : Letters) →
  Dec (∃ λ (v∈ : Any Vowel ls) → FollowedByInner Q v∈)
∃-vowel-followedByInner Q? [] = no λ ()
∃-vowel-followedByInner Q? (l ∷ ls)
  with ¿ Vowel l ¿
... | yes vl
  with Q? ls
... | yes q  = yes (here vl , q)
... | no  ¬q
  with ∃-vowel-followedByInner Q? ls
... | yes (v∈ , q) = yes (there v∈ , q)
... | no  ¬∃       = no λ where (here _ , q)   → ¬q q ; (there v∈ , q) → ¬∃ (v∈ , q)
∃-vowel-followedByInner Q? (l ∷ ls) | no ¬vl
  with ∃-vowel-followedByInner Q? ls
... | yes (v∈ , q) = yes (there v∈ , q)
... | no  ¬∃       = no λ where (here vl , _) → ¬vl vl ; (there v∈ , q) → ¬∃ (v∈ , q)

-- ** ~?′/~? decisions (parameterised by context)

module QuantityDec fq next (let ⋯ = fq , next) where
  open QuantityRules ⋯

  private
    doubleOrTwo? : (ls : Letters) → Dec ((StartsWithDoubleConsonant ∪¹ StartsWithTwoConsonants) ls)
    doubleOrTwo? ls with StartsWithDoubleConsonant? ls | StartsWithTwoConsonants? ls
    ... | yes dc  | _      = yes (inj₁ dc)
    ... | no  _   | yes tc = yes (inj₂ tc)
    ... | no  ¬dc | no ¬tc = no λ where (inj₁ dc) → ¬dc dc ; (inj₂ tc) → ¬tc tc

  -- sy ~∗ ─
  dec-~∗─ : (sy : Syllable) → Dec (sy ~∗ ─)
  dec-~∗─ sy
    with ∃-vowel-followedBy ⋯ doubleOrTwo? (toList sy)
  ... | yes (v∈ , fb) = yes ([522] v∈ fb)
  ... | no  ¬522

    with ⟫ fq

  ... | ⟫ all = no λ where
    ([522] v∈ fb) → ¬522 (v∈ , fb)
    ([1173] _ () _ _)
    ([524] _ () _)

  ... | ⟫ none
    = no λ where
    ([522] v∈ fb) → ¬522 (v∈ , fb)

  ... | ⟫ single ─
    = QED
    where
    QED : _
    QED
      with ∃-lastVowel-followedBy ⋯ StartsWithVowel? (toList sy)
    ... | yes (v∈ , lv∈ , sv)
      = yes $ [1173] v∈ refl lv∈ sv
    ... | no ¬1173
      = no λ where
      ([522] v∈ fb) → ¬522 (v∈ , fb)
      ([1173] v∈ refl lv∈ sv) → ¬1173 (v∈ , lv∈ , sv)

  ... | ⟫ single ·
    = QED
    where
    QED : _
    QED
      with ∃-vowel-followedByInner MuteThenLiquid? (toList sy)
     ⊎-dec ∃-vowel-followedByOuter ⋯ MuteThenLiquid? (toList sy)
    ... | yes (inj₁ (v∈ , ml))
      = yes $ [524] v∈ refl (inj₁ ml)
    ... | yes (inj₂ (v∈ , ml))
      = yes $ [524] v∈ refl (inj₂ ml)
    ... | no ¬524
      = no λ where
      ([522] v∈ fb) → ¬522 (v∈ , fb)
      ([524] v∈ _ (inj₁ ml)) → ¬524 $ inj₁ (v∈ , ml)
      ([524] v∈ _ (inj₂ ml)) → ¬524 $ inj₂ (v∈ , ml)

  -- sy ~∗ ·
  dec-~∗· : (sy : Syllable) → Dec (sy ~∗ ·)
  dec-~∗· sy
    with ⟫ fq
  dec-~∗· sy | ⟫ single ─
    with ∃-lastVowel-followedBy ⋯ StartsWithVowel? (toList sy)
  ... | yes (v∈ , la , sv) = yes ([1173] v∈ refl la sv)
  ... | no  ¬1173 = no λ where
    ([1173] v∈ refl la sv) → ¬1173 (v∈ , la , sv)
  dec-~∗· sy | ⟫ single ·
    with ∃-vowel-followedByInner MuteThenLiquid? (toList sy)
   ⊎-dec ∃-vowel-followedByOuter ⋯ MuteThenLiquid? (toList sy)
  ... | yes (inj₁ (v∈ , ml)) = yes $ [524] v∈ refl (inj₁ ml)
  ... | yes (inj₂ (v∈ , ml)) = yes $ [524] v∈ refl (inj₂ ml)
  ... | no  ¬ml       = no λ where
    ([524] v∈ refl (inj₁ ml)) → ¬ml $ inj₁ (v∈ , ml)
    ([524] v∈ refl (inj₂ ml)) → ¬ml $ inj₂ (v∈ , ml)
  dec-~∗· sy | ⟫ none
    = no λ where
    ([1173] _ () _ _)
  dec-~∗· sy | ⟫ all
    = no λ where
    ([1173] _ () _ _)

  -- sy ~? mq  (unique mq for each (sy, ctx))
  𝟛-theQuantity :
    (sy : Syllable) →
    ∃ λ mq → (sy ~? mq)
           × (∀ {mq′} → sy ~? mq′ → mq′ ≡ mq)
  𝟛-theQuantity sy
    with dec-~∗─ sy | dec-~∗· sy
  ... | yes ~─ | yes ~·
    = all
    , ambivalent ~─ ~·
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ─) ~─)
              (ambivalent _ _)           → refl
              (certain {q = ─} _ ¬~·)    → ⊥-elim (¬~· ~·)
              (certain {q = ·} _ ¬~─)    → ⊥-elim (¬~─ ~─)
  ... | yes ~─ | no  ¬~·
    = single ─
    , certain ~─ ¬~·
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ─) ~─)
              (ambivalent _ ~·)          → ⊥-elim (¬~· ~·)
              (certain {q = ─} _ _)      → refl
              (certain {q = ·} _ ¬~─)    → ⊥-elim (¬~─ ~─)
  ... | no  ¬~─ | yes ~·
    = single ·
    , certain ~· ¬~─
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ·) ~·)
              (ambivalent ~─ _)          → ⊥-elim (¬~─ ~─)
              (certain {q = ─} _ ¬~·)    → ⊥-elim (¬~· ~·)
              (certain {q = ·} _ _)      → refl
  ... | no  ¬~─ | no  ¬~·
    = none
    , ambiguous (λ where ─ ~─ → ¬~─ ~─ ; · ~· → ¬~· ~·)
    , λ where (ambiguous  _)         → refl
              (ambivalent ~─ _)      → ⊥-elim (¬~─ ~─)
              (certain {q = ─} ~─ _) → ⊥-elim (¬~─ ~─)
              (certain {q = ·} ~· _) → ⊥-elim (¬~· ~·)

-- ** Lift to sequences and connect to _~³_

𝟛-theQuantities :
  (ws : Words n) (mqs₂ : Quantities n) →
  ∃ λ (mqs₃ : Quantities n) →
      ((ws , mqs₂) ~³ mqs₃)
    × (∀ {mqs₃′} → (ws , mqs₂) ~³ mqs₃′ → mqs₃′ ≡ mqs₃)
𝟛-theQuantities {n = n} ws mqs₂ = go (inContext ws mqs₂)
  where
  go : ∀ {m} →
    (syctxs : Vec (Syllable × Flat Quantity × Context) m) →
    ∃ λ (mqs₃ : Quantities m) →
        VPointwise _~_ syctxs mqs₃
      × (∀ {mqs₃′} → VPointwise _~_ syctxs mqs₃′ → mqs₃′ ≡ mqs₃)
  go [] = [] , [] , λ where [] → refl
  go ((sy , fq , ctx) ∷ syctxs)
    with QuantityDec.𝟛-theQuantity fq ctx sy | go syctxs
  ... | mq , mq~ , mq-uniq | mqs , mqs~ , mqs-uniq
    = mq ∷ mqs
    , mq~ ∷ mqs~
    , λ where (mq~′ ∷ mqs~′) → cong₂ _∷_ (mq-uniq mq~′) (mqs-uniq mqs~′)
