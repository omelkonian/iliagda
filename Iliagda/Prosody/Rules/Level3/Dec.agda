{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level3.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level1.Dec
open import Iliagda.Prosody.Rules.Level3

-- ** ~ˢʸⁿ decidability

_~ˢʸⁿ?_ : (sy : Syllable) (q : Quantity) → Dec (sy ~ˢʸⁿ q)
sy ~ˢʸⁿ? q
  with ¿ SynezizedOrDipthong sy ¿ | q ≟ ─ | sy ~₁? q
... | yes syn | yes refl | _       = yes (synLong syn)
... | yes syn | no  q≢─  | _       = no λ where (synLong _)     → q≢─ refl ; (¬synLong ns _) → ns syn
... | no ¬syn | _        | yes ~q  = yes (¬synLong ¬syn ~q)
... | no ¬syn | _        | no  ¬~q = no λ where (synLong s)     → ¬syn s   ; (¬synLong _ ~q) → ¬~q ~q

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

module _ (next : Context) where
  open QuantityRules next

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

-- ** ↝, ~∗, ~? decisions (parameterised by context)

module QuantityDec (next : Context) where
  open QuantityRules next

  private
    doubleOrTwo? : (ls : Letters) → Dec ((StartsWithDoubleConsonant ∪₁ StartsWithTwoConsonants) ls)
    doubleOrTwo? ls with StartsWithDoubleConsonant? ls | StartsWithTwoConsonants? ls
    ... | yes dc  | _      = yes (inj₁ dc)
    ... | no  _   | yes tc = yes (inj₂ tc)
    ... | no  ¬dc | no ¬tc = no λ where (inj₁ dc) → ¬dc dc ; (inj₂ tc) → ¬tc tc

  -- sy ↝ ─ (the only possible ↝ quantity)
  dec-↝─ : (sy : Syllable) → Dec (sy ↝ ─)
  dec-↝─ sy with ∃-vowel-followedBy next doubleOrTwo? (toList sy)
  ... | yes (v∈ , fb) = yes (longByPosition v∈ fb)
  ... | no  ¬∃        = no λ where (longByPosition v∈ fb) → ¬∃ (v∈ , fb)

  -- sy ~∗ ─
  dec-~∗─ : (sy : Syllable) → Dec (sy ~∗ ─)
  dec-~∗─ sy
    with dec-↝─ sy
  ... | yes ↝─ = yes ([522] ↝─)
  ... | no  ¬↝─
    with sy ~ˢʸⁿ? ·
  ... | no  ¬syn·  = no λ where
    ([522] ↝─)        → ¬↝─ ↝─
    ([524] v∈ syn· _) → ¬syn· syn·
  ... | yes syn·
    with ∃-vowel-followedByInner MuteThenLiquid? (toList sy)
  ... | yes (v∈ , ml) = yes ([524] v∈ syn· ml)
  ... | no  ¬ml       = no λ where
    ([522] ↝─)          → ¬↝─ ↝─
    ([524] v∈ _ ml)     → ¬ml (v∈ , ml)

  -- sy ~∗ ·
  dec-~∗· : (sy : Syllable) → Dec (sy ~∗ ·)
  dec-~∗· sy
    with sy ~ˢʸⁿ? ─
  ... | yes syn─
    with ∃-lastVowel-followedBy next StartsWithVowel? (toList sy)
  ... | yes (v∈ , la , sv) = yes ([1173] v∈ la syn─ sv)
  ... | no  ¬1173
    with sy ~ˢʸⁿ? ·
  ... | yes syn·
    with ∃-vowel-followedByInner MuteThenLiquid? (toList sy)
  ... | yes (v∈ , ml) = yes ([524] v∈ syn· ml)
  ... | no  ¬ml       = no λ where
    ([1173] v∈ la _ sv)  → ¬1173 (v∈ , la , sv)
    ([524]  v∈ syn· ml)  → ¬ml (v∈ , ml)
  dec-~∗· sy | yes syn─ | no ¬1173 | no ¬syn·
    = no λ where
    ([1173] v∈ la _ sv) → ¬1173 (v∈ , la , sv)
    ([524]  _ syn· _)   → ¬syn· syn·
  dec-~∗· sy | no ¬syn─
    with sy ~ˢʸⁿ? ·
  ... | yes syn·
    with ∃-vowel-followedByInner MuteThenLiquid? (toList sy)
  ... | yes (v∈ , ml) = yes ([524] v∈ syn· ml)
  ... | no  ¬ml       = no λ where
    ([1173] _ _ syn─ _) → ¬syn─ syn─
    ([524]  v∈ _ ml)    → ¬ml (v∈ , ml)
  dec-~∗· sy | no ¬syn─ | no ¬syn·
    = no λ where
    ([1173] _ _ syn─ _) → ¬syn─ syn─
    ([524]  _ syn· _)   → ¬syn· syn·

  -- sy ~? mq  (unique mq for each (sy, ctx))
  𝟛-theQuantity :
    (sy : Syllable) →
    ∃ λ (mq : Maybe Quantity) →
        (sy ~? mq)
      × (∀ {mq′} → sy ~? mq′ → mq′ ≡ mq)
  𝟛-theQuantity sy
    with dec-~∗─ sy | dec-~∗· sy
  ... | yes ~─ | yes ~·
    = nothing
    , ambivalent ~─ ~·
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ─) ~─)
              (ambivalent _ _)           → refl
              (certain {q = ─} _ ¬~·)    → ⊥-elim (¬~· ~·)
              (certain {q = ·} _ ¬~─)    → ⊥-elim (¬~─ ~─)
  ... | yes ~─ | no  ¬~·
    = just ─
    , certain ~─ ¬~·
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ─) ~─)
              (ambivalent _ ~·)          → ⊥-elim (¬~· ~·)
              (certain {q = ─} _ _)      → refl
              (certain {q = ·} _ ¬~─)    → ⊥-elim (¬~─ ~─)
  ... | no  ¬~─ | yes ~·
    = just ·
    , certain ~· ¬~─
    , λ where (ambiguous  ¬any)          → ⊥-elim ((¬any ·) ~·)
              (ambivalent ~─ _)          → ⊥-elim (¬~─ ~─)
              (certain {q = ─} _ ¬~·)    → ⊥-elim (¬~· ~·)
              (certain {q = ·} _ _)      → refl
  ... | no  ¬~─ | no  ¬~·
    = nothing
    , ambiguous (λ where ─ ~─ → ¬~─ ~─ ; · ~· → ¬~· ~·)
    , λ where (ambiguous  _)         → refl
              (ambivalent ~─ _)      → ⊥-elim (¬~─ ~─)
              (certain {q = ─} ~─ _) → ⊥-elim (¬~─ ~─)
              (certain {q = ·} ~· _) → ⊥-elim (¬~· ~·)

-- ** Lift to sequences and connect to _~³_

𝟛-theQuantities :
  (ws : Words n) →
  ∃ λ (mqs : Quantities n) →
      (ws ~³ mqs)
    × (∀ {mqs′} → ws ~³ mqs′ → mqs′ ≡ mqs)
𝟛-theQuantities {n = n} ws = go (inContext {n = n} ws)
  where
  go : ∀ {m} →
    (syctxs : Vec (Syllable × Context) m) →
    ∃ λ (mqs : Quantities m) →
        VPointwise _~_ syctxs mqs
      × (∀ {mqs′} → VPointwise _~_ syctxs mqs′ → mqs′ ≡ mqs)
  go [] = [] , [] , λ where [] → refl
  go ((sy , ctx) ∷ syctxs)
    with QuantityDec.𝟛-theQuantity ctx sy | go syctxs
  ... | mq , mq~ , mq-uniq | mqs , mqs~ , mqs-uniq
    = mq ∷ mqs
    , mq~ ∷ mqs~
    , λ where (mq~′ ∷ mqs~′) → cong₂ _∷_ (mq-uniq mq~′) (mqs-uniq mqs~′)
