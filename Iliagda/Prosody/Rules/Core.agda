{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Core where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis

-- A complies with B
record _-compliesWith-_ (A B : Type) : Type₁ where
  infix 0 _~_
  field _~_ : A → B → Type
  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_

  NonDerivable NonDerivable∃ : A → Type
  NonDerivable  a = ∀ b → a ≁ b
  NonDerivable∃ a = ¬ ∃ λ b → a ~ b

  NonDerivable′ NonDerivable∃′ : B → Type
  NonDerivable′  b = ∀ a → a ≁ b
  NonDerivable∃′ b = ¬ ∃ λ a → a ~ b

  NonDerivable∃⇒ : ∀ {a} → NonDerivable∃ a → NonDerivable a
  NonDerivable∃⇒ ∄b b a~b = ∄b (b , a~b)

  NonDerivable∃′⇒ : ∀ {b} → NonDerivable∃′ b → NonDerivable′ b
  NonDerivable∃′⇒ ∄a a a~b = ∄a (a , a~b)

open _-compliesWith-_ ⦃ ... ⦄ public

-- ** quantity knowledge

data Flat (A : Type) : Type where
  single : A → Flat A
  none   : Flat A
  all    : Flat A

Quantities : ℕ → Type
Quantities = Vec (Flat Quantity)

variable
  mq mq′ mq″ : Flat Quantity
  mqs mqs′ : Quantities n

synezize : ∀ {sys : Syllables n} {sys′ : Syllables n′}
  (syn : sys -synezizes*- sys′) →
  Quantities n →
  Quantities n′
synezize = λ where
  []        mqs           → mqs
  (_ ∷ syn) (mq ∷ mqs)    → mq ∷ synezize syn mqs
  (_ ∺ syn) (_ ∷ _ ∷ mqs) → single ─ ∷ synezize syn mqs

-- ** enumerations

record Enumeration (_~_ : A → B → Type) : Type where
  field
    allBs    : A → List B
    sound    : ∀ {a b} → b ∈ allBs a → a ~ b
    complete : ∀ {a b} → a ~ b → b ∈ allBs a
open Enumeration public

-- ** words

firstSyllable : Word n → Syllable
firstSyllable (word (sy ∷ _)) = sy

private
  -- Forded `Words`
  data `Words : ℕ → Type where
    [] : ⦃ n ≡ 0 ⦄ → `Words n
    _∷_ : ⦃ m ≡ n + n′ ⦄ → Word n → `Words n′ → `Words m

  toWords : `Words n → Words n
  toWords = λ where
    ([] ⦃ refl ⦄) → []
    (_∷_ ⦃ refl ⦄ w ws) → w ∷ toWords ws

  fromWords : Words n → `Words n
  fromWords = λ where
    [] → []
    (w ∷ ws) → w ∷ fromWords ws

  to∘fromWords : toWords (fromWords ws) ≡ ws
  to∘fromWords {ws = []} = refl
  to∘fromWords {ws = _ ∷ ws} rewrite to∘fromWords {ws = ws} = refl

  private variable `ws : `Words n

  from∘toWords : fromWords (toWords `ws) ≡ `ws
  from∘toWords {`ws = [] ⦃ refl ⦄} = refl
  from∘toWords {`ws = _∷_ ⦃ refl ⦄ _ ws} rewrite from∘toWords {`ws = ws} = refl

  `emptyWords : (ws : `Words 0) → ws ≡ []
  `emptyWords ([] ⦃ refl ⦄) = refl
  `emptyWords (_∷_ (word {zero} {n≢0} _) _) = contradict n≢0
  `emptyWords (_∷_ ⦃ m≡ ⦄ (word {suc _} _) _) = contradict m≡

  `dropSy′ : `Words (1 + n) → Syllable × `Words n
  `dropSy′ (word [ sy ] ∷ ws)
    = sy , subst `Words (Nat.suc-injective (sym it)) ws
  `dropSy′ (word (sy ∷ sys@(_ ∷ _)) ∷ ws)
    = sy , subst `Words (Nat.suc-injective $ sym it) (word sys ∷ ws)

emptyWords : (ws : Words 0) → ws ≡ []
emptyWords = trans (sym to∘fromWords) ∘ cong toWords ∘ `emptyWords ∘ fromWords

dropSy′ : Words (1 + n) → Syllable × Words n
dropSy′ = map₂ toWords ∘ `dropSy′ ∘ fromWords

firstSy : Words (1 + n) → Syllable
firstSy = proj₁ ∘ dropSy′

dropSy : Words (1 + n) → Words n
dropSy = proj₂ ∘ dropSy′

dropSys′ : ∀ m → Words (m + n) → (Syllable ^ m) × Words n
dropSys′ = λ where
  zero    ws → tt , ws -- tt , ws
  (suc m) ws →
    let sys , ws′ = dropSys′ m (dropSy ws)
    in (firstSy ws , sys) , ws′

module _ m (ws : Words (m + n)) where
  firstSys : Syllable ^ m
  firstSys = dropSys′ m ws .proj₁

  dropSys : Words n
  dropSys = dropSys′ m ws .proj₂

data SingleSyllable : Words n → Type where
  singleSy : SingleSyllable (word [ sy ] ∷ ws)

instance
  Dec-SingleSyllable : SingleSyllable ws ⁇
  Dec-SingleSyllable {ws = ws} .dec
    with ws
  ... | [] = no λ ()
  ... | word [ _ ] ∷ _ = yes singleSy
  ... | word (_ ∷ _ ∷ _) ∷ _ = no λ ()

-- -}
-- -}
-- -}
-- -}
