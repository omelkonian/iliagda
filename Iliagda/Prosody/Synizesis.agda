{-# OPTIONS --safe #-}
module Iliagda.Prosody.Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = Vowel ∘ head
LastVowel  = Vowel ∘ last

_⁀_ : Syllable → Syllable → Syllable
_⁀_ = L.NE._⁺++⁺_

data _-synezizes*-_ : Vec Syllable n → Vec Syllable n′ → Type

private _~_ = _-synezizes*-_

-- Design decisions:
--    (1) reflexive? YES
--    (2) allow recursive/iterative synezesis? NO
--          * counterexample: Πινδαρος, Νεμεα
data _-synezizes*-_ where

  [] :
    ───────
    [] ~ []

  _∷_ :
    ∀ sy →
    ∙ sys ~ sys′
      ────────────────────────
      (sy ∷ sys) ~ (sy ∷ sys′)

  _∺_ :
      LastVowel sy × FirstVowel sy′
    → sys ~ sys′
    → ⦃ _ : sy″ ≡ sy ⁀ sy′ ⦄
    → ───────────────────────────────
      (sy ∷ sy′ ∷ sys) ~ (sy″ ∷ sys′)

  {- TODO: to allow recursive/iterative synezesis
  _∺_ :
      LastVowel sy × FirstVowel sy′
    → sy″ ∷ sys ~ sys′
    → ⦃ _ : sy″ ≡ sy ⁀ sy′ ⦄
    → ───────────────────────────────
      (sy ∷ sy′ ∷ sys) ~ sys′
  -}

m>0⇒n≢n+m : m > 0 → n ≢ n + m
m>0⇒n≢n+m {suc _} {zero}  _ = auto
m>0⇒n≢n+m {suc m} {suc n} _ rewrite Nat.+-suc n m = Nat.m≢1+m+n _

private variable
  xs ys : List⁺ A

length⁺-irrefl : length⁺ xs ≢ length⁺ (xs ⁺++⁺ ys)
length⁺-irrefl {xs = xs} {ys = ys}
  rewrite L.NE.toList-⁺++⁺ xs ys
        | L.length-++ (toList xs) {toList ys}
        = m>0⇒n≢n+m auto

⁺++⁺-irrefl : xs ≢ xs ⁺++⁺ ys
⁺++⁺-irrefl {xs = xs} = length⁺-irrefl {xs = xs} ∘ cong length⁺

⁀-irrefl : sy ≢ sy ⁀ sy′
⁀-irrefl = ⁺++⁺-irrefl

uncons : (sy ∷ sys) -synezizes*- (sy ∷ sys′) → sys -synezizes*- sys′
uncons {sys = []} (_ ∷ []) = []
uncons {sys = _ ∷ _} ((_ ∺ _) ⦃ eq ⦄) = ⊥-elim $ ⁀-irrefl eq
uncons {sys = _ ∷ _} {sys′ = _ ∷ _} (_ ∷ syn) = syn

syn-refl : sys ~ sys
syn-refl {sys = []} = []
syn-refl {sys = _ ∷ sys} = _ ∷ syn-refl {sys = sys}

syn-++ˡ : sys ~ sys′ → (sys″ V.++ sys) -synezizes*- (sys″ V.++ sys′)
syn-++ˡ {sys″ = []} = id
syn-++ˡ {sys″ = _ ∷ sys″} = (_ ∷_) ∘ syn-++ˡ {sys″ = sys″}

open import Iliagda.Prosody.Core

synezize : ∀ {sys : Vec Syllable n} {sys′ : Vec Syllable n′}
  (syn : sys -synezizes*- sys′) →
  Vec (Maybe Quantity) n →
  Vec (Maybe Quantity) n′
synezize = λ where
  []        mqs           → mqs
  (_ ∷ syn) (mq ∷ mqs)    → mq ∷ synezize syn mqs
  (_ ∺ syn) (_ ∷ _ ∷ mqs) → just ─ ∷ synezize syn mqs

-- ** minimal synezesis
-- NB: if we allow minimal 0 synezeses, subsumes general rule.

penalty : sys ~ sys′ → ℕ
penalty = λ where
  [] → 0
  (_ ∷ syn) → penalty syn
  (_ ∺ syn) → 1 + penalty syn

record _-synezizes+-_ (sys : Vec Syllable n) (sys′ : Vec Syllable n′) : Type where
  constructor _⊣_
  field syn  : sys -synezizes*- sys′
        syn+ : penalty syn > 0

-- a "minimal" synezesis has the least amount of ∺ operations.
_≼_ _≺_ : ∀ {sys‴ : Vec Syllable n} → (sys ~ sys′) → (sys″ ~ sys‴) → Type
p ≼ q = penalty p ≤ penalty q
p ≺ q = penalty p < penalty q

-- -}
-- -}
-- -}
-- -}
