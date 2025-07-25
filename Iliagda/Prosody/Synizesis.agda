module Iliagda.Prosody.Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology

import Data.Maybe as M

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = Vowel ∘ head
LastVowel  = Vowel ∘ last

_⁀_ : Op₂ Syllable
_⁀_ = L.NE._⁺++⁺_

data _-synizizes*-_ : Vec Syllable n → Vec Syllable n′ → Type

private _~_ = _-synizizes*-_

-- Design decisions:
--    (1) reflexive? YES
--    (2) allow recursive/iterative synizesis? NO
data _-synizizes*-_ where

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

uncons : (sy ∷ sys) -synizizes*- (sy ∷ sys′) → sys -synizizes*- sys′
uncons {sys = []} (_ ∷ []) = []
uncons {sys = _ ∷ _} ((_ ∺ _) ⦃ eq ⦄) = ⊥-elim $ ⁀-irrefl eq
uncons {sys = _ ∷ _} {sys′ = _ ∷ _} (_ ∷ syn) = syn

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

syn-refl : sys ~ sys
syn-refl {sys = []} = []
syn-refl {sys = _ ∷ sys} = _ ∷ syn-refl {sys = sys}

syn-++ˡ : sys ~ sys′ → (sys″ V.++ sys) -synizizes*- (sys″ V.++ sys′)
syn-++ˡ {sys″ = []} = id
syn-++ˡ {sys″ = _ ∷ sys″} = (_ ∷_) ∘ syn-++ˡ {sys″ = sys″}

postulate
  syn-++ʳ : sys ~ sys′ → (sys V.++ sys″) -synizizes*- (sys′ V.++ sys″)
-- private
--   cast : .(eq : m ≡ n) → Vec A m → Vec A n
--   cast {n = zero}  eq []       = []
--   cast {n = suc _} eq (x ∷ xs) = x ∷ cast (cong Nat.pred eq) xs

--   ++-identityʳ : ∀ .(eq : n + zero ≡ n) (xs : Vec A n) → cast eq (xs V.++ []) ≡ xs
--   ++-identityʳ eq []       = refl
--   ++-identityʳ eq (x ∷ xs) = cong (x ∷_) (++-identityʳ (cong Nat.pred eq) xs)
-- syn-++ʳ {sys = sys} {sys″ = []} rewrite ++-identityʳ (Nat.+-identityʳ _) sys = {!!}
-- syn-++ʳ {sys″ = x ∷ sys″} = {!!}

open import Iliagda.Prosody.Core

synizize : ∀ {sys : Vec Syllable n} {sys′ : Vec Syllable n′}
  (syn : sys -synizizes*- sys′) →
  Vec (Maybe Quantity) n →
  Vec (Maybe Quantity) n′
synizize = λ where
  []        mqs           → mqs
  (_ ∷ syn) (mq ∷ mqs)    → mq ∷ synizize syn mqs
  (_ ∺ syn) (_ ∷ _ ∷ mqs) → just ─ ∷ synizize syn mqs

-- ** minimal synizesis
-- NB: if we allow minimal 0 synizeses, subsumes general rule.

penalty : sys ~ sys′ → ℕ
penalty = λ where
  [] → 0
  (_ ∷ syn) → penalty syn
  (_ ∺ syn) → 1 + penalty syn

record _-synizizes+-_ (sys : Vec Syllable n) (sys′ : Vec Syllable n′) : Type where
  constructor _⊣_
  field syn  : sys -synizizes*- sys′
        syn+ : penalty syn > 0

_≺_ : Rel₀ (sys ~ sys′)
_≺_ = _<_ on penalty

-- -}
-- -}
-- -}
-- -}
