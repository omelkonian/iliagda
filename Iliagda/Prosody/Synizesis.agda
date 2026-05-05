{-# OPTIONS --safe #-}
module Iliagda.Prosody.Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = Vowel ∘ head
LastVowel  = Vowel ∘ last

_⁀_ : Syllable → Syllable → Syllable
_⁀_ = L.NE._⁺++⁺_

data _-synezizes*-_ : Syllables n → Syllables n′ → Type

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
      -- TODO: διαλυτικα??
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

_∷ʷˢ_ : Syllable → Words n → Words (suc n)
sy ∷ʷˢ [] = word [ sy ] ∷ []
sy ∷ʷˢ (word sys ∷ ws) = word (sy ∷ sys) ∷ ws

unwords-∷ʷˢ : unwords (sy ∷ʷˢ ws) ≡ sy ∷ unwords ws
unwords-∷ʷˢ {ws = []} = refl
unwords-∷ʷˢ {ws = word _ ∷ _} = refl

_++ʷˢ_ : Syllables m → Words n → Words (m + n)
[] ++ʷˢ ws = ws
(sy ∷ sys) ++ʷˢ ws = sy ∷ʷˢ (sys ++ʷˢ ws)

unwords-++ʷˢ : unwords (sys ++ʷˢ ws) ≡ sys V.++ unwords ws
unwords-++ʷˢ {sys = []} = refl
unwords-++ʷˢ {sys = sy ∷ sys} {ws = ws} =
  trans (unwords-∷ʷˢ {ws = sys ++ʷˢ ws})
        (cong (sy ∷_) $ unwords-++ʷˢ {ws = ws})

synezizeWords : ∀ (ws : Words n) {sys′ : Syllables n′}
  (syn : unwords ws -synezizes*- sys′) →
  Words n′
synezizeWords [] [] = []
synezizeWords (word [ sy ] ∷ []) (.sy ∷ []) =
  word [ sy ] ∷ []
synezizeWords (word [ sy ] ∷ (word (sy′ ∷ sys) ∷ ws)) (.sy ∷ syn) =
  -- keep word boundary
  word [ sy ] ∷ synezizeWords (word (sy′ ∷ sys) ∷ ws) syn
synezizeWords (word [ sy ] ∷ (word (sy′ ∷ sys) ∷ ws)) {_ ∷ sys′} (_ ∺ syn) =
  -- forget word boundary
  let syn′ = subst (_~ sys′) (sym $ unwords-++ʷˢ {ws = ws}) syn in
  (sy ⁀ sy′) ∷ʷˢ synezizeWords (sys ++ʷˢ ws) syn′
synezizeWords (word (sy ∷ sy′ ∷ sys) ∷ ws) (.sy ∷ syn) =
  -- no word boundary
  sy ∷ʷˢ synezizeWords (word (sy′ ∷ sys) ∷ ws) syn
synezizeWords (word (sy ∷ sy′ ∷ sys) ∷ ws) {_ ∷ sys′} (_ ∺ syn) =
  -- no word boundary
  let syn′ = subst (_~ sys′) (sym $ unwords-++ʷˢ {ws = ws}) syn in
  (sy ⁀ sy′) ∷ʷˢ synezizeWords (sys ++ʷˢ ws) syn′

-- ** unique synezesis

Vowel-irr : (p q : Vowel l) → p ≡ q
Vowel-irr = unique⇒irrelevant auto
  where open import Data.List.Membership.Propositional.Properties.WithK

uniqueSyn : (p q : sys -synezizes*- sys′) → p ≡ q
uniqueSyn [] [] = refl
uniqueSyn (sy ∷ p) (.sy ∷ q) = cong (sy ∷_) (uniqueSyn p q)
uniqueSyn (sy ∷ _) ((_ ∺ _) ⦃ eq ⦄) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn ((_ ∺ _) ⦃ eq ⦄) (sy ∷ _) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn (((lv , fv) ∺ p) ⦃ refl ⦄) (((lv′ , fv′) ∺ q) ⦃ refl ⦄)
  -- rewrite Vowel-irr lv lv′ | Vowel-irr fv fv′
  = subst (λ ◆ → _ ≡ (◆ , _) ∺ _) (Vowel-irr lv lv′)
  $ subst (λ ◆ → _ ≡ (_ , ◆) ∺ _) (Vowel-irr fv fv′)
  $ cong (_ ∺_) (uniqueSyn p q)
