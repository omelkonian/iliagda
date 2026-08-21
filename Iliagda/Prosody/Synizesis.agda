{-# OPTIONS --safe #-}
module Iliagda.Prosody.Synizesis where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Dec.Core

FirstVowel LastVowel : Pred₀ Syllable
FirstVowel = Vowel ∘ head
LastVowel  = Vowel ∘ last

record Coalescing (sy sy′ : Syllable) : Type where
  constructor coalescing
  field
    vowels      : LastVowel sy × FirstVowel sy′
    .¬diaeresis : ¬ HasDiaeresis (head sy′)

no-diaeresis : Coalescing sy sy′ → ¬ HasDiaeresis (head sy′)
no-diaeresis (coalescing _ ¬d) = ¬-recompute ¬d

instance
  Dec-Coalescing : Coalescing sy sy′ ⁇
  Dec-Coalescing {sy} {sy′} .dec
    with ¿ LastVowel sy × FirstVowel sy′ ¿ | ¿ HasDiaeresis (head sy′) ¿
  ... | no ¬vv | _      = no $ ¬vv ∘ Coalescing.vowels
  ... | yes _  | yes d  = no λ c → no-diaeresis c d
  ... | yes vv | no ¬d  = yes (coalescing vv ¬d)

_⁀_ : Syllable → Syllable → Syllable
_⁀_ = L.NE._⁺++⁺_

data _-synizizes*-_ : Syllables n → Syllables n′ → Type

private _~_ = _-synizizes*-_

-- Design decisions:
--    (1) reflexive? YES
--    (2) allow recursive/iterative synizesis? NO
--          * counterexample: Πινδαρος, Νεμεα
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
      Coalescing sy sy′
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

syn-refl : sys ~ sys
syn-refl {sys = []} = []
syn-refl {sys = _ ∷ sys} = _ ∷ syn-refl {sys = sys}

syn-++ˡ : sys ~ sys′ → (sys″ V.++ sys) -synizizes*- (sys″ V.++ sys′)
syn-++ˡ {sys″ = []} = id
syn-++ˡ {sys″ = _ ∷ sys″} = (_ ∷_) ∘ syn-++ˡ {sys″ = sys″}

_∷ʷˢ_ : Syllable → Words n → Words (suc n)
sy ∷ʷˢ [] = word [ sy ] ∷ []
sy ∷ʷˢ (word sys ∷ ws) = word (sy ∷ sys) ∷ ws

unwords-∷ʷˢ : unwords (sy ∷ʷˢ ws) ≡ sy ∷ unwords ws
unwords-∷ʷˢ {ws = []} = refl
unwords-∷ʷˢ {ws = word _ ∷ _} = refl

synizizeWords : ∀ (ws : Words n) {sys′ : Syllables n′}
  (syn : unwords ws -synizizes*- sys′) →
  Words n′
synizizeWords [] [] = []
synizizeWords (word [ sy ] ∷ []) (.sy ∷ []) =
  word [ sy ] ∷ []
synizizeWords (word [ sy ] ∷ (word (sy′ ∷ sys) ∷ ws)) (.sy ∷ syn) =
  -- keep word boundary
  word [ sy ] ∷ synizizeWords (word (sy′ ∷ sys) ∷ ws) syn
synizizeWords (word [ sy ] ∷ (word [ sy′ ] ∷ ws)) (_ ∺ syn) =
  -- the two words coalesce into a monosyllable, the boundary after it survives
  word [ sy ⁀ sy′ ] ∷ synizizeWords ws syn
synizizeWords (word [ sy ] ∷ (word (sy′ ∷ sys@(_ ∷ _)) ∷ ws)) (_ ∺ syn) =
  -- the two words coalesce, the rest of the second stays inside the merged word
  (sy ⁀ sy′) ∷ʷˢ synizizeWords (word sys ∷ ws) syn
synizizeWords (word (sy ∷ sy′ ∷ sys) ∷ ws) (.sy ∷ syn) =
  -- no word boundary
  sy ∷ʷˢ synizizeWords (word (sy′ ∷ sys) ∷ ws) syn
synizizeWords (word (sy ∷ sy′ ∷ []) ∷ ws) (_ ∺ syn) =
  -- the merge exhausts this word, the boundary after it survives
  word [ sy ⁀ sy′ ] ∷ synizizeWords ws syn
synizizeWords (word (sy ∷ sy′ ∷ sys@(_ ∷ _)) ∷ ws) (_ ∺ syn) =
  -- word-internal merge
  (sy ⁀ sy′) ∷ʷˢ synizizeWords (word sys ∷ ws) syn

-- ** unique synizesis

Vowel-irr : (p q : Vowel l) → p ≡ q
Vowel-irr = unique⇒irrelevant auto
  where open import Data.List.Membership.Propositional.Properties.WithK

Coalescing-irr : ∀ {sy sy′} (p q : Coalescing sy sy′) → p ≡ q
Coalescing-irr (coalescing (lv , fv) ¬d) (coalescing (lv′ , fv′) _) =
  cong₂ (λ ◆ ◆′ → coalescing (◆ , ◆′) ¬d) (Vowel-irr lv lv′) (Vowel-irr fv fv′)

uniqueSyn : (p q : sys -synizizes*- sys′) → p ≡ q
uniqueSyn [] [] = refl
uniqueSyn (sy ∷ p) (.sy ∷ q) = cong (sy ∷_) (uniqueSyn p q)
uniqueSyn (sy ∷ _) ((_ ∺ _) ⦃ eq ⦄) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn ((_ ∺ _) ⦃ eq ⦄) (sy ∷ _) = ⊥-elim $ ⁀-irrefl eq
uniqueSyn (_∺_ {sy = sy} {sy′ = sy′} c p ⦃ refl ⦄) ((c′ ∺ q) ⦃ refl ⦄)
  = cong₂ (λ ◆ ◆′ → (◆ ∺ ◆′) ⦃ refl ⦄) (Coalescing-irr {sy} {sy′} c c′) (uniqueSyn p q)
