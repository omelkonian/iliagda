{-# OPTIONS --safe #-}
module Iliagda.Prosody.Synizesis.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis

private pattern 𝟘 = here refl

allSynizeses : ∀ (sys : Vec Syllable n) n′ →
  ∃ λ (syss : List (Vec Syllable n′)) →
      (∀ {sys′} → sys′ ∈ syss → sys -synizizes*- sys′)
    × (∀ {sys′} → sys -synizizes*- sys′ → sys′ ∈ syss)

-- n′ = 0
allSynizeses [] 0 = [ [] ] , (λ where 𝟘 → []) , λ where [] → 𝟘
allSynizeses [] (suc _) = [] , (λ ()) , λ ()

-- n′ = 1
allSynizeses [ sy ] 0 = [] , (λ ()) , λ ()
allSynizeses [ sy ] 1 = [ [ sy ] ] , (λ where 𝟘 → _ ∷ []) , λ where (_ ∷ []) → 𝟘
allSynizeses [ sy ] (suc (suc _)) = [] , (λ ()) , λ where (_ ∷ ())

-- n′ > 1
allSynizeses (sy ∷ sys@(sy′ ∷ _)) 0
  = [] , (λ ()) , λ ()
allSynizeses (sy ∷ sys@(sy′ ∷ sys′)) n′@(suc n′-1)
  with ¿ LastVowel sy × FirstVowel sy′ ¿
... | yes vv

  -- DON'T DO THE SYNIZESIS
  using syss , sound-syss , complete-syss ← allSynizeses sys n′-1

  -- DO DO THE SYNIZESIS
  using syss′ , sound-syss′ , complete-syss′ ← allSynizeses sys′ n′-1

  using sysˡ ← map (sy ∷_) syss
  using sysʳ ← map ((sy ⁀ sy′) ∷_) syss′
  = sysˡ ++ sysʳ
  , (λ syn∈ → case ∈-++⁻ sysˡ syn∈ of λ where
       (inj₁ syn∈ˡ) → let syn′ , syn′∈ , sys≡ = ∈-map⁻ (sy ∷_) syn∈ˡ
                       in subst (_ -synizizes*-_) (sym sys≡) (sy ∷ sound-syss syn′∈)
       (inj₂ syn∈ʳ) → let syn′ , syn′∈ , sys≡ = ∈-map⁻ ((sy ⁀ sy′) ∷_) syn∈ʳ
                       in subst (_ -synizizes*-_) (sym sys≡) (vv ∺ sound-syss′ syn′∈)
    )
  , λ where (sy ∷ p) → ∈-++⁺ˡ (∈-map⁺ (sy ∷_) (complete-syss p))
            ((vv ∺ p) ⦃ refl ⦄) → ∈-++⁺ʳ sysˡ (∈-map⁺ ((sy ⁀ sy′) ∷_) (complete-syss′ p))
... | no ¬vv
  using syss , sound-syss , complete-syss ← allSynizeses sys n′-1
  = map (sy ∷_) syss
  , (λ syn∈ → let syn′ , syn′∈ , sys≡ = ∈-map⁻ (sy ∷_) syn∈
               in subst (_ -synizizes*-_) (sym sys≡) (sy ∷ sound-syss syn′∈))
  , λ where (sy ∷ p) → ∈-map⁺ (sy ∷_) (complete-syss p)
            (vv ∺ _) → ⊥-elim $ ¬vv vv

syn⇒≤ : ∀ {sys : Vec Syllable n} {n′} {sys′ : Vec Syllable n′}
  → sys -synizizes*- sys′
  → n ≥ n′
syn⇒≤ = λ where
  []      → z≤n
  (_ ∷ p) → s≤s $ syn⇒≤ p
  (_ ∺ p) → Nat.m≤n⇒m≤1+n $ s≤s $ syn⇒≤ p

allSynizeses′ : ∀ (sys : Syllables n) →
  ∃ λ (n×syss : List (∃ λ n′ → Syllables n′)) →
      (∀ {n′ sys′} → (n′ , sys′) ∈ n×syss → sys -synizizes*- sys′)
    × (∀ {n′ sys′} → sys -synizizes*- sys′ → (n′ , sys′) ∈ n×syss)
allSynizeses′ {n} sys
  = n×syss , sou , com
  where
  ns′    = n L.∷ L.downFrom n
  mk     = (λ n′ → map (n′ ,_) $ allSynizeses sys n′ .proj₁)
  n×syss = concatMap mk ns′

  sou : ∀ {n′ sys′} → (n′ , sys′) ∈ n×syss → sys -synizizes*- sys′
  sou {n′}{sys′} n×sys∈
    using syss , sound-syss , _ ← allSynizeses sys n′
    = sound-syss sys∈
    where
    sys∈ : sys′ ∈ syss
    sys∈ with ∈-concatMap⁻ mk {ns′} n×sys∈
    ... | here p
      with sys , sys∈ , refl ← ∈-map⁻ (_ ,_) p
      = sys∈
    ... | there n∈
      with _ , _ , p ← L.Any.applyDownFrom⁻ id n∈
      with sys , sys∈ , refl ← ∈-map⁻ (_ ,_) p
      = sys∈

  com : ∀ {n′ sys′} → sys -synizizes*- sys′ → (n′ , sys′) ∈ n×syss
  com {n′} {sys′} syn
    using syss , _ , complete-syss ← allSynizeses sys n′
    = ∈-concatMap⁺ mk
    $ L.Any.map (λ where refl → ∈-map⁺ (_ ,_) (complete-syss syn)) n∈
    where
    n∈ : n′ ∈ ns′
    n∈ with Nat.m≤n⇒m<n∨m≡n $ syn⇒≤ syn
    ... | inj₁ n′<n = there (∈-downFrom⁺ n′<n)
    ... | inj₂ refl = here refl
