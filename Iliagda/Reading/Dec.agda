{-# OPTIONS --safe #-}
module Iliagda.Reading.Dec where
open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Lexicon using (unsyllables)
open import Iliagda.Reading

allReadings :
  (ws : Words n) →
  ∃ λ (wss : List (Words n)) →
      (∀ {ws′} → ws′ ∈ wss → ws -reads- ws′)
    × (∀ {ws′} → ws -reads- ws′ → ws′ ∈ wss)
allReadings [] = [ [] ] , sound , complete
  where
  sound : ∀ {ws′} → ws′ ∈ [ [] ] → [] -reads- ws′
  sound (here refl) = []

  complete : ∀ {ws′} → [] -reads- ws′ → ws′ ∈ [ [] ]
  complete [] = here refl
allReadings (w ∷ ws)
  using wss , sound , complete ← allReadings ws
  = go (readingLookup (unsyllables (unword w))) refl
  where
  skips : List (Words _)
  skips = map (w ∷_) wss

  sound-skip : ∀ {ws′} → ws′ ∈ skips → (w ∷ ws) -reads- ws′
  sound-skip x∈ with _ , y∈ , refl ← ∈-map⁻ (w ∷_) x∈ = skip (sound y∈)

  go : (m : Maybe Reading) → readingLookup (unsyllables (unword w)) ≡ m →
    ∃ λ (wss′ : List (Words _)) →
        (∀ {ws′} → ws′ ∈ wss′ → (w ∷ ws) -reads- ws′)
      × (∀ {ws′} → (w ∷ ws) -reads- ws′ → ws′ ∈ wss′)
  go nothing eqL = skips , sound-skip , complete′
    where
    complete′ : ∀ {ws′} → (w ∷ ws) -reads- ws′ → ws′ ∈ skips
    complete′ (skip rd) = ∈-map⁺ (w ∷_) (complete rd)
    complete′ (edit eqL′ _ _) = case trans (sym eqL) eqL′ of λ ()
  go (just r) eqL = go′ (readingEdit (unword w) r) refl
    where
    go′ : (me : Maybe (Edit (unword w) _)) → readingEdit (unword w) r ≡ me →
      ∃ λ (wss′ : List (Words _)) →
          (∀ {ws′} → ws′ ∈ wss′ → (w ∷ ws) -reads- ws′)
        × (∀ {ws′} → (w ∷ ws) -reads- ws′ → ws′ ∈ wss′)
    go′ nothing eqE = skips , sound-skip , complete′
      where
      complete′ : ∀ {ws′} → (w ∷ ws) -reads- ws′ → ws′ ∈ skips
      complete′ (skip rd) = ∈-map⁺ (w ∷_) (complete rd)
      complete′ (edit eqL′ eqE′ _)
        with refl ← May.just-injective (trans (sym eqL) eqL′)
        = case trans (sym eqE) eqE′ of λ ()
    go′ (just e) eqE = subs ++ skips , sound′ , complete′
      where
      wᵣ : Word _
      wᵣ = readWord w e

      subs : List (Words _)
      subs = map (wᵣ ∷_) wss

      sound′ : ∀ {ws′} → ws′ ∈ subs ++ skips → (w ∷ ws) -reads- ws′
      sound′ x∈ with L.Mem.∈-++⁻ subs x∈
      ... | inj₂ y∈ = sound-skip y∈
      ... | inj₁ y∈ with _ , z∈ , refl ← ∈-map⁻ (wᵣ ∷_) y∈
        = edit eqL eqE (sound z∈)

      complete′ : ∀ {ws′} → (w ∷ ws) -reads- ws′ → ws′ ∈ subs ++ skips
      complete′ (skip rd) = L.Mem.∈-++⁺ʳ subs (∈-map⁺ (w ∷_) (complete rd))
      complete′ (edit eqL′ eqE′ rd)
        with refl ← May.just-injective (trans (sym eqL) eqL′)
        with refl ← May.just-injective (trans (sym eqE) eqE′)
        = L.Mem.∈-++⁺ˡ (∈-map⁺ (wᵣ ∷_) (complete rd))
