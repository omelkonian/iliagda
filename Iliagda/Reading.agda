{-# OPTIONS --safe #-}
module Iliagda.Reading where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Lexicon using (stripProclitic)

-- ** The declared table of inserted (unwritten) letters.

data Reading : Type where
  unwritten : Letters
            → Letter
            → ℕ -- which syllable in the word
            → ℕ -- which position in the syllable
            → Reading

readings : List Reading
readings
  = unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ⨾ ν ] ϝ 1 1
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ς ] ϝ 1 1
  ∷ unwritten [ ἐ ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ τ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ὑ ⨾ π ⨾ έ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ν ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ν ⨾ τ ⨾ ε ⨾ ς ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ς ] ϝ 2 1
  ∷ unwritten [ Β ⨾ ο ⨾ ρ ⨾ έ ⨾ ῃ ] ρ 0 2
  ∷ unwritten [ Β ⨾ ο ⨾ ρ ⨾ έ ⨾ η ⨾ ς ] ρ 0 2
  ∷ unwritten [ φ ⨾ ι ⨾ ƛ ⨾ ο ⨾ μ ⨾ ε ⨾ ι ⨾ δ ⨾ ὴ ⨾ ς ] μ 1 2
  ∷ unwritten [ φ ⨾ ι ⨾ ƛ ⨾ ο ⨾ μ ⨾ ε ⨾ ι ⨾ δ ⨾ ή ⨾ ς ] μ 1 2
  ∷ unwritten [ ἐ ⨾ ƛ ⨾ ί ⨾ σ ⨾ σ ⨾ ε ⨾ τ ⨾ ο ] ἰ 0 1
  -- ** DB-Monro pg.343 footnote
  -- ∷ deletion [ ἀ ⨾ ν ⨾ δ ; ρ ⨾ ο ⨾ τ ⨾ ῆ ⨾ τ ⨾ α ] 1
  -- ∷ deletion [ ἀ ⨾ ν ⨾ δ ; ρ ⨾ ο ⨾ τ ⨾ ῆ ⨾ τ ⨾ ά ] 1
  ∷ []

-- ** looking up readings

readingKey : Reading → Letters
readingKey (unwritten k _ _ _) = k

readingLookup : Syllables n → Maybe Reading
readingLookup sys
  using ls ← stripProclitic $ unsyllables sys
  = go readings
  where
  go : List Reading → Maybe Reading
  go [] = nothing
  go (r ∷ rs) = if ⌊ readingKey r ≟ ls ⌋ then just r else go rs

-- ** the induced edits from a reading

data Edit {n} (sys : Syllables n) : ℕ → Type where
  unwritten : Letter → (i : Fin n) → Fin (suc $ length⁺ $ V.lookup sys i) → Edit sys n

readingEdit : ∀ {n} (sys : Syllables n) → Reading → Maybe (Edit sys n)
readingEdit {n} sys (unwritten _ c s k)
  with s Nat.<? n
... | no _ = nothing
... | yes s<n
  with k Nat.<? suc (length⁺ $ V.lookup sys $ Fi.fromℕ< s<n)
... | no _    = nothing
... | yes k<∣ = just $′ unwritten c (Fi.fromℕ< s<n) (Fi.fromℕ< k<∣)

applyEdit : (w : Word n) → Edit (unword w) n → Word n
applyEdit w = reword w ∘ asRead
  where
  insertSy : (sy : Syllable) → Fin (suc (length⁺ sy)) → Letter → Syllable
  insertSy (h ∷ t) Fi.zero  c = c ∷ h ∷ t
  insertSy (h ∷ t) (fsuc k) c = h ∷ L.insertAt t k c

  asRead : ∀ {n m} {sys : Syllables n} → Edit sys m → Syllables m
  asRead {sys = sys} (unwritten c i k) = sys V.[ i ]≔ insertSy (V.lookup sys i) k c

  reword : Word n → Syllables n → Word n
  reword (word {_} {p} _) sys = word {_} {p} sys

infix 2 _-reads-_
data _-reads-_ : Words n → Words n → Type where

  [] :
    ─────────────
    [] -reads- []

  skip : ∀ {w : Word n} {ws ws′ : Words n′} →
    ws -reads- ws′
    ──────────────────────────
    (w ∷ ws) -reads- (w ∷ ws′)

  edit : ∀ {w : Word n} {ws ws′ : Words n′} {r} (let sys = unword w) {e : Edit sys n} →
    ∙ readingLookup sys ≡ just r
    ∙ readingEdit sys r ≡ just e
    ∙ ws -reads- ws′
      ──────────────────────────────────────
      (w ∷ ws) -reads- (applyEdit w e ∷ ws′)

reads-refl : (ws : Words n) → ws -reads- ws
reads-refl = λ where
  [] → []
  (w ∷ ws) → skip $ reads-refl ws

-- ** decision procedure

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
  = go (readingLookup (unword w)) refl
  where
  skips : List (Words _)
  skips = map (w ∷_) wss

  sound-skip : ∀ {ws′} → ws′ ∈ skips → (w ∷ ws) -reads- ws′
  sound-skip x∈ with _ , y∈ , refl ← ∈-map⁻ (w ∷_) x∈ = skip (sound y∈)

  go : (m : Maybe Reading) → readingLookup (unword w) ≡ m →
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
      wᵣ = applyEdit w e

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
