{-# OPTIONS --safe #-}
module Iliagda.Reading where
open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Lexicon using (unsyllables; stripProclitic)

-- ** Restoring an unwritten letter into a syllable.
-- Total by construction: the position is a `Fin (suc ∣sy∣)`, i.e. one of the
-- ∣sy∣+1 gaps in `sy`, so there is no out-of-range case to default.
insertSy : (sy : Syllable) → Fin (suc (length⁺ sy)) → Letter → Syllable
insertSy (h ∷ t) Fi.zero   c = c ∷ (h ∷ t)
insertSy (h ∷ t) (fsuc k)  c = h ∷ L.insertAt t k c

-- ** A resolved edit, indexed by the text it edits.
-- The `ℕ` index is the *output* syllable count, so a future count-changing
-- constructor (diectasis, augment, un-elision) lands here as `Edit sys (suc n)`
-- without re-indexing anything downstream.
data Edit {n} (sys : Syllables n) : ℕ → Type where
  unwritten :
    (c : Letter) (i : Fin n) → Fin (suc (length⁺ (V.lookup sys i))) → Edit sys n

asRead : ∀ {n m} {sys : Syllables n} → Edit sys m → Syllables m
asRead {sys = sys} (unwritten c i k) = sys V.[ i ]≔ insertSy (V.lookup sys i) k c

-- ** The declared table.
-- Keyed on flattened letters (as `Iliagda.Lexicon` is), so it is robust to
-- changes in syllabification. The two `ℕ`s are the target syllable and the gap
-- within it; both are bounds-checked against the actual word by `readingEdit`,
-- and an entry that fails either check is inert rather than misapplied.
data Reading : Type where
  unwritten : Letters → Letter → ℕ → ℕ → Reading

readingKey : Reading → Letters
readingKey (unwritten k _ _ _) = k

readingEdit : ∀ {n} (sys : Syllables n) → Reading → Maybe (Edit sys n)
readingEdit {n} sys (unwritten _ c s k)
  with s Nat.<? n
... | no _ = nothing
... | yes s<n
  with k Nat.<? suc (length⁺ (V.lookup sys (Fi.fromℕ< s<n)))
... | no _    = nothing
... | yes k<∣ = just (unwritten c (Fi.fromℕ< s<n) (Fi.fromℕ< k<∣))

readings : List Reading
readings
  = unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ⨾ ν ] ϝ 1 1
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ἔ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ς ] ϝ 1 1
  ∷ unwritten [ ἐ ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ τ ⨾ ε ] ϝ 1 1
  ∷ unwritten [ ὑ ⨾ π ⨾ έ ⨾ δ ⨾ ε ⨾ ι ⨾ σ ⨾ α ⨾ ν ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ν ⨾ τ ⨾ ε ⨾ ς ] ϝ 2 1
  ∷ unwritten [ ὑ ⨾ π ⨾ ο ⨾ δ ⨾ ε ⨾ ί ⨾ σ ⨾ α ⨾ ς ] ϝ 2 1
  ∷ []

readingLookup : Letters → Maybe Reading
readingLookup ls = go readings
  module ∣readingLookup∣ where
  go : List Reading → Maybe Reading
  go [] = nothing
  go (r ∷ rs) = if ⌊ readingKey r ≟ stripProclitic ls ⌋ then just r else go rs

reword : Word n → Syllables n → Word n
reword (word {_} {p} _) sys = word {_} {p} sys

readWord : (w : Word n) → Edit (unword w) n → Word n
readWord w e = reword w (asRead e)

infix 2 _-reads-_
data _-reads-_ : Words n → Words n → Type where

  [] :
    ─────────────
    [] -reads- []

  skip : ∀ {w : Word n} {ws ws′ : Words n′} →
    ws -reads- ws′
    ───────────────────────────
    (w ∷ ws) -reads- (w ∷ ws′)

  edit : ∀ {w : Word n} {ws ws′ : Words n′} {r} {e : Edit (unword w) n} →
    ∙ readingLookup (unsyllables (unword w)) ≡ just r
    ∙ readingEdit (unword w) r ≡ just e
    ∙ ws -reads- ws′
      ─────────────────────────────────────────────
      (w ∷ ws) -reads- (readWord w e ∷ ws′)

reads-refl : (ws : Words n) → ws -reads- ws
reads-refl [] = []
reads-refl (w ∷ ws) = skip (reads-refl ws)
