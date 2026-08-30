{-# OPTIONS --safe #-}
module Iliagda.Lexicon where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core

-- ** the lexicon

data Locus : Type where
  from-start from-end : ℕ → Locus

data Mode : Type where
  exact  : Locus → Mode
  prefix : ℕ → Mode

record Entry : Type where
  constructor mkEntry
  field key  : Letters
        mode : Mode
        qty  : Quantity
open Entry public

lexicon : List Entry
lexicon
  = mkEntry [ Ἀ ⨾ φ ⨾ ρ ⨾ ο ⨾ δ ⨾ ί ⨾ τ ] (prefix 0) ·
  ∷ mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ι ] (prefix 1) ·
  ∷ mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ὶ ] (prefix 1) ·
  ∷ mkEntry [ ἀ ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ὀ ⨾ ξ ⨾ ὺ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ῥ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ ῥ ⨾ ά ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἔ ⨾ ρ ⨾ γ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ π ⨾ τ ⨾ ε ⨾ ρ ⨾ ό ⨾ ε ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ δ ⨾ ο ⨾ υ ⨾ ρ ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ π ⨾ ο ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἄ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ κ ⨾ α ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ ƛ ⨾ ε ⨾ ε ⨾ ι ⨾ ν ⨾ ὰ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ σ ⨾ σ ⨾ ι ] (exact (from-end 0)) ·
  ∷ mkEntry [ ἐ ⨾ σ ⨾ τ ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ ὅ ⨾ θ ⨾ ι ] (exact (from-end 0)) · -- due to Wyer Grammar book (dative plural)
  ∷ mkEntry [ ε ⨾ ἰ ⨾ ν ⨾ ὶ ] (exact (from-end 0)) ·
  ∷ mkEntry [ γ ⨾ υ ⨾ μ ⨾ ν ⨾ ω ⨾ θ ⨾ έ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·
  ∷ mkEntry [ τ ⨾ ε ⨾ ι ⨾ χ ⨾ ε ⨾ σ ⨾ ι ⨾ π ⨾ ƛ ⨾ ῆ ⨾ τ ⨾ α ] (exact (from-start 2)) ·
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ό ⨾ τ ⨾ η ] (exact (from-start 0)) ·
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ο ⨾ τ ⨾ ά ⨾ ξ ⨾ ο ⨾ μ ⨾ ε ⨾ ν ] (exact (from-start 0)) · -- DB-Monro pg.??
  ∷ mkEntry [ ἀ ⨾ ν ⨾ δ ⨾ ρ ⨾ ο ⨾ τ ⨾ ῆ ⨾ τ ] (prefix 0) · -- DB-Monro pg.343 footnote
  -- (["φί","λε"]:ws) -> (["φη","λε"]:ws)
  -- (["ἐ","πεὶ"]:ws) -> (["η","πεὶ"]:ws)
  ∷ []

stripProclitic : Letters → Letters
stripProclitic (_ ∷ ᾽ ∷ ls) = ls
stripProclitic ls = ls

lexLookup : Letters → Maybe Entry
lexLookup ls = L.findᵇ (matchesE ls) lexicon
  where
  _isPrefixOf_ : Letters → Letters → Bool
  []       isPrefixOf _        = true
  (_ ∷ _)  isPrefixOf []       = false
  (k ∷ ks) isPrefixOf (l ∷ ls) = (⌊ k ≟ l ⌋) 𝔹.∧ (ks isPrefixOf ls)

  matchesE : Letters → Entry → Bool
  matchesE ls e = case e .mode of λ where
   (exact _)  → ⌊ e .key ≟ stripProclitic ls ⌋
   (prefix _) → e .key isPrefixOf stripProclitic ls

-- ** locus information

locusOf : Mode → Locus
locusOf = λ where
  (exact l)  → l
  (prefix k) → from-start k

locusIx : Locus → (n : ℕ) → Maybe (Fin n)
locusIx (from-start k) n with k Nat.<? n
... | yes k<n = just (Fi.fromℕ< k<n)
... | no  _   = nothing
locusIx (from-end k) n with k Nat.<? n
... | yes k<n = just (Fi.opposite (Fi.fromℕ< k<n))
... | no  _   = nothing

record LexHit {n} (sys : Syllables n) : Type where
  constructor lexHit
  field
    entry   : Entry
    ix      : Fin n
    found   : lexLookup (unsyllables sys) ≡ just entry
    atLocus : locusIx (locusOf (entry .mode)) n ≡ just ix
open LexHit public
