{-# OPTIONS --safe #-}
module Iliagda.Lexicon where
open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core

unsyllables : Syllables n → Letters
unsyllables = L.concat ∘ map toList ∘ toList

data Locus : Type where
  from-start from-end : ℕ → Locus

data Mode : Type where
  exact  : Locus → Mode
  prefix : ℕ → Mode

record Entry : Type where
  constructor mkEntry
  field key : Letters
        mode : Mode
        qty  : Quantity
open Entry public

locusOf : Mode → Locus
locusOf (exact l)  = l
locusOf (prefix k) = from-start k

stripProclitic : Letters → Letters
stripProclitic (_ ∷ ᾽ ∷ ls) = ls
stripProclitic ls = ls

_isPrefixOf_ : Letters → Letters → Bool
[]       isPrefixOf _        = true
(_ ∷ _)  isPrefixOf []       = false
(k ∷ ks) isPrefixOf (l ∷ ls) = (⌊ k ≟ l ⌋) 𝔹.∧ (ks isPrefixOf ls)

matchesE : Entry → Letters → Bool
matchesE e ls with e .mode
... | exact _  = ⌊ e .key ≟ stripProclitic ls ⌋
... | prefix _ = e .key isPrefixOf stripProclitic ls

locusIx : Locus → (n : ℕ) → Maybe (Fin n)
locusIx (from-start k) n with k Nat.<? n
... | yes k<n = just (Fi.fromℕ< k<n)
... | no  _   = nothing
locusIx (from-end k) n with k Nat.<? n
... | yes k<n = just (Fi.opposite (Fi.fromℕ< k<n))
... | no  _   = nothing

-- ** the lexicon
-- INCOMPLETE: add as needed
lexicon : List Entry
lexicon
  = mkEntry [ Ἀ ⨾ φ ⨾ ρ ⨾ ο ⨾ δ ⨾ ί ⨾ τ ] (prefix 0) ·                                    -- Ἀφροδίτ-
  ∷ mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ι ] (prefix 1) ·                                                -- ἀμφι-
  ∷ mkEntry [ ἀ ⨾ μ ⨾ φ ⨾ ὶ ] (prefix 1) ·                                                -- ἀμφὶ-
  ∷ mkEntry [ ἀ ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·                                      -- ἀλλὰ
  ∷ mkEntry [ ὀ ⨾ ξ ⨾ ὺ ] (exact (from-end 0)) ·                                          -- ὀξὺ
  ∷ mkEntry [ ῥ ⨾ α ] (exact (from-end 0)) ·                                              -- ῥα
  ∷ mkEntry [ ῥ ⨾ ά ] (exact (from-end 0)) ·                                              -- ῥά
  ∷ mkEntry [ ἔ ⨾ ρ ⨾ γ ⨾ α ] (exact (from-end 0)) ·                                      -- ἔργα
  ∷ mkEntry [ π ⨾ τ ⨾ ε ⨾ ρ ⨾ ό ⨾ ε ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·                  -- πτερόεντα
  ∷ mkEntry [ δ ⨾ ο ⨾ υ ⨾ ρ ⨾ ὶ ] (exact (from-end 0)) ·                                  -- δουρὶ
  ∷ mkEntry [ π ⨾ ο ⨾ ƛ ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·                                  -- πολλὰ
  ∷ mkEntry [ ἄ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·                                      -- ἄντα
  ∷ mkEntry [ κ ⨾ α ⨾ ƛ ⨾ ὰ ] (exact (from-end 0)) ·                                      -- καλὰ
  ∷ mkEntry [ ἐ ⨾ ƛ ⨾ ε ⨾ ε ⨾ ι ⨾ ν ⨾ ὰ ] (exact (from-end 0)) ·                          -- ἐλεεινὰ
  ∷ mkEntry [ ἐ ⨾ σ ⨾ σ ⨾ ι ] (exact (from-end 0)) ·                                      -- ἐσσι
  ∷ mkEntry [ ἐ ⨾ σ ⨾ τ ⨾ ὶ ] (exact (from-end 0)) ·                                      -- ἐστὶ
  ∷ mkEntry [ ὅ ⨾ θ ⨾ ι ] (exact (from-end 0)) ·                                          -- ὅθι
  ∷ mkEntry [ ε ⨾ ἰ ⨾ ν ⨾ ὶ ] (exact (from-end 0)) ·                                      -- εἰνὶ
  ∷ mkEntry [ γ ⨾ υ ⨾ μ ⨾ ν ⨾ ω ⨾ θ ⨾ έ ⨾ ν ⨾ τ ⨾ α ] (exact (from-end 0)) ·              -- γυμνωθέντα
  ∷ mkEntry [ τ ⨾ ε ⨾ ι ⨾ χ ⨾ ε ⨾ σ ⨾ ι ⨾ π ⨾ ƛ ⨾ ῆ ⨾ τ ⨾ α ] (exact (from-start 2)) ·    -- τειχεσιπλῆτα
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ό ⨾ τ ⨾ η ] (exact (from-start 0)) ·                            -- ἀβρότη
  ∷ mkEntry [ ἀ ⨾ β ⨾ ρ ⨾ ο ⨾ τ ⨾ ά ⨾ ξ ⨾ ο ⨾ μ ⨾ ε ⨾ ν ] (exact (from-start 0)) ·        -- ἀβροτάξομεν
  ∷ []

lexLookup : Letters → Maybe Entry
lexLookup ls = go lexicon
  module ∣lexLookup∣ where
  go : List Entry → Maybe Entry
  go [] = nothing
  go (e ∷ es) = if matchesE e ls then just e else go es
