
# Default logic

There's a connection between our negation-stratification and default logic's "exceptional" construction.

# Defeasible logic

There's a connection between proving decidability of our rules and defeasible logic's separation between logic and "defeasible" inference.

# Three-valued logic

Is there a connection between our "Maybe Quantity" (ambiguous roles) with 3-valued logic?


# CONTRIBUTIONS

- Type-checked prosody rules
-
- Deciding derivability
  ⇒ proof-by-computation for automatic closed-term proving
- Deciding non-derivability
  ⇒ provably the most "unmetrical" lyric of Homer :)


# BIBLIOGRAPHY


# DUMP

- Alternative definition of synezesis
```agda
module _ {A : Type} {P : A × A → Type} (_⊗_ : A → A → A) where
  map× : (xs : List A) → Any× P xs → List A
  map× (x ∷ y ∷ xs) (here px) = (x ⊗ y) ∷ xs
  map× (x ∷ xs@(_ ∷ _)) (there ∃p) = map× xs ∃p

SynezisedDiphthong : Pred₀ (Syllable × Syllable)
SynezisedDiphthong = {!!}
    -- ∙ x ends in vowel
    -- ∙ y begins in vowel

_-synezizes¹-_ : List Syllable → List Syllable → Type
sys -synezizes¹- sys′ =
  ∃ λ (∃p : Any× SynezisedDiphthong sys) →
    sys′ ≡ map× _++_ sys ∃p
```
