module Iliagda.Prosody.Rules.Level3 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core

-- ** LEVEL 3: syllable context

-- data LastAny {xs : List A} {P : A → Type} : Any P xs → Type where
--   isLastAny : (p : P x) → LastAny (here {xs = []} p)
LastAny : ∀ {xs : List A} {P : A → Type} → Any P xs → Type
LastAny = λ where
  (here {xs = xs} _) → xs ≡ []
  (there p)          → LastAny p

-- (522)
-- We have to look at the next syllable for "vowel before".
-- (523)
-- We might also need to look at the next word
-- (in the case of the final syllable of a word).

data Context : Type where

  inner : Syllable → Context

  outer : Syllable → Context

  -- = List Letter -- the following letters

variable ctx ctx′ : Context

data StartsWithDoubleConsonant : Context → Type where
  doubleConsonant :
    DoubleConsonant l
    ───────────────────────────────────
    StartsWithDoubleConsonant (l ∷ ctx)

data StartsWithTwoConsonants : Context → Type where
  twoConsonants :
    ∙ Consonant l
    ∙ Consonant l′
      ──────────────────────────────────────
      StartsWithTwoConsonants (l ∷ l′ ∷ ctx)

Mute Liquid Nasal : Letter → Type
Mute   = _∈ [ π ⨾ β ⨾ φ ⨾ κ ⨾ γ ⨾ χ ⨾ τ ⨾ δ ⨾ θ ]
Liquid = _∈ [ ƛ ⨾ ρ ]
Nasal  = _∈ [ μ ⨾ ν ]

-- TODO: inner ctx
data MuteThenLiquid : Context → Type where
  twoConsonants :
    ∙ Mute l
    ∙ Liquid l′ ⊎ Nasal l′
      ──────────────────────────────────────
      StartsWithTwoConsonants (l ∷ l′ ∷ ctx)

data StartsWithVowel : Context → Type where
  vowel :
    Vowel l
    ─────────────────────────
    StartsWithVowel (l ∷ ctx)

!_ : Quantity → Quantity
!_ = λ{ ─ → ·; · → ─ }

-- TODO: consider commas, full stops, etc.

module QuantityRules (next : Context) where

  -- TODO: fix!! inner/outer
  FollowedBy : (Q : Context → Type) {P : Letter → Type} {ls : List Letter} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = xs} _) → Q (xs ++ next)
    (there p) → FollowedBy Q p

  -- [522]
  data _↝_ : Syllable → Quantity → Type where

    longByPosition :
      (v∈ : Any Vowel sy) →
      -- ∙ ¬ [526/1167.2] ... (lexicon-based)
      ∙ FollowedBy
          (λ ctx → StartsWithDoubleConsonant ctx
                 ⊎ StartsWithTwoConsonants ctx)
          v∈
        ───────────────
        sy ↝ ─


  data _~∗_ : Syllable → Quantity → Type where

    {- TODO: apparent exception 526/1167.2, lexicon-based -}

    [522] :
      sy ↝ q
      -- ∙ ¬ [1173] sy -- "regularly"
      ───────
      sy ~∗ q

    -- (572)
    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ LastAny v∈
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ ·

    -- mutes followed by liquids within the same word make a short syllable
    -- either long or short according to the needs of the verse
    -- (a.k.a. *common* syllable)
    [524] :
      (v∈ : Any Vowel sy) →
      ∙ sy ~ ·
      ∙ FollowedBy MuteThenLiquid v∈
        ────────────────────────────
        sy ~∗ q

  _≁∗_ = λ x y →  ¬ (x ~∗ y)

  data _~?_ : Syllable → Maybe Quantity → Type where

    ambiguous :
      (∀ q → sy ≁∗ q)
      ───────────────
      sy ~? nothing

    ambivalent :
      ∙ sy ~∗ ─
      ∙ sy ~∗ ·
        ─────────────
        sy ~? nothing

    certain :
      ∙ sy ~∗ q
      ∙ sy ≁∗ (! q)
        ────────────
        sy ~? just q

  ─Syllable = _~? just ─
  ·Syllable = _~? just ·

open QuantityRules
  renaming ( _↝_ to _⊢_↝_
           ; _~∗_ to _⊢_~∗_; _≁∗_ to _⊢_≁∗_
           ; _~?_ to _⊢_~?_)

instance
  Complies-Sy-MQ : (Syllable × Context) -compliesWith- Maybe Quantity
  Complies-Sy-MQ ._~_ = _~′_
    module ∣Complies-Sy-MQ∣ where
      data _~′_ : Syllable × Context → Maybe Quantity → Type where

        ambiguous :
          (∀ q → ctx ⊢ sy ≁∗ q)
          ─────────────────────
          (sy , ctx) ~′ nothing

        ambivalent :
          ∙ (ctx ⊢ sy ~∗ ─)
          ∙ (ctx ⊢ sy ~∗ ·)
            ─────────────────────
            (sy , ctx) ~′ nothing

        certain :
          ∙ ctx ⊢ sy ~∗ q
          ∙ ctx ⊢ sy ≁∗ (! q)
            ────────────────────
            (sy , ctx) ~′ just q

inContext : Vec Syllable n × Context → Vec (Syllable × Context) n
inContext (sys , ctx) = go sys
  where
  go : Vec Syllable n → Vec (Syllable × Context) n
  go = λ where
    [] → []
    [ sy ] → [ sy , ctx ]
    (sy ∷ sys@(sy′ ∷ _)) → (sy , toList sy′) ∷ go sys

instance
  Complies-Sys-MQs : (Vec Syllable n × Context) -compliesWith- Quantities n
  Complies-Sys-MQs ._~_ = VPointwise _~_ ∘ inContext

  Complies-Ws-MQs : Words n -compliesWith- Quantities n
  Complies-Ws-MQs ._~_ ws qs = (unwords ws , []) ~ qs

-- -}
-- -}
-- -}
-- -}
