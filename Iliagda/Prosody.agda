{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}
module Iliagda.Prosody where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core

-- (522)
-- We have to look at the next syllable for "vowel before".
-- (523)
-- We might also need to look at the next word
-- (in the case of the final syllable of a word).

Context = List Letter -- the following consonants

module _ (next : Context) where
  ─Syllable : Pred₀ Syllable
  ─Syllable sy =
    (  Any ─Vowel     -- \ by nature
    ∪₁ Any× Diphthong -- /
    ∪₁ Any×₃ VowelBeforeTwoConsonants  -- \ by position
    ∪₁ Any× VowelBeforeDoubleConsonant -- /
    ) (sy L.NE.⁺++ next)

  ·Syllable : Pred₀ Syllable
  ·Syllable = (¬_ ∘ ─Syllable)
            ∩¹ (Any ·Vowel) -- beware of dipthongs (now covered by ─Syllable)

private
  _ : ¬ ─Syllable [] [ ν ⨾ ι ⨾ ν ]
  _ = auto

  _ : ¬ ·Syllable [] [ ν ⨾ ι ⨾ ν ]
  _ = auto

  _ : ─Syllable [] [ μ ⨾ ῆ ]
  _ = auto

  _ : ─Syllable [ κ ⨾ α ⨾ ι ] [ ν ⨾ ι ⨾ ν ]
  _ = auto

private variable x : X; mx : Maybe X

data _-masks-_ : Maybe X → X → Type where
  mask : nothing -masks- x
  refl : just x  -masks- x

_-masks*-_ : Vec (Maybe X) n → Vec X n → Type
_-masks*-_ = VPointwise _-masks-_

_ : (nothing ∷ just q′ ∷ nothing ∷ []) -masks*-
    (q       ∷ q′      ∷ q       ∷ [])
_ = mask     ∷ refl    ∷ mask    ∷ []

_ : (nothing ∷ just q′ ∷ nothing ∷ []) -masks*-
    (q       ∷ q′      ∷ q       ∷ [])
_ = mask     ∷ refl    ∷ mask    ∷ []

-- A complies with B
record _-compliesWith-_ (A B : Type) : Type₁ where
  infix 0 _~_
  field _~_ : A → B → Type
  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_

  NonDerivable NonDerivable∃ : A → Type
  NonDerivable  a = ∀ b → a ≁ b
  NonDerivable∃ a = ¬ ∃ λ b → a ~ b

  NonDerivable′ NonDerivable∃′ : B → Type
  NonDerivable′  b = ∀ a → a ≁ b
  NonDerivable∃′ b = ¬ ∃ λ a → a ~ b

  NonDerivable∃⇒ : ∀ {a} → NonDerivable∃ a → NonDerivable a
  NonDerivable∃⇒ ∄b b a~b = ∄b (b , a~b)

  NonDerivable∃′⇒ : ∀ {b} → NonDerivable∃′ b → NonDerivable′ b
  NonDerivable∃′⇒ ∄a a a~b = ∄a (a , a~b)

open _-compliesWith-_ ⦃ ... ⦄ public

private variable ctx : Context

firstConsonants : ⦃ _ : ToList A Letter ⦄ → A → List Letter
firstConsonants = L.takeWhile (λ l → ¿ Consonant l ¿) ∘ toList

inContext : Vec Syllable n × Context → Vec (Syllable × Context) n
inContext (sys , ctx) = go sys
  where
  go : Vec Syllable n → Vec (Syllable × Context) n
  go = λ where
    [] → []
    [ sy ] → [ sy , ctx ]
    (sy ∷ sys@(sy′ ∷ _)) → (sy , firstConsonants sy′) ∷ go sys

instance
  Complies-Sy-MQ : (Syllable × Context) -compliesWith- Maybe Quantity
  Complies-Sy-MQ ._~_ = _~′_
    module ∣Complies-Sy-MQ∣ where
      data _~′_ : Syllable × Context → Maybe Quantity → Type where

        long  :

          ─Syllable ctx sy
          ────────────────────
          (sy , ctx) ~′ just ─

        short :

          ·Syllable ctx sy
          ────────────────────
          (sy , ctx) ~′ just ·

        ambiguous :

          ∙ ¬ ─Syllable ctx sy
          ∙ ¬ ·Syllable ctx sy
            ─────────────────────
            (sy , ctx) ~′ nothing

  Complies-Sys-MQs : (Vec Syllable n × Context) -compliesWith- Quantities n
  Complies-Sys-MQs ._~_ = VPointwise _~_ ∘ inContext

data _ˢ~ᵐ_ : Vec Quantity n → Meter n m → Type where

  [] :
    ─────────────
    [] ˢ~ᵐ mkPM []

  sponde :

    qs ˢ~ᵐ pm
    ───────────────────────────
    (─ ∷ ─ ∷ qs) ˢ~ᵐ (── ∷ᵖᵐ pm)

  dactyl :

    qs ˢ~ᵐ pm
    ────────────────────────────────
    (─ ∷ · ∷ · ∷ qs) ˢ~ᵐ (─·· ∷ᵖᵐ pm)

instance
  Complies-Qs-PM : Vec Quantity n -compliesWith- Meter n m
  Complies-Qs-PM ._~_ = _ˢ~ᵐ_

  -- (1180)
  -- There are six feet to the verse...
  Complies-MQs-PM : Quantities n -compliesWith- Hexameter n
  Complies-MQs-PM ._~_ = _~′_
    module ∣Complies-MQs-PM∣ where

      -- (1184)
      -- The last syllable of a verse is considered long (due to pause).
      mkLastLong : n > 0 → Vec Quantity n → Vec Quantity n
      mkLastLong {n = suc n} _ = V._[ ultIndex ]≔ ─
        where ultIndex = Fi.fromℕ n

      data _~′_ : Vec (Maybe Quantity) n → Hexameter n → Type where

        reify :
          ∙ mqs -masks*- qs
          ∙ mkLastLong (Hex>0 pm) qs ~ pm
            ─────────────────────────────
            mqs ~′ pm

CircumflexPenult : Pred₀ (Word (2 + n))
CircumflexPenult (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = Any HasCircumflex penult

circumflexPenult? : (w : Word (2 + n)) → Dec (CircumflexPenult w)
circumflexPenult? (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = dec

-- (1160)
-- The vowel of the ultima in every circumflex on the penult is short.
mkShortUltima : n > 1 → Quantities n → Quantities n
mkShortUltima {n = suc n@(suc _)} (s≤s (s≤s _)) = V._[ lastIndex ]≔ just ·
  where lastIndex = Fi.fromℕ n

[1160] : Word n → Quantities n → Quantities n
[1160] {n} w
  with ¿ n > 1 ¿
... | no _ = id
... | yes n>1@(s≤s (s≤s _)) =
  if ⌊ circumflexPenult? w ⌋ then
  -- NB: should we also require hat the ultima be a *doubtful vowel*?
    mkShortUltima n>1
  else
    id

data _~ʷ_ : (Word n × Context) → Quantities n → Type where

  base : ∀ {mqs} →

    (unword w , ctx) ~ mqs
    ─────────────────────────
    (w , ctx) ~ʷ [1160] w mqs

data _~ʷˢ_ : Words n → Vec (Maybe Quantity) n → Type where

  [] :
    ────────
    [] ~ʷˢ []

  _∷_ : ∀ {w : Word n}
          {mqs : Quantities n}
          {ws : Words n′}
          {mqs′ : Quantities n′}
          {mqs₀ : Quantities (n + n′)}
          ⦃ _ : mqs₀ ≡ mqs V.++ mqs′ ⦄ →

    let
      nextSy : Maybe Syllable
      nextSy = L.head $ toList $ unwords ws

      wctx = maybe firstConsonants [] nextSy
    in
    ∙ (w , wctx) ~ʷ mqs
    ∙ ws ~ʷˢ mqs′
      ────────────────
      (w ∷ ws) ~ʷˢ mqs₀

instance
  Complies-W-MQs : (Word n × Context) -compliesWith- Quantities n
  Complies-W-MQs ._~_ = _~ʷ_

  Complies-Ws-MQs : Words n -compliesWith- Quantities n
  Complies-Ws-MQs ._~_ = _~ʷˢ_

  Complies-Ws-HM : Words n -compliesWith- Hexameter n′
  Complies-Ws-HM ._~_ = _~↑′_
    -- NB: note duality with [1160]
    module ∣Complies-Ws-HM∣ where

      data _~′_ : Words n → Hexameter n → Type where

        _~∘~_ : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n} →
          ∙ ws  ~ mqs
          ∙ mqs ~ pm
            ────────
            ws ~′ pm

      open import Iliagda.Prosody.Synizesis

      data _~↑′_ : Words n → Hexameter n′ → Type where

        fromBelow :
          ws ~′ pm
          ─────────
          ws ~↑′ pm

        -- synizesis
        [586] : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n}
                  {sys′ : Vec Syllable n′} {pm : Hexameter n′} →
          ∀ (syn : unwords ws -synizizes*- sys′) →
          ∙ ws ~ mqs
          ∙ NonDerivable mqs
          ∙ synizize syn mqs ~ pm -- TODO: accept only minimal synizeses
            ─────────────────────
            ws ~↑′ pm

open ∣Complies-Sy-MQ∣ public
  hiding (_~′_)
open ∣Complies-MQs-PM∣ public
  hiding (_~′_)
open ∣Complies-Ws-HM∣ public
  hiding (_~′_)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
