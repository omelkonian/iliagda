{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}
module Iliagda.Prosody where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core

{-
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

Context = List Letter -- the following letters

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

data StartsWithVowel : Context → Type where
  vowel :
    Vowel l
    ─────────────────────────
    StartsWithVowel (l ∷ ctx)

!_ : Quantity → Quantity
!_ = λ{ ─ → ·; · → ─ }

-- TODO: consider commas, full stops, etc.

module QuantityRules (next : Context) where

  FollowedBy : (Q : Context → Type) {P : Letter → Type} {ls : List Letter} →
    Any P ls → Type
  FollowedBy Q = λ where
    (here {xs = xs} _) → Q (xs ++ next)
    (there p) → FollowedBy Q p

  -- [522]
  data _↝_ : Syllable → Quantity → Type where

    longByNature :
      ( Any× Diphthong sy
      ⊎ Any ─Vowel sy
      ⊎ Any HasCircumflex sy )
      ────────────────────────
      sy ↝ ─

    longByPosition :
      (v∈ : Any Vowel sy) →
      ∙ FollowedBy
          (λ ctx → StartsWithDoubleConsonant ctx
                 ⊎ StartsWithTwoConsonants ctx)
          v∈
        ───────────────
        sy ↝ ─

    shortByNature :
      ∀ (v∈ : Any ·Vowel sy) →
      ∙ ¬ Any× Diphthong sy
      -- ∙ ¬ longByPosition sy
      ∙ ¬ FollowedBy
            (λ ctx → StartsWithDoubleConsonant ctx
                   ⊎ StartsWithTwoConsonants ctx)
                   v∈
        ───────────────────
        sy ↝ ·

  data _~∗_ : Syllable → Quantity → Type where

    [522] :
      sy ↝ q
      -- ∙ ¬ [1173] sy -- "regularly"
      ───────
      sy ~∗ q

    [1173] :
      (v∈ : Any Vowel sy) →
      ∙ LastAny v∈
      ∙ FollowedBy StartsWithVowel v∈
        ─────────────────────────────
        sy ~∗ ·

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

instance
  -- (1180)
  -- There are six feet to the verse...
  Complies-MQs-HM : Quantities n -compliesWith- Hexameter n
  Complies-MQs-HM ._~_ = _~′_
    module ∣Complies-MQs-HM∣ where

      -- (1184)
      -- The last syllable of a verse is considered long (due to pause).
      mkLastLong : n > 0 → Vec Quantity n → Vec Quantity n
      mkLastLong {n = suc n} _ = V._[ ultIndex ]≔ ─
        where ultIndex = Fi.fromℕ n

      data _~′_ : Vec (Maybe Quantity) n → Hexameter n → Type where

        reify :
          ∙ mqs -masks*- qs
          ∙ mkLastLong (Hex>0 hm) qs ~ hm
            ─────────────────────────────
            mqs ~′ hm

CircumflexPenult : Pred₀ (Word (2 + n))
CircumflexPenult (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = Any HasCircumflex penult

circumflexPenult? : (w : Word (2 + n)) → Dec (CircumflexPenult w)
circumflexPenult? (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = dec

data _~↓↓ʷ_ : (Word n × Context) → Quantities n → Type where

  base :
    (unword w , ctx) ~ mqs
    ──────────────────────
    (w , ctx) ~↓↓ʷ mqs

data VLast (P : A → Type) : Vec A (suc n) → Type where
  here :
    P x
    ─────────────
    VLast P [ x ]

  there : ∀ {xs : Vec A (suc n)} →
    VLast P xs
    ────────────────
    VLast P (x ∷ xs)

_∶⋯_ : Vec A (suc n) → A → Type
xs ∶⋯ x = VLast (_≡ x) xs

V-init : Vec A (suc n) → Vec A n
V-init = λ where
  (x ∷ []) → []
  (x ∷ xs@(_ ∷ _)) → x ∷ V-init xs

_∶⋯_∣_ : Vec A (2 + n) → A → A → Type
xs ∶⋯ penult ∣ ult
  = (xs ∶⋯ ult)
  × (V-init xs ∶⋯ penult)

_∶⋯_∣_∣_ : Vec A (3 + n) → A → A → A → Type
xs ∶⋯ antepenult ∣ penult ∣ ult
  = (xs ∶⋯ ult)
  × (V-init xs ∶⋯ penult)
  × (V-init (V-init xs) ∶⋯ antepenult)

variable antepenult : Syllable

_≔ₙ_ : Quantities (1 + n) → Quantity → Quantities (1 + n)
_≔ₙ_ {n = n} mqs q = mqs V.[ lastIndex ]≔ just q
  where lastIndex = Fi.fromℕ n

_≔ₙ₋₁_ : Quantities (2 + n) → Quantity → Quantities (2 + n)
_≔ₙ₋₁_ {n = n} mqs q = mqs V.[ penultIndex ]≔ just q
  where penultIndex = Fi.inject₁ $ Fi.fromℕ n

infix 10 _≔ₙ_ _≔ₙ₋₁_

data _~↓ʷ_ : (Word n × Context) → Quantities n → Type where

  -- The vowel of the ultima in every word
  -- having the circumflex on the penult is short.
  [1160] :
    ∙ unword w ∶⋯ penult ∣ ult
    ∙ Any HasCircumflex penult
    ∙ (w , ctx) ~↓↓ʷ mqs
      ────────────────────────
      (w , ctx) ~↓ʷ (mqs ≔ₙ ·)

  -- If a long, penult has the acute accent,
  -- then the ultima must be long also.
  [1161] :
    ∙ unword w ∶⋯ penult ∣ ult
    ∙ toList ult ⊢ penult ↝ ─
    ∙ Any HasAcute penult
    ∙ (w , ctx) ~↓↓ʷ mqs
      ────────────────────────
      (w , ctx) ~↓ʷ (mqs ≔ₙ ─)

  -- If the ultima is short and the penult has the acute accent,
  -- then the penult must be short also.
  [1162] :
    ∙ unword w ∶⋯ penult ∣ ult
    ∙ ctx ⊢ ult ↝ ·
    ∙ Any HasAcute penult
    ∙ (w , ctx) ~↓↓ʷ mqs
      ──────────────────────────
      (w , ctx) ~↓ʷ (mqs ≔ₙ₋₁ ·)

  -- If the antepenult has the accent,
  -- the vowel of the ultima must be short.
  [1163] :
    ∙ unword w ∶⋯ antepenult ∣ penult ∣ ult
    ∙ Any HasAccent antepenult
      ─────────────────────────────────────
      (w , ctx) ~↓ʷ (mqs ≔ₙ ·)

FinalDiphthong : Pred₀ (Letter × Letter)
FinalDiphthong = _∈
  ( (α , ι)
  ∷ (α , ὶ)
  ∷ (ο , ι)
  ∷ (ο , ῖ)
  ∷ (ο , ἰ)
  ∷ (ο , ὶ)
  ∷ (ο , ί)
  ∷ []
  )

-- (1164) exception rules
data EndsInDiphthong : Word n → Type where
  finalDipthong :
    ∙ unword w ∶⋯ ult
    ∙ Any× FinalDiphthong ult
      ───────────────────────
      EndsInDiphthong w

data _~ʷ_ : (Word n × Context) → Quantities n → Type where

  [1164] :
    ∙ EndsInDiphthong w
    ∙ (w , ctx) ~↓↓ʷ mqs
      ──────────────────
      (w , ctx) ~ʷ mqs

  [1165] :
    ∙ ApparentException w
    ∙ (w , ctx) ~↓↓ʷ mqs
      ──────────────────
      (w , ctx) ~ʷ mqs

  fromBelow :
    ∙ ¬ EndsInDiphthong w
    ∙ ¬ ApparentException w
    ∙ (w , ctx) ~↓ʷ mqs
      ───────────────────
      (w , ctx) ~ʷ mqs

instance
  Complies-W-MQs : (Word n × Context) -compliesWith- Quantities n
  Complies-W-MQs ._~_ = _~ʷ_

{-
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

      wctx : Context
      wctx = maybe toList [] nextSy
    in
    ∙ (w , wctx) ~ mqs
    ∙ ws ~ʷˢ mqs′
      ────────────────
      (w ∷ ws) ~ʷˢ mqs₀

instance
  Complies-Ws-MQs : Words n -compliesWith- Quantities n
  Complies-Ws-MQs ._~_ = _~ʷˢ_

{-
  Complies-Ws-HM : Words n -compliesWith- Hexameter n′
  Complies-Ws-HM ._~_ = _~↑′_
    -- NB: note duality with [1160]
    module ∣Complies-Ws-HM∣ where

      data _~′_ : Words n → Hexameter n → Type where

        _~∘~_ : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n} →
          ∙ ws  ~ mqs
          ∙ mqs ~ hm
            ────────
            ws ~′ hm

      open import Iliagda.Prosody.Synizesis

      data _~↑′_ : Words n → Hexameter n′ → Type where

        fromBelow :
          ws ~′ hm
          ─────────
          ws ~↑′ hm

        -- synezesis
        [586] : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n}
                  {sys′ : Vec Syllable n′} {hm : Hexameter n′} →
          ∀ (syn : unwords ws -synezizes*- sys′) →
          ∙ ws ~ mqs
          ∙ NonDerivable mqs
          ∙ synezize syn mqs ~ hm
          -- it is a minimal synezesis
          -- ∙ (∀ {n″}
          --      {sys″ : Vec Syllable n″}
          --      {hm′ : Hexameter n″}
          --      {syn′ : unwords ws -synezizes*- sys″}
          --      → synezize syn′ mqs ~ hm′
          --      → syn ≼ syn′)
            ─────────────────────
            ws ~↑′ hm

open ∣Complies-Sy-MQ∣ public
  hiding (_~′_)
open ∣Complies-MQs-HM∣ public
  hiding (_~′_)
open ∣Complies-Ws-HM∣ public
  hiding (_~′_)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
