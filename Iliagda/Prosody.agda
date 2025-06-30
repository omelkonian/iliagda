module Iliagda.Prosody where

open import Iliagda.Init
open import Iliagda.Morphology

data Quantity : Type where
  · {- short -} : Quantity
  ─ {- long  -} : Quantity
unquoteDecl DecEq-Quantity = DERIVE DecEq [ quote Quantity , DecEq-Quantity ]

data Foot : (n : ℕ) {- syllables -} → Vec Quantity n → Type where
  ─·· {- dactyl -} : Foot 3 (─ ∷ · ∷ · ∷ [])
  ──  {- sponde -} : Foot 2 (─ ∷ ─ ∷ [])
unquoteDecl DecEq-Foot = DERIVE DecEq [ quote Foot , DecEq-Foot ]
∃∃Foot = ∃ (∃ ∘ Foot)

Feet = List ∃∃Foot

-- PartialMeter : ℕ {- syllables -} → ℕ {- feet -} → Type
-- PartialMeter n m = ∃ λ (fs : List ∃∃Foot) → (n ≡ ∑₁ fs) × (m ≡ length fs)

data PartialMeter : ℕ {- syllables -} → ℕ {- feet -} → Type where
  mkPM : (fs : Feet) → PartialMeter (∑₁ fs) (length fs)

Meter = ∃ λ n → PartialMeter n 6
-- Meter = (∃ λ n → PartialMeter n 5) × ∃ (Foot 2)
-- -- NB: actually Vec Foot 5 ∷ ──
-- data Meter : Type where
--   mkMeter : PartialMeter n 5 → ∃ (Foot 2) → Meter

variable
  q q′ : Quantity
  qs qs′ : Vec Quantity n
  mq mq′ mq″ : Maybe Quantity
  mqs mqs′ : Vec (Maybe Quantity) n
  pm  : PartialMeter n m
  pm′ : PartialMeter n′ m′
  meter meter′ : Meter

_∷ᵖᵐ_ : Foot n qs → PartialMeter n′ m′ → PartialMeter (n + n′) (1 + m′)
f ∷ᵖᵐ (mkPM fs) = mkPM ((-, -, f) ∷ fs)

-- (519)
─Vowel ·Vowel Doubtful HasCircumflex : Pred₀ Letter
─Vowel = _∈ [ ῆ ⨾ η ⨾ ἣ ⨾ ω ]
·Vowel = _∈ [ ἔ ⨾ ε ⨾ έ ⨾ ο ]
-- Doubtful = _∈ [ ἄ ⨾ ὰ ⨾ ά ⨾ Ἀ ⨾ ι ⨾ ϊ ⨾ ί ⨾ υ ] -- (n)either long or short
Doubtful      = (¬_ ∘ ─Vowel) ∩¹ (¬_ ∘ ·Vowel)
HasCircumflex = _∈ [ ῆ ]

HasCircumflex⇒─Vowel : HasCircumflex ⊆₁ ─Vowel
HasCircumflex⇒─Vowel (here refl) = auto

-- (518)
DoubleConsonant : Pred₀ Letter
DoubleConsonant = _∈ [] -- ζ ξ ψ

-- (504)
Diphthong : Pred₀ (Letter × Letter)
Diphthong = _∈
  [ (α , ι)
  ⨾ (α , υ)
  ⨾ (ε , ι)
  ⨾ (ε , υ)
  ⨾ (η , υ)
  ⨾ (ο , ι)
  ⨾ (ο , ῖ)
  ⨾ (ο , υ)
  ⨾ (ο , ὐ)
  ⨾ (υ , ι)
  ⨾ (ω , υ)
  ]

VowelBeforeDoubleConsonant DoubleVowel : Pred₀ (Letter × Letter)
VowelBeforeDoubleConsonant (v , c) = Vowel v × DoubleConsonant c
DoubleVowel (v , v′) = Vowel v × Vowel v′

VowelBeforeTwoConsonants : Pred₀ (Letter × Letter × Letter)
VowelBeforeTwoConsonants (v , c , c′) = Vowel v × Consonant c × Consonant c′

-- TODO: generalize?
Any× : Pred₀ (X × X) → Pred₀ (List⁺ X)
Any× P = Any P ∘ pairs ∘ toList

triples : List X → List (X × X × X)
triples = map (map₁ proj₁) ∘ pairs ∘ pairs

Any×₃ : Pred₀ (X × X × X) → Pred₀ (List⁺ X)
Any×₃ P = Any P ∘ triples ∘ toList

-- (522)
─Syllable : Pred₀ Syllable
─Syllable
  =  Any ─Vowel     -- \ by nature
  ∪₁ Any× Diphthong -- /
  ∪₁ Any×₃ VowelBeforeTwoConsonants  -- \ by position
  ∪₁ Any× VowelBeforeDoubleConsonant -- /
  ∪₁ Any× DoubleVowel -- by synizesis

-- (519)??
·Syllable : Pred₀ Syllable
-- ·Syllable = ¬_ ∘ ─Syllable
·Syllable = Any ·Vowel
-- ·Syllable = All (¬ ─Vowel)

private
  _ : ¬ ─Syllable [ ν ⨾ ι ⨾ ν ]
  _ = auto

  _ : ¬ ·Syllable [ ν ⨾ ι ⨾ ν ]
  _ = auto

  _ : ─Syllable [ μ ⨾ ῆ ]
  _ = auto

  -- * not actually syllables... see NB on Syllable type
  _ : ─Syllable [ η ⨾ ε ]
  _ = auto

  _ : ·Syllable [ η ⨾ ε ]
  _ = auto

Subsumes : Rel₀ (Vec (Maybe X) n)
Subsumes = VPointwise _≤ᵐ_
  where
    _≤ᵐ_ : Rel₀ (Maybe X)
    _≤ᵐ_ = λ where
      nothing  (just _) → ⊤
      x        y        → x ≡ y
-- T0D0: Subsumes ⁇

_ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
             (just q  ∷ just q′ ∷ nothing ∷ [])
_ = tt ∷ refl ∷ refl ∷ []

_ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
             (just q  ∷ just q′ ∷ just q ∷ [])
_ = tt ∷ refl ∷ tt ∷ []

-- A complies with B
record _-compliesWith-_ (A B : Type) : Type₁ where
  infix 0 _~_
  field _~_ : A → B → Type
  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_
open _-compliesWith-_ ⦃ ... ⦄ public

instance
  Complies-Sy-MQ : Syllable -compliesWith- Maybe Quantity
  Complies-Sy-MQ ._~_ = _~′_
    module ∣Complies-Sy-MQ∣ where
      data _~′_ : Syllable → Maybe Quantity → Type where

        long  :

          ─Syllable sy
          ───────────────
          sy ~′ just ─

        short :

          ·Syllable sy
          ───────────────
          sy ~′ just ·

        ambiguous :

          ∙ ¬ ─Syllable sy
          ∙ ¬ ·Syllable sy
            ───────────────
            sy ~′ nothing

  -- ** more general instance of `Complies-Sys-MQs`
  -- Complies-Vec : ∀ {A B : Type} ⦃ _ : A -compliesWith- B ⦄ →
  --   Vec A n -compliesWith- Vec B n
  -- Complies-Vec ._~_ = VPointwise _~_

  Complies-Sys-MQs : Vec Syllable n -compliesWith- Vec (Maybe Quantity) n
  Complies-Sys-MQs ._~_ = VPointwise _~_

  Complies-Qs-PM : Vec Quantity n -compliesWith- PartialMeter n m
  Complies-Qs-PM ._~_ = _~′_
    module ∣Complies-Qs-PM∣ where
      data _~′_ : Vec Quantity n → PartialMeter n m → Type where

        base :
          ─────────────
          [] ~′ mkPM []

        sponde :

          qs ~′ pm
          ───────────────────────────
          (─ ∷ ─ ∷ qs) ~′ (── ∷ᵖᵐ pm)

        dactyl :

          qs ~′ pm
          ────────────────────────────────
          (─ ∷ · ∷ · ∷ qs) ~′ (─·· ∷ᵖᵐ pm)

  Complies-MQs-PM : Vec (Maybe Quantity) n -compliesWith- PartialMeter n m
  Complies-MQs-PM ._~_ = _~′_
    module ∣Complies-MQs-PM∣ where
      data _~′_ : Vec (Maybe Quantity) n → PartialMeter n m → Type where

        base : ∀ {qs : Vec Quantity n} {pm : PartialMeter n m} →

          qs ~ pm
          ─────────────────────
          V.map just qs ~′ pm

        reify :

          ∙ Subsumes mqs mqs′
          ∙ mqs′ ~′ pm
            ─────────────────
            mqs ~′ pm

CircumflexPenult : Pred₀ (Word (suc (suc n)))
CircumflexPenult (word w)
  with _ ∷ penult ∷ _ ← V.reverse w
  = Any HasCircumflex penult

instance
  Complies-W-MQs : Word n -compliesWith- Vec (Maybe Quantity) n
  Complies-W-MQs ._~_ = _~′_
    module ∣Complies-W-MQs∣ where

      -- NB: replace with intrinsic function call graph (constructor C₁ ⋯ Cₙ).
      data _~↓_ : Word n → Vec (Maybe Quantity) n → Type where

        [1160] : ∀ {sys₀ : Vec Syllable (suc (suc n))}
                   ⦃ _ : V.reverse sys₀ ≡ ult ∷ penult ∷ sys ⦄
                   {mqs₀ : Vec (Maybe Quantity) (suc (suc n))}
                   ⦃ _ : V.reverse mqs₀ ≡ just · ∷ just ─ ∷ mqs ⦄ →

          ∙ sys₀ ~ (mqs V.∷ʳ mq V.∷ʳ mq′)
          -- mq -shouldBe- just ─
          ∙ CircumflexPenult (word sys₀)
          ∙ mq′ ≢ just ─ -- NB: should the ultima be a *doubtful vowel*
            ──────────────────────────────────────────────────────────
            word sys₀ ~↓ mqs₀

      ¬[1160] : ¬ CircumflexPenult w
              → ¬ w ~↓ mqs
      ¬[1160] ¬circum ([1160] _ circum _) = ⊥-elim $ ¬circum circum

      data _~′_ : Word n → Vec (Maybe Quantity) n → Type where

        base : ∀ {w : Word n} {mqs : Vec (Maybe Quantity) n} →

          ∙ ¬ w ~↓ mqs -- change to ∀ mqs′ → w ≁↓ mqs′
          ∙ unword w ~ mqs
            ───────────────
            w ~′ mqs

        fromBelow :

          w ~↓ mqs
          ────────
          w ~′ mqs

  Complies-Ws-MQs : Words n -compliesWith- Vec (Maybe Quantity) n
  Complies-Ws-MQs ._~_ = _~′_
    module ∣Complies-Ws-MQs∣ where
      data _~′_ : Words n → Vec (Maybe Quantity) n → Type where

        [] :

          ────────
          [] ~′ []

        _∷_ : ∀ {w : Word n}
                {mqs : Vec (Maybe Quantity) n}
                {ws : Words n′}
                {mqs′ : Vec (Maybe Quantity) n′}
                {mqs₀ : Vec (Maybe Quantity) (n + n′)}
                ⦃ _ : mqs₀ ≡ mqs V.++ mqs′ ⦄ →

          ∙ w  ~  mqs
          ∙ ws ~′ mqs′
            ────────────────
            (w ∷ ws) ~′ mqs₀

  Complies-Ws-PM : Words n -compliesWith- PartialMeter n m
  Complies-Ws-PM ._~_ = _~↑′_
    -- NB: note duality with [1160]
    module ∣Complies-Ws-PM∣ where

      data _~′_ : Words n → PartialMeter n m → Type where

        _~∘~_ : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n} →
          ∙ ws  ~ mqs
          ∙ mqs ~ pm
            ────────
            ws ~′ pm

      open import Iliagda.Prosody.Synizesis

      private
        MQ  = Maybe Quantity
        MQS = ∃ λ n → Vec (Maybe Quantity) n

        -- ⟦_⟧ : ∀ {sys sys′} (syn : sys -synizizes*- sys′) → MQS → MQS
        -- ⟦_⟧ = {!!}

      data _~↑′_ : Words n → PartialMeter n m → Type where

        fromBelow :
          ws ~′ pm
          ─────────
          ws ~↑′ pm

        -- synizesis
        -- TODO: change index bounds
        [586] : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n} →
          ∙ ws ~ mqs
          ∙ mqs ≁ pm -- change to ∀ mqs′ → ws ~ mqs′ → mqs′ ≁ pm
          -- TODO: add these
          -- ∀ (syn : unword ws -synizizes*- sys′) →
          -- ∙ (⟦ syn ⟧ mqs) ~′ pm
            ──────────────────────────────────────────────────────────
            ws ~↑′ pm

      --   [586] : -- let sys = L.concat ws in
      --     ∙ ¬ ws ~′ pm
      --   -- ∙ sys ~synizise~ sys′{(i,j),...}

      --   -- ∙ ws[(i,j)/...] ~′ pm

      --   -- ∙ ws[sys/sys′] ~′ pm
      --       ──────────────────────────────────────────────────────────
      --       ws ~↑′ pm

-- Complies-V-PM : Verse -compliesWith- PartialMeter
-- Complies-V-PM ._~_ = ?

open ∣Complies-Sy-MQ∣ public
  hiding (_~′_)
open ∣Complies-Qs-PM∣ public
  hiding (_~′_)
open ∣Complies-MQs-PM∣ public
  hiding (_~′_)
-- open ∣Complies-Sys-PM∣
open ∣Complies-W-MQs∣ public
  hiding (_~′_)
open ∣Complies-Ws-MQs∣ public
  hiding (_~′_)
open ∣Complies-Ws-PM∣ public
  hiding (_~′_)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
