module Iliagda.Prosody where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core

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

-- _≤ᵐ_ : Rel₀ (Maybe X)
-- _≤ᵐ_ = λ where
--   nothing  (just _) → ⊤
--   x        y        → x ≡ y

private variable x : X; mx : Maybe X

data _≤ᵐ_ : Rel₀ (Maybe X) where
  forget : nothing ≤ᵐ just x
  refl   : mx      ≤ᵐ mx

Subsumes : Rel₀ (Vec (Maybe X) n)
Subsumes = VPointwise _≤ᵐ_

_ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
             (just q  ∷ just q′ ∷ nothing ∷ [])
_ =           forget  ∷ refl    ∷ refl    ∷ []

_ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
             (just q  ∷ just q′ ∷ just q  ∷ [])
_ =           forget  ∷ refl    ∷ forget  ∷ []

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

  Complies-Qs-PM : Vec Quantity n -compliesWith- Meter n m
  Complies-Qs-PM ._~_ = _~′_
    module ∣Complies-Qs-PM∣ where
      data _~′_ : Vec Quantity n → Meter n m → Type where

        [] :
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

  Complies-MQs-PM : Vec (Maybe Quantity) n -compliesWith- Hexameter n
  Complies-MQs-PM ._~_ = _~″_
    module ∣Complies-MQs-PM∣ where
      data _~′_ : Vec (Maybe Quantity) n → Hexameter n → Type where

        just : ∀ {qs : Vec Quantity n} {pm : Hexameter n} →

          qs ~ pm
          ─────────────────────
          V.map just qs ~′ pm

        reify :

          ∙ Subsumes mqs mqs′
          ∙ mqs′ ~′ pm
            ─────────────────
            mqs ~′ pm

      mkLastLong : Vec (Maybe Quantity) n → Vec (Maybe Quantity) n
      mkLastLong {n = 0} = id
      mkLastLong {n = suc n} = V._[ lastIndex ]≔ just ─
        where lastIndex : Fin (suc n)
              lastIndex = F.fromℕ n

      data _~″_ : Vec (Maybe Quantity) n → Hexameter n → Type where
        [1184] :
          mkLastLong mqs ~′ pm
          ────────────────────
          mqs ~″ pm

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
          ∙ (∀ (pm : Hexameter n) → mqs ≁ pm)
          ∙ synizize syn mqs ~ pm -- TODO: accept only minimal synizeses
            ──────────────────────────────────────────────────────────
            ws ~↑′ pm

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
open ∣Complies-Ws-HM∣ public
  hiding (_~′_)

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
