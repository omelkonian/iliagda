module Iliagda.Prosody.Rules.Level4 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
-- open import Iliagda.Prosody.Rules.Level23

-- ** LEVEL 4: meter structure

private variable x : X; mx : Maybe X

data _-masks-_ {X : Type} : Maybe X → X → Type where
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
  Complies-MQs-HM : Quantities n -compliesWith- Hexameter n
  Complies-MQs-HM ._~_ = _~′_
    module ∣Complies-MQs-HM∣ where
      -- (1184)
      -- The last syllable of a verse is considered long (due to pause).
      mkLastLong : n > 0 → Vec Quantity n → Vec Quantity n
      mkLastLong {n = suc n} _ = V._[ ultIndex ]≔ ─
        where ultIndex = Fi.fromℕ n

      data _~′_ : Quantities n → Hexameter n → Type where
        reify :
          ∙ mqs -masks*- qs
          ∙ mkLastLong (Hex>0 hm) qs ~ hm
            ─────────────────────────────
            mqs ~′ hm

  Complies-Ws-HM : Words n -compliesWith- Hexameter n′
  Complies-Ws-HM ._~_ = _~′_
    module ∣Complies-Ws-HM∣ where
      open import Iliagda.Prosody.Synizesis

      data _~′_ : Words n → Hexameter n′ → Type where

        _~∘~⟨_⟩_ : ∀ {ws : Words n} {mqs : Quantities n} →
                     {sys′ : Vec Syllable n′} {hm : Hexameter n′} →
          ∙ ws ~ mqs
          -- [586] synezesis
          → (syn : unwords ws -synezizes*- sys′) →
          ∙ synezize syn mqs ~ hm
            ────────────────────────────────────
            ws ~′ hm

      --   _~∘~⟨_⟩_ : ∀ {ws : Words n} {mqs : Quantities n} →
      --                {sys′ : Vec Syllable n′} {hm : Hexameter n′} →
      --     -- ∙ ws ~ mqs
      --     ∙ ws 𝟚.~ʷˢ mqs
      --     -- [586] synezesis
      --     → (syn : unwords ws -synezizes*- sys′) →
      --     let mqs = synezize syn mqs⊗ in
      --     ∙ ws 𝟛.~ʷˢ mqs′
      --     let mqs⊗ = mqs ⊗ mqs′ in
      --     ∙ mqs⊗ ~ hm
      --       ────────────────────────────────────
      --       ws ~′ hm
