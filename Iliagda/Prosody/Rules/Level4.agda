module Iliagda.Prosody.Rules.Level4 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core

-- ** LEVEL 4: meter structure

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
