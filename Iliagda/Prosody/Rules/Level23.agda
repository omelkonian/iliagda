module Iliagda.Prosody.Rules.Level23 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1

import Iliagda.Prosody.Rules.Level2 as 𝟚
import Iliagda.Prosody.Rules.Level3 as 𝟛

open import Algebra using (Op₂)

-- ** LEVEL 2&3: merging information

_⊗₁_ : Op₂ $ Maybe Quantity
_⊗₁_ = λ where
  nothing mq → mq
  mq nothing → mq
  (just _) (just q′) → just q′

_⊗_ : Op₂ $ Quantities n
_⊗_ = V.zipWith _⊗₁_

data _~ʷˢ_ : Words n → Quantities n → Type where

  _∪_ :
     ∙ ws 𝟚.~ʷˢ mqs
     ∙ ws 𝟛.~ʷˢ mqs′
       ───────────────────
       ws ~ʷˢ (mqs ⊗ mqs′)

instance
  Complies-Ws-MQs : Words n -compliesWith- Quantities n
  Complies-Ws-MQs ._~_ = _~ʷˢ_

{- ** ALTERNATIVE DESIGNS

data _∪₁_≈_ : MQuantity n → MQuantity n → MQuantity n : Type where

  CLASH-LEFT :
     (just q) ∪₁ (just q′) ≈ just q

  CLASH-RIGHT :
     (just q) ∪₁ (just q′) ≈ just q′

  CLASH-RECONSIDER-LEFT :
    TRY LEVEL2~>3 DEPENDENCY
  CLASH-RECONSIDER-RIGHT :
    TRY LEVEL3~>2 DEPENDENCY


data _∪_ : Quantities n → Quantities n → Quantities n : Type where

  [] :
  _∷_

_∪_ : Quantities n → Quantities n → Quantities n
_∪_ = {!!}
  -- (ans , ans′) ← ....
  -- if left then
  --   inj₁ ans
  -- else if right then
  --   inj₂ ans
-}
