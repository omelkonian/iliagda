{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level23 where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level2
open import Iliagda.Prosody.Rules.Level3

-- ** LEVEL 2&3: merging information

_⊗₁_ : Op₂ $ Flat Quantity
_⊗₁_ = λ where
  (single _) (single q) → single q  -- RIGHT BIASED
  -- (single q) (single q′) → if q == q′ then single q else *
  (single q) none → single q
  (single _) all → all              -- RIGHT BIASED
  none mq → mq
  all mq → mq                       -- IMPOSSIBLE

_⊗_ : Op₂ $ Quantities n
_⊗_ = V.zipWith _⊗₁_

data _~ʷˢ_ : Words n → Quantities n → Type where

  _∪_ :
     ∙ ws ~² mqs
     ∙ ws ~³ mqs′
       ───────────────────
       ws ~ʷˢ (mqs ⊗ mqs′)

instance
  Complies-Ws-MQs : Words n -compliesWith- Quantities n
  Complies-Ws-MQs ._~_ = _~ʷˢ_
