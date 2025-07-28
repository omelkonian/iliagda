{-# OPTIONS --safe #-}
module Iliagda.Dec.Core where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core

-- ** decidable equality
unquoteDecl DecEq-Letter = derive-DecEq [ quote Letter , DecEq-Letter ]
unquoteDecl DecEq-Quantity = derive-DecEq [ quote Quantity , DecEq-Quantity ]
-- unquoteDecl DecEq-Foot = derive-DecEq [ quote Foot , DecEq-Foot ]
instance
  DecEq-Foot : DecEq (Foot n qs)
  DecEq-Foot ._≟_ = λ where
    ──  ──  → yes refl
    ─·· ─·· → yes refl
