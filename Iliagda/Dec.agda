-- ** decision procedures
module Iliagda.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody

instance
  Dec-Complies-Sy-MQ : _~_ ⁇²
  Dec-Complies-Sy-MQ {x = sy}{mq} .dec
    with ¿ ─Syllable sy ¿ | ¿ ·Syllable sy ¿ | mq
  ... | yes ─sy | _ | just ─
    = yes $ long ─sy
  ... | _ | yes ·sy | just ·
    = yes $ short ·sy
  ... | no ¬─sy | no ¬·sy | nothing
    = yes $ ambiguous ¬─sy ¬·sy
  ... | _ | no ¬·sy | just ·
    = no λ where (short ·sy) → ¬·sy ·sy
  ... | no ¬─sy | _ | just ─
    = no λ where (long ─sy) → ¬─sy ─sy
  ... | yes ─sy | _ | nothing
    = no λ where (ambiguous ¬─sy _) → ¬─sy ─sy
  ... | _ | yes ·sy | nothing
    = no λ where (ambiguous _ ¬·sy) → ¬·sy ·sy

  import Data.Vec.Relation.Binary.Pointwise.Inductive as VPointwise

  Dec-Complies-Sys-MQs : _~_ {A = Vec Syllable n} ⁇²
  Dec-Complies-Sys-MQs .dec = VPointwise.decidable dec² _ _
