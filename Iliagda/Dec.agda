-- ** decision procedures
module Iliagda.Dec where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Prosody

-- ** VPointwise
instance
  Dec-VPointwise : ∀ {_~_ : X → Y → Type ℓ} {xs : Vec X n} {ys : Vec Y n} →
    ⦃ _~_ ⁇² ⦄ → VPointwise _~_ xs ys ⁇
  Dec-VPointwise .dec = VP.decidable dec² _ _
    where import Data.Vec.Relation.Binary.Pointwise.Inductive as VP

-- ** Subsumes
module _ ⦃ _ : DecEq X ⦄ where instance
  Dec-masks : ∀ {mx : Maybe X}{y} → (mx -masks- y) ⁇
  Dec-masks {mx = mx} {y = y} .dec
    with mx
  ... | nothing = yes mask
  ... | just x  = mapDec (λ where refl → refl) (λ where refl → refl) (x ≟ y)

_ : (nothing ∷ just ─ ∷ nothing ∷ []) -masks*-
    (q       ∷ ─      ∷ q       ∷ [])
_ = auto

-- ** Complies-with
instance
  Dec-Complies-Sy-MQ : _~_ {A = Syllable} {B = Maybe Quantity} ⁇²
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

_ : _~_ {A = Vec Syllable n} {B = Vec (Maybe Quantity) n} ⁇²
_ = it

-- instance
--   Dec-Complies-Qs-PM : _~_ {A = Vec Quantity n} {B = Meter n m} ⁇²
--   Dec-Complies-Qs-PM {x = qs}{pm} .dec = {!qs!}
