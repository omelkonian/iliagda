module Iliagda.Init where

open import Agda.Primitive public
  using () renaming (Set to Type)
open import Prelude.Init public
  -- hiding (module Word)
  hiding (module Word; Any; All)
open L public
  using (_∷ʳ_)
open L.Mem public
open L.NE public
  using (head; last; _⁺∷ʳ_) renaming (length to length⁺)
open Unary public
  using () renaming (_∪_ to _∪₁_; _∩_ to _∩¹_; _⊆_ to _⊆₁_)
open import Prelude.General public
open import Prelude.Lists public
open import Prelude.ToList public
open import Prelude.Functor public
open import Prelude.Bifunctor public
open import Prelude.DecEq public
open import Prelude.Decidable public
open import Prelude.InferenceRules public
open import Prelude.Ord public
open import Prelude.Anyable public
instance
  Anyable-List⁺ : Anyable {ℓ} List⁺
  Anyable-List⁺ .Any P = Any P ∘ toList
open import Prelude.Allable public

-- import Data.Vec.Relation.Binary.Pointwise.Inductive as V
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_) public
  renaming (Pointwise to VPointwise)

open import ListNotation public

variable
  X : Type
  n n′ m m′ : ℕ
