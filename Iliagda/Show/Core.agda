{-# OPTIONS --safe #-}
module Iliagda.Show.Core where

open import Iliagda.Init

pad : String → ℕ → String
pad s n = let ∣s∣ = Str.length s in
  if ∣s∣ Nat.<ᵇ n then
    s ◇ fromList (L.replicate (n ∸ ∣s∣) ' ')
  else
    s

merge spaces lines : List String → String
merge  = Str.intersperse ""
spaces = Str.intersperse " "
lines  = ("\n" ◇_) ∘ Str.intersperse "\n\n"

merged spaced lined : ⦃ Show A ⦄ → List A → String
merged = merge ∘ map show
spaced = spaces ∘ map show
lined  = lines ∘ map show

padded : ⦃ Show A ⦄ → ⦃ Show B ⦄ → List A → List B → String
padded xs ys =
  let
    `xs = map show xs
    ns  = map Str.length `xs
  in
    spaces `xs ◇ "\n"
  ◇ spaces (map (uncurry pad) $ L.zip (map show ys) ns )

instance
  Show-∃ : ∀ {P : A → Type} → ⦃ Show¹ P ⦄ → Show (∃ λ a → P a)
  Show-∃ .show (_ , p) = show p

  Show-Pad : ⦃ Show A ⦄ → ⦃ Show B ⦄ → ⦃ ToList X A ⦄ → ⦃ ToList Y B ⦄ → Show (X × Y)
  Show-Pad .show (xs , ys) = padded (toList xs) (toList ys)
