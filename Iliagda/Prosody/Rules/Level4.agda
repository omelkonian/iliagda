-- ** LEVEL 4: meter structure

{-# OPTIONS --safe #-}
module Iliagda.Prosody.Rules.Level4 where

open import Iliagda.Init; open import Prelude.Vectors
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level2
open import Iliagda.Prosody.Rules.Level3
open import Iliagda.Prosody.Rules.Level23 using (_⊗_)

-- ** masking

private variable x : X

data _-masks-_ {X : Type} : Flat X → X → Type where
  none   : none      -masks- x
  all    : all       -masks- x
  single : single x  -masks- x

_-masks*-_ : Vec (Flat X) n → Vec X n → Type
_-masks*-_ = VPointwise _-masks-_

infix 2 _ˢ~ᵐ_
data _ˢ~ᵐ_ : Words n × Vec Quantity n → Meter n m → Type where

  [] :
    ───────────────────
    [] , [] ˢ~ᵐ mkPM []

  sponde : let ws = dropSys 2 ws′ in
    ws , qs ˢ~ᵐ pm
    ───────────────────────────────────
    ws′ , ─  ∷ ─ ∷ qs ˢ~ᵐ ── ∷ᵖᵐ pm

  dactyl : let ws = dropSys 3 ws′ in
    ws , qs ˢ~ᵐ pm
    ─────────────────────────────────────────
    ws′ , ─  ∷ · ∷ · ∷ qs ˢ~ᵐ ─·· ∷ᵖᵐ pm

  -- ** Lengthen-by-thesis
  -- Short syllables ending in a single consonant are occasionally
  -- lengthened in thesis (the accented or ictus-syllable), although
  -- the next word begins with a vowel.
  [1168] : let sy′ = firstSy ws in
    ∙ EndsWith [ Vowel ⨾ Consonant ] (toList sy)
    ∙ BeginsWith [ Vowel ] (toList sy′)
    ∙ word [ sy ] ∷ ws , ─ ∷ qs ˢ~ᵐ pm
      ───────────────────────────────────────────
      word [ sy ] ∷ ws , · ∷ qs ˢ~ᵐ pm

  -- ** 3rd-foot caesura
  -- There is almost always a caesura in the third foot.
  [1186] : ∀ {pm : Meter _ m} →
    ∙ m ≡ 4  -- start of 3rd foot ≈ 4 foots remaining
    ∙ word [ sy ] ∷ ws , ─ ∷ qs ˢ~ᵐ pm
      ───────────────────────────────────────────
      word [ sy ] ∷ ws , · ∷ qs ˢ~ᵐ pm

instance
  Complies-Qs-PM :
    (Words n × Vec Quantity n) -compliesWith- Meter n m
  Complies-Qs-PM ._~_ = _ˢ~ᵐ_

  -- (1180)
  -- There are six feet to the verse...
  Complies-MQs-HM : (Words n × Quantities n) -compliesWith- Hexameter n
  Complies-MQs-HM ._~_ = _~′_
    module ∣Complies-MQs-HM∣ where
      -- (1184)
      -- The last syllable of a verse is considered long (due to pause).
      data _~′_ : (Words n × Quantities n) → Hexameter n → Type where
        reify : {mqs : Quantities n} → let mkLastLong = _≔ₙ⟨ Hex>0 hm ⟩ single ─ in
          ∙ mkLastLong mqs -masks*- qs
          ∙ ws , qs ~ hm
            ─────────────────────────────────────
            (ws , mqs) ~′ hm

  Complies-Ws-HM : Words n -compliesWith- Hexameter n′
  Complies-Ws-HM ._~_ = _~′_
    module ∣Complies-Ws-HM∣ where

      data _~′_ : Words n → Hexameter n′ → Type where

        _≫⟨_⟩≫_≫_ : ∀ {ws : Words n} {sys′ : Syllables n′} {hm : Hexameter n′} →
          ∙ ws ~² mqs
          -- [586] synizesis
          → (syn : unwords ws -synizizes*- sys′) →
          let ws′ = synizizeWords ws syn in
          ∙ ws′ ~³ mqs′
          ∙ ws′ , synizize syn mqs ⊗ mqs′ ~ hm
            ──────────────────────────────────────────
            ws ~′ hm

Derivation : Words n → Type
Derivation ws = ∃ λ n′ → ∃ λ (hm : Hexameter n′) → ws ~ hm

Derivations : Words n → Type
Derivations ws = List (Derivation ws)
