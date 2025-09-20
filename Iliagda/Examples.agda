{-# OPTIONS --safe #-}
module Iliagda.Examples where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody
open import Iliagda.Dec.Core
open import Iliagda.Dec
open import Iliagda.Verses
open import Iliagda.Show

--
NonEmpty : List A → Type
NonEmpty = λ where
  [] → ⊥
  (_ ∷ _) → ⊤

Derivable : Words n → Type
Derivable ws =
  -- length (allDerivations ws) > 0
  NonEmpty (allDerivations ws)
--
∃Derivations = ∃ λ n → ∃ λ (ws : Words n) → Derivations ws

instance
  Show-Derivations : Show (Derivations ws)
  -- Show-Derivations .show [] = "∅∅∅∅∅∅"
  -- Show-Derivations .show ds = lined ds
  Show-Derivations .show = lined

  Show-ManyDerivations : Show (List ∃Derivations)
  -- Show-ManyDerivations .show = lined
  Show-ManyDerivations .show dss =
    "\n" ◇ Str.intersperse "\n\n***************\n" (map show dss)
--

dss : List ∃Derivations
dss = map (λ (_ , v) → -, -, allDerivations v) verses

{- ** Interactively showing all derivations of given verses **

-- [C-u C-u C-c C-n] allDerivations v1

μῆ νιν ἄ ει δε θε ὰ Πη ƛη ϊ ά δε⁀ω Ἀ χι ƛῆ ος
─  ·   · ─  ·  ·  ─ ─  ─  · · ─    · ·  ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη⁀ϊ ά δε ω Ἀ χι ƛῆ ος
─  ·   · ─  ·  ·  ─ ─  ─    · ·  ─ · ·  ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη ϊ ά δε⁀ω Ἀ χι ƛῆ⁀ος
─  ·   · ─  ·  ·  ─ ─  ─  · · ─    ─ ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη ϊ⁀ά δε⁀ω Ἀ χι ƛῆ ος
─  ·   · ─  ·  ·  ─ ─  ─  ─   ─    · ·  ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη⁀ϊ ά δε ω Ἀ χι ƛῆ⁀ος
─  ·   · ─  ·  ·  ─ ─  ─    · ·  ─ ─ ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη⁀ϊ ά δε ω⁀Ἀ χι ƛῆ ος
─  ·   · ─  ·  ·  ─ ─  ─    · ·  ─   ─  ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη⁀ϊ ά δε⁀ω Ἀ χι ƛῆ ος
─  ·   · ─  ·  ·  ─ ─  ─    ─ ─    · ·  ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη ϊ⁀ά δε⁀ω Ἀ χι ƛῆ⁀ος
─  ·   · ─  ·  ·  ─ ─  ─  ─   ─    ─ ─  ─

μῆ νιν ἄ ει δε θε ὰ Πη ƛη⁀ϊ ά δε⁀ω Ἀ χι ƛῆ⁀ος
─  ·   · ─  ·  ·  ─ ─  ─    ─ ─    ─ ─  ─

-- [C-u C-u C-c C-n] allDerivations v2

οὐ ƛο μέ νην ἣ μυ ρί Ἀ χαι οῖς ἄƛ γε ἔ θη κε
─  ·  ·  ─   ─ ─  ·  · ─   ─   ─  ·  · ─  ─

-- [C-u C-u C-c C-n] allDerivations v3

ποƛ ƛὰς δἰφ θί μους ψυ χὰς Ἄ ϊ δι προ ΐ α ψεν
─   ─   ─   ─  ─    ·  ·   ─ ─ ─  ·   · ─ ─

ποƛ ƛὰς δἰφ θί μους ψυ χὰς Ἄ ϊ δι προ ΐ α ψεν
─   ─   ─   ─  ─    ─  ─   · · ─  ·   · ─ ─

-- [C-u C-u C-c C-n] allDerivations v4

ἡρ ώ ων αὐ τοὺς δὲ ἑ ƛώ ρι α τεῦ χε κύ νεσ σιν
─  ─ ─  ─  ─    ·  · ─  ·  · ─   ·  ·  ─   ─

ἡρ ώ ων αὐ τοὺς δὲ ἑ ƛώ ρι α τεῦ χε κύ νεσ σιν
─  ─ ─  ─  ─    ·  · ─  ·  · ─   ·  ·  ─   ─

-- [C-u C-u C-c C-n] allDerivations v5

οἰ ω νοῖ σί τε πᾶ σι Δι ὸς δἐ τε ƛεί ε το βου ƛή
─  ─ ─   ·  ·  ─  ·  ·  ─  ·  ·  ─   · ·  ─   ─

-- [C-u C-u C-c C-n] allDerivations v6

ἐξ οὗ δὴ τὰ πρῶ τα δι α στή την ἐ ρί σα ντε
─  ─  ─  ─  ─   ·  ·  ─ ─   ─   · ·  ─  ─

-- [C-u C-u C-c C-n] allDerivations v7

Ἀ τρε ΐ δης τε ἄ ναξ ἀν δρῶν καὶ δῖ ος Ἀ χιƛ ƛεύς
─ ·   · ─   ·  · ─   ─  ─    ─   ─  ·  · ─   ─

-- [C-u C-u C-c C-n] allDerivations v8

τίς τἄρ σφω ε θε ῶν ἔ ρι δι ξυ νέ η κε μά χε σθαι
─   ─   ─   · ·  ─  · ·  ─  ·  ·  ─ ·  ·  ─  ─

-- [C-u C-u C-c C-n] allDerivations v9

-- [C-u C-u C-c C-n] allDerivations v10

-- [C-u C-u C-c C-n] allDerivations v11

-}

-- v1~ : v1 ~ mkPM
--   ( (-, -, ─··)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ──)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ──)
--   ∷ [])
-- v1~ = auto

-- nn : ℕ
-- nn = length $ allDerivations v1

-- _ : Derivable v1
-- _ = tt -- auto

-- v1~ : v1 ~ mkPM
--   ( (-, -, ─··)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ──)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ─··)
--   ∷ (-, -, ──)
--   ∷ [])
-- v1~ = auto

{-
_ : Derivable v2
_ = auto

-- [Ctrl+n] allDerivations v3

_ : Derivable v3
_ = auto

_ : Derivable v4
_ = auto

_ : Derivable v5
_ = auto

_ : Derivable v6
_ = auto

_ : Derivable v7
_ = auto

_ : Derivable v8
_ = auto


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
