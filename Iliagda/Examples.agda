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
  -- Show-Derivations .show = lined
  Show-Derivations {ws = ws} .show = λ where
    [] → "\n" ◇ show (unwords ws) ◇ "\n∅"
    ds → lined ds

  Show-ManyDerivations : Show (List ∃Derivations)
  -- Show-ManyDerivations .show = lined
  Show-ManyDerivations .show dss =
    "\n" ◇ Str.intersperse "\n\n***************\n" (map show dss)
--

dss : List ∃Derivations
dss = map (λ (_ , v) → -, -, allDerivations v) verses

{- ** Interactively showing all derivations of given verses **

-- [C-u C-u C-c C-n] dss

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

***************

οὐ ƛο μέ νην ἣ μυ ρί Ἀ χαι οῖς ἄƛ γε ἔ θη κε
─  ·  ·  ─   ─ ─  ·  · ─   ─   ─  ·  · ─  ─

***************

ποƛ ƛὰς δἰφ θί μους ψυ χὰς Ἄ ϊ δι προ ΐ α ψεν
─   ─   ─   ─  ─    ·  ·   ─ ─ ─  ·   · ─ ─

ποƛ ƛὰς δἰφ θί μους ψυ χὰς Ἄ ϊ δι προ ΐ α ψεν
─   ─   ─   ─  ─    ─  ─   · · ─  ·   · ─ ─

***************

ἡρ ώ ων αὐ τοὺς δὲ ἑ ƛώ ρι α τεῦ χε κύ νεσ σιν
─  ─ ─  ─  ─    ·  · ─  ·  · ─   ·  ·  ─   ─

ἡρ ώ ων αὐ τοὺς δὲ ἑ ƛώ ρι α τεῦ χε κύ νεσ σιν
─  ─ ─  ─  ─    ·  · ─  ·  · ─   ·  ·  ─   ─

***************

οἰ ω νοῖ σί τε πᾶ σι Δι ὸς δἐ τε ƛεί ε το βου ƛή
─  ─ ─   ·  ·  ─  ·  ·  ─  ·  ·  ─   · ·  ─   ─

***************

ἐξ οὗ δὴ τὰ πρῶ τα δι α στή την ἐ ρί σα ντε
─  ─  ─  ─  ─   ·  ·  ─ ─   ─   · ·  ─  ─

***************

Ἀ τρε ΐ δης τε ἄ ναξ ἀν δρῶν καὶ δῖ ος Ἀ χιƛ ƛεύς
─ ·   · ─   ·  · ─   ─  ─    ─   ─  ·  · ─   ─

***************

τίς τἄρ σφω ε θε ῶν ἔ ρι δι ξυ νέ η κε μά χε σθαι
─   ─   ─   · ·  ─  · ·  ─  ·  ·  ─ ·  ·  ─  ─

***************

Λη τοῦς καὶ Δι ὸς υἱ ός ὃ γὰρ βα σι ƛῆ ϊ χο ƛω θεὶς
─  ─    ─   ·  ·  ─  ·  · ─   ·  ·  ─  · ·  ─  ─

***************

νοῦ σον ἀ νὰ στρα τὸν ὄρ σε κα κήν ὀ ƛέ κο ντο δὲ ƛα οί
─   ·   · ─  ·    ·   ─  ·  ·  ─   · ·  ─  ·   ·  ─  ─

***************

οὕ νε κα τὸν Χρύ σην ἠ τί μα σεν ἀ ρη τῆ ρα
─  ·  ·  ─   ─   ─   ─ ─  ·  ·   ─ ─  ─  ─

***************

Ἀ τρε ΐ δης ὃ γὰρ ἦƛ θε θο ὰς ἐ πὶ νῆ ας Ἀ χαι ῶν
─ ·   · ─   · ·   ─  ·  ·  ─  · ·  ─  ·  · ─   ─

***************

ƛυ σό με νός τε θύ γα τρα φέ ρων τἀ πε ρεί σι ἄ ποι να
─  ·  ·  ─   ·  ·  ─  ·   ·  ─   ·  ·  ─   ·  · ─   ─

ƛυ σό με νός τε θύ γα τρα φέ ρων τἀ πε ρεί σι ἄ ποι να
─  ·  ·  ─   ·  ·  ─  ·   ·  ─   ·  ·  ─   ·  · ─   ─

***************



***************

-}

{-
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
