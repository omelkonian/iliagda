-- {-# OPTIONS --allow-unsolved-metas #-}
-- ** analysis of actual Iliad verses
module Iliagda.Examples where

open import Iliagda.Init
open import Iliagda.Morphology
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody
open import Iliagda.Dec

-- ** Verse I: μῆνιν ἄειδε θεὰ Πηληϊάδεω Ἀχιλῆος

_ : [ ─ ⨾ · ⨾ · ] ~ mkPM [ -, -, ─·· ]
_ = dactyl []

-- _ : (just ─ ∷ just · ∷ just · ∷ []) ~ mkPM [ -, -, ─·· ]
-- _ = base (dactyl base)

-- _ : (just ─ ∷ nothing ∷ just · ∷ []) ~ mkPM [ -, -, ─·· ]
-- _ = reify (refl ∷ tt ∷ refl ∷ []) $ base (dactyl base)

-- _ : (nothing ∷ nothing ∷ just · ∷ []) ~ mkPM [ -, -, ─·· ]
-- _ = reify (tt ∷ tt ∷ refl ∷ []) $ base (dactyl base)

μῆνιν : word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ] ~ (just ─ ∷ just · ∷ [])
μῆνιν = fromBelow $′
  [1160] {sys = []} {mqs = []} h auto contradict
  where
    h : ([ μ ⨾ ῆ ] ∷ [ ν ⨾ ι ⨾ ν ] ∷ []) ~ (just ─ ∷ nothing ∷ [])
    h = auto

-- *μῆνιν-ἄ : (word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ] ∷ word [ [ ἄ ] ] ∷ [])
--           ~ mkPM [ -, -, ─·· ]
-- *μῆνιν-ἄ = fromBelow $′
--   (μῆνιν ∷ base (λ ()) (ambiguous contradict contradict ∷ []) ∷ [])
--   ~∘~ [1169]
--   where
--     [1169] : (just ─ ∷ just · ∷ nothing ∷ []) ~ mkPM [ -, -, ─·· ]
--     [1169] = reify (refl ∷ refl ∷ tt ∷ []) $ base (dactyl base)

*μῆνιν-ῆ : (word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ] ∷ word [ [ ῆ ] ] ∷ [])
          ≁ (just ─ ∷ just ─ ∷ just ─ ∷ [])
*μῆνιν-ῆ = λ where
  (base _ (_ ∷ long ─ι ∷ _) ∷ _) → contradict ─ι
  (_∷_ {mqs = _ ∷ _ ∷ []} ⦃ () ⦄ (fromBelow ([1160] ⦃ refl ⦄ ⦃ refl ⦄ _ _ _)) _)

ἄειδε : word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
      ~ (nothing ∷ just ─ ∷ just · ∷ [])
ἄειδε = base (¬[1160] contradict) auto

μῆνιν-ἄειδε :
  ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
  ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
  ∷ []) ~ ( just ─ ∷ just · ∷ nothing
          ∷ just ─ ∷ just ·
          ∷ [])
μῆνιν-ἄειδε = μῆνιν ∷ ἄειδε ∷ []

*θε : word [ [ θ ⨾ ε ] ]
    ~ V.[ just · ]
*θε = base (λ ()) auto

-- *μῆνιν-ἄειδε-θε :
--   ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
--   ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
--   ∷ word [ [ θ ⨾ ε ] ]
--   ∷ []) ~ mkPM ((-, -, ─··) ∷ (-, -, ─··) ∷ [])
-- *μῆνιν-ἄειδε-θε = fromBelow $′
--   (μῆνιν ∷ ἄειδε ∷ *θε ∷ [])
--   ~∘~ reify (refl ∷ refl ∷ tt ∷ refl ∷ refl ∷ refl ∷ [])
--             (base $′ dactyl $′ dactyl base)

θεὰ : word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
    ~ (just · ∷ nothing ∷ [])
θεὰ = base (¬[1160] contradict) auto

*Πη : word [ [ Π ⨾ η ] ]
    ~ (just ─ ∷ [])
*Πη = base (λ ()) auto

-- *μῆνιν-ἄειδε-θεὰ-Πη :
--   ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
--   ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
--   ∷ word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
--   ∷ word [ [ Π ⨾ η ] ]
--   ∷ []) ~ mkPM ((-, -, ─··) ∷ (-, -, ─··) ∷ (-, -, ──) ∷ [])
-- *μῆνιν-ἄειδε-θεὰ-Πη = fromBelow $′
--   (μῆνιν ∷ ἄειδε ∷ θεὰ ∷ *Πη ∷ [])
--   ~∘~ reify (refl ∷ refl ∷ tt ∷ refl ∷ refl ∷ refl ∷ tt ∷ refl ∷ [])
--             (base $′ dactyl $′ dactyl $′ sponde base)

*Πηƛηϊά : word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ]
        ~ (just ─ ∷ just ─ ∷ nothing ∷ nothing ∷ [])
*Πηƛηϊά = base (¬[1160] contradict) auto

-- *μῆνιν-ἄειδε-θεὰ-Πηƛηϊά :
--   ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
--   ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
--   ∷ word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
--   ∷ word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ]
--   ∷ []) ~ mkPM ((-, -, ─··) ∷ (-, -, ─··) ∷ (-, -, ──) ∷ (-, -, ─··) ∷ [])
-- *μῆνιν-ἄειδε-θεὰ-Πηƛηϊά = fromBelow $′
--   (μῆνιν ∷ ἄειδε ∷ θεὰ ∷ *Πηƛηϊά ∷ [])
--   ~∘~ reify ( refl ∷ refl
--             ∷ tt ∷ refl ∷ refl
--             ∷ refl ∷ tt
--             ∷ refl ∷ refl ∷ tt ∷ tt
--             ∷ [])
--             (base $′ dactyl $′ dactyl $′ sponde $′ dactyl base)

Πηƛηϊάδεω : word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
          ~ (just ─ ∷ just ─ ∷ nothing ∷ nothing ∷ just · ∷ just ─ ∷ [])
Πηƛηϊάδεω = base (¬[1160] contradict) auto

Ἀχιλῆος : word [ [ Ἀ ] ⨾ [ χ ⨾ ι ] ⨾ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]
        ~ (nothing ∷ nothing ∷ just ─ ∷ just · ∷ [])
Ἀχιλῆος = fromBelow $′
  [1160] {mq = just ─} {mq′ = just ·} auto auto contradict
  -- TODO: decision procedure to avoid giving mq/mq′

_μῆνιν-ἄειδε-θεὰ-Πηƛηϊάδεω-Ἀχιλῆος :
  ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
  ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
  ∷ word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
  ∷ word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
  ∷ word [ [ Ἀ ] ⨾ [ χ ⨾ ι ] ⨾ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]
  ∷ []) ~
  ( just ─ ∷ just ·
  ∷ nothing ∷ just ─ ∷ just ·
  ∷ just · ∷ nothing
  ∷ just ─ ∷ just ─ ∷ nothing ∷ nothing ∷ just · ∷ just ─
  ∷ nothing ∷ nothing ∷ just ─ ∷ just ·
  ∷ [])
_μῆνιν-ἄειδε-θεὰ-Πηƛηϊάδεω-Ἀχιλῆος = μῆνιν ∷ ἄειδε ∷ θεὰ ∷ Πηƛηϊάδεω ∷ Ἀχιλῆος ∷ []

*syn :
  ( [ μ ⨾ ῆ ] ∷ [ ν ⨾ ι ⨾ ν ]
  ∷ [ ἄ ] ∷ [ ε ⨾ ι ] ∷ [ δ ⨾ ε ]
  ∷ [ θ ⨾ ε ] ∷ [ ὰ ]
  ∷ [ Π ⨾ η ] ∷ [ ƛ ⨾ η ] ∷ [ ϊ ] ∷ [ ά ] ∷ [ δ ⨾ ε ] ∷ [ ω ]
  ∷ [ Ἀ ] ∷ [ χ ⨾ ι ] ∷ [ ƛ ⨾ ῆ ] ∷ [ ο ⨾ ς ]
  ∷ [] )
  -synizizes*-
  ( [ μ ⨾ ῆ ] ∷ [ ν ⨾ ι ⨾ ν ]
  ∷ [ ἄ ] ∷ [ ε ⨾ ι ] ∷ [ δ ⨾ ε ]
  ∷ [ θ ⨾ ε ] ∷ [ ὰ ]
  ∷ [ Π ⨾ η ] ∷ [ ƛ ⨾ η ] ∷ [ ϊ ] ∷ [ ά ] ∷ [ δ ⨾ ε ⨾ ω ]
  ∷ [ Ἀ ] ∷ [ χ ⨾ ι ] ∷ [ ƛ ⨾ ῆ ] ∷ [ ο ⨾ ς ]
  ∷ [] )
*syn = auto

μῆνιν-ἄειδε-θεὰ-Πηƛηϊάδεω-Ἀχιλῆος :
  ( word [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ]
  ∷ word [ [ ἄ ] ⨾ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ]
  ∷ word [ [ θ ⨾ ε ] ⨾ [ ὰ ] ]
  ∷ word [ [ Π ⨾ η ] ⨾ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ⨾ [ δ ⨾ ε ] ⨾ [ ω ] ]
  ∷ word [ [ Ἀ ] ⨾ [ χ ⨾ ι ] ⨾ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]
  ∷ []) ~
  mkPM
  ( (-, -, ─··)
  ∷ (-, -, ─··)
  ∷ (-, -, ──)
  ∷ (-, -, ─··)
  ∷ (-, -, ─··)
  ∷ (-, -, ──)
  ∷ [])
μῆνιν-ἄειδε-θεὰ-Πηƛηϊάδεω-Ἀχιλῆος =
  [586] *syn _μῆνιν-ἄειδε-θεὰ-Πηƛηϊάδεω-Ἀχιλῆος
    {!!}
    (reify {qs = ─ ∷ · ∷ · ∷ ─ ∷ · ∷ · ∷ ─ ∷ ─ ∷ ─ ∷ · ∷ · ∷ ─ ∷ · ∷ · ∷ ─ ∷ · ∷ []}
           auto
           $′ dactyl $′ dactyl $′ sponde $′ dactyl $′ dactyl $′ sponde [])


{-  foot [ [ μ ⨾ ῆ ] ⨾ [ ν ⨾ ι ⨾ ν ] ⨾ [ ἄ ] ]     -- (-, -, ─··)
  ∷ foot [ [ ε ⨾ ι ] ⨾ [ δ ⨾ ε ] ⨾ [ θ ⨾ ε ] ]     -- (-, -, ─··)
  ∷ foot [ [ ὰ ] ⨾ [ Π ⨾ η ] ]                     -- (-, -, ──)
  ∷ foot [ [ ƛ ⨾ η ] ⨾ [ ϊ ] ⨾ [ ά ] ]             -- (-, -, ─··)
  ∷ foot [ [ δ ⨾ ε ] ⨾ [ ω ] ⨾ [ Ἀ ] ⨾ [ χ ⨾ ι ] ] -- (-, -, ─··)
  ∷ foot [ [ ƛ ⨾ ῆ ] ⨾ [ ο ⨾ ς ] ]                 -- (-, -, ──)
  ∷ []
-}

{-
-- ** Verse II: οὐλομένην, ἣ μυρί᾽ Ἀχαιοῖς ἄλγε᾽ ἔθηκε,

οὐλομένην : word [ [ ο ⨾ ὐ ] ⨾ [ ƛ ⨾ ο ] ⨾ [ μ ⨾ έ ] ⨾ [ ν ⨾ η ⨾ ν ] ]
          ~ [ just ─ ⨾ just · ⨾ just · ⨾ just ─ ]
οὐλομένην = base (¬[1160] contradict) auto

_ἣ : word [ [ ἣ ] ] ~ [ just ─ ]
_ἣ = base (λ ()) auto

μυρί : word [ [ μ ⨾ υ ] ⨾ [ ρ ⨾ ί ] ] ~ [ nothing ⨾ nothing ]
μυρί = base (¬[1160] contradict) auto

Ἀχαιοῖς : word [ [ Ἀ ] ⨾ [ χ ⨾ α ⨾ ι ] ⨾ [ ο ⨾ ῖ ⨾ ς ] ]
        ~ [ nothing ⨾ just ─ ⨾ just ─ ]
Ἀχαιοῖς = base (¬[1160] contradict) auto

ἄλγε᾽ : word [ [ ἄ ⨾ ƛ ] ⨾ [ γ ⨾ ε ] ] ~ [ nothing ⨾ just · ]
ἄλγε᾽ = base (¬[1160] contradict) auto

ἔθηκε : word [ [ ἔ ] ⨾ [ θ ⨾ η ] ⨾ [ κ ⨾ ε ] ] ~ [ just · ⨾ just ─ ⨾ just · ]
ἔθηκε = base (¬[1160] contradict) auto

οὐλομένην-ἣ-μυρί᾽-Ἀχαιοῖς-ἄλγε᾽-ἔθηκε :
  ( word [ [ ο ⨾ ὐ ] ⨾ [ ƛ ⨾ ο ] ⨾ [ μ ⨾ έ ] ⨾ [ ν ⨾ η ⨾ ν ] ]
  ∷ word [ [ ἣ ] ]
  ∷ word [ [ μ ⨾ υ ] ⨾ [ ρ ⨾ ί ] ]
  ∷ word [ [ Ἀ ] ⨾ [ χ ⨾ α ⨾ ι ] ⨾ [ ο ⨾ ῖ ⨾ ς ] ]
  ∷ word [ [ ἄ ⨾ ƛ ] ⨾ [ γ ⨾ ε ] ]
  ∷ word [ [ ἔ ] ⨾ [ θ ⨾ η ] ⨾ [ κ ⨾ ε ] ]
  ∷ []
  ) ~ mkPM ((-, -, ─··) ∷ (-, -, ──) ∷ (-, -, ─··) ∷ (-, -, ──) ∷ (-, -, ─··) ∷ (-, -, ──) ∷ [])
οὐλομένην-ἣ-μυρί᾽-Ἀχαιοῖς-ἄλγε᾽-ἔθηκε = {!!}
  -- use [1180, 1184], maybe a proper definition of 6-foot verse?
{-
πολλὰς δ᾽ ἰφθίμους ψυχὰς Ἄϊδι προΐαψεν
ἡρώων, αὐτοὺς δὲ ἑλώρια τεῦχε κύνεσσιν
οἰωνοῖσί τε πᾶσι, Διὸς δ᾽ ἐτελείετο βουλή,
ἐξ οὗ δὴ τὰ πρῶτα διαστήτην ἐρίσαντε
Ἀτρεΐδης τε ἄναξ ἀνδρῶν καὶ δῖος Ἀχιλλεύς.
τίς τ᾽ ἄρ σφωε θεῶν ἔριδι ξυνέηκε μάχεσθαι;
Λητοῦς καὶ Διὸς υἱός: ὃ γὰρ βασιλῆϊ χολωθεὶς
νοῦσον ἀνὰ στρατὸν ὄρσε κακήν, ὀλέκοντο δὲ λαοί,
οὕνεκα τὸν Χρύσην ἠτίμασεν ἀρητῆρα
Ἀτρεΐδης: ὃ γὰρ ἦλθε θοὰς ἐπὶ νῆας Ἀχαιῶν
λυσόμενός τε θύγατρα φέρων τ᾽ ἀπερείσι᾽ ἄποινα,
στέμματ᾽ ἔχων ἐν χερσὶν ἑκηβόλου Ἀπόλλωνος
χρυσέῳ ἀνὰ σκήπτρῳ, καὶ λίσσετο πάντας Ἀχαιούς,
Ἀτρεΐδα δὲ μάλιστα δύω, κοσμήτορε λαῶν:
Ἀτρεΐδαι τε καὶ ἄλλοι ἐϋκνήμιδες Ἀχαιοί,
ὑμῖν μὲν θεοὶ δοῖεν Ὀλύμπια δώματ᾽ ἔχοντες
ἐκπέρσαι Πριάμοιο πόλιν, εὖ δ᾽ οἴκαδ᾽ ἱκέσθαι:
παῖδα δ᾽ ἐμοὶ λύσαιτε φίλην, τὰ δ᾽ ἄποινα δέχεσθαι,
ἁζόμενοι Διὸς υἱὸν ἑκηβόλον Ἀπόλλωνα.

ἔνθ᾽ ἄλλοι μὲν πάντες ἐπευφήμησαν Ἀχαιοὶ
αἰδεῖσθαί θ᾽ ἱερῆα καὶ ἀγλαὰ δέχθαι ἄποινα:
ἀλλ᾽ οὐκ Ἀτρεΐδῃ Ἀγαμέμνονι ἥνδανε θυμῷ,
ἀλλὰ κακῶς ἀφίει, κρατερὸν δ᾽ ἐπὶ μῦθον ἔτελλε:
μή σε γέρον κοίλῃσιν ἐγὼ παρὰ νηυσὶ κιχείω
ἢ νῦν δηθύνοντ᾽ ἢ ὕστερον αὖτις ἰόντα,
μή νύ τοι οὐ χραίσμῃ σκῆπτρον καὶ στέμμα θεοῖο:
τὴν δ᾽ ἐγὼ οὐ λύσω: πρίν μιν καὶ γῆρας ἔπεισιν
ἡμετέρῳ ἐνὶ οἴκῳ ἐν Ἄργεϊ τηλόθι πάτρης
ἱστὸν ἐποιχομένην καὶ ἐμὸν λέχος ἀντιόωσαν:
ἀλλ᾽ ἴθι μή μ᾽ ἐρέθιζε σαώτερος ὥς κε νέηαι.--



...ἀνδρειφόντης... <--- most unmetrical line!!!
-}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
