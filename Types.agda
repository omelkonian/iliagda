module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open L.Mem
open Unary using () renaming (_∪_ to _∪₁_)
open import Prelude.General
open import Prelude.Lists
open import Prelude.Bifunctor
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules

private variable
  X : Type
  n : ℕ

⟦_⟧ : X ^ n → List X
⟦_⟧ {n = zero}  x        = [ x ]
⟦_⟧ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧

-- data Vowel : Type where
--   α η ε

-- data Accent : Type where
--   accute
--   grave
--   cirmuflex

-- T0D0: bake into definition of `Vowel`

data Letter : Type where
  ῆ ι ἄ ε ὰ η ϊ ά ω Ἀ ο : Letter
  μ ν θ Π δ χ ƛ ς : Letter
-- Letter = Vowel ⊎ Consonant
unquoteDecl DecEq-Letter = DERIVE DecEq [ quote Letter , DecEq-Letter ]

Vowel Consonant : Pred₀ Letter
Vowel = _∈ ⟦ ῆ , ι , ἄ , ε , ὰ , η , ϊ , ά , ω , Ἀ , ο ⟧
-- Consonant = ¬_ ∘ Vowel
Consonant = _∈ ⟦ μ , ν , θ , Π , δ , χ , ƛ , ς ⟧

-- NB: ← first define Syllables and then Word?

-- Word = List Letter
Syllable = List Letter
Word = List Syllable

Verse = List Word

_ = Verse
  ∋ ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧
    , ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧
    , ⟦ ⟦ θ , ε ⟧ , ⟦ ὰ ⟧ ⟧
    , ⟦ ⟦ Π , η ⟧ , ⟦ ƛ , η ⟧ , ⟦ ϊ ⟧ , ⟦ ά ⟧ , ⟦ δ , ε ⟧ , ⟦ ω ⟧ ⟧
    , ⟦ ⟦ Ἀ ⟧ , ⟦ χ , ι ⟧ , ⟦ ƛ , ῆ ⟧ , ⟦ ο , ς ⟧ ⟧
    ⟧

-- NB: actually (w : Word) → Vec Length (length w) → Type
-- OMIT, no sensible definition within word boundaries
-- Word → List Length → Type

data Length : Type where
  ˘ ─ : Length

data Foot : Type where
  ─˘˘ {- dactyl -} : Foot
  ──  {- sponde -} : Foot

PartialMeter = List Foot
Meter = Vec Foot 6
-- NB: actually Vec Foot 5 ∷ ──

private variable
  l l′ : Letter
  sy   : Syllable
  w w′ : Word
  len len′ : Length
  lens lens′ : List Length
  mlen mlen′ : Maybe Length
  mlens mlens′ : List (Maybe Length)
  f f′ : Foot
  pm pm′ : PartialMeter
  m m′ : Meter
  v v′ : Verse

─Vowel ˘Vowel : Pred₀ Letter
─Vowel = _∈ ⟦ ῆ , η , ω ⟧
˘Vowel = _∈ ⟦ ε , ο ⟧

DoubleConsonant : Pred₀ Letter
DoubleConsonant = _∈ [] -- ζ ξ ψ

Diphthong : Pred₀ (Letter × Letter)
Diphthong = _∈ [ (ε , ι) ]

VowelBeforeTwoConsonants : Pred₀ (Letter × Letter × Letter)
VowelBeforeTwoConsonants (v , c , c′) =
  Vowel v × Consonant c × Consonant c′

VowelBeforeDoubleConsonant : Pred₀ (Letter × Letter)
VowelBeforeDoubleConsonant (v , c) =
  Vowel v × DoubleConsonant c

Any× : Pred₀ (X × X) → Pred₀ (List X)
Any× P = Any P ∘ pairs

triples : List X → List (X × X × X)
triples = map (map₁ proj₁) ∘ pairs ∘ pairs

Any×₃ : Pred₀ (X × X × X) → Pred₀ (List X)
Any×₃ P = Any P ∘ triples

-- (522)
─Syllable : Pred₀ Syllable
─Syllable = Any ─Vowel  -- \ by nature
         ∪₁ Any× Diphthong -- /
         ∪₁ Any×₃ VowelBeforeTwoConsonants  -- \ by position
         ∪₁ Any× VowelBeforeDoubleConsonant -- /
-- ()
postulate ˘Syllable : Pred₀ Syllable

-- μῆνιν ἄειδε θεὰ Πηληϊάδεω Ἀχιλῆος

_ : ─Syllable ⟦ μ , ῆ ⟧
_ = auto

-- e.g. mi ~ ─

data _~ˢ_ : Syllable → Maybe Length → Type where

  long  :

    ─Syllable sy
    ───────────────
    sy ~ˢ just ─

  short :

    ˘Syllable sy
    ───────────────
    sy ~ˢ just ˘

  ambiguous :

    ∙ ¬ ─Syllable sy
    ∙ ¬ ˘Syllable sy
      ───────────────
      sy ~ˢ nothing


-- _~_ : Syllable → Length → Type
-- _~_ = ?

-- minin ~ ─˘

{-
data _~◐′_ : List Syllable → PartialMeter → Type where

  sy  ~ˢ just ─
  sy′ ~ˢ just ─
  v ~◐ pm
  ─────────────────────────
  sy ∷ sy′ ∷ v ~◐′ ── ∷ pm

data _~◐_ : Verse → PartialMeter → Type where

  let (sy ∷ sy′ ∷ []) = L.take 2 (L.flatten v) in

  sy  ~ˢ just ─
  sy′ ~ˢ just ─
  v ~◐ pm

  ─────────────────
  (sy ∷ sy′ ∷ w) ∷ v ~◐
  (sy ∷ []) ∷ (sy′ ∷ w) ∷ v ~◐
-}

-- #NOT : List (Maybe Length) → List Length
-- #NOT = fix $ (refine ∘ reverse) ∘ refine

-- refine : List (Maybe Length) → List (Maybe Length)
-- refine = id

data _<_ : Rel₀ (List (Maybe Length)) where

  <-head :

    ──────────────────────────────────────
    (nothing ∷ mlens) < (just len ∷ mlens)

  <-tail :

    mlens < mlens′
    ────────────────────────────────
    (mlen ∷ mlens) < (mlen ∷ mlens′)

_ : (nothing  ∷ just len′ ∷ nothing ∷ [])
  < (just len ∷ just len′ ∷ nothing ∷ [])
_ = <-head

data _ˡ~ᵖᵐ_ : List (Maybe Length) → PartialMeter → Type where

  base :
    [] ˡ~ᵖᵐ []

  sponde :

    mlens ˡ~ᵖᵐ pm
    ───────────────────────────────────
    (just ─ ∷ just ─ ∷ mlens) ˡ~ᵖᵐ (── ∷ pm)

  dactyl :

    mlens ˡ~ᵖᵐ pm
    ─────────────────────────────────────────────
    (just ─ ∷ just ˘ ∷ just ˘ ∷ mlens) ˡ~ᵖᵐ (─˘˘ ∷ pm)

  reify :

    ∙ mlens < mlens′
    ∙ mlens′ ˡ~ᵖᵐ pm
      ─────────────────────────────────────────────
      mlens ˡ~ᵖᵐ pm

-- reify∗ :
-- reify (reify ... (reify ... ....)













{-
data _ˡ~ᵖᵐ_ : List (Maybe Length) → PartialMeter → Type where

  base :
    [] ˡ~ᵖᵐ []

  sponde : ∀ {x : Maybe Length} →

    ∙ mlens ˡ~ᵖᵐ pm
    ∙ x ≢ just ˘       -- M.All (_≡ ─) x
      ───────────────────────────────────
      (x ∷ just ─ ∷ mlens) ˡ~ᵖᵐ (── ∷ pm)

  dactyl : ∀ {x y z : Maybe Length} →

    ∙ mlens ˡ~ᵖᵐ pm
    ∙ x ≢ just ˘ -- M.All (_≡ ─) x
    ∙ ((y ≡ just ˘) × (z ≢ just ─)) -- M.All (_≡ ˘) z)
    ⊎ ((z ≡ just ˘) × (y ≢ just ─)) -- M.All (_≡ ˘) y)
      ─────────────────────────────────────────────
      (x ∷ y ∷ z ∷ mlens) ˡ~ᵖᵐ (─˘˘ ∷ pm)

_ : (nothing ∷ nothing ∷ []) ˡ~ᵖᵐ [ ── ]
_ = {!!}

_ : (nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ [ ─˘˘ ]
_ = {!!}

_ : (nothing ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ
    (── ∷ ─˘˘ ∷ [])
_ = {!!}

_ : (nothing ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ
    (─˘˘ ∷ ── ∷ [])
_ = {!!}

H : (just ─ ∷ nothing ∷ just ─ ∷ just ─ ∷ []) ˡ~ᵖᵐ (── ∷ ── ∷ [])
H = {!sponde!}
-}

{-
-- e.g. verse1 ~ ─˘˘ | ─˘˘ | ── | ─˘˘ | ─˘˘ | ──
inferLengths : Verse → List (Maybe Length)

_~_ : Verse → Meter → Type
v ~ m = ??? v ˡ∼ᵖᵐ V.toList m

data _~_ : Verse → Meter → Type where


  ~ˢ ─
  ~ˢ ˘
  ~ˢ ˘

  ────────────────────
  verse ∷ ~ ─˘˘ ...

data _EPIC∼_ : Verse → EpicMeter → Type where
-}

{-
  οὐλομένην, ἣ μυρί᾽ Ἀχαιοῖς ἄλγε᾽ ἔθηκε,

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
  ἀλλ᾽ ἴθι μή μ᾽ ἐρέθιζε σαώτερος ὥς κε νέηαι.
-}
