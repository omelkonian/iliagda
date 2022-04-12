module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open L.Mem
open L using (_∷ʳ_)
open Unary using () renaming (_∪_ to _∪₁_; _⊆_ to _⊆₁_)
open import Prelude.General
open import Prelude.Lists
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules
open import Prelude.Ord

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
Word = List Syllable -- T0D0: List ↝ List⁺
Verse = List Word

private
  verse1 = Verse
    ∋ ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧
      , ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧
      , ⟦ ⟦ θ , ε ⟧ , ⟦ ὰ ⟧ ⟧
      , ⟦ ⟦ Π , η ⟧ , ⟦ ƛ , η ⟧ , ⟦ ϊ ⟧ , ⟦ ά ⟧ , ⟦ δ , ε ⟧ , ⟦ ω ⟧ ⟧
      , ⟦ ⟦ Ἀ ⟧ , ⟦ χ , ι ⟧ , ⟦ ƛ , ῆ ⟧ , ⟦ ο , ς ⟧ ⟧
      ⟧

-- NB: actually (w : Word) → Vec Quantity (length w) → Type
-- OMIT, no sensible definition within word boundaries
-- Word → List Quantity → Type

data Quantity : Type where
  ˘ ─ : Quantity
unquoteDecl DecEq-Quantity = DERIVE DecEq [ quote Quantity , DecEq-Quantity ]

data Foot : Type where
  ─˘˘ {- dactyl -} : Foot
  ──  {- sponde -} : Foot
unquoteDecl DecEq-Foot = DERIVE DecEq [ quote Foot , DecEq-Foot ]

PartialMeter = List Foot
Meter = Vec Foot 6
-- NB: actually Vec Foot 5 ∷ ──

private variable
  l l′ : Letter
  sy sy′ penult penult′ ult ult′ : Syllable
  sys sys′ : List Syllable
  w w′ : Word
  q q′ : Quantity
  qs qs′ : List Quantity
  mq mq′ : Maybe Quantity
  mqs mqs′ : List (Maybe Quantity)
  f f′ : Foot
  pm pm′ : PartialMeter
  m m′ : Meter
  v v′ : Verse

─Vowel ˘Vowel HasCircumflex : Pred₀ Letter
─Vowel = _∈ ⟦ ῆ , η , ω ⟧
˘Vowel = _∈ ⟦ ε , ο ⟧
HasCircumflex = _∈ ⟦ ῆ ⟧

HasCircumflex⇒─Vowel : HasCircumflex ⊆₁ ─Vowel
HasCircumflex⇒─Vowel (here refl) = auto

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

-- T0D0: model Syllables more property

-- (522)
─Syllable : Pred₀ Syllable
─Syllable = Any ─Vowel     -- \ by nature
         ∪₁ Any× Diphthong -- /
         ∪₁ Any×₃ VowelBeforeTwoConsonants  -- \ by position
         ∪₁ Any× VowelBeforeDoubleConsonant -- /

private
  _ : ¬ ─Syllable ⟦ ν , ι , ν ⟧
  _ = λ where
    (inj₁ ─v) → contradict ─v
    (inj₂ (inj₁ di)) → contradict di
    (inj₂ (inj₂ (inj₁ vcc))) → contradict vcc
    (inj₂ (inj₂ (inj₂ vdc))) → contradict vdc

-- (519)
˘Syllable : Pred₀ Syllable
˘Syllable = Any ˘Vowel -- × All (¬ ─Vowel)

-- private
--   _ : ˘Syllable

-- μῆνιν ἄειδε θεὰ Πηληϊάδεω Ἀχιλῆος

_ : ─Syllable ⟦ μ , ῆ ⟧
_ = auto

Subsumes : Rel₀ (List $ Maybe X)
Subsumes = Pointwise _≤ᵐ_
  where
    _≤ᵐ_ : Rel₀ (Maybe X)
    _≤ᵐ_ = λ where
      nothing  (just _) → ⊤
      x        y        → x ≡ y
-- T0D0: Subsumes ⁇

private
  _ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
               (just q  ∷ just q′ ∷ nothing ∷ [])
  _ = tt ∷ refl ∷ refl ∷ []

  _ : Subsumes (nothing ∷ just q′ ∷ nothing ∷ [])
               (just q  ∷ just q′ ∷ just q ∷ [])
  _ = tt ∷ refl ∷ tt ∷ []

-- A complies with B
record _-compliesWith-_ (A B : Type) : Type₁ where
  field _~_ : A → B → Type
  _≁_ : A → B → Type
  _≁_ = ¬_ ∘₂ _~_
open _-compliesWith-_ ⦃ ... ⦄ public

instance
  Complies-Sy-MQ : Syllable -compliesWith- Maybe Quantity
  Complies-Sy-MQ ._~_ = _~′_
    module ∣Complies-Sy-MQ∣ where
      data _~′_ : Syllable → Maybe Quantity → Type where

        long  :

          ─Syllable sy
          ───────────────
          sy ~′ just ─

        short :

          ˘Syllable sy
          ───────────────
          sy ~′ just ˘

        ambiguous :

          ∙ ¬ ─Syllable sy
          ∙ ¬ ˘Syllable sy
            ───────────────
            sy ~′ nothing

  -- NB: maybe generalise to `⦃ A ~ B ⦄ → [A] ~ [B]`
  Complies-Sys-MQs : List Syllable -compliesWith- List (Maybe Quantity)
  Complies-Sys-MQs ._~_ = Pointwise _~_

  Complies-Qs-PM : List Quantity -compliesWith- PartialMeter
  Complies-Qs-PM ._~_ = _~′_
    module ∣Complies-Qs-PM∣ where
      data _~′_ : List Quantity → PartialMeter → Type where

        base :
          [] ~′ []

        sponde :

          qs ~′ pm
          ───────────────────────────
          (─ ∷ ─ ∷ qs) ~′ (── ∷ pm)

        dactyl :

          qs ~′ pm
          ────────────────────────────────
          (─ ∷ ˘ ∷ ˘ ∷ qs) ~′ (─˘˘ ∷ pm)

  -- NB: Quantity ↝ ∀ (A : Type) → ...
  Complies-MQs-PM : List (Maybe Quantity) -compliesWith- PartialMeter
  Complies-MQs-PM ._~_ = _~′_
    module ∣Complies-MQs-PM∣ where
      data _~′_ : List (Maybe Quantity) → PartialMeter → Type where

        base :
          qs ~ pm
          ──────────────────
          (just <$> qs) ~′ pm

        reify :

          ∙ Subsumes mqs mqs′
          ∙ mqs′ ~′ pm
            ─────────────────────────────────────────────
            mqs ~′ pm

{-
  Complies-Sys-PM : List Syllable -compliesWith- PartialMeter
  Complies-Sys-PM ._~_ = _~′_
    module ∣Complies-Sys-PM∣ where
      -- _~′_ : List Syllable → PartialMeter → Type
      -- sys ~′ pm = ∃ λ (mqs : List $ Maybe Quantity)
      --   → (sys ~ mqs) × (mqs ~ pm)
      data _~′_ : List Syllable → PartialMeter → Type where

        ~-trans :
          ∙ sys ~ mqs
          ∙ mqs ~ pm
            ────────────────
            sys ~′ pm
-}

-- TEST :
--   ∙ (sy ∷ w) ~ (mq ∷ mqs)
--   ∙ Any HasCircumflex sy
--     ────────────────────────
--     mq ≡ just ─
-- TEST (∣Complies-Sy-MQ∣.long x ∷ _) circum = {!!}
-- TEST (∣Complies-Sy-MQ∣.short x ∷ _) circum = cong just {!!}
--   -- T0D0: make Agda understand syllables
-- TEST (∣Complies-Sy-MQ∣.ambiguous ¬─v _ ∷ _) circum = {!!}

Complies-W-MQs : Word -compliesWith- List (Maybe Quantity)
Complies-W-MQs ._~_ = _~′_
  module ∣Complies-W-MQs∣ where
    data _~′_ : Word → List (Maybe Quantity) → Type where

      base :
        ∙ length w < 2
        ∙ w ~ mqs
          ────────────────────
          w ~′ mqs

      [1660] :
        -- NB: what happens here is what Conor McBride calls "green slime"
        ∙ (w ∷ʳ penult ∷ʳ ult) ~ (mqs ∷ʳ mq ∷ʳ mq′)
        -- mq_penult -shouldBe- just ─
        ∙ Any HasCircumflex penult
        ∙ mq′ ≢ just ─
          ─────────────────────────────────────────────────
          (w ∷ʳ penult ∷ʳ ult) ~′ (mqs ∷ʳ just ─ ∷ʳ just ˘)

  -- Complies-V-PM : Verse -compliesWith- PartialMeter
  -- Complies-V-PM ._~_ = ?






open ∣Complies-Sy-MQ∣  using (long; short; ambiguous)
open ∣Complies-Qs-PM∣  using (base; sponde; dactyl)
open ∣Complies-MQs-PM∣ using (base; reify)
-- open ∣Complies-Sys-PM∣ using (~-trans)
open ∣Complies-W-MQs∣ using ([1660]) renaming (_~′_ to _~ʷ_)

private
  _ : ⟦ ─ , ˘ , ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = dactyl base

  _ : ⟦ just ─ , just ˘ , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = base (dactyl base)

  _ : ⟦ just ─ , nothing , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = reify (refl ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  _ : ⟦ nothing , nothing , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = reify (tt ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  H : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧ ~ ⟦ just ─ , nothing ⟧
  H = long (inj₁ auto)
    ∷ ambiguous contradict contradict
    ∷ []

  _ : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧ ~ʷ ⟦ just ─ , just ˘ ⟧
  _ = [1660] {w = []} {mqs = []} H auto contradict

{-
private
  _ : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ε , ν ⟧ , ⟦ ε ⟧ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = ~-trans {mqs = ⟦ just ─ , just ˘ , just ˘ ⟧}
              ( long (inj₁ (there $′ here $′ here refl))
              ∷ short (there $′ here $′ here refl)
              ∷ short (here (here refl))
              ∷ [])
              (reify (refl ∷ refl ∷ refl ∷ [])
              (base (dactyl base)))
  -- postulate NIN : ⟦ sy , ⟦ ν , ι , ν ⟧ ⟧ ~ ⟦ ˘ ⟧

  _ : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ , ⟦ ἄ ⟧ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = ~-trans {mqs = ⟦ just ─ , just ˘ , nothing ⟧}
              ( long (inj₁ (there $′ here $′ here refl))
              ∷ {!!}
              ∷ ambiguous {!!} (λ x → {!!})
              ∷ [])
              (reify (refl ∷ refl ∷ tt ∷ [])
              (base (dactyl base)))

  _ : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ , ⟦ ἄ ⟧ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = ~-trans {mqs = ⟦ just ─ , nothing , nothing ⟧}
              ( long (inj₁ (there $′ here $′ here refl))
              ∷ ambiguous (λ{ x → {!x!} }) (λ x → {!!})
              ∷ ambiguous {!!} (λ x → {!!})
              ∷ [])
              (reify (refl ∷ tt ∷ tt ∷ []) (base (dactyl base)))
-}

{-
-- #NOT : List (Maybe Quantity) → List Quantity
-- #NOT = fix $ (refine ∘ reverse) ∘ refine

-- refine : List (Maybe Quantity) → List (Maybe Quantity)
-- refine = id
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
-- data _ˡ~ᵖᵐ_ : List (Maybe Quantity) → PartialMeter → Type where

--   base :
--     [] ˡ~ᵖᵐ []

--   sponde : ∀ {x : Maybe Quantity} →

--     ∙ mqs ˡ~ᵖᵐ pm
--     ∙ x ≢ just ˘       -- M.All (_≡ ─) x
--       ───────────────────────────────────
--       (x ∷ just ─ ∷ mqs) ˡ~ᵖᵐ (── ∷ pm)

--   dactyl : ∀ {x y z : Maybe Quantity} →

--     ∙ mqs ˡ~ᵖᵐ pm
--     ∙ x ≢ just ˘ -- M.All (_≡ ─) x
--     ∙ ((y ≡ just ˘) × (z ≢ just ─)) -- M.All (_≡ ˘) z)
--     ⊎ ((z ≡ just ˘) × (y ≢ just ─)) -- M.All (_≡ ˘) y)
--       ─────────────────────────────────────────────
--       (x ∷ y ∷ z ∷ mqs) ˡ~ᵖᵐ (─˘˘ ∷ pm)

-- _ : (nothing ∷ nothing ∷ []) ˡ~ᵖᵐ [ ── ]
-- _ = {!!}

-- _ : (nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ [ ─˘˘ ]
-- _ = {!!}

-- _ : (nothing ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ
--     (── ∷ ─˘˘ ∷ [])
-- _ = {!!}

-- _ : (nothing ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ []) ˡ~ᵖᵐ
--     (─˘˘ ∷ ── ∷ [])
-- _ = {!!}

-- H : (just ─ ∷ nothing ∷ just ─ ∷ just ─ ∷ []) ˡ~ᵖᵐ (── ∷ ── ∷ [])
-- H = {!sponde!}
-- -}

-- {-
-- -- e.g. verse1 ~ ─˘˘ | ─˘˘ | ── | ─˘˘ | ─˘˘ | ──
-- inferQuantities : Verse → List (Maybe Quantity)

-- _~_ : Verse → Meter → Type
-- v ~ m = ??? v ˡ∼ᵖᵐ V.toList m

-- data _~_ : Verse → Meter → Type where


--   ~ˢ ─
--   ~ˢ ˘
--   ~ˢ ˘

--   ────────────────────
--   verse ∷ ~ ─˘˘ ...

-- data _EPIC∼_ : Verse → EpicMeter → Type where
-- -}

-- {-
--   οὐλομένην, ἣ μυρί᾽ Ἀχαιοῖς ἄλγε᾽ ἔθηκε,

--   πολλὰς δ᾽ ἰφθίμους ψυχὰς Ἄϊδι προΐαψεν
--   ἡρώων, αὐτοὺς δὲ ἑλώρια τεῦχε κύνεσσιν
--   οἰωνοῖσί τε πᾶσι, Διὸς δ᾽ ἐτελείετο βουλή,
--   ἐξ οὗ δὴ τὰ πρῶτα διαστήτην ἐρίσαντε
--   Ἀτρεΐδης τε ἄναξ ἀνδρῶν καὶ δῖος Ἀχιλλεύς.
--   τίς τ᾽ ἄρ σφωε θεῶν ἔριδι ξυνέηκε μάχεσθαι;
--   Λητοῦς καὶ Διὸς υἱός: ὃ γὰρ βασιλῆϊ χολωθεὶς
--   νοῦσον ἀνὰ στρατὸν ὄρσε κακήν, ὀλέκοντο δὲ λαοί,
--   οὕνεκα τὸν Χρύσην ἠτίμασεν ἀρητῆρα
--   Ἀτρεΐδης: ὃ γὰρ ἦλθε θοὰς ἐπὶ νῆας Ἀχαιῶν
--   λυσόμενός τε θύγατρα φέρων τ᾽ ἀπερείσι᾽ ἄποινα,
--   στέμματ᾽ ἔχων ἐν χερσὶν ἑκηβόλου Ἀπόλλωνος
--   χρυσέῳ ἀνὰ σκήπτρῳ, καὶ λίσσετο πάντας Ἀχαιούς,
--   Ἀτρεΐδα δὲ μάλιστα δύω, κοσμήτορε λαῶν:
--   Ἀτρεΐδαι τε καὶ ἄλλοι ἐϋκνήμιδες Ἀχαιοί,
--   ὑμῖν μὲν θεοὶ δοῖεν Ὀλύμπια δώματ᾽ ἔχοντες
--   ἐκπέρσαι Πριάμοιο πόλιν, εὖ δ᾽ οἴκαδ᾽ ἱκέσθαι:
--   παῖδα δ᾽ ἐμοὶ λύσαιτε φίλην, τὰ δ᾽ ἄποινα δέχεσθαι,
--   ἁζόμενοι Διὸς υἱὸν ἑκηβόλον Ἀπόλλωνα.

--   ἔνθ᾽ ἄλλοι μὲν πάντες ἐπευφήμησαν Ἀχαιοὶ
--   αἰδεῖσθαί θ᾽ ἱερῆα καὶ ἀγλαὰ δέχθαι ἄποινα:
--   ἀλλ᾽ οὐκ Ἀτρεΐδῃ Ἀγαμέμνονι ἥνδανε θυμῷ,
--   ἀλλὰ κακῶς ἀφίει, κρατερὸν δ᾽ ἐπὶ μῦθον ἔτελλε:
--   μή σε γέρον κοίλῃσιν ἐγὼ παρὰ νηυσὶ κιχείω
--   ἢ νῦν δηθύνοντ᾽ ἢ ὕστερον αὖτις ἰόντα,
--   μή νύ τοι οὐ χραίσμῃ σκῆπτρον καὶ στέμμα θεοῖο:
--   τὴν δ᾽ ἐγὼ οὐ λύσω: πρίν μιν καὶ γῆρας ἔπεισιν
--   ἡμετέρῳ ἐνὶ οἴκῳ ἐν Ἄργεϊ τηλόθι πάτρης
--   ἱστὸν ἐποιχομένην καὶ ἐμὸν λέχος ἀντιόωσαν:
--   ἀλλ᾽ ἴθι μή μ᾽ ἐρέθιζε σαώτερος ὥς κε νέηαι.--
-- -}
