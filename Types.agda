module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open L using (_∷ʳ_)
open L.Mem
open L.NE using (_⁺∷ʳ_) renaming (length to length⁺)
open Unary using () renaming (_∪_ to _∪₁_; _⊆_ to _⊆₁_)
open import Prelude.General
open import Prelude.Lists
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules
open import Prelude.Ord

private variable
  X : Type
  n : ℕ

-- open import Prelude.Nary
⟦_⟧ : X ^ n → List X
⟦_⟧ {n = zero}  x        = [ x ]
⟦_⟧ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧

⟦_⟧⁺ : X ^ n → List⁺ X
⟦_⟧⁺ {n = zero}  x        = [ x ]⁺
⟦_⟧⁺ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧

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

Syllable = List Letter
Word = List⁺ Syllable
Verse = List Word

private
  verse1 = Verse
    ∋ ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺
      , ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧⁺
      , ⟦ ⟦ θ , ε ⟧ , ⟦ ὰ ⟧ ⟧⁺
      , ⟦ ⟦ Π , η ⟧ , ⟦ ƛ , η ⟧ , ⟦ ϊ ⟧ , ⟦ ά ⟧ , ⟦ δ , ε ⟧ , ⟦ ω ⟧ ⟧⁺
      , ⟦ ⟦ Ἀ ⟧ , ⟦ χ , ι ⟧ , ⟦ ƛ , ῆ ⟧ , ⟦ ο , ς ⟧ ⟧⁺
      ⟧

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
  ws ws′ : List Word
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
VowelBeforeTwoConsonants (v , c , c′) = Vowel v × Consonant c × Consonant c′

VowelBeforeDoubleConsonant : Pred₀ (Letter × Letter)
VowelBeforeDoubleConsonant (v , c) = Vowel v × DoubleConsonant c

Any× : Pred₀ (X × X) → Pred₀ (List X)
Any× P = Any P ∘ pairs

triples : List X → List (X × X × X)
triples = map (map₁ proj₁) ∘ pairs ∘ pairs

Any×₃ : Pred₀ (X × X × X) → Pred₀ (List X)
Any×₃ P = Any P ∘ triples

-- T0D0: model Syllables more properly

-- (522)
─Syllable : Pred₀ Syllable
─Syllable = Any ─Vowel     -- \ by nature
         ∪₁ Any× Diphthong -- /
         ∪₁ Any×₃ VowelBeforeTwoConsonants  -- \ by position
         ∪₁ Any× VowelBeforeDoubleConsonant -- /

-- (519)
˘Syllable : Pred₀ Syllable
˘Syllable = Any ˘Vowel -- × All (¬ ─Vowel)

private
  _ : ¬ ─Syllable ⟦ ν , ι , ν ⟧
  _ = λ where
    (inj₁ ─v) → contradict ─v
    (inj₂ (inj₁ di)) → contradict di
    (inj₂ (inj₂ (inj₁ vcc))) → contradict vcc
    (inj₂ (inj₂ (inj₂ vdc))) → contradict vdc

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
  infix 0 _~_
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

  Complies-W-MQs : Word -compliesWith- List (Maybe Quantity)
  Complies-W-MQs ._~_ = _~′_
    module ∣Complies-W-MQs∣ where
      data _~₀_ : Word → List (Maybe Quantity) → Type where

        [1160] : ∀ {w₀} ⦃ _ : L.NE.reverse w₀ ≡ ult ∷ penult ∷ sys ⦄ →

          ∙ (sys ∷ʳ penult ∷ʳ ult) ~ (mqs ∷ʳ mq ∷ʳ mq′)
          -- mq -shouldBe- just ─
          ∙ Any HasCircumflex penult
          ∙ mq′ ≢ just ─ -- NB: should the ultima be a *doubtful vowel*
            ──────────────────────────────────────────────────────────
            w₀ ~₀ (mqs ∷ʳ just ─ ∷ʳ just ˘)

      data _~′_ : Word → List (Maybe Quantity) → Type where

        base :
          ∙ ¬ w ~₀ mqs
          ∙ w ∙toList ~ mqs
            ───────────────
            w ~′ mqs

        fromBelow :

          w ~₀ mqs
          ────────
          w ~′ mqs

      ¬[1160] : length⁺ w ≡ 1 → ¬ w ~₀ mqs
      ¬[1160] {w = sy ∷ []} refl ([1160] ⦃ () ⦄ _ _ _)

  Complies-Ws-MQs : List Word -compliesWith- List (Maybe Quantity)
  Complies-Ws-MQs ._~_ = _~′_
    module ∣Complies-Ws-MQs∣ where
      data _~′_ : List Word → List (Maybe Quantity) → Type where

        [] :

          ────────
          [] ~′ []

        _∷_ : ∀ {mqs₀} ⦃ _ : mqs₀ ≡ mqs ++ mqs′ ⦄ →

          ∙ w  ~  mqs
          ∙ ws ~′ mqs′
            ────────────────
            (w ∷ ws) ~′ mqs₀

  Complies-Ws-PM : List Word -compliesWith- PartialMeter
  Complies-Ws-PM ._~_ = _~′_
    module ∣Complies-Ws-PM∣ where
      data _~′_ : List Word → PartialMeter → Type where

        _~∘~_ :

          ∙ ws  ~ mqs
          ∙ mqs ~ pm
            ────────
            ws ~′ pm

--   -- Complies-V-PM : Verse -compliesWith- PartialMeter
--   -- Complies-V-PM ._~_ = ?

open ∣Complies-Sy-MQ∣
open ∣Complies-Qs-PM∣
open ∣Complies-MQs-PM∣
-- open ∣Complies-Sys-PM∣
open ∣Complies-W-MQs∣
open ∣Complies-Ws-MQs∣
open ∣Complies-Ws-PM∣

-- μῆνιν ἄειδε θεὰ Πηληϊάδεω Ἀχιλῆος

private
  _ : ⟦ ─ , ˘ , ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = dactyl base

  _ : ⟦ just ─ , just ˘ , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = base (dactyl base)

  _ : ⟦ just ─ , nothing , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = reify (refl ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  _ : ⟦ nothing , nothing , just ˘ ⟧ ~ ⟦ ─˘˘ ⟧
  _ = reify (tt ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  H₁ : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ ~ ⟦ just ─ , just ˘ ⟧
  H₁ = fromBelow $ [1160] {sys = []} {mqs = []} h auto contradict
    where
      h : ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧ ~ ⟦ just ─ , nothing ⟧
      h = long (inj₁ auto)
        ∷ ambiguous contradict contradict
        ∷ []

  H₂ : ⟦ ⟦ ἄ ⟧ ⟧⁺ ~ ⟦ nothing ⟧
  H₂ = base (¬[1160] auto)
            (ambiguous contradict contradict ∷ [])

  H : ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ , ⟦ ⟦ ἄ ⟧ ⟧⁺ ⟧
    ~ ⟦ just ─ , just ˘ , nothing ⟧
  H = H₁ ∷ H₂ ∷ []

  μῆνιν-ἄ : ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ , ⟦ ⟦ ἄ ⟧ ⟧⁺ ⟧ ~ ⟦ ─˘˘ ⟧
  μῆνιν-ἄ = H ~∘~ [1169]
    where
      [1169] : ⟦ just ─ , just ˘ , nothing ⟧ ~ ⟦ ─˘˘ ⟧
      [1169] = reify (refl ∷ refl ∷ tt ∷ []) $ base (dactyl base)

  _ : ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ , ⟦ ⟦ ῆ ⟧ ⟧⁺ ⟧
    ≁ ⟦ just ─ , just ─ , just ─ ⟧
  _ = λ where
      (base _ (_ ∷ long p ∷ _) ∷ _) → contradict p
      (_∷_ {mqs′ = mqs′} ⦃ absurd ⦄ (fromBelow ([1160] x x₁ x₂)) _) →
        WOOOT {mqs′ = mqs′} absurd
    where
      WOOOT : just ─ ∷ just ─ ∷ [ just ─ ] ≢ mqs ∷ʳ just ─ ∷ʳ just ˘ ++ mqs′
      WOOOT {mqs = []} ()
      WOOOT {mqs = _ ∷ _ ∷ []} ()
      WOOOT {mqs = _ ∷ _ ∷ _ ∷ []} ()
      WOOOT {mqs = _ ∷ _ ∷ _ ∷ _ ∷ mqs} ()

  -- L₂ : ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧⁺ ~ ⟦ nothing , just ─ , just ˘ ⟧
  -- L₂ = {!base!}
  -- -- base auto (ambiguous contradict contradict ∷ [])

  -- -- L₂ : ⟦ ⟦ ἄ ⟧ , ⟦ ῆ ⟧ , ⟦ δ , ε ⟧ ⟧⁺ ≁ ⟦ nothing , just ─ , just ˘ ⟧

  -- L : ⟦ ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ , ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧⁺ ⟧
  --   ~ ⟦ just ─ , just ˘ , nothing , just ─ , just ˘ ⟧
  -- L = H₁ ∷ L₂ ∷ []

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
  ἀλλ᾽ ἴθι μή μ᾽ ἐρέθιζε σαώτερος ὥς κε νέηαι.--
-}
