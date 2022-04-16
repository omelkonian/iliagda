module Types where

open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init hiding (module Word)
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

-- import Data.Vec.Relation.Binary.Pointwise.Inductive as V
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
  renaming (Pointwise to VPointwise)

private variable
  X : Type
  n n′ m m′ : ℕ

-- open import Prelude.Nary
⟦_⟧ : X ^ n → List X
⟦_⟧ {n = zero}  x        = [ x ]
⟦_⟧ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧

⟦_⟧⁺ : X ^ n → Vec X (suc n)
⟦_⟧⁺ {n = zero}  x        = V.[ x ]
⟦_⟧⁺ {n = suc n} (x , xs) = x ∷ ⟦ xs ⟧⁺

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

-- T0D0: silently use suc, i.e. Word 1 ≈ words with one syllable
data Word : ℕ → Type where
  word : ⦃ _ : False $ n ≟ 0 ⦄ → Vec Syllable n → Word n
-- Word = Vec Syllable ∘ suc
∃Word = ∃ Word

unword : Word n → Vec Syllable n
unword (word sys) = sys

data Words : ℕ → Type where
  [] : Words 0
  _∷_ : Word n → Words n′ → Words (n + n′)

Verse = List ∃Word

private
  verse1 : Verse
  verse1 =
    -- T0D0: find a way to use n-ary notation
    ( (-, word ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺)
    ∷ (-, word ⟦ ⟦ ἄ ⟧ , ⟦ ε , ι ⟧ , ⟦ δ , ε ⟧ ⟧⁺)
    ∷ (-, word ⟦ ⟦ θ , ε ⟧ , ⟦ ὰ ⟧ ⟧⁺)
    ∷ (-, word ⟦ ⟦ Π , η ⟧ , ⟦ ƛ , η ⟧ , ⟦ ϊ ⟧ , ⟦ ά ⟧ , ⟦ δ , ε ⟧ , ⟦ ω ⟧ ⟧⁺)
    ∷ (-, word ⟦ ⟦ Ἀ ⟧ , ⟦ χ , ι ⟧ , ⟦ ƛ , ῆ ⟧ , ⟦ ο , ς ⟧ ⟧⁺)
    ∷ [])

data Quantity : Type where
  ˘ ─ : Quantity
unquoteDecl DecEq-Quantity = DERIVE DecEq [ quote Quantity , DecEq-Quantity ]

data Foot : (n : ℕ) → Vec Quantity n → Type where
  ─˘˘ {- dactyl -} : Foot 3 (─ ∷ ˘ ∷ ˘ ∷ [])
  ──  {- sponde -} : Foot 2 (─ ∷ ─ ∷ [])
unquoteDecl DecEq-Foot = DERIVE DecEq [ quote Foot , DecEq-Foot ]
∃∃Foot = ∃ (∃ ∘ Foot)

-- PartialMeter : ℕ {- syllables -} → ℕ {- feet -} → Type
-- PartialMeter n m = ∃ λ (fs : List ∃∃Foot) → (n ≡ ∑₁ fs) × (m ≡ length fs)

data PartialMeter : ℕ {- syllables -} → ℕ {- feet -} → Type where
  mkPM : (fs : List ∃∃Foot) → PartialMeter (∑₁ fs) (length fs)

Meter = ∃ λ n → PartialMeter n 6
-- Meter = (∃ λ n → PartialMeter n 5) × ∃ (Foot 2)
-- -- NB: actually Vec Foot 5 ∷ ──
-- data Meter : Type where
--   mkMeter : PartialMeter n 5 → ∃ (Foot 2) → Meter

private variable
  l l′ : Letter
  sy sy′ penult penult′ ult ult′ : Syllable
  sys  : Vec Syllable n
  sys′ : Vec Syllable n′
  w  : Word n
  w′ : Word n′
  ws  : Words n
  ws′ : Words n′
  q q′ : Quantity
  qs qs′ : Vec Quantity n
  mq mq′ : Maybe Quantity
  mqs mqs′ : Vec (Maybe Quantity) n
  pm  : PartialMeter n m
  pm′ : PartialMeter n′ m′
  meter meter′ : Meter
  v v′ : Verse

_∷ᵖᵐ_ : Foot n qs → PartialMeter n′ m′ → PartialMeter (n + n′) (1 + m′)
f ∷ᵖᵐ (mkPM fs) = mkPM ((-, -, f) ∷ fs)

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

Subsumes : Rel₀ (Vec (Maybe X) n)
Subsumes = VPointwise _≤ᵐ_
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
  Complies-Sys-MQs : Vec Syllable n -compliesWith- Vec (Maybe Quantity) n
  Complies-Sys-MQs ._~_ = VPointwise _~_

  Complies-Qs-PM : Vec Quantity n -compliesWith- PartialMeter n m
  Complies-Qs-PM ._~_ = _~′_
    module ∣Complies-Qs-PM∣ where
      data _~′_ : Vec Quantity n → PartialMeter n m → Type where

        base :
          ─────────────
          [] ~′ mkPM []

        sponde :

          qs ~′ pm
          ───────────────────────────
          (─ ∷ ─ ∷ qs) ~′ (── ∷ᵖᵐ pm)

        dactyl :

          qs ~′ pm
          ────────────────────────────────
          (─ ∷ ˘ ∷ ˘ ∷ qs) ~′ (─˘˘ ∷ᵖᵐ pm)

  Complies-MQs-PM : Vec (Maybe Quantity) n -compliesWith- PartialMeter n m
  Complies-MQs-PM ._~_ = _~′_
    module ∣Complies-MQs-PM∣ where
      data _~′_ : Vec (Maybe Quantity) n → PartialMeter n m → Type where

        base : ∀ {qs : Vec Quantity n} {pm : PartialMeter n m} →

          qs ~ pm
          ─────────────────────
          (V.map just qs) ~′ pm

        reify :

          ∙ Subsumes mqs mqs′
          ∙ mqs′ ~′ pm
            ─────────────────
            mqs ~′ pm

  Complies-W-MQs : Word n -compliesWith- Vec (Maybe Quantity) n
  Complies-W-MQs ._~_ = _~′_
    module ∣Complies-W-MQs∣ where

      data _~₀_ : Word n → Vec (Maybe Quantity) n → Type where

        [1160] : ∀ {sys₀ : Vec Syllable (suc (suc n))}
                   ⦃ _ : V.reverse sys₀ ≡ ult V.∷ penult V.∷ sys ⦄
                   {mqs : Vec (Maybe Quantity) n} →

          ∙ (sys V.∷ʳ penult V.∷ʳ ult) ~ (mqs V.∷ʳ mq V.∷ʳ mq′)
          -- mq -shouldBe- just ─
          ∙ Any HasCircumflex penult
          ∙ mq′ ≢ just ─ -- NB: should the ultima be a *doubtful vowel*
            ──────────────────────────────────────────────────────────
            word sys₀ ~₀ (mqs V.∷ʳ just ─ V.∷ʳ just ˘)

      data _~′_ : Word n → Vec (Maybe Quantity) n → Type where

        base :
          ∙ ¬ w ~₀ mqs
          ∙ unword w ~ mqs
            ───────────────
            w ~′ mqs

        fromBelow :

          w ~₀ mqs
          ────────
          w ~′ mqs

      -- ¬[1160] : V.length sys ≡ 1 → ¬ w ~₀ mqs
      -- ¬[1160] {w = sy ∷ []} refl ([1160] ⦃ () ⦄ _ _ _)

  Complies-Ws-MQs : Words n -compliesWith- Vec (Maybe Quantity) n
  Complies-Ws-MQs ._~_ = _~′_
    module ∣Complies-Ws-MQs∣ where
      data _~′_ : Words n → Vec (Maybe Quantity) n → Type where

        [] :

          ────────
          [] ~′ []

        _∷_ : ∀ {w : Word n}
                {mqs : Vec (Maybe Quantity) n}
                {ws : Words n′}
                {mqs′ : Vec (Maybe Quantity) n′}
                {mqs₀ : Vec (Maybe Quantity) (n + n′)}
                ⦃ _ : mqs₀ ≡ mqs V.++ mqs′ ⦄ →

          ∙ w  ~  mqs
          ∙ ws ~′ mqs′
            ────────────────
            (w ∷ ws) ~′ mqs₀

  Complies-Ws-PM : Words n -compliesWith- PartialMeter n m
  Complies-Ws-PM ._~_ = _~′_
    module ∣Complies-Ws-PM∣ where
      data _~′_ : Words n → PartialMeter n m → Type where

        _~∘~_ : ∀ {ws : Words n} {mqs : Vec (Maybe Quantity) n} →

          ∙ ws  ~ mqs
          ∙ mqs ~ pm
            ────────
            ws ~′ pm

-- Complies-V-PM : Verse -compliesWith- PartialMeter
-- Complies-V-PM ._~_ = ?

open ∣Complies-Sy-MQ∣
open ∣Complies-Qs-PM∣
open ∣Complies-MQs-PM∣
-- open ∣Complies-Sys-PM∣
open ∣Complies-W-MQs∣
open ∣Complies-Ws-MQs∣
open ∣Complies-Ws-PM∣

-- μῆνιν ἄειδε θεὰ Πηληϊάδεω Ἀχιλῆος

private
  _ : (─ ∷ ˘ ∷ ˘ ∷ []) ~ mkPM [ -, -, ─˘˘ ]
  _ = dactyl base

  _ : (just ─ ∷ just ˘ ∷ just ˘ ∷ []) ~ mkPM [ -, -, ─˘˘ ]
  _ = base (dactyl base)

  _ : (just ─ ∷ nothing ∷ just ˘ ∷ []) ~ mkPM [ -, -, ─˘˘ ]
  _ = reify (refl ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  _ : (nothing ∷ nothing ∷ just ˘ ∷ []) ~ mkPM [ -, -, ─˘˘ ]
  _ = reify (tt ∷ tt ∷ refl ∷ []) $ base (dactyl base)

  H₁ : word ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ ~ (just ─ ∷ just ˘ ∷ [])
  H₁ = fromBelow $ [1160] {sys = []} {mqs = []} h auto contradict
    where
      h : (⟦ μ , ῆ ⟧ ∷ ⟦ ν , ι , ν ⟧ ∷ []) ~ (just ─ ∷ nothing ∷ [])
      h = long (inj₁ auto)
        ∷ ambiguous contradict contradict
        ∷ []

  H₂ : word ⟦ ⟦ ἄ ⟧ ⟧⁺ ~ V.[ nothing ]
  H₂ = base (λ ()) (ambiguous contradict contradict ∷ [])

  H : (word ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ ∷ word ⟦ ⟦ ἄ ⟧ ⟧⁺ ∷ [])
    ~ (just ─ ∷ just ˘ ∷ nothing ∷ [])
  H = H₁ ∷ H₂ ∷ []

  μῆνιν-ἄ : (word ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ ∷ word ⟦ ⟦ ἄ ⟧ ⟧⁺ ∷ [])
          ~ mkPM [ -, -, ─˘˘ ]
  μῆνιν-ἄ = H ~∘~ [1169]
    where
      [1169] : (just ─ ∷ just ˘ ∷ nothing ∷ []) ~ mkPM [ -, -, ─˘˘ ]
      [1169] = reify (refl ∷ refl ∷ tt ∷ []) $ base (dactyl base)

  ABSURD : (word ⟦ ⟦ μ , ῆ ⟧ , ⟦ ν , ι , ν ⟧ ⟧⁺ ∷ word ⟦ ⟦ ῆ ⟧ ⟧⁺ ∷ [])
         ≁ (just ─ ∷ just ─ ∷ just ─ ∷ [])
  ABSURD (base _ (_ ∷ long ─ι ∷ _) ∷ _) = contradict ─ι
  ABSURD (_∷_ ⦃ () ⦄ (fromBelow ([1160] {mqs = []} _ _ _)) _)

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
