module Iliagda.Explanation.Explain where

open import Iliagda.Init
open import Prelude.Vectors
open import Iliagda.Morphology
open import Iliagda.Dec.Core
open import Iliagda.Prosody.Core
open import Iliagda.Prosody.Synizesis
open import Iliagda.Prosody.Rules.Core
open import Iliagda.Prosody.Rules.Level1
open import Iliagda.Prosody.Rules.Level2
open import Iliagda.Prosody.Rules.Level3
open import Iliagda.Prosody.Rules.Level4
open import Iliagda.Lexicon
open import Iliagda.Reading
open import Iliagda.Explanation

private variable i o k : ℕ

chr : Letter → Char
chr ƛ = 'λ'
chr l = toChar l

str : Letters → String
str = Str.fromList ∘ map chr

sylStr : Syllable → String
sylStr = str ∘ toList

toQ : Quantity → Qty
toQ = λ where
  ─ → long
  · → short

di : Letter × Letter → Ground
di (a , b) = diphthong (chr a) (chr b)

factQ : Fact → Maybe Qty
factQ = qty

resolveIn : List Fact → Ix → Maybe Ref
resolveIn es i = go 0 es nothing
  where
  go : ℕ → List Fact → Maybe Ref → Maybe Ref
  go _ [] acc = acc
  go r (e ∷ es) acc = go (suc r) es (if ⌊ e .locus Nat.≟ i ⌋ then just r else acc)

getAt : List Fact → ℕ → Maybe Fact
getAt [] _ = nothing
getAt (e ∷ _) zero = just e
getAt (_ ∷ es) (suc r) = getAt es r

appendFact : List Fact → Fact → List Fact
appendFact es e = es L.∷ʳ e

appendFacts : List Fact → List Fact → List Fact
appendFacts = _++_

preIx : {sys : Syllables n} {sys′ : Syllables n′}
  → sys -synizizes*- sys′ → ℕ → ℕ
preIx [] i = i
preIx (_ ∷ syn) zero = zero
preIx (_ ∷ syn) (suc i) = suc (preIx syn i)
preIx (_ ∺ syn) zero = 1
preIx (_ ∺ syn) (suc i) = suc (suc (preIx syn i))


trailingVowels : Syllable → Letters
trailingVowels = L.reverse ∘ go ∘ L.reverse ∘ toList
  where
  go : Letters → Letters
  go [] = []
  go (l ∷ ls) = case ¿ Vowel l ¿ of λ where
    (yes _) → l ∷ go ls
    (no _)  → []

last₂ : (ls : Letters)
  → CheckList (Vowel ∷ Consonant ∷ []) (L.drop (length ls ∸ 2) ls)
  → Letter × Letter
last₂ ls pf with L.drop (length ls ∸ 2) ls | pf
... | v ∷ c ∷ _ | _        = v , c
... | _ ∷ []    | (_ , ())
... | []        | ()

inPenultContent : ∀ {P : Pred₀ Syllable} {sys : Syllables n} → InPenult P sys → ∃ P
inPenultContent (here p) = -, p
inPenultContent (there u) = inPenultContent u

inAntepenultContent : ∀ {P : Pred₀ Syllable} {sys : Syllables n} → InAntepenult P sys → ∃ P
inAntepenultContent (here p) = -, p
inAntepenultContent (there u) = inAntepenultContent u

lastSy : Syllables n → String
lastSy sys = case L.last (toList sys) of λ where
  (just sy) → sylStr sy
  nothing   → ""

wordWidth : Word n → ℕ
wordWidth w = length (toList (unword w))

wordWidths : Words n → List ℕ
wordWidths [] = []
wordWidths (w ∷ ws) = wordWidth w ∷ wordWidths ws

mkRestoration : ∀ {sys : Syllables n} → Ix → Edit sys n → Reading → Fact
mkRestoration o (unwritten c i k) r =
  mkFact (o + Fi.toℕ i) (unwritten (chr c) (Fi.toℕ k) (str (readingKey r))) nothing

explainReads : Ix → ws -reads- ws′ → List Fact
explainReads o [] = []
explainReads o (skip {w = w} rd) = explainReads (o + wordWidth w) rd
explainReads o (edit {w = w} {r = r} {e = e} _ _ rd) =
  mkRestoration o e r ∷ explainReads (o + wordWidth w) rd

open ∣Sy-Q∣
open ∣Sy-MQ∣

explain¹ : Ix → sy ∣Sy-Q∣.~′ q → Fact
explain¹ i = λ where
  (longByNature (inj₁ d∈)) →
    mkFact i (longByNature (di (L.Any.lookup d∈))) nothing
  (longByNature (inj₂ (inj₁ v∈))) →
    mkFact i (longByNature (longVowel (chr (L.Any.lookup v∈)))) nothing
  (longByNature (inj₂ (inj₂ c∈))) →
    mkFact i (longByNature (circumflex (chr (L.Any.lookup c∈)))) nothing
  (shortByNature v∈ _) →
    mkFact i (shortByNature (chr (L.Any.lookup v∈))) nothing

explainSys : Ix → sys ∣Sys-Qs∣.~′ mqs → List Fact
explainSys o ∣Sys-Qs∣.[] = []
explainSys o (p ∣Sys-Qs∣.∷ ps) with p
... | byNature p¹ = explain¹ o p¹ ∷ explainSys (suc o) ps
... | doubtful _  = explainSys (suc o) ps

matchOf : Mode → Match
matchOf (exact _)  = whole
matchOf (prefix _) = stem

explainLex : ∀ {lex} → Ix → sys ~L lex → List Fact
explainLex o (byLexicon h) =
  [ mkFact (o + Fi.toℕ (h .ix))
         (byLexicon (toQ (h .entry .qty)) (str (h .entry .key)) (matchOf (h .entry .mode)))
         nothing ]
explainLex o (noLex _) = []

explainNature : Ix → ws ~² mqs → List Fact
explainNature o [] = []
explainNature o (_∷_ {w = w} (𝟙-then-L-then-𝟚 p₁ _ _) pws) =
  explainSys o p₁ ++ explainNature (o + wordWidth w) pws

explainLexicon : Ix → ws ~² mqs → List Fact
explainLexicon o [] = []
explainLexicon o (_∷_ {w = w} (𝟙-then-L-then-𝟚 _ pₗ _) pws) =
  explainLex o pₗ ++ explainLexicon (o + wordWidth w) pws

module _ (resolve : Ix → Maybe Ref) where

  explain²′ : Ix → ℕ → String → ∀ {f} → mqs ⊨ sys ~%′ f → List Fact
  explain²′ o k ult = λ where
    ([1160] ip) →
      [ mkFact (o + k ∸ 1) ([1160] (chr (L.Any.lookup (inPenultContent ip .proj₂)))
                                 (sylStr (inPenultContent ip .proj₁))) nothing ]
    ([1161] _ ip) →
      [ mkFact (o + k ∸ 1) ([1161] (chr (L.Any.lookup (inPenultContent ip .proj₂)))
                                 (sylStr (inPenultContent ip .proj₁)))
             (resolve (o + k ∸ 2)) ]
    ([1162] _ _ ip) →
      [ mkFact (o + k ∸ 2) ([1162] (chr (L.Any.lookup (inPenultContent ip .proj₂)))
                                 ult)
             (resolve (o + k ∸ 1)) ]
    ([1163] ia) →
      [ mkFact (o + k ∸ 1) ([1163] (chr (L.Any.lookup (inAntepenultContent ia .proj₂)))
                                 (sylStr (inAntepenultContent ia .proj₁))) nothing ]

  explain² : Ix → ℕ → String → ∀ {f} → mqs ⊨ sys ~% f → List Fact
  explain² o k ult = λ where
    ([1164] _) → []
    ([574] _) → []
    ([575] _) → []
    (fromBelow _ _ _ _ p) → explain²′ o k ult p
    (noop _) → []

  explainAccent : Ix → ws ~² mqs → List Fact
  explainAccent o [] = []
  explainAccent o (_∷_ {w = w} (𝟙-then-L-then-𝟚 _ _ pw) pws) =
    let k = wordWidth w in
    explain² o k (lastSy (unword w)) pw ++ explainAccent (o + k) pws

wordEnds : Words n → List ℕ
wordEnds = go 0
  where
  go : ℕ → Words n → List ℕ
  go o [] = []
  go o (w ∷ ws) = let k = wordWidth w in (o + k ∸ 1) ∷ go (o + k) ws

mergeFacts : {sys : Syllables n} {sys′ : Syllables n′}
  → List ℕ → ℕ → sys -synizizes*- sys′ → List Fact
mergeFacts bounds i [] = []
mergeFacts bounds i (_ ∷ syn) = mergeFacts bounds (suc i) syn
mergeFacts bounds i (_∺_ {sy = sy} {sy′ = sy′} _ syn) =
  mkFact (suc i) (merge (sylStr sy) (sylStr sy′) ⌊ ¿ i ∈ bounds ¿ ⌋) nothing
  ∷ mergeFacts bounds (2 + i) syn

mtl : MuteThenLiquid ls → Letter × Letter × Bool
mtl (muteLiquid {l = l} {l′ = l′} _ ln) =
  l , l′ , (case ln of λ where (inj₁ _) → false; (inj₂ _) → true)

dcLetter : StartsWithDoubleConsonant ls → Letter
dcLetter (doubleConsonant {l = l} _) = l

ccLetters : StartsWithTwoConsonants ls → Letter × Letter
ccLetters (twoConsonants {l = l} {l′ = l′} _ _) = l , l′

swVowel : StartsWithVowel ls → Letter
swVowel (vowel {l = l} _) = l

module _ {⋯ : Flat Quantity × Context} where
  open QuantityRules ⋯

  private
    spill straddle : Reach
    spill = case ⋯ .proj₂ of λ where
      (outer _) → nextWord
      (inner _) → nextSyllable
      ∅ → within
    straddle = case ⋯ .proj₂ of λ where
      (outer _) → straddleWord
      (inner _) → straddleSyllable
      ∅ → within

  posFB : (v∈ : Any Vowel ls)
    → FollowedBy (StartsWithDoubleConsonant ∪¹ StartsWithTwoConsonants) v∈
    → Position
  posFB (there v∈) q = posFB v∈ q
  posFB (here {xs = sys} _) (inj₁ dc) =
    doubleConsonant (chr (dcLetter dc)) (if ⌊ length sys Nat.≤? 0 ⌋ then spill else within)
  posFB (here {xs = sys} _) (inj₂ cc) =
    let l , l′ = ccLetters cc
        reach = case length sys of λ where
          0 → spill
          1 → straddle
          _ → within
    in twoConsonants (chr l) (chr l′) reach

  vowelFB : (v∈ : Any Vowel ls) → FollowedBy StartsWithVowel v∈ → Letter
  vowelFB (there v∈) q = vowelFB v∈ q
  vowelFB (here _) q = swVowel q

  mtlOuter : (v∈ : Any Vowel ls) → FollowedByOuter MuteThenLiquid v∈
    → Letter × Letter × Bool
  mtlOuter (there v∈) q = mtlOuter v∈ q
  mtlOuter (here {xs = []} _) q = mtl q
  mtlOuter (here {xs = _ ∷ _} _) ()

mtlInner : (v∈ : Any Vowel ls) → FollowedByInner MuteThenLiquid v∈
  → Letter × Letter × Bool
mtlInner (there v∈) q = mtlInner v∈ q
mtlInner (here _) q = mtl q

isOuter : Context → Bool
isOuter = λ where
  (outer _) → true
  _ → false

module _ (resolve : Ix → Maybe Ref) where

  explain³∗ : ∀ {mq ctx} → Ix → Qty → (mq , ctx) ⊢ sy ~∗ q → Fact
  explain³∗ {sy = sy} {ctx = ctx} i qt = λ where
    (QuantityRules.[522] v∈ pf) →
      mkFact i ([522] (chr (L.Any.lookup v∈)) (posFB v∈ pf)) (resolve i)
    (QuantityRules.[1173] v∈ _ _ pf) →
      mkFact i ([1173] qt (str (trailingVowels sy)) (chr (vowelFB v∈ pf)) (isOuter ctx))
             (resolve i)
    (QuantityRules.[524] v∈ _ (inj₁ pf)) →
      let m , l , nas = mtlInner v∈ pf
      in mkFact i ([524] qt (chr (L.Any.lookup v∈)) (chr m) (chr l) nas) (resolve i)
    (QuantityRules.[524] v∈ _ (inj₂ pf)) →
      let m , l , nas = mtlOuter v∈ pf
      in mkFact i ([524] qt (chr (L.Any.lookup v∈)) (chr m) (chr l) nas) (resolve i)

  explain³′ : ∀ {mq ctx} → Ix → Quantity → (mq , ctx) ⊢ sy ~? mq′ → List Fact
  explain³′ i rq = λ where
    (QuantityRules.ambiguous _) → []
    (QuantityRules.certain {q = q} p _) → [ explain³∗ i (toQ q) p ]
    (QuantityRules.ambivalent _ p·) → [ explain³∗ i (toQ rq) p· ]

  explain³ : ∀ {xs : Vec (Syllable × Flat Quantity × Context) n} {mqs : Quantities n}
    → Ix → Vec Quantity n → VPointwise _~_ xs mqs → List Fact
  explain³ i [] [] = []
  explain³ i (rq ∷ rqs) (p ∷ ps) = explain³′ i rq p ++ explain³ (suc i) rqs ps

  explain⁴ : ∀ {ws : Words n} {qs : Vec Quantity n} {pm : Meter n m}
    → Ix → ℕ → (ws , qs) ˢ~ᵐ pm → List Fact
  explain⁴ i f [] = []
  explain⁴ i f (sponde p) = explain⁴ (2 + i) (suc f) p
  explain⁴ i f (dactyl p) = explain⁴ (3 + i) (suc f) p
  explain⁴ i f ([1168] {ws = ws′} {sy = sy} e b p) =
    let v , c = last₂ (toList sy) e
    in mkFact i ([1168] (chr v) (chr c) (chr (head (firstSy ws′)))) (resolve i) ∷ explain⁴ i f p
  explain⁴ i f ([1167/1a] p) =
    mkFact i [1167/1a] (resolve i) ∷ explain⁴ i f p
  explain⁴ i f ([1167/1b] _ p) =
    mkFact (suc i) ([1167/1b] (suc f)) (resolve (suc i)) ∷ explain⁴ (2 + i) (suc f) p

private
  indexed : List Fact → List (ℕ × Fact)
  indexed es = L.zip (L.upTo (length es)) es

  findNew : List ℕ → Ref → Maybe Ref
  findNew ord r = go 0 ord
    where
    go : ℕ → List ℕ → Maybe Ref
    go _ [] = nothing
    go k (x ∷ xs) = if ⌊ x Nat.≟ r ⌋ then just k else go (suc k) xs

  Assoc : Type → Type
  Assoc A = List (ℕ × A)

  look : ∀ {A : Type} → Assoc A → ℕ → Maybe A
  look [] _ = nothing
  look ((j , v) ∷ m) i = if ⌊ i Nat.≟ j ⌋ then just v else look m i

  isMerge : Rule → Bool
  isMerge = λ where
    (merge _ _ _) → true
    _ → false

  _∈ᵇ_ : ℕ → List ℕ → Bool
  i ∈ᵇ [] = false
  i ∈ᵇ (j ∷ js) = if ⌊ i Nat.≟ j ⌋ then true else i ∈ᵇ js

  filterᵇ : ∀ {A : Type} → (A → Bool) → List A → List A
  filterᵇ p [] = []
  filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

reloc : (ℕ → ℕ) → List Fact → List Fact
reloc f = map λ e → record e { locus = f (e .locus) }

absorbed : {sys : Syllables n} {sys′ : Syllables n′}
  → ℕ → sys -synizizes*- sys′ → List ℕ
absorbed i [] = []
absorbed i (_ ∷ syn) = absorbed (suc i) syn
absorbed i (_ ∺ syn) = i ∷ suc i ∷ absorbed (2 + i) syn

prune : List ℕ → List Fact → List Fact
prune dead es = let kept , red = go 0 0 [] [] [] [] es in
                map (λ e → record e { ref = e .ref May.>>= look red }) kept
  where
  reaffirms : Assoc Qty → List ℕ → Fact → Bool
  reaffirms std mgd e = if isMerge (e .rule) then false else
    if e .locus ∈ᵇ dead 𝔹.∧ 𝔹.not (e .locus ∈ᵇ mgd) then true else
    case e .qty of λ where
      nothing  → false
      (just q) → case look std (e .locus) of λ where
                   nothing   → false
                   (just q′) → ⌊ q ≟ q′ ⌋

  stand : Assoc Qty → Fact → Assoc Qty
  stand std e = case e .qty of λ where
    nothing  → std
    (just q) → (e .locus , q) ∷ std

  own : Assoc Ref → ℕ → Fact → Assoc Ref
  own o new e = case e .qty of λ where
    nothing  → o
    (just _) → (e .locus , new) ∷ o

  go : ℕ → ℕ → Assoc Qty → Assoc Ref → List ℕ → Assoc Ref → List Fact
     → List Fact × Assoc Ref
  go old new std o mgd red [] = [] , red
  go old new std o mgd red (e ∷ es) =
    if reaffirms std mgd e
    then go (suc old) new std o mgd
            (case look o (e .locus) of λ where
               (just r) → (old , r) ∷ red
               nothing  → red) es
    else let mgd′ = if isMerge (e .rule) then e .locus ∷ mgd else mgd
             ks , red′ = go (suc old) (suc new) (stand std e) (own o new e) mgd′
                            ((old , new) ∷ red) es
         in e ∷ ks , red′

byLocus : ℕ → List Fact → List Fact
byLocus n′ es = map reref sorted
  where
  isText : Fact → Bool
  isText e = case e .qty of λ where
    nothing  → true
    (just _) → false

  pick : (Fact → Bool) → List (ℕ × Fact)
  pick p = concatMap
    (λ i → filterᵇ (λ ie → ⌊ ie .proj₂ .locus Nat.≟ i ⌋ 𝔹.∧ p (ie .proj₂)) (indexed es))
    (L.upTo n′)

  byLocus′ : List (ℕ × Fact)
  byLocus′ = pick isText ++ pick (𝔹.not ∘ isText)

  factAt : ℕ → Maybe (ℕ × Fact)
  factAt r = L.head (filterᵇ (λ x → ⌊ x .proj₁ Nat.≟ r ⌋) byLocus′)

  emit : ℕ → List ℕ → ℕ × Fact → List ℕ × List (ℕ × Fact)
  emit zero seen x@(i , _) = i ∷ seen , [ x ]
  emit (suc f) seen x@(i , e) =
    if i ∈ᵇ seen then seen , [] else
    case e .ref of λ where
      nothing  → i ∷ seen , [ x ]
      (just r) → if r ∈ᵇ seen then i ∷ seen , [ x ] else
                 case factAt r of λ where
                   nothing  → i ∷ seen , [ x ]
                   (just y) → let seen′ , ys = emit f seen y
                              in i ∷ seen′ , ys ++ [ x ]

  sorted : List (ℕ × Fact)
  sorted = go byLocus′ (length byLocus′) []
    where
    go : List (ℕ × Fact) → ℕ → List ℕ → List (ℕ × Fact)
    go []       _ _    = []
    go (x ∷ xs) f seen = let seen′ , ys = emit f seen x
                         in ys ++ go xs f seen′

  ord : List ℕ
  ord = map proj₁ sorted

  reref : ℕ × Fact → Fact
  reref (_ , e) = record e { ref = e .ref May.>>= findNew ord }

open ∣Complies-MQs-HM∣
open ∣Complies-Ws-HM∣

explain : {ws : Words n} {hm : Hexameter n′} → ws ~ hm → Explanation
explain {ws = ws} {hm = hm}
  (_▷_≫⟨_⟩≫_≫_ {ws″ = ws″} rd p₂ syn p₃ (reify {qs = qs} _ p₄)) =
  let
    sys  = unwords ws″
    m    = length (toList sys)
    pre  = preIx syn
    acc₀ = explainReads 0 rd
    acc₁ = appendFacts acc₀ (explainNature 0 p₂)
    acc₂ = appendFacts acc₁ (explainLexicon 0 p₂)
    acc₃ = appendFacts acc₂ (explainAccent (resolveIn acc₂) 0 p₂)
    acc₄ = appendFacts acc₃ (mergeFacts (wordEnds ws) 0 syn)
    acc₅ = appendFacts acc₄ (reloc pre (explain³ (resolveIn acc₄ ∘ pre) 0 qs p₃))
    acc₆ = appendFacts acc₅ (reloc pre (explain⁴ (resolveIn acc₅ ∘ pre) 0 0 p₄))
    last = m ∸ 1
    ref₁₈₄ = case resolveIn acc₆ last of λ where
      (just r) → case getAt acc₆ r of λ where
        (just e) → case factQ e of λ where
          (just short) → just r
          _ → nothing
        nothing → nothing
      nothing → nothing
  in
    explanation
      1
      (map sylStr (toList sys))
      (wordWidths ws″)
      (map toQ (toList (meter-qs hm)))
      (byLocus m (prune (absorbed 0 syn) (appendFact acc₆ (mkFact last [1184] ref₁₈₄))))
