{-# LANGUAGE LambdaCase, ViewPatterns, BlockArguments #-}
module Main where

import Prelude hiding (Word)
import System.Environment (getArgs)
import System.IO
import System.CPUTime
import Control.Monad (forM, when)
import Data.List (sort)
import Data.List.Split (splitOn)
import Text.Printf (printf)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified MAlonzo.Code.Iliagda.ToHaskell as AGDA
import Books.All (allBooks)

type Letter   = Char
type Syllable = String
type Word     = [Syllable]
type Verse    = [Word]
type Book     = [Verse]

-- ** pre-processing

onLetter :: (Letter -> Letter) -> Verse -> Verse
onLetter = map . map . map
onWord :: (Word -> Word) -> Verse -> Verse
onWord = map
onVerse :: (Verse -> Verse) -> Verse -> Verse
onVerse = id

preprocess, insertDigamma, fixDoubtfuls, unlambda :: Verse -> Verse
preprocess
  = repairVerses
  . insertDigamma
  . fixDoubtfuls
  . unlambda
repairVerses = onVerse \case
  (["φί","λε"]:ws) -> (["φη","λε"]:ws)
    -- NB: also remove acute accent to disable [1161]
  (["ἐ","πεὶ"]:ws) -> (["η","πεὶ"]:ws)
  v -> v
insertDigamma = onWord \case
  ["ἔ","δει","σεν"] -> ["ἔ","δϝει","σεν"]
  ["ὑ","πέ","δει","σαν"] -> ["ὑ","πέ","δϝει","σαν"]
  ["ὑ","πο","δεί","σαν","τες"] -> ["ὑ","πο","δϝεί","σαν","τες"]
  ["δ᾽ἔ","δει","σε"] -> ["δ᾽ἔ","δϝει","σε"]
  ["ἐ","δεί","σα","τε"] -> ["ἐ","δϝεί","σα","τε"]
  ["σ᾽ὑ","πο","δεί","σαν","τες"] -> ["σ᾽ὑ","πο","δϝεί","σαν","τες"]
  ["γ᾽ἔ","δει","σας"] -> ["γ᾽ἔ","δϝει","σας"]
  ["σ᾽ὑ","πο","δεί","σας"] -> ["σ᾽ὑ","πο","δϝεί","σας"]
  -- other cases of inserting consonants
  ["Βο","ρέ","ῃ"] -> ["Βορ","ρέ","ῃ"]
  ["Βο","ρέ","ης"] -> ["Βορ","ρέ","ης"]
  ["φι","λο","μει","δὴς"] -> ["φι","λομ","μει","δὴς"]
  ["φι","λο","μει","δής"] -> ["φι","λομ","μει","δής"]
  -- other cases of inserting vowels
  ["ἐ","λίσ","σε","το"] -> ["εἰ","λίσ","σε","το"]
  w -> w
fixDoubtfuls = onWord $ \case
  -- vrachy ᾰ
  ["ῥα"] -> ["ῥᾰ"]
  ["ῥά"] -> ["ῥᾰ"]
  ["πτε","ρό","εν","τα"] -> ["πτε","ρό","εν","τᾰ"]
  ["πολ","λὰ"] -> ["πολ","λᾰ"]
  ["ἔρ","γα"] -> ["ἔρ","γᾰ"]
  ["ἀλ","λὰ"] -> ["ἀλ","λᾰ"]
  ["ἄν","τα"] -> ["ἄν","τᾰ"]
  ["Ἀ","φρο","δί","τη"] -> ["Ᾰ","φρο","δί","τη"]
  ["Ἀ","φρο","δί","τῃ"] -> ["Ᾰ","φρο","δί","τῃ"]
  ["Ἀ","φρο","δί","της"] -> ["Ᾰ","φρο","δί","της"]
  ["Ἀ","φρο","δί","την"] -> ["Ᾰ","φρο","δί","την"]
  ["δ᾽Ἀ","φρο","δί","την"] -> ["δ᾽Ᾰ","φρο","δί","την"]
  ["τ᾽Ἀ","φρο","δί","τη"] -> ["τ᾽Ᾰ","φρο","δί","τη"]
  ["γυμ","νω","θέν","τα"] -> ["γυμ","νω","θέν","τᾰ"]
  ["ἀ","βρό","τη"] -> ["ᾰ","βρό","τη"]
  ["κα","λὰ"] -> ["κα","λᾰ"]
  ["ἐ","λε","ει","νὰ"] -> ["ἐ","λε","ει","νᾰ"]
  -- vrachy ῐ
  ("ἀμ":('φ':i:ls):sys) | i `elem` "ιὶ" -> ("ἀμ":("φῐ" <> ls):sys)
  ["τει","χε","σι","πλῆ","τα"] -> ["τει","χε","σῐ","πλῆ","τα"]
  ["ἐσ","σι"{-ί-}] -> ["ἐσ","σῐ"]
  ["ἐ","στὶ"] -> ["ἐ","στῐ"]
  ["δ᾽εἰ","νὶ"] -> ["δ᾽εἰ","νῐ"]
  ["ὅ","θι"] -> ["ὅ","θῐ"] -- due to Wyer Grammar book (dative plural)
  ["δου","ρὶ"] -> ["δου","ρῐ"]
  ["δ᾽ἀμ","φὶ"] -> ["δ᾽ἀμ","φῐ"]
  -- vrachy ῠ
  ["ὀ","ξὺ"] -> ["ὀ","ξῠ"]
  -- DB-Monro pg.343 footnote
  ["ἀν","δρο","τῆ","τά"] -> ["ᾰ","δρο","τῆ","τά"]
  ["ἀν","δρο","τῆ","τα"] -> ["ᾰ","δρο","τῆ","τα"]
  -- DB-Monro pg.??
  ["ἀ","βρο","τά","ξο","μεν"] -> ["ᾰ","βρο","τά","ξο","μεν"]

  -- ???
  -- ["χάρ","μα"] -> ["χάρ","μᾰ"]
  w -> w
unlambda = onLetter $ \case
  'ƛ' -> 'λ'
  c -> c

-- ** indexing books & verses

data VerseIndex = Int :.: Int

instance Show VerseIndex where
  show (b :.: v) = show (b + 1) <> "." <> show (v + 1)

readVerseIndex :: String -> VerseIndex
readVerseIndex s
  | (b,'.':v) <- break (== '.') s
  = (read b - 1) :.: (read v - 1)
  | otherwise
  = error "Input verse in `BOOK.VERSE` format."

getVerse :: VerseIndex -> Verse
getVerse (b :.: v) = (allBooks !! b) !! v

allIndices :: [VerseIndex]
allIndices =
  flip concatMap (zip [0..] allBooks) $ \(i, b) ->
    flip map (zip [0..] b) $ \(j, _) ->
      i :.: j

-- ** computing derivations

type Derivations = [[T.Text]]

derivations :: Verse -> Derivations
derivations = AGDA.checkVerseMin . preprocess

showDerivations :: Verse -> Derivations -> T.Text
showDerivations v (concat -> ds)
  | null ds   = T.pack "∅\n" <> AGDA.debugVerse v
  | otherwise = T.unlines $ map (<> T.pack "\n") ds

reportDerivations :: [Int] -> String
reportDerivations ns
  | null ns   = "×"
  | otherwise = "✓ " <> show ns

reportStats :: [[Int]] -> String
reportStats nss = unlines (byFeet ++ [""] ++ bySpurious)
  where
  byFeet = let fs = map length nss in
    flip map [0..maximum fs] $ \f ->
     show f <> "-meter derivations: " <> show (length $ filter (== f) fs)
  bySpurious = let ns = concat nss in
    flip map [1..maximum ns] $ \n ->
     show n <> "-parse derivations: " <> show (length $ filter (== n) ns)

-- ** USAGE **
--
-- Report on derivations of all verses:
--    $ iliagda
--
-- Check a single verse from one of the books:
--    $ iliagda <BOOK>.<VERSE>
--
-- Explain a single verse from one of the books:
--    $ iliagda explain <BOOK>.<VERSE>
--
-- Explain a single given verse (syllables separated by '-'):
--    $ iliagda sy₁-sy₂-...-syₙ <WORD₂> ... <WORDₘ>
--
main :: IO ()
main = getArgs >>= \case
  [] -> do
    start <- getCPUTime
    nss <- forM allIndices $ \i -> let ds = derivations $ getVerse i in do
      let ns = map length ds
      putStrLn $ show i <> ": " <> reportDerivations ns
      hFlush stdout
      return ns
    end <- getCPUTime
    putStrLn "--------------------------------"
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "total time: %0.3f sec\n" (diff :: Double)
    putStrLn "--------------------------------"
    putStrLn $ reportStats nss
  [s] -> checkVerse =<< readVerse s
  ["--explain", s] -> do
    v <- preprocess <$> readVerse s
    T.putStrLn $ AGDA.explainVerse v
  as -> checkVerse (map (splitOn "-") as)
 where
  readVerse :: String -> IO Verse
  readVerse s = do
    let i = readVerseIndex s
    putStrLn $ "\nv" <> show i <> ")\n"
    return $ getVerse i

  checkVerse :: Verse -> IO ()
  checkVerse (preprocess -> v) = do
    let ds = AGDA.checkVerseMin v
    T.putStrLn $ showDerivations v ds
