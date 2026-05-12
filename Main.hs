{-# LANGUAGE LambdaCase, ViewPatterns #-}
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

type Syllable = String
type Word     = [Syllable]
type Verse    = [Word]
type Book     = [Verse]

-- ** pre-processing

preprocess, insertDigamma, fixDoubtfuls, unlambda :: Verse -> Verse
preprocess
  = insertDigamma
  . fixDoubtfuls
  . unlambda
insertDigamma = map $ \case
  ["ἔ","δει","σεν"] -> ["ἔ","ϝδει","σεν"]
  w -> w
fixDoubtfuls = map $ \case
  ["ῥα"] -> ["ῥᾰ"]
  ["ῥά"] -> ["ῥᾰ"]
  w -> w
unlambda = map $ map $ map $ \case
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
derivations = AGDA.checkVerseMin . insertDigamma . fixDoubtfuls

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
    v <- readVerse s
    checkVerse v
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
    let ds = derivations v
    T.putStrLn $ showDerivations v ds


