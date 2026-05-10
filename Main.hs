{-# LANGUAGE LambdaCase, ViewPatterns #-}
module Main where

import Prelude hiding (Word)
import System.Environment (getArgs)
import System.IO
import Control.Monad (forM_, when)
import Data.List.Split (splitOn)
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

reportDerivations :: Derivations -> String
reportDerivations ds
  | null ds   = "×"
  | otherwise = "✓ " <> show (map length ds)

showDerivations :: Verse -> Derivations -> T.Text
showDerivations v (concat -> ds)
  | null ds   = T.pack "∅\n" <> AGDA.debugVerse v
  | otherwise = T.unlines $ map (<> T.pack "\n") ds

-- **
main :: IO ()
main = getArgs >>= \case
  [] -> do
    forM_ allIndices $ \i -> let ds = derivations $ getVerse i in do
      putStrLn $ show i <> ": " <> reportDerivations ds
      hFlush stdout
  ["--explain", s] -> do
    v <- readVerse s
    checkVerse v
    T.putStrLn $ AGDA.explainVerse v
  [s] -> checkVerse =<< readVerse s
  as -> checkVerse (parseVerse as)
    where
    parseVerse :: [String] -> Verse
    parseVerse = map (splitOn "-")
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


