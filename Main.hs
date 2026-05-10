{-# LANGUAGE LambdaCase, ViewPatterns #-}
module Main where

import Prelude hiding (Word)
import System.Environment (getArgs)
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

derivations :: Verse -> T.Text
derivations = AGDA.checkVerseMin . insertDigamma . fixDoubtfuls

nonDerivable :: T.Text -> Bool
nonDerivable = T.elem '∅'

data VerseIndex = Int :.: Int

instance Show VerseIndex where
  show (b :.: v) = show (b + 1) <> "." <> show (v + 1)

readVerseIndex :: String -> VerseIndex
readVerseIndex s =
  let
    (b,'.':v) = break (== '.') s
  in
    (read b - 1) :.: (read v - 1)

getVerse :: VerseIndex -> Verse
getVerse (b :.: v) = (allBooks !! b) !! v

enumerateFrom :: Int -> [a] -> [(Int, a)]
enumerateFrom n = zip [n..]

enumerate :: [a] -> [(Int, a)]
enumerate = enumerateFrom 0

allIndices :: [VerseIndex]
allIndices =
  flip concatMap (enumerate allBooks) $ \(i, b) ->
    flip map (enumerate b) $ \(j, _) ->
      i :.: j

main :: IO ()
main = getArgs >>= \case
  [] -> do
    putStrLn "Counterexamples:"
    forM_ allIndices $ \i -> let v = getVerse i in
      when (nonDerivable $ derivations v) $
        print i
  ["--explain", s] -> do
    v <- readVerse s
    checkVerse v
    T.putStrLn $ AGDA.explainVerse v
  [s] -> checkVerse =<< readVerse s
  as -> checkVerse (parseVerse as)
 where
  readVerse :: String -> IO Verse
  readVerse s = do
    let i = readVerseIndex s
    putStrLn $ "\nv" <> show i <> ")\n"
    return $ getVerse i

  parseVerse :: [String] -> Verse
  parseVerse = map (splitOn "-")

  checkVerse :: Verse -> IO ()
  checkVerse (preprocess -> v) = do
    let ds = derivations v
    if (nonDerivable ds) then
      T.putStrLn $ T.pack "∅\n" <> AGDA.debugVerse v
    else
      T.putStrLn ds


