{-# LANGUAGE LambdaCase #-}
module Main where

import Prelude hiding (Word)
import System.Environment (getArgs)
import Control.Monad (forM_, when)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified MAlonzo.Code.Iliagda.ToHaskell as AGDA
import Books.All (allBooks)

type Syllable = String
type Word     = [Syllable]
type Verse    = [Word]

verses :: [Verse]
verses = allBooks

-- ** pre-processing

preprocess, insertDigamma, fixDoubtfuls :: Verse -> Verse
preprocess
  = insertDigamma
  . fixDoubtfuls
insertDigamma = map $ \case
  ["ἔ","δει","σεν"] -> ["ἔ","ϝδει","σεν"]
  w -> w
fixDoubtfuls = map $ \case
  ["ῥα"] -> ["ῥᾰ"]
  ["ῥά"] -> ["ῥᾰ"]
  w -> w

derivations :: Verse -> T.Text
derivations = AGDA.checkVerseMin . insertDigamma . fixDoubtfuls

nonDerivable :: T.Text -> Bool
nonDerivable = T.elem '∅'

-- ** ranges

data Range = Int :-: Int

(!) :: [a] -> Range -> [a]
xs ! (i :-: j) = take (j - i + 1) $ drop (i - 1) xs

instance Show Range where
  show (i :-: j) = show i <> ".." <> show j

readRange :: String -> Range
readRange s
  | (i, ('.':'.':j)) <- break (== '.') s
  = readIndex 1 i :-: readIndex (length verses - 1) j
  | otherwise
  = read s :-: read s
  where readIndex def = \case {"" -> def; s -> read s}

-- ** USAGE **
--
-- FIND COUNTER-EXAMPLES:
--   $ iliagda
-- OR SHOW DERIVATIONS:
--   $ iliagda <verse_range>*
--  eg iliagda ..42 1258..3780 15000..
main :: IO ()
main = getArgs >>= \case
  [] -> do
    putStrLn "Counterexamples:"
    forM_ (zip [1..] $ verses) $ \(i, v) ->
      when (nonDerivable $ derivations v) $ print i
  ["explain", s] -> do
    putStrLn $ "\nv" <> s <> ")\n"
    let v = verses !! (read s - 1)
    T.putStrLn $ AGDA.explainVerse v
  as -> forM_ (map readRange as) $ \r@(i0 :-: j) -> do
    putStrLn "-----------------------------------------------"
    when (i0 /= j) $ putStrLn $ "Derivations (" <> show r <> "):\n"
    forM_ (zip [i0..] $ verses ! r) $ \(i, v) -> do
      putStrLn $ "\nv" <> show i <> ")\n"
      let v' = preprocess v
      let ds = derivations v'
      if (nonDerivable ds) then
        T.putStrLn $ T.pack "∅\n" <> AGDA.debugVerse v'
      else
        T.putStrLn ds

