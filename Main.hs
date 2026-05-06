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

insertDigamma :: Verse -> Verse
insertDigamma = map $ \case
  ["ἔ","δει","σεν"] -> ["ἔ","ϝδει","σεν"]
  w -> w

derivations :: Verse -> T.Text
derivations = AGDA.checkVerseMin . insertDigamma

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
  as -> forM_ (map readRange as) $ \r@(i0 :-: _) -> do
    putStrLn "-----------------------------------------------"
    putStrLn $ "Derivations (" <> show r <> "):\n\n"
    forM_ (zip [i0..] $ verses ! r) $ \(i, v) -> do
      putStrLn $ "v" <> show i <> ")\n"
      let ds = derivations v
      if (nonDerivable ds) then
        T.putStrLn $ T.pack "∅\n" <> AGDA.debugVerse v
      else
        T.putStrLn ds

