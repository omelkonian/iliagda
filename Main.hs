{-# LANGUAGE LambdaCase, ViewPatterns, BlockArguments #-}
module Main where

import Prelude hiding (Word)
import System.Environment (getArgs)
import System.IO
import System.CPUTime
import Control.Monad (forM, forM_, when)
import Data.List (sort)
import Data.List.Split (splitOn)
import Text.Printf (printf)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified MAlonzo.Code.Iliagda.ToHaskell as AGDA
import qualified Explanation.Render as Render
import qualified Explanation.Check as Check
import Explanation (Explanation (..), Fact (..), ruleName, ruleNames)
import Books.All (allBooks)

type Letter   = Char
type Syllable = String
type Word     = [Syllable]
type Verse    = [Word]
type Book     = [Verse]

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
derivations = AGDA.checkVerseMin

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
-- Explain a single verse from one of the books, or a given one:
--    $ iliagda --explain <BOOK>.<VERSE>
--    $ iliagda --explain sy₁-sy₂-...-syₙ <WORD₂> ... <WORDₘ>
--
-- Check the Explanation invariants over a book (or the whole corpus):
--    $ iliagda --check [BOOK]
--
-- Check a single given verse (syllables separated by '-'):
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
  ["--explain", s] -> explainVerse =<< readVerse s
  ("--explain" : as) -> explainVerse (map (splitOn "-") as)
  ["--check"] -> checkAll allIndices
  ["--check", b] -> checkAll [i | i@(b' :.: _) <- allIndices, b' == read b - 1]
  [s] -> checkVerse =<< readVerse s
  as -> checkVerse (map (splitOn "-") as)
 where
  checkAll :: [VerseIndex] -> IO ()
  checkAll ixs = do
    fired <- fmap concat $ forM ixs $ \i -> do
      let ds = AGDA.explainVerse (getVerse i)
      fmap concat $ forM ds $ \d@(Explanation _ _ _ fs) -> do
        mapM_ (\v -> T.putStrLn (T.pack (show i <> ": ") <> v)) (Check.violations d)
        return [ruleName r | Fact _ r _ _ <- fs]
    putStrLn "--------------------------------"
    forM_ ruleNames $ \r ->
      putStrLn $ T.unpack r <> ": " <> case length (filter (== r) fired) of
        0 -> "NEVER FIRED"
        k -> show k

  readVerse :: String -> IO Verse
  readVerse s = do
    let i = readVerseIndex s
    putStrLn $ "\nv" <> show i <> ")\n"
    return $ getVerse i

  explainVerse :: Verse -> IO ()
  explainVerse v = case AGDA.explainVerse v of
    [] -> putStrLn "∅"
    ds -> sequence_
      [ do putStrLn ("  derivation " <> show i <> " of " <> show (length ds))
           T.putStrLn (Render.render d)
      | (i, d) <- zip [1 :: Int ..] ds ]

  checkVerse :: Verse -> IO ()
  checkVerse v = do
    let ds = AGDA.checkVerseMin v
    T.putStrLn $ showDerivations v ds
