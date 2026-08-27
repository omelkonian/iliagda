{-# LANGUAGE OverloadedStrings #-}
module Corpus (allBooks) where

import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Text as T
import qualified Data.Text.IO as T

allBooks :: [[[[String]]]]
allBooks = map readBook [1 .. 24]

readBook :: Int -> [[[String]]]
readBook b = unsafePerformIO $
  map (map (map T.unpack . T.splitOn "-") . T.words) . T.lines
    <$> T.readFile ("artifacts/syllabified/" <> show b <> ".txt")
{-# NOINLINE readBook #-}
