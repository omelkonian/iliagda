{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Main where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Directory (createDirectoryIfMissing, copyFile, listDirectory, doesFileExist)

import Corpus (allBooks)
import Explanation.ToJson (J (..), parseJson, (.:), jList, jText, jInt)
import Site.Html

restored :: [(Int, Int)]
restored = [(8, 548), (8, 550), (8, 551), (8, 552),
            (9, 458), (9, 459), (9, 460), (9, 461),
            (18, 604)]

scansion :: J -> Scansion
scansion j = Scansion
  { sSyllables  = map jText (jList (j .: "syl"))
  , sWords      = map jInt  (jList (j .: "w"))
  , sQuantities = jText (j .: "q")
  , sMerges     = [locus f | f <- facts, rule f == "merge"]
  , sSupplied   = [(locus f, jInt (jList (f .: "a") !! 1)) | f <- facts, rule f == "unwritten"]
  }
  where
  facts = jList (j .: "f")
  locus f = jInt (f .: "i")
  rule f = jText (f .: "r")

bookVerses :: Int -> [[[String]]] -> J -> [Verse]
bookVerses b bookWords doc =
  [ Verse n (maybe [] id (lookup n byNumber)) (map (map T.pack) ws) ((b, n) `elem` restored)
  | (n, ws) <- zip [1 ..] bookWords ]
  where
  byNumber = [ (jInt (v .: "n"), map scansion (jList (v .: "s")))
             | v <- jList (doc .: "verses") ]

quotesJson :: IO Text
quotesJson = do
  let path = "Site/rule_quotes.json"
  have <- doesFileExist path
  if not have then pure "{}" else do
    raw <- T.readFile path
    case parseJson raw of
      Left e        -> fail (path <> ": " <> e)
      Right (O kvs) -> do
        let written = length [() | (_, S t) <- kvs, not (T.null (T.strip t))]
        putStrLn $ "quotes: " <> show written <> " of " <> show (length kvs) <> " written"
        pure raw
      Right _       -> fail (path <> ": expected an object of rule number to text")

main :: IO ()
main = do
  createDirectoryIfMissing True "docs/books"
  tpl <- T.readFile "Site/book.html"
  quotes <- quotesJson
  mapM_ (buildBook tpl quotes) (zip [1 ..] allBooks)
  copyFile "Site/index.html" "docs/index.html"
  static <- listDirectory "Site/static"
  mapM_ (\f -> copyFile ("Site/static/" <> f) ("docs/" <> f)) static
  putStrLn "wrote docs/"

buildBook :: Text -> Text -> (Int, [[[String]]]) -> IO (Int, Int)
buildBook tpl quotes (b, bookWords) = do
  let path = "artifacts/explanations/" <> show b <> ".json"
  have <- doesFileExist path
  if not have
    then do
      putStrLn $ "book " <> show b <> ": no artifact at " <> path <> ", skipped"
      pure (0, 0)
    else do
      raw <- T.readFile path
      doc <- either (fail . ((path <> ": ") <>)) pure (parseJson raw)
      let vs = bookVerses b bookWords doc
          un = length [() | v <- vs, null (vScansions v)]
      T.writeFile ("docs/books/" <> show b <> ".html") (bookPage tpl b vs raw quotes)
      putStrLn $ "book " <> show b <> ": " <> show (length vs) <> " verses, "
              <> show un <> " unscanned"
      pure (length vs, un)
