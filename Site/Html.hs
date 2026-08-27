{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Site.Html (Scansion (..), Verse (..), bookPage) where

import Data.Text (Text)
import qualified Data.Text as T

data Scansion = Scansion
  { sSyllables  :: [Text]
  , sWords      :: [Int]
  , sQuantities :: Text
  , sMerges     :: [Int]
  , sSupplied   :: [(Int, Int)]
  }

data Verse = Verse
  { vNumber    :: Int
  , vScansions :: [Scansion]
  , vWords     :: [[Text]]
  , vRestored  :: Bool
  }

bookLetters :: [Text]
bookLetters = T.chunksOf 1 "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"

greekNumerals :: [Text]
greekNumerals = ["α´", "β´", "γ´", "δ´", "ε´", "ϛ´"]

-- ** written syllables grouped into the syllables the metre scans

data Token = Token
  { tText  :: Text
  , tLast  :: Bool
  , tLocus :: Int
  , tSpan  :: Int
  }

type Glyph = (Char, Bool)

tokens :: Scansion -> [Token]
tokens sc = go 0 (lasts (sWords sc))
  where
  go _ [] = []
  go i (_ : l' : ls)
    | (i + 1) `elem` sMerges sc =
        Token (markup (glyphs i ++ [('\8255', False)] ++ glyphs (i + 1))) l' i 2
        : go (i + 2) ls
  go i (l : ls) = Token (markup (glyphs i)) l i 1 : go (i + 1) ls

  glyphs :: Int -> [Glyph]
  glyphs i = [(c, k `elem` ks) | (k, c) <- zip [0 :: Int ..] (T.unpack (sSyllables sc !! i))]
    where ks = [k | (j, k) <- sSupplied sc, j == i]

markup :: [Glyph] -> Text
markup gs = T.concat [wrap k g | (k, g) <- zip [0 ..] gs]
  where
  nucleus = case [k | (k, (c, _)) <- zip [0 ..] gs, isVowel c] of
    [] -> 0 :: Int
    ks -> last ks
  wrap k (c, supplied) =
    let inner = escape (T.singleton c)
        nuc | k == nucleus = "<i class=\"nuc\">" <> inner <> "</i>"
            | otherwise    = inner
    in if supplied then "<i class=\"sup\">" <> nuc <> "</i>" else nuc

isVowel :: Char -> Bool
isVowel c
  | c `elem` ("αεηιουωΑΕΗΙΟΥΩ" :: String)     = True
  | c `elem` ("\x1FE4\x1FE5\x1FEC" :: String) = False
  | c `elem` diacritics                       = False
  | c >= '\x1F00' && c <= '\x1FFF'            = True
  | c `elem` monotonic                        = True
  | otherwise                                 = False
  where
  diacritics = "\x1FBD\x1FBF\x1FC0\x1FC1\x1FCD\x1FCE\x1FCF\x1FDD\x1FDE\x1FDF\
               \\x1FED\x1FEE\x1FEF\x1FFD\x1FFE" :: String
  monotonic  = "\x0386\x0388\x0389\x038A\x038C\x038E\x038F\x0390\x03AC\x03AD\x03AE\x03AF\
               \\x03B0\x03CA\x03CB\x03CC\x03CD\x03CE" :: String

lasts :: [Int] -> [Bool]
lasts = concatMap (\n -> replicate (n - 1) False ++ [True])

-- ** the verse

verseHtml :: Verse -> Text
verseHtml v = T.concat
  [ "<div class=\"verse\" id=\"v", n, "\">\n"
  , "  <a class=\"vno\" href=\"#v", n, "\">"
  , if vRestored v then "[" <> n <> "]" else n, "</a>\n"
  , case vScansions v of
      [] -> "  " <> unscanned <> "\n"
      ss -> T.concat (zipWith scansionHtml [0 ..] ss)
  , "  ", selector, "\n"
  , "</div>\n"
  ]
  where
  n = tshow (vNumber v)

  unscanned = "<span class=\"vtext greek on nosc\" lang=\"grc\">"
           <> T.intercalate " " [escape (T.concat w) | w <- vWords v] <> "</span>"

  selector
    | null (vScansions v)       = "<span class=\"vside\"><span class=\"none\">\9785\65038\
                                  \<span class=\"why\">No derivations.</span>\
                                  \</span></span>"
    | length (vScansions v) < 2 = "<span class=\"vside\"></span>"
    | otherwise = "<span class=\"vside greek\" lang=\"grc\">"
        <> T.concat
           [ "<a data-r=\"" <> tshow i <> "\""
             <> (if i == (0 :: Int) then " class=\"on\"" else "")
             <> ">" <> num <> "</a>"
           | (i, num) <- zip [0 ..] (take (length (vScansions v)) greekNumerals) ]
        <> "</span>"

  scansionHtml :: Int -> Scansion -> Text
  scansionHtml i sc = T.concat
    [ "  <span class=\"vtext greek", on, "\" lang=\"grc\" data-r=\"", tshow i, "\">"
    , T.intercalate "\n    " (sylls sc), "</span>\n"
    , "  <ol class=\"varg", on, "\" data-r=\"", tshow i, "\" data-v=\"", n, "\"></ol>\n"
    ]
    where on = if i == 0 then " on" else ""

sylls :: Scansion -> [Text]
sylls sc =
  [ "<span class=\"w\">" <> T.concat [sylHtml k t | (k, t) <- w] <> "</span>"
  | w <- byWord (zip [0 :: Int ..] (tokens sc)) ]
  where
  byWord [] = []
  byWord ts = case break (tLast . snd) ts of
    (w, [])      -> [w]
    (w, t : ts') -> (w ++ [t]) : byWord ts'

  sylHtml k t = T.concat
    [ "<span class=\"syl"
    , "\" data-q=\"", mark k
    , "\" data-i=\"", tshow (tLocus t)
    , if tSpan t > 1 then "\" data-n=\"" <> tshow (tSpan t) else ""
    , "\">", tText t, "</span>"
    ]

  mark k = case T.unpack (T.take 1 (T.drop k (sQuantities sc))) of
    "S" -> "S"
    _   -> "L"

escape :: Text -> Text
escape = T.replace "<" "&lt;" . T.replace "&" "&amp;"

tshow :: Show a => a -> Text
tshow = T.pack . show

-- ** the page

fill :: [(Text, Text)] -> Text -> Text
fill env = go
  where
  go t
    | T.null rest = before
    | T.null close = t
    | otherwise = before <> maybe hole id (lookup key env) <> go (T.drop 2 close)
    where
    (before, rest) = T.breakOn "{{" t
    (key, close)   = T.breakOn "}}" (T.drop 2 rest)
    hole           = "{{" <> key <> "}}"

blob :: Text -> Text -> Text
blob i t
  | T.null t  = ""
  | otherwise = "<script type=\"application/json\" id=\"" <> i <> "\">" <> t <> "</script>\n"

booksNav :: Text -> Maybe Int -> Text
booksNav prefix current = T.concat
  [ "<a href=\"" <> prefix <> tshow b <> ".html\""
    <> (if Just b == current then " class=\"on\"" else "") <> ">" <> letter <> "</a>"
  | (b, letter) <- zip [1 :: Int ..] bookLetters ]

homeLink :: Text -> Text
homeLink root = "<a class=\"home\" href=\"" <> root <> "index.html\">Index</a>"

bookPage :: Text -> Int -> [Verse] -> Text -> Text -> Text
bookPage tpl b verses factsJson quotesJson = fill
  [ ("root", "../")
  , ("tab", "Book " <> tshow b <> " \8211 Iliagda")
  , ("title", title)
  , ("home", homeLink "../")
  , ("nav", booksNav "" (Just b))
  , ("body", T.concat (map verseHtml verses))
  , ("data", blob "facts" factsJson <> blob "quotes" quotesJson)
  ] tpl
  where title = "ΙΛΙΑΔΟΣ " <> bookLetters !! (b - 1)


