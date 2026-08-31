{-# LANGUAGE OverloadedStrings, LambdaCase #-}
-- | The wire format: an Explanation as JSON, hand-rolled.
--
-- The corpus run emits this; the site build reads it and links neither Agda nor
-- MAlonzo. Rule payloads go out positionally, keyed by 'ruleName': a consumer that
-- renders a rule necessarily knows that rule's shape, and an unknown name is a hard
-- error rather than a blank.
module Explanation.ToJson
  ( verseJson, bookJson
  , J (..), parseJson, (.:), jList, jText, jInt
  ) where

import Data.Char (isDigit)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Numeric (readHex)
import Explanation

-- ** a minimal JSON writer

data J = S Text | N Integer | B Bool | Null | A [J] | O [(Text, J)]

json :: J -> Text
json = \case
  S t   -> str t
  N n   -> T.pack (show n)
  B b   -> if b then "true" else "false"
  Null  -> "null"
  A xs  -> "[" <> T.intercalate "," (map json xs) <> "]"
  O kvs -> "{" <> T.intercalate "," [str k <> ":" <> json v | (k, v) <- kvs] <> "}"

-- @<@ is escaped so the document can be inlined in a @<script>@ element.
str :: Text -> Text
str t = "\"" <> T.concatMap esc t <> "\""
  where
  esc = \case
    '"'  -> "\\\""
    '\\' -> "\\\\"
    '<'  -> "\\u003c"
    '\n' -> "\\n"
    '\r' -> "\\r"
    '\t' -> "\\t"
    c    -> T.singleton c

-- ** the Explanation

qty :: Qty -> Text
qty = \case Long -> "L"; Short -> "S"

ch :: Char -> J
ch = S . T.singleton

-- | Positional, per rule. Nested sums lead with their own tag.
args :: Rule -> [J]
args = \case
  Unwritten c k form -> [ch c, N k, S form]
  LongByNature g -> case g of
    Diphthong a b -> [S "diphthong", ch a, ch b]
    LongVowel v   -> [S "longVowel", ch v]
    Circumflex v  -> [S "circumflex", ch v]
  ShortByNature v   -> [ch v]
  ByLexicon q key m -> [S (qty q), S key, S (case m of Whole -> "whole"; Stem -> "stem")]
  R1160 c w         -> [ch c, S w]
  R1161 c w         -> [ch c, S w]
  R1162 c w         -> [ch c, S w]
  R1163 c w         -> [ch c, S w]
  Merge l r cross   -> [S l, S r, B cross]
  R522 v p -> ch v : case p of
    DoubleConsonant c rc -> [S "doubleConsonant", ch c, S (reach rc)]
    TwoConsonants a b rc -> [S "twoConsonants", ch a, ch b, S (reach rc)]
  R1173 q nucleus next cross -> [S (qty q), S nucleus, ch next, B cross]
  R524 q v m l nasal         -> [S (qty q), ch v, ch m, ch l, B nasal]
  R1168 v c next             -> [ch v, ch c, ch next]
  R1167a                     -> []
  R1167b n                   -> [N n]
  R1184                      -> []
  R1164 u blocked            -> [S u, S blocked]
  R1165 w blocked            -> [S w, S blocked]
  where
  reach = \case
    Within -> "within"
    StraddleSyllable -> "straddleSyllable"; NextSyllable -> "nextSyllable"
    StraddleWord -> "straddleWord";         NextWord -> "nextWord"

fact :: Fact -> J
fact (Fact i r mq mref) = O $
  [("i", N i), ("r", S (ruleName r)), ("a", A (args r))]
  ++ [("q", S (qty q)) | Just q <- [mq]]
  ++ [("ref", N n) | Just n <- [mref]]

-- | @syl@ is the verse as read, one entry per written syllable; @q@ is one letter per
-- *scanned* syllable, and so is shorter by the number of merges.
scansion :: Explanation -> J
scansion (Explanation _ sys ws qs fs) = O
  [ ("syl", A (map S sys))
  , ("w",   A (map N ws))
  , ("q",   S (T.concat (map qty qs)))
  , ("f",   A (map fact fs))
  ]

-- ** one book, one document, one line per verse
--
-- Split in two so the corpus run can render and force a verse at a time: the progress
-- it reports is then work actually done, not a thunk.

verseJson :: Int -> [Explanation] -> Text
verseJson n es = json (O [("n", N (fromIntegral n)), ("s", A (map scansion es))])

bookJson :: Int -> [Text] -> Text
bookJson b vs = T.concat
  [ "{\"book\":", T.pack (show b), ",\"verses\":[\n"
  , T.intercalate ",\n" vs
  , "\n]}\n"
  ]

-- ** reading it back
--
-- Recursive descent, integers only — the writer above emits no other numbers. \\uXXXX is
-- read as a single code point; the writer never emits a surrogate pair.
--
-- The site build decodes the verse skeleton and lets the fact array travel to the page
-- as text, so nothing outside this module reconstructs a Rule.

parseJson :: Text -> Either String J
parseJson t = do
  (v, rest) <- value (skip t)
  if T.null (skip rest)
    then Right v
    else Left ("trailing input: " <> T.unpack (T.take 30 (skip rest)))

type P a = Either String (a, Text)

skip :: Text -> Text
skip = T.dropWhile (`elem` (" \n\r\t" :: String))

value :: Text -> P J
value t = case T.uncons t of
  Nothing -> Left "unexpected end of input"
  Just (c, r)
    | c == '"' -> fmap (\(s, r') -> (S s, r')) (string r)
    | c == '[' -> array (skip r)
    | c == '{' -> object (skip r)
    | c == 't', Just r' <- T.stripPrefix "rue" r   -> Right (B True, r')
    | c == 'f', Just r' <- T.stripPrefix "alse" r  -> Right (B False, r')
    | c == 'n', Just r' <- T.stripPrefix "ull" r   -> Right (Null, r')
    | c == '-' || isDigit c -> fmap (\(n, r') -> (N n, r')) (TR.signed TR.decimal t)
    | otherwise -> Left ("unexpected character " <> show c)

-- | after the opening quote
string :: Text -> P Text
string = go ""
  where
  go acc t = case T.break (\c -> c == '"' || c == '\\') t of
    (chunk, rest) -> case T.uncons rest of
      Just ('"', r)  -> Right (acc <> chunk, r)
      Just ('\\', r) -> case T.uncons r of
        Nothing -> Left "end of input inside escape"
        Just ('u', r') ->
          let (h, r'') = T.splitAt 4 r' in case readHex (T.unpack h) of
            [(n, "")] -> go (acc <> chunk <> T.singleton (toEnum n)) r''
            _         -> Left ("bad \\u escape: " <> T.unpack h)
        Just (e, r') -> case lookup e escapes of
          Just c  -> go (acc <> chunk <> T.singleton c) r'
          Nothing -> Left ("bad escape: \\" <> [e])
      _ -> Left "end of input inside string"
  escapes = [('"', '"'), ('\\', '\\'), ('/', '/'), ('n', '\n'), ('r', '\r'), ('t', '\t')
            ,('b', '\b'), ('f', '\f')]

array :: Text -> P J
array t0
  | Just r <- T.stripPrefix "]" t0 = Right (A [], r)
  | otherwise = go [] t0
  where
  go acc t = do
    (v, r) <- value t
    case T.uncons (skip r) of
      Just (',', r') -> go (v : acc) (skip r')
      Just (']', r') -> Right (A (reverse (v : acc)), r')
      _              -> Left "expected ',' or ']'"

object :: Text -> P J
object t0
  | Just r <- T.stripPrefix "}" t0 = Right (O [], r)
  | otherwise = go [] t0
  where
  go acc t = do
    (k, r)  <- key (skip t)
    (v, r') <- value (skip r)
    case T.uncons (skip r') of
      Just (',', r'') -> go ((k, v) : acc) (skip r'')
      Just ('}', r'') -> Right (O (reverse ((k, v) : acc)), r'')
      _               -> Left "expected ',' or '}'"
  key t = case T.uncons t of
    Just ('"', r) -> do
      (k, r') <- string r
      case T.uncons (skip r') of
        Just (':', r'') -> Right (k, r'')
        _               -> Left "expected ':' after object key"
    _ -> Left "expected object key"

-- ** accessors
--
-- Partial on purpose: the build reads an artifact written by the encoder above, so a
-- shape mismatch is a bug in this module, not bad input to tolerate.

(.:) :: J -> Text -> J
O kvs .: k = maybe (error ("Json: no key " <> T.unpack k)) id (lookup k kvs)
_     .: k = error ("Json: not an object, looking for " <> T.unpack k)

jList :: J -> [J]
jList = \case A xs -> xs; _ -> error "Json: not an array"

jText :: J -> Text
jText = \case S t -> t; _ -> error "Json: not a string"

jInt :: J -> Int
jInt = \case N n -> fromInteger n; _ -> error "Json: not a number"
