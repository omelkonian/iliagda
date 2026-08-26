{-# LANGUAGE OverloadedStrings, LambdaCase #-}
module Explanation.Render (render) where

import Data.Text (Text)
import qualified Data.Text as T
import Explanation

render :: Explanation -> Text
render (Explanation _ sys ws qs fs) = T.unlines $
  scansion (scanned fs sys ws) qs ++ [""]
  ++ concat (zipWith (numbered fs sys ws) [1 ..] fs)

-- ** written syllables grouped into the syllables the metre scans

scanned :: [Fact] -> [Text] -> [Integer] -> [(Text, Bool)]
scanned fs sys ws = go 0 (zip (zipWith bracket [0 ..] sys) (lasts ws))
  where
  merges = [ j | Fact j Merge{} _ _ <- fs ]
  go _ [] = []
  go i ((s, _) : (s', b) : rest)
    | (i + 1) `elem` merges = (s <> "\8255" <> s', b) : go (i + 2) rest
  go i ((s, b) : rest) = (s, b) : go (i + 1) rest

  -- ⟨ ⟩ marks a letter the editor supplies (Leiden)
  bracket :: Integer -> Text -> Text
  bracket i s = foldr wrap s [ k | Fact j (Unwritten _ k _) _ _ <- fs, j == i ]
    where wrap k t = let (a, b) = T.splitAt (fromInteger k) t
                     in a <> "\10216" <> T.take 1 b <> "\10217" <> T.drop 1 b

-- ** the verse and its quantities, one column per syllable

scansion :: [(Text, Bool)] -> [Qty] -> [Text]
scansion sc qs = [row (map fst cs), row (map snd cs)]
  where
  cs = zipWith (\(s, b) q -> cell s q b) sc (map mark qs)
  cell s q lastOfWord =
    let w = max (T.length s) (T.length q)
        gap = if lastOfWord then "   " else " "
    in (T.justifyLeft w ' ' s <> gap, T.justifyLeft w ' ' q <> gap)
  row = ("  " <>) . T.stripEnd . T.concat
  mark = \case Long -> "\9472"; Short -> "\183"

lasts :: [Integer] -> [Bool]
lasts = concatMap (\n -> replicate (fromInteger n - 1) False ++ [True])

-- ** one numbered sentence per fact

numbered :: [Fact] -> [Text] -> [Integer] -> Int -> Fact -> [Text]
numbered fs sys ws k f = case wrap (76 - T.length label) (sentence fs sys ws f) of
  []       -> []
  (l : ls) -> label <> " " <> l : map (T.replicate (T.length label + 1) " " <>) ls
  where label = T.justifyRight 4 ' ' ("(" <> T.pack (show k) <> ")")

wrap :: Int -> Text -> [Text]
wrap w = chunks . T.words
  where
  chunks [] = []
  chunks (x : xs) = let (l, rest) = fill x xs in l : chunks rest
  fill acc (y : ys)
    | T.length acc + 1 + T.length y <= w = fill (acc <> " " <> y) ys
  fill acc ys = (acc, ys)

sentence :: [Fact] -> [Text] -> [Integer] -> Fact -> Text
sentence fs sys ws (Fact i r _ mref) = body <> "."
  where
  self = case [ l <> r' | Fact j (Merge l r' _) _ _ <- fs, j == i ] of
    (t : _) -> t
    []      -> at sys i
  me | namesWord = self
     | length (filter (== self) sys) > 1, wd /= self = self <> " of " <> wd
     | otherwise = self
  namesWord = case r of
    R1160{} -> True; R1161{} -> True; R1162{} -> True; R1163{} -> True
    Unwritten{} -> True; _ -> False
  wd = wordOf sys ws i
  cite = maybe "" (\n -> " (" <> tshow (n + 1) <> ")") mref
  despite q' = case mref >>= qtyAt of
    Just q | q /= q' -> me <> " would be " <> qty q <> cite <> ", but"
    _                -> me
  qtyAt n = case drop (fromInteger n) fs of (Fact _ _ mq _ : _) -> mq; [] -> Nothing
  its v = if T.singleton v == self then "it " else "its " <> T.singleton v <> " "
  body = case r of
    Unwritten c _ key ->
      key <> " is read " <> wd <> ": its " <> T.singleton c <> " is not written"
    LongByNature g -> me <> " is long by nature: " <> case g of
      Diphthong a b -> "it contains the diphthong " <> T.pack [a, b]
      LongVowel v   -> "it contains the long vowel " <> T.singleton v
      Circumflex v  -> its v <> "bears a circumflex"
    ShortByNature v -> me <> " is short: " <> its v <> "is short by nature"
    ByLexicon q key m ->
      me <> " is " <> qty q <> ": the vocabulary fixes the doubtful vowel of "
      <> key <> (case m of Whole -> ""; Stem -> ", matched as a stem")
    R1160 _ penult ->
      me <> " is short: it is the ultima of " <> wd <> ", whose penult "
      <> penult <> " bears the circumflex"
    R1161 _ penult ->
      me <> " is long: it is the ultima of " <> wd <> ", whose penult "
      <> penult <> " is long" <> cite <> " and bears the acute"
    R1162 _ ult ->
      me <> " is short: it is the penult of " <> wd
      <> ", bearing the acute while the ultima " <> ult <> " is short" <> cite
    R1163 _ antepenult ->
      me <> " is short: it is the ultima of " <> wd <> ", whose antepenult "
      <> antepenult <> " bears the accent"
    Merge l r' cross ->
      l <> " and " <> r' <> " are read as the one syllable " <> me
      <> (if cross then ", across the word boundary" else "")
      <> ", which counts long" <> cite
    R522 v p ->
      despite Long <> " is long: its " <> T.singleton v <> " is followed by " <> case p of
        DoubleConsonant c -> "the double consonant " <> T.singleton c
        TwoConsonants a b rc -> T.singleton a <> " and " <> T.singleton b <> reach rc
    R1173 q nucleus next cross ->
      me <> " may be shortened: its " <> nucleus <> " stands before vowel-initial "
      <> T.singleton next <> (if cross then " of the following word" else "")
      <> "; the verse takes it " <> qty q <> cite
    R524 q v m l nasal ->
      me <> " is common: its " <> T.singleton v
      <> " is a short vowel standing before the mute " <> T.singleton m <> " and the "
      <> (if nasal then "nasal " else "liquid ") <> T.singleton l
      <> " in the same word; the verse takes it " <> qty q <> cite
    R1168 v c next ->
      me <> " is lengthened in thesis: it ends in " <> T.pack [v, c]
      <> " before vowel-initial " <> T.singleton next <> cite
    R1167a ->
      me <> " counts long: its word ends at the caesura, whose pause fills out"
      <> " the time required" <> cite
    R1167b n ->
      me <> " counts long: its word ends here, closing the " <> ordinal n
      <> " foot as a spondee" <> cite
    R1184 ->
      me <> " counts long: it is the last syllable of the verse" <> cite

-- ** helpers

at :: [Text] -> Integer -> Text
at sys i
  | i < 0 || i >= fromIntegral (length sys) =
      error ("Render: syllable index out of range: " ++ show i)
  | otherwise = sys !! fromInteger i

wordOf :: [Text] -> [Integer] -> Integer -> Text
wordOf sys ws i = go sys ws i
  where
  go _ [] _ = error ("Render: no word contains syllable " ++ show i)
  go ss (n : ns) j
    | j < n     = T.concat (take (fromInteger n) ss)
    | otherwise = go (drop (fromInteger n) ss) ns (j - n)

qty :: Qty -> Text
qty = \case Long -> "long"; Short -> "short"

reach :: Reach -> Text
reach = \case
  Within -> ""
  NextSyllable -> " in the next syllable"
  NextWord -> " of the following word"

ordinal :: Integer -> Text
ordinal n
  | n >= 1 && n <= 6 = ["first", "second", "third", "fourth", "fifth", "sixth"] !! (fromInteger n - 1)
  | otherwise = tshow n <> "th"

tshow :: Show a => a -> Text
tshow = T.pack . show
