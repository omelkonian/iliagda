{-# LANGUAGE LambdaCase #-}
module Main where

import Prelude hiding (Word)
import Data.List (intercalate)
import Control.Monad (forM_, forM)
import System.Environment (getArgs)
import MAlonzo.Code.Iliagda.ToHaskell (checkVerse)
import qualified Data.Text as T
import qualified Data.Text.IO as T

type Word  = String
type Verse = [Word]
type Iliad = [Verse]

readIliad :: String -> Iliad
readIliad = map words . lines

-- ** digamma insertion

insertDigamma :: Word -> Word
insertDigamma = \case
  "ἔδεισεν" -> "ἔδδεισεν"
  w -> w

digammaInsertion :: Iliad -> Iliad
digammaInsertion = map (map insertDigamma)

-- ** syllabification

type Syllable = String
type WordSy   = [Syllable]
type VerseSy  = [WordSy]
type IliadSy  = [VerseSy]

writeIliadSy :: IliadSy -> String
writeIliadSy = unlines . map writeVerse
  where
  writeVerse :: VerseSy -> String
  writeVerse = unwords . map writeWord

  writeWord :: WordSy -> String
  writeWord = intercalate "-"

-- INCOMPLETE: add as needed
vowel, consonant, accentedVowel, dialytics :: Char -> Bool
vowel = (`elem` "ἈἌαἀἁἂἄὰάᾶᾷεἐἑἔἕέὲηῆῇῃἠἡἢἣἤἦἥἭήὴᾔιίὶἰἱἳἴἶἼῖϊΐῒοΟὀὈὁὃὄὅόὸυὐὑὔὖὕὗὺύῦϋΰωὠὣὤὥὦᾤᾧώὼῶῳῴῷὡ")
consonant = (`elem` "ΒβΓγΔδΖζΘθΚκΛƛΜμΝνΞξΠπΡρῥΣσςΤτΦφΧχΨψ")
accentedVowel = (`elem` "ἈἌἀἁἂἄὰάᾶᾷἐἑἔἕέὲῆῇἠἡἢἣἤἦἥἭήὴᾔίὶἰἱἳἴἶἼῖϊΐῒὀὈὁὃὄὅόὸὐὑὔὖὕὗὺύῦϋΰὠὣὤὥὦᾤᾧώὼῶῴῷὡ")
dialytics = (`elem` "ϊΐῒϋΰ")

dipthong :: Char -> Char -> Bool
dipthong c c' = [c, c'] `elem`
  [ "αι"
  , "αὶ"
  , "αί"
  , "ει"
  , "εί"
  , "εὶ"
  , "εἰ"
  , "ηυ"
  , "οι"
  , "οῖ"
  , "οἰ"
  , "οὶ"
  , "οί"
  , "οἱ"
  , "ου"
  , "οὐ"
  , "οὺ"
  , "οὗ"
  , "οὕ"
  , "οῦ"
  , "ού"
  , "υι"
  , "υὶ"
  , "υἱ"
  , "ωυ"
  ]

(\/) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
(p \/ q) x = p x || q x

mergeVowel :: Char -> Char -> Bool
mergeVowel c c'
  | accentedVowel c
  = False
  | dialytics c'
  = False
  | otherwise
  = dipthong c c'

nextVowel :: Char -> String -> (String, String)
nextVowel c s
  | ([c'], s) <- splitAt 1 s
  , mergeVowel c c'
  = ([c'], s)
  | otherwise
  = ("", s)

afterVowels :: String -> (String, String)
afterVowels s
  | all (not . vowel) s
  = (s, "")
  | otherwise
  = ("", s)

syllabify :: Word -> WordSy
syllabify s
  | (cs, s) <- break vowel s
  , ([v], s) <- splitAt 1 s
  , (vs, s) <- nextVowel v s
  , (rest, s) <- afterVowels s
  -- , (vs, s'') <- break (consonant \/ accentedVowel) s'
  -- , sy <- cs <> vs
  -- = if null sy then [s] else sy : syllabify s''
  = cs <> [v] <> vs <> rest
  : syllabify s
  | otherwise
  = []

showSyllables :: WordSy -> Word
showSyllables = intercalate "-"

syllabification :: Iliad -> IliadSy
syllabification = map (map syllabify)

toRemove :: Char -> Bool
toRemove = (`elem` "·,.;")

sanitize :: String -> String
sanitize = filter (not . toRemove)

joinWords :: [String] -> [String]
joinWords = \case
  [] -> []
  [ s ] -> [ s ]
  (s:s':ss) ->
    if all (not . vowel) s then
      joinWords (s <> s' : ss)
    else
      s : joinWords (s':ss)

-- checkVerseMain :: IO ()
-- checkVerseMain = do
--   [userInput] <- getArgs
--   let v = read userInput
--   T.putStrLn $ checkVerse v

main :: IO ()
main = do
  verses <- lines <$> readFile "artifacts/raw.txt"
  forM_ verses $ \v -> do
    let v' = sanitize v
    let ws = joinWords . map insertDigamma $ words v'
    let ws' = map syllabify ws
    -- T.putStrLn $ checkVerse ws'
    T.appendFile "artifacts/derivations.txt" $ checkVerse ws' <> T.pack "\n"
    appendFile "artifacts/syllables.txt" $ unwords (map showSyllables ws') <> "\n"

