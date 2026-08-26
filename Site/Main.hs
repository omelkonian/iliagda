-- | The site build, entry point.
--
-- Separate from the corpus runner on purpose: this executable links neither Agda nor
-- MAlonzo, so @docs/@ is buildable from the committed artifact alone.
--
--    $ ghc --make Site/Main.hs -o site -i. && ./site
module Main where

import Site.Build (build)

main :: IO ()
main = build
