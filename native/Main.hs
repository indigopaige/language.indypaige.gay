module Main where

import Control.Monad (void)
import Data.Word
import Export ()

foreign import ccall safe "entry"
  entry :: IO Word64

main :: IO ()
main = do
  result <- entry
  print result
