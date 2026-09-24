module Main where

import System.Environment
import System.Exit
import Language

main :: IO ()
main = do
  args <- getArgs

  case args of
    [input, output] -> do
      ok <- compileFile input output

      if ok
        then exitSuccess
        else exitFailure

    _ -> do
      putStrLn "usage: gayc <input> <output.bc>"
      exitFailure
