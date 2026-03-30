module Main where

import System.Exit (exitFailure, exitSuccess)
import Exhaustive (runExhaustiveTests)
import Properties (runPropertyTests)

main :: IO ()
main = do
  putStrLn "Running Pont kernel validation tests...\n"

  r1 <- runExhaustiveTests
  putStrLn ""
  r2 <- runPropertyTests

  putStrLn ""
  if r1 && r2
    then putStrLn "All tests passed." >> exitSuccess
    else putStrLn "Some tests FAILED." >> exitFailure
