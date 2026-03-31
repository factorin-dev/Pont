module Main where

import System.Exit (exitFailure, exitSuccess)
import Exhaustive (runExhaustiveTests)
import Sigma (runSigmaTests)
import PathTests (runPathTests)
import Univalence (runUnivalenceTests)
import Properties (runPropertyTests)

main :: IO ()
main = do
  putStrLn "Running Pont kernel validation tests...\n"

  r1 <- runExhaustiveTests
  putStrLn ""
  r2 <- runSigmaTests
  putStrLn ""
  r3 <- runPathTests
  putStrLn ""
  r4 <- runUnivalenceTests
  putStrLn ""
  r5 <- runPropertyTests

  putStrLn ""
  if r1 && r2 && r3 && r4 && r5
    then putStrLn "All tests passed." >> exitSuccess
    else putStrLn "Some tests FAILED." >> exitFailure
