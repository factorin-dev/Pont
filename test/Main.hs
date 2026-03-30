module Main where

import System.Exit (exitFailure, exitSuccess)
import Exhaustive (runExhaustiveTests)
import Sigma (runSigmaTests)
import Properties (runPropertyTests)

main :: IO ()
main = do
  putStrLn "Running Pont kernel validation tests...\n"

  r1 <- runExhaustiveTests
  putStrLn ""
  r2 <- runSigmaTests
  putStrLn ""
  r3 <- runPropertyTests

  putStrLn ""
  if r1 && r2 && r3
    then putStrLn "All tests passed." >> exitSuccess
    else putStrLn "Some tests FAILED." >> exitFailure
