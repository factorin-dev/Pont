module Main where

import Kernel.Syntax
import Kernel.Value (evalTerm)
import Kernel.Check
import Kernel.Context

-- | The identity function: λ (A : U 0) . λ (x : A) . x
-- In de Bruijn: Lam (Lam (Var 0))
-- Type: Π (A : U 0) . Π (x : A) . A
-- In de Bruijn: Pi (U 0) (Pi (Var 0) (Var 1))
main :: IO ()
main = do
  putStrLn "Pont type checker v0.1 \x2014 Milestone 1 (\x03A0 + Universe)"
  putStrLn ""

  let idTy   = Pi (U 0) (Pi (Var 0) (Var 1))   -- Π (A : U 0) . A → A
  let idTerm = Lam (Lam (Var 0))                -- λ A . λ x . x

  putStrLn "Checking: (\x03BB A . \x03BB x . x) : \x03A0 (A : U 0) . A \x2192 A"
  case check emptyCtx idTerm (evalTerm [] idTy) of
    Right ()  -> putStrLn "\x2713 Type check passed."
    Left err  -> putStrLn $ "\x2717 Type error: " ++ show err

  putStrLn ""

  -- Negative test: applying U 0 to itself (should fail)
  putStrLn "Checking: U 0 applied to U 0 (should fail)"
  case infer emptyCtx (App (U 0) (U 0)) of
    Right ty  -> putStrLn $ "\x2717 Unexpected success: " ++ show ty
    Left err  -> putStrLn $ "\x2713 Correctly rejected: " ++ show err
