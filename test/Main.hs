module Main where

import Kernel.Syntax
import Kernel.Value (Val(..), evalTerm)
import Kernel.Check
import Kernel.Context
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  putStrLn "Running Pont kernel tests...\n"
  results <- sequence
    [ test "identity function type checks" $
        isRight (check emptyCtx
          (Lam (Lam (Var 0)))                          -- λ A . λ x . x
          (evalTerm [] (Pi (U 0) (Pi (Var 0) (Var 1))))) -- Π (A : U 0) . A → A

    , test "U 0 : U 1" $
        case infer emptyCtx (U 0) of
          Right (VU 1) -> True
          _            -> False

    , test "U 5 : U 6" $
        case infer emptyCtx (U 5) of
          Right (VU 6) -> True
          _            -> False

    , test "applying non-function fails" $
        isLeft (infer emptyCtx (App (U 0) (U 0)))

    , test "bare lambda cannot be inferred" $
        isLeft (infer emptyCtx (Lam (Var 0)))

    , test "Pi (A : U 0) . A  is in U 1" $
        -- Domain U 0 : U 1, codomain A : U 0, so Pi : U (max 1 0) = U 1
        case infer emptyCtx (Pi (U 0) (Var 0)) of
          Right (VU 1) -> True
          _            -> False

    , test "Pi (A : U 1) . U 0  is in U 2" $
        -- Domain U 1 : U 2, codomain U 0 : U 1, so Pi : U (max 2 1) = U 2
        case infer emptyCtx (Pi (U 1) (U 0)) of
          Right (VU 2) -> True
          _            -> False

    , test "const function type checks" $
        -- const : Π (A : U 0) . Π (B : U 0) . A → B → A
        -- const = λ A . λ B . λ x . λ y . x
        let constTy = Pi (U 0) (Pi (U 0) (Pi (Var 1) (Pi (Var 1) (Var 3))))
            constTm = Lam (Lam (Lam (Lam (Var 1))))
        in isRight (check emptyCtx constTm (evalTerm [] constTy))

    , test "variable out of scope is rejected" $
        isLeft (infer emptyCtx (Var 0))
    ]
  putStrLn ""
  if and results
    then putStrLn "All tests passed." >> exitSuccess
    else putStrLn "Some tests FAILED." >> exitFailure

-- | Run a single test, print result
test :: String -> Bool -> IO Bool
test name passed = do
  let mark = if passed then "\x2713" else "\x2717"
  putStrLn $ "  " ++ mark ++ " " ++ name
  return passed

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _         = False

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
