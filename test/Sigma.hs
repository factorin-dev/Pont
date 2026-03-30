-- | Σ-type tests for Milestone 2.
-- Tests all rules from KERNEL.md Section 5.
module Sigma (runSigmaTests) where

import Kernel.Syntax
import Kernel.Value
import Kernel.Eval (eval)
import Kernel.Quote (quote)
import Kernel.Conv (conv)
import Kernel.Check
import Kernel.Context

-- ============================================================
-- Test infrastructure
-- ============================================================

runSigmaTests :: IO Bool
runSigmaTests = do
  putStrLn "=== Sigma Tests (Milestone 2) ==="
  putStrLn ""
  results <- sequence allTests
  let passed = length (filter id results)
      total  = length results
  putStrLn ""
  putStrLn $ "  " ++ show passed ++ "/" ++ show total ++ " sigma tests passed."
  return (and results)

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

inferIsU :: Ctx -> Term -> Int -> Bool
inferIsU ctx t expectedLvl =
  case infer ctx t of
    Right (VU n) -> n == expectedLvl
    _            -> False

-- ============================================================
-- Σ-Form tests (Section 5)
-- ============================================================

-- | Σ (A : U 0) . A : U (max 1 0) = U 1
-- NOTE: Same logic as Pi — domain U 0 : U 1, so ℓ₁ = 1.
test_sigma_simple :: IO Bool
test_sigma_simple = test "Sigma (U 0) (Var 0) : U 1"
  (inferIsU emptyCtx (Sigma (U 0) (Var 0)) 1)

-- | Σ (_ : U 0) . U 0 : U (max 1 1) = U 1
test_sigma_universe :: IO Bool
test_sigma_universe = test "Sigma (U 0) (U 0) : U 1"
  (inferIsU emptyCtx (Sigma (U 0) (U 0)) 1)

-- | Σ (A : U 3) . A : U (max 4 3) = U 4
test_sigma_higher :: IO Bool
test_sigma_higher = test "Sigma (U 3) (Var 0) : U 4"
  (inferIsU emptyCtx (Sigma (U 3) (Var 0)) 4)

-- ============================================================
-- Σ-Intro tests (Section 5)
-- ============================================================

-- | (U 0, U 0) : Σ (_ : U 1) . U 1
test_pair_simple :: IO Bool
test_pair_simple = test "Pair (U 0, U 0) : Sigma (U 1) (U 1)" $
  isRight (check emptyCtx (Pair (U 0) (U 0)) (eval [] (Sigma (U 1) (U 1))))

-- | Dependent pair: (U 0, λ x . x) : Σ (A : U 1) . (A → A)
-- A = U 0, second must have type U 0 → U 0, which λx.x does.
test_pair_dependent :: IO Bool
test_pair_dependent = test "dependent pair (U 0, lam x.x) : Sigma (U 1) (A -> A)" $
  isRight (check emptyCtx
    (Pair (U 0) (Lam (Var 0)))
    (eval [] (Sigma (U 1) (Pi (Var 0) (Var 1)))))

-- | Wrong second component: (U 0, U 1) : Σ (A : U 1) . A
-- A = U 0, so second must be : U 0. But U 1 : U 2 ≠ U 0.
test_pair_wrong :: IO Bool
test_pair_wrong = test "pair with wrong second component rejected" $
  isLeft (check emptyCtx
    (Pair (U 0) (U 1))
    (eval [] (Sigma (U 1) (Var 0))))

-- ============================================================
-- Σ-fst / Σ-snd tests (Section 5)
-- ============================================================

-- | In context [p : Σ (A : U 0) . A], fst p : U 0
test_fst :: IO Bool
test_fst = test "fst p : U 0 (in sigma context)" $
  let sigTy = eval [] (Sigma (U 0) (Var 0))
      ctx1 = bind emptyCtx sigTy
  in case infer ctx1 (Fst (Var 0)) of
      Right ty -> conv 1 ty (VU 0)
      Left _ -> False

-- | snd p has type B[x ↦ fst p]
test_snd :: IO Bool
test_snd = test "snd p type-checks (in sigma context)" $
  let sigTy = eval [] (Sigma (U 0) (Var 0))
      ctx1 = bind emptyCtx sigTy
  in isRight (infer ctx1 (Snd (Var 0)))

-- | fst of non-sigma should fail
test_fst_nonsigma :: IO Bool
test_fst_nonsigma = test "fst of non-sigma (U 0) rejected" $
  isLeft (infer emptyCtx (Fst (U 0)))

-- | snd of non-sigma should fail
test_snd_nonsigma :: IO Bool
test_snd_nonsigma = test "snd of non-sigma (U 0) rejected" $
  isLeft (infer emptyCtx (Snd (U 0)))

-- ============================================================
-- β-reduction tests (Σ-β₁, Σ-β₂)
-- ============================================================

-- | fst (U 0, U 1) = U 0
test_fst_beta :: IO Bool
test_fst_beta = test "fst (U 0, U 1) = U 0" $
  quote 0 (eval [] (Fst (Pair (U 0) (U 1)))) == U 0

-- | snd (U 0, U 1) = U 1
test_snd_beta :: IO Bool
test_snd_beta = test "snd (U 0, U 1) = U 1" $
  quote 0 (eval [] (Snd (Pair (U 0) (U 1)))) == U 1

-- | Nested: fst (snd (U 0, (U 1, U 2))) = U 1
test_nested_proj :: IO Bool
test_nested_proj = test "fst (snd (U0, (U1, U2))) = U 1" $
  quote 0 (eval [] (Fst (Snd (Pair (U 0) (Pair (U 1) (U 2)))))) == U 1

-- ============================================================
-- Σ-η conversion tests (Section 5)
-- ============================================================

-- | (fst p, snd p) ≡ p for neutral p
test_sigma_eta :: IO Bool
test_sigma_eta = test "sigma eta: (fst p, snd p) = p" $
  let p = VNeutral (NVar 0)
      reconstructed = VPair (vFst p) (vSnd p)
  in conv 1 reconstructed p

-- | Symmetric direction
test_sigma_eta_rev :: IO Bool
test_sigma_eta_rev = test "sigma eta reverse: p = (fst p, snd p)" $
  let p = VNeutral (NVar 0)
      reconstructed = VPair (vFst p) (vSnd p)
  in conv 1 p reconstructed

-- ============================================================
-- Quote round-trip tests
-- ============================================================

-- | quote (eval (Sigma (U 0) (Var 0))) = Sigma (U 0) (Var 0)
test_quote_sigma :: IO Bool
test_quote_sigma = test "quote roundtrip: Sigma (U 0) (Var 0)" $
  quote 0 (eval [] (Sigma (U 0) (Var 0))) == Sigma (U 0) (Var 0)

-- | quote (eval (Pair (U 0) (U 1))) = Pair (U 0) (U 1)
test_quote_pair :: IO Bool
test_quote_pair = test "quote roundtrip: Pair (U 0) (U 1)" $
  quote 0 (eval [] (Pair (U 0) (U 1))) == Pair (U 0) (U 1)

-- ============================================================
-- Product type (non-dependent Σ)
-- ============================================================

-- | A × B = Σ (_ : A) . B (B doesn't use the variable)
test_product :: IO Bool
test_product = test "product type: (U 0, U 0) : U 1 x U 1" $
  isRight (check emptyCtx (Pair (U 0) (U 0)) (eval [] (Sigma (U 1) (U 1))))

-- ============================================================
-- Integration: proto-equivalence type
-- ============================================================

-- | Σ (f : A → B) . (B → A) in context [A : U 0, B : U 0]
-- Should type-check as a well-formed type.
test_proto_equiv :: IO Bool
test_proto_equiv = test "proto-equiv Sigma (A->B) (B->A) type-checks" $
  let ctx1 = bind emptyCtx (VU 0)      -- A : U 0 (level 0)
      ctx2 = bind ctx1 (VU 0)           -- B : U 0 (level 1)
      -- In ctx2: Var 0 = B, Var 1 = A
      -- A → B = Pi (Var 1) (Var 1)
      --   (domain = Var 1 = A; after Pi binder: Var 1 = B)
      -- Sigma body, under binder for f: f = Var 0, B = Var 1, A = Var 2
      -- B → A = Pi (Var 1) (Var 3)
      --   (domain = Var 1 = B; after Pi binder: Var 3 = A)
      protoEquiv = Sigma (Pi (Var 1) (Var 1)) (Pi (Var 1) (Var 3))
  in isRight (infer ctx2 protoEquiv)

-- ============================================================
-- Pair cannot be inferred
-- ============================================================

test_pair_no_infer :: IO Bool
test_pair_no_infer = test "bare pair cannot be inferred" $
  isLeft (infer emptyCtx (Pair (U 0) (U 0)))

-- ============================================================
-- All tests
-- ============================================================

allTests :: [IO Bool]
allTests =
  -- Formation (3)
  [ test_sigma_simple, test_sigma_universe, test_sigma_higher
  -- Introduction (3)
  , test_pair_simple, test_pair_dependent, test_pair_wrong
  -- Projections (4)
  , test_fst, test_snd, test_fst_nonsigma, test_snd_nonsigma
  -- β-reduction (3)
  , test_fst_beta, test_snd_beta, test_nested_proj
  -- η-conversion (2)
  , test_sigma_eta, test_sigma_eta_rev
  -- Quote (2)
  , test_quote_sigma, test_quote_pair
  -- Product (1)
  , test_product
  -- Integration (1)
  , test_proto_equiv
  -- Inference (1)
  , test_pair_no_infer
  ]
