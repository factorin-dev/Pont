-- | Path type + J eliminator tests for Milestone 3.
-- Tests all rules from KERNEL.md Section 6.
module PathTests (runPathTests) where

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

runPathTests :: IO Bool
runPathTests = do
  putStrLn "=== Path Tests (Milestone 3) ==="
  putStrLn ""
  results <- sequence allTests
  let passed = length (filter id results)
      total  = length results
  putStrLn ""
  putStrLn $ "  " ++ show passed ++ "/" ++ show total ++ " path tests passed."
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

-- ============================================================
-- Path formation (Section 6: Path-Form)
-- ============================================================

-- | Path (U 1) (U 0) (U 0) : U 2
-- A = U 1, inferUniverse gives 2 (since U 1 : U 2). Path lives in U 2.
test_path_formation :: IO Bool
test_path_formation = test "Path (U 1) (U 0) (U 0) : U 2" $
  case infer emptyCtx (PathT (U 1) (U 0) (U 0)) of
    Right (VU 2) -> True
    _            -> False

-- | In context [A : U 0, x : A]: Path A x x : U 0
test_path_formation_var :: IO Bool
test_path_formation_var = test "Path A x x : U 0 (in context)" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
  in case infer ctx2 (PathT (Var 1) (Var 0) (Var 0)) of
      Right ty -> conv 2 ty (VU 0)
      Left _   -> False

-- | Path A x y with x:A, y:B (different types) — must fail
test_path_mismatch :: IO Bool
test_path_mismatch = test "Path A x y with y:B (not A) rejected" $
  let ctx1 = bind emptyCtx (VU 0)               -- A : U 0
      ctx2 = bind ctx1 (VU 0)                    -- B : U 0
      ctx3 = bind ctx2 (VNeutral (NVar 0))       -- x : A
      ctx4 = bind ctx3 (VNeutral (NVar 1))       -- y : B
      -- PathT (Var 3) (Var 1) (Var 0): Path A x y, y:B not A
  in isLeft (infer ctx4 (PathT (Var 3) (Var 1) (Var 0)))

-- | Path (U 0) (U 0) (U 0) is ill-formed: U 0 : U 1, not U 0.
test_path_ill_formed :: IO Bool
test_path_ill_formed = test "Path (U 0) (U 0) (U 0) ill-formed" $
  isLeft (infer emptyCtx (PathT (U 0) (U 0) (U 0)))

-- | Path with non-type first arg: Path x x x where x : A
test_path_nontype :: IO Bool
test_path_nontype = test "Path x x x rejected (x not a type)" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
  in isLeft (infer ctx2 (PathT (Var 0) (Var 0) (Var 0)))

-- ============================================================
-- Refl (Section 6: Path-Intro)
-- ============================================================

-- | refl (U 0) : Path (U 1) (U 0) (U 0)
test_refl_universe :: IO Bool
test_refl_universe = test "refl (U 0) : Path (U 1) (U 0) (U 0)" $
  case infer emptyCtx (Refl (U 0)) of
    Right (VPathT a t u) -> conv 0 a (VU 1) && conv 0 t (VU 0) && conv 0 u (VU 0)
    _ -> False

-- | In context [A : U 0, x : A]: refl x : Path A x x
test_refl_var :: IO Bool
test_refl_var = test "refl x : Path A x x (in context)" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
  in case infer ctx2 (Refl (Var 0)) of
      Right (VPathT _ t u) -> conv 2 t u  -- both endpoints are x
      _ -> False

-- ============================================================
-- J-β computation (Section 6: J-β)
-- ============================================================

-- | J A a C d a (refl a) ≡ d  (the critical computation rule)
-- Context: [A : U 0, a : A]
-- J (Var 1) (Var 0) (Var 3) (Var 0) (Var 0) (Refl (Var 0))
-- C = Var 3 = A (constant motive, under 2 extra binders: A at index 3)
-- d = Var 0 = a
-- Result should be a (= NVar 1)
test_j_beta :: IO Bool
test_j_beta = test "J-beta: J A a C d a (refl a) = d" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
      jTerm = J (Var 1) (Var 0) (Var 3) (Var 0) (Var 0) (Refl (Var 0))
      result = eval (ctxEnv ctx2) jTerm
  in conv 2 result (VNeutral (NVar 1))

-- | J on neutral path stays stuck (NJ)
test_j_stuck :: IO Bool
test_j_stuck = test "J on neutral path stays stuck" $
  let ctx1 = bind emptyCtx (VU 0)               -- A : U 0 (lvl 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))      -- a : A (lvl 1)
      ctx3 = bind ctx2 (VNeutral (NVar 0))      -- b : A (lvl 2)
      pathTy = VPathT (VNeutral (NVar 0)) (VNeutral (NVar 1)) (VNeutral (NVar 2))
      ctx4 = bind ctx3 pathTy                     -- p : Path A a b (lvl 3)
      -- J A a C d b p: Var 3=A, Var 2=a, C=Var5(=A under 2 extra), d=Var2(=a), Var 1=b, Var 0=p
      jTerm = J (Var 3) (Var 2) (Var 5) (Var 2) (Var 1) (Var 0)
  in case eval (ctxEnv ctx4) jTerm of
      VNeutral (NJ {}) -> True
      _ -> False

-- ============================================================
-- Transport (derived from J, tested via J-β)
-- ============================================================

-- | transport (refl a) x = x
-- J A a (λy_.A) a a (refl a) → a
test_transport_refl :: IO Bool
test_transport_refl = test "transport (refl a) x = x (J-beta)" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
      -- C = Var 3 (= A under 2 extra binders), d = Var 0 (= a)
      jTerm = J (Var 1) (Var 0) (Var 3) (Var 0) (Var 0) (Refl (Var 0))
      result = eval (ctxEnv ctx2) jTerm
  in conv 2 result (VNeutral (NVar 1))

-- ============================================================
-- Symmetry (derived from J, tested via J-β)
-- ============================================================

-- | sym (refl a) = refl a
-- J A a (λy_. Path A y a) (refl a) a (refl a) → refl a
test_sym_refl :: IO Bool
test_sym_refl = test "sym (refl a) = refl a (J-beta)" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
      -- C (motive): Path A y a
      -- Under 2 extra binders [y,p]: A=Var3, a=Var2, y=Var1, p=Var0
      -- C = PathT (Var 3) (Var 1) (Var 2)
      -- d = Refl (Var 0) = refl a (in outer context)
      symRefl = J (Var 1) (Var 0)
                  (PathT (Var 3) (Var 1) (Var 2))
                  (Refl (Var 0)) (Var 0) (Refl (Var 0))
      result = eval (ctxEnv ctx2) symRefl
  in case result of
      VRefl _ -> True
      _ -> False

-- ============================================================
-- J type checking
-- ============================================================

-- | J with correct types passes
test_j_typechecks :: IO Bool
test_j_typechecks = test "J A a C d a (refl a) type-checks" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
      jTerm = J (Var 1) (Var 0) (Var 3) (Var 0) (Var 0) (Refl (Var 0))
      expectedTy = VNeutral (NVar 0)  -- A
  in isRight (check ctx2 jTerm expectedTy)

-- | J with wrong base case type should fail
test_j_wrong_base :: IO Bool
test_j_wrong_base = test "J with wrong base case type rejected" $
  let ctx1 = bind emptyCtx (VU 0)
      ctx2 = bind ctx1 (VNeutral (NVar 0))
      -- d = U 0 which has type U 1, not A (the motive C=Var3=A expects d:A)
      jTerm = J (Var 1) (Var 0) (Var 3) (U 0) (Var 0) (Refl (Var 0))
  in isLeft (infer ctx2 jTerm)

-- ============================================================
-- Conversion tests
-- ============================================================

-- | Path types with same components are convertible
test_path_conv :: IO Bool
test_path_conv = test "Path type conversion (same components)" $
  conv 0 (VPathT (VU 0) (VU 0) (VU 0)) (VPathT (VU 0) (VU 0) (VU 0))

-- | Path types with different endpoints are NOT convertible
test_path_noconv :: IO Bool
test_path_noconv = test "Path types with different endpoints not convertible" $
  not (conv 1
    (VPathT (VU 0) (VNeutral (NVar 0)) (VNeutral (NVar 0)))
    (VPathT (VU 0) (VNeutral (NVar 0)) (VU 0)))

-- | Refl values with same argument are convertible
test_refl_conv :: IO Bool
test_refl_conv = test "refl conversion (same argument)" $
  conv 0 (VRefl (VU 0)) (VRefl (VU 0))

-- ============================================================
-- Quote round-trip tests
-- ============================================================

test_quote_path :: IO Bool
test_quote_path = test "quote roundtrip: PathT (U 1) (U 0) (U 0)" $
  quote 0 (eval [] (PathT (U 1) (U 0) (U 0))) == PathT (U 1) (U 0) (U 0)

test_quote_refl :: IO Bool
test_quote_refl = test "quote roundtrip: Refl (U 0)" $
  quote 0 (eval [] (Refl (U 0))) == Refl (U 0)

-- ============================================================
-- All tests
-- ============================================================

allTests :: [IO Bool]
allTests =
  -- Path formation (5)
  [ test_path_formation, test_path_formation_var, test_path_mismatch
  , test_path_ill_formed, test_path_nontype
  -- Refl (2)
  , test_refl_universe, test_refl_var
  -- J-β (2)
  , test_j_beta, test_j_stuck
  -- Derived: transport + symmetry (2)
  , test_transport_refl, test_sym_refl
  -- J type checking (2)
  , test_j_typechecks, test_j_wrong_base
  -- Conversion (3)
  , test_path_conv, test_path_noconv, test_refl_conv
  -- Quote (2)
  , test_quote_path, test_quote_refl
  ]
