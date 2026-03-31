-- | Univalence axiom tests for Milestone 4.
-- Tests rules from KERNEL.md Section 8.
module Univalence (runUnivalenceTests) where

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

runUnivalenceTests :: IO Bool
runUnivalenceTests = do
  putStrLn "=== Univalence Tests (Milestone 4) ==="
  putStrLn ""
  results <- sequence allTests
  let passed = length (filter id results)
      total  = length results
  putStrLn ""
  putStrLn $ "  " ++ show passed ++ "/" ++ show total ++ " univalence tests passed."
  return (and results)

test :: String -> Bool -> IO Bool
test name passed = do
  let mark = if passed then "\x2713" else "\x2717"
  putStrLn $ "  " ++ mark ++ " " ++ name
  return passed

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False

-- ============================================================
-- ua-β computation (THE critical test) — Section 8
-- ============================================================

-- | ua-β with identity function:
-- equiv = (λx.x, dummy)
-- vJ ... (VUa equiv) should apply (fst equiv) = id to d, giving d back.
test_ua_beta_id :: IO Bool
test_ua_beta_id = test "ua-beta: transport along ua(id-equiv) = id" $
  let idFn   = VLam (Closure [] (Var 0))          -- λx.x
      equiv  = VPair idFn (VRefl (VU 0))           -- (id, dummy)
      uaPath = VUa equiv
      someVal = VU 0
      result = vJ (VU 1) (VU 0) (Closure2 [] (Var 1)) someVal (VU 0) uaPath
  in conv 0 result (VU 0)  -- id(U 0) = U 0

-- | ua-β with a non-trivial function:
-- f = λx. Pair x x (conceptual; we use a neutral to test structure)
-- equiv = (f, dummy)
-- vJ ... (VUa equiv) d = f d = NApp f d
test_ua_beta_neutral :: IO Bool
test_ua_beta_neutral = test "ua-beta: transport along ua(f-equiv) = f d" $
  let fVal   = VNeutral (NVar 0)                   -- f (neutral)
      equiv  = VPair fVal (VNeutral (NVar 1))      -- (f, something)
      uaPath = VUa equiv
      dVal   = VNeutral (NVar 2)
      result = vJ (VU 0) (VNeutral (NVar 3)) (Closure2 [] (Var 0)) dVal (VNeutral (NVar 4)) uaPath
  in case result of
      VNeutral (NApp (NVar 0) (VNeutral (NVar 2))) -> True  -- f applied to d
      _ -> False

-- ============================================================
-- J-β still works (regression check)
-- ============================================================

test_j_beta_still_works :: IO Bool
test_j_beta_still_works = test "J-beta still works after ua-beta addition" $
  let result = vJ (VU 1) (VU 0) (Closure2 [] (Var 1)) (VU 0) (VU 0) (VRefl (VU 0))
  in conv 0 result (VU 0)

-- ============================================================
-- ua type checking
-- ============================================================

-- | ua on non-equivalence (not a Sigma) should fail
test_ua_non_equiv :: IO Bool
test_ua_non_equiv = test "ua on non-equivalence (U 0) rejected" $
  isLeft (infer emptyCtx (Ua (U 0)))

-- | ua on Sigma that doesn't have function first component should fail
test_ua_non_function :: IO Bool
test_ua_non_function = test "ua on Sigma without function first-comp rejected" $
  let -- Sigma (U 0) (U 0) — first component type is U 0, not a function
      sigTy = eval [] (Sigma (U 0) (U 0))
      ctx1  = bind emptyCtx sigTy   -- e : Sigma (U 0) (U 0)
  in isLeft (infer ctx1 (Ua (Var 0)))

-- ============================================================
-- ua⁻¹ type checking
-- ============================================================

-- | ua⁻¹ on non-path should fail
test_uainv_non_path :: IO Bool
test_uainv_non_path = test "ua-inv on non-path (U 0) rejected" $
  isLeft (infer emptyCtx (UaInv (U 0)))

-- | ua⁻¹ on path not between types should fail
test_uainv_non_universe_path :: IO Bool
test_uainv_non_universe_path = test "ua-inv on non-universe path rejected" $
  let ctx1 = bind emptyCtx (VU 0)                  -- A : U 0
      ctx2 = bind ctx1 (VNeutral (NVar 0))         -- x : A
      -- refl x : Path A x x — not Path (U _) _ _
  in isLeft (infer ctx2 (UaInv (Refl (Var 0))))

-- ============================================================
-- Conversion tests
-- ============================================================

test_ua_conv :: IO Bool
test_ua_conv = test "ua conversion: same argument convertible" $
  let v = VUa (VPair (VLam (Closure [] (Var 0))) (VRefl (VU 0)))
  in conv 0 v v

test_ua_noconv :: IO Bool
test_ua_noconv = test "ua non-conversion: different arguments" $
  let v1 = VUa (VPair (VLam (Closure [] (Var 0))) (VRefl (VU 0)))
      v2 = VUa (VPair (VLam (Closure [] (U 0))) (VRefl (VU 0)))
  in not (conv 0 v1 v2)

test_uainv_conv :: IO Bool
test_uainv_conv = test "ua-inv conversion: same argument" $
  conv 0 (VUaInv (VRefl (VU 0))) (VUaInv (VRefl (VU 0)))

-- ============================================================
-- Quote round-trip tests
-- ============================================================

test_quote_ua :: IO Bool
test_quote_ua = test "quote roundtrip: Ua (Refl (U 0))" $
  let v = VUa (VRefl (VU 0))
  in quote 0 v == Ua (Refl (U 0))

test_quote_uainv :: IO Bool
test_quote_uainv = test "quote roundtrip: UaInv (Refl (U 0))" $
  let v = VUaInv (VRefl (VU 0))
  in quote 0 v == UaInv (Refl (U 0))

-- ============================================================
-- DeFi transport demo (integration test)
-- ============================================================

-- | The goal of the entire project:
-- Given an equivalence (bridge) between TokenA and TokenB,
-- ua turns it into a path, and J (transport) along that path
-- applies the forward function.
test_defi_transport :: IO Bool
test_defi_transport = test "DeFi: transport along ua(bridge) applies forward fn" $
  let bridge = VLam (Closure [] (Var 0))            -- bridge forward: identity
      equiv  = VPair bridge bridge                   -- (forward, backward)
      uaPath = VUa equiv                             -- path via ua
      tokenAVal = VU 0                               -- some value on TokenA side
      -- transport: J ... (ua equiv) should give (fst equiv) tokenAVal = bridge tokenAVal
      result = vJ (VU 1) (VU 0) (Closure2 [] (Var 1)) tokenAVal (VU 0) uaPath
  in conv 0 result tokenAVal                          -- bridge=id, so result=input

-- ============================================================
-- All tests
-- ============================================================

allTests :: [IO Bool]
allTests =
  -- ua-β computation (2)
  [ test_ua_beta_id, test_ua_beta_neutral
  -- J-β regression (1)
  , test_j_beta_still_works
  -- ua type checking (2)
  , test_ua_non_equiv, test_ua_non_function
  -- ua⁻¹ type checking (2)
  , test_uainv_non_path, test_uainv_non_universe_path
  -- Conversion (3)
  , test_ua_conv, test_ua_noconv, test_uainv_conv
  -- Quote (2)
  , test_quote_ua, test_quote_uainv
  -- Integration (1)
  , test_defi_transport
  ]
