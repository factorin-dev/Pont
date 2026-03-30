-- | Exhaustive hand-written tests for the Pont kernel.
-- Tests every rule from KERNEL.md that is implemented in Milestone 1.
module Exhaustive (runExhaustiveTests) where

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

runExhaustiveTests :: IO Bool
runExhaustiveTests = do
  putStrLn "=== Exhaustive Tests ==="
  putStrLn ""
  results <- sequence allTests
  let passed = length (filter id results)
      total  = length results
  putStrLn ""
  putStrLn $ "  " ++ show passed ++ "/" ++ show total ++ " exhaustive tests passed."
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

-- | Compare inferred type by quoting both to normal-form terms.
inferEq :: Ctx -> Term -> Term -> Bool
inferEq ctx t expected =
  case infer ctx t of
    Right got -> quote (ctxLvl ctx) got == expected
    Left _    -> False

-- | Check that infer returns a universe at the given level.
inferIsU :: Ctx -> Term -> ULvl -> Bool
inferIsU ctx t expectedLvl =
  case infer ctx t of
    Right (VU n) -> n == expectedLvl
    _            -> False

-- ============================================================
-- 2a. Universe rules (6 tests)
-- ============================================================
--
-- Implements: U-Type (Section 3)
--   Γ ⊢ U ℓ : U (ℓ+1)

test_U0_type, test_U1_type, test_U5_type :: IO Bool
test_U0_check_U1, test_U0_check_U0, test_U1_check_U1 :: IO Bool

test_U0_type = test "U 0 : U 1"
  (inferIsU emptyCtx (U 0) 1)

test_U1_type = test "U 1 : U 2"
  (inferIsU emptyCtx (U 1) 2)

test_U5_type = test "U 5 : U 6"
  (inferIsU emptyCtx (U 5) 6)

test_U0_check_U1 = test "check U 0 : U 1 succeeds"
  (isRight (check emptyCtx (U 0) (VU 1)))

-- U 0 : U 0 is circular — must fail
test_U0_check_U0 = test "check U 0 : U 0 fails (circular)"
  (isLeft (check emptyCtx (U 0) (VU 0)))

-- U 1 : U 1 would require U 1 : U 1 — must fail
test_U1_check_U1 = test "check U 1 : U 1 fails"
  (isLeft (check emptyCtx (U 1) (VU 1)))

-- ============================================================
-- 2b. Π-type formation (5 tests)
-- ============================================================
--
-- Implements: Π-Form (Section 4)
--   Γ ⊢ A : U ℓ₁    Γ, x : A ⊢ B : U ℓ₂
--  ────────────────────────────────────────────
--          Γ ⊢ Π (x : A) . B : U (max ℓ₁ ℓ₂)

test_pi_simple, test_pi_universe, test_pi_nested :: IO Bool
test_pi_higher, test_pi_max_level :: IO Bool

-- Π (A : U 0) . A : U (max 1 0) = U 1
-- Domain U 0 : U 1, so ℓ₁ = 1. Body Var 0 : U 0, so ℓ₂ = 0.
-- NOTE: The instruction expected VU 0, but this is incorrect.
-- U 0 inhabits U 1, not U 0, so ℓ₁ = 1 and max(1,0) = 1.
test_pi_simple = test "Pi (U 0) (Var 0) : U 1"
  (inferIsU emptyCtx (Pi (U 0) (Var 0)) 1)

-- Π (_ : U 0) . U 0 : U (max 1 1) = U 1
test_pi_universe = test "Pi (U 0) (U 0) : U 1"
  (inferIsU emptyCtx (Pi (U 0) (U 0)) 1)

-- Π (A : U 0) . Π (B : U 0) . A : U (max 1 1) = U 1
-- Outer: ℓ₁ = 1 (U 0 : U 1)
-- Inner Pi (U 0) (Var 1): ℓ₁' = 1, ℓ₂' = 0 (Var 1 = A : U 0) → U 1
-- So outer ℓ₂ = 1 (inner Pi : U 1). max(1,1) = 1.
test_pi_nested = test "Pi (U 0) (Pi (U 0) (Var 1)) : U 1"
  (inferIsU emptyCtx (Pi (U 0) (Pi (U 0) (Var 1))) 1)

-- Π (A : U 3) . A : U (max 4 3) = U 4
-- Domain U 3 : U 4, so ℓ₁ = 4. Body Var 0 : U 3, so ℓ₂ = 3.
-- NOTE: The instruction suggested VU 3, but U 3 : U 4, hence ℓ₁ = 4.
test_pi_higher = test "Pi (U 3) (Var 0) : U 4"
  (inferIsU emptyCtx (Pi (U 3) (Var 0)) 4)

-- Π (_ : U 0) . U 5 : U (max 1 6) = U 6
test_pi_max_level = test "Pi (U 0) (U 5) : U 6"
  (inferIsU emptyCtx (Pi (U 0) (U 5)) 6)

-- ============================================================
-- 2c. Lambda + Application (10 tests)
-- ============================================================

test_identity, test_const, test_lam_no_infer :: IO Bool
test_var_lookup, test_app_simple, test_type_mismatch :: IO Bool
test_double_app, test_wrong_arg_type :: IO Bool
test_app_id_result, test_lam_check_nonpi :: IO Bool

-- | Implements: Π-Intro (Section 4)
-- Identity: λ A . λ x . x  :  Π (A : U 0) . A → A
test_identity = test "identity function type checks" $
  isRight (check emptyCtx
    (Lam (Lam (Var 0)))
    (eval [] (Pi (U 0) (Pi (Var 0) (Var 1)))))

-- | Const: λ A B x y . x  :  Π (A : U 0) . Π (B : U 0) . A → B → A
test_const = test "const function type checks" $
  let constTy = Pi (U 0) (Pi (U 0) (Pi (Var 1) (Pi (Var 1) (Var 3))))
      constTm = Lam (Lam (Lam (Lam (Var 1))))
  in isRight (check emptyCtx constTm (eval [] constTy))

-- | Lambda cannot be inferred without annotation.
test_lam_no_infer = test "bare lambda cannot be inferred" $
  isLeft (infer emptyCtx (Lam (Var 0)))

-- | Variable lookup in context.
-- Context: [A : U 0, x : A]
-- Var 0 (= x) should have type A.
test_var_lookup = test "variable lookup returns correct type" $
  let ctx1 = bind emptyCtx (VU 0)          -- A : U 0 (level 0)
      vA   = VNeutral (NVar 0)             -- value of A
      ctx2 = bind ctx1 vA                  -- x : A (level 1)
      -- infer ctx2 (Var 0) should give type of x = vA = NVar 0
      -- quote at lvl 2: NVar 0 → Var (2 - 0 - 1) = Var 1
  in inferEq ctx2 (Var 0) (Var 1)

-- | Implements: Π-Elim (Section 4)
-- Context: [A : U 0, f : A → A, x : A]
-- f x : A
test_app_simple = test "simple application f x : A" $
  let ctx1 = bind emptyCtx (VU 0)
      vA   = VNeutral (NVar 0)
      -- A → A as a value: VPi vA (closure returning vA)
      fTy  = evalTerm (ctxEnv ctx1) (Pi (Var 0) (Var 1))
      ctx2 = bind ctx1 fTy                 -- f : A → A (level 1)
      ctx3 = bind ctx2 vA                  -- x : A (level 2)
      -- f x = App (Var 1) (Var 0), result type should be A
      -- At level 3, A (= NVar 0) quotes to Var (3 - 0 - 1) = Var 2
  in inferEq ctx3 (App (Var 1) (Var 0)) (Var 2)

-- | Type mismatch: λ . U 0 checked against Π (A : U 0) . A
-- Body U 0 : U 1, but expected type is A (a neutral). conv(VU 1, NVar) = False.
test_type_mismatch = test "lambda body type mismatch is rejected" $
  isLeft (check emptyCtx (Lam (U 0)) (eval [] (Pi (U 0) (Var 0))))

-- | Double application: f x y in context [A : U 0, f : A → A → A, x : A, y : A]
test_double_app = test "double application f x y : A" $
  let ctx1 = bind emptyCtx (VU 0)          -- A : U 0
      vA   = VNeutral (NVar 0)
      -- A → A → A = Π(_:A).Π(_:A).A
      fTy  = evalTerm (ctxEnv ctx1) (Pi (Var 0) (Pi (Var 1) (Var 2)))
      ctx2 = bind ctx1 fTy                 -- f : A → A → A
      ctx3 = bind ctx2 vA                  -- x : A
      ctx4 = bind ctx3 vA                  -- y : A
      -- f x y = App (App (Var 2) (Var 1)) (Var 0)
      -- result type should be A
      -- At level 4, A (= NVar 0) quotes to Var (4 - 0 - 1) = Var 3
  in inferEq ctx4 (App (App (Var 2) (Var 1)) (Var 0)) (Var 3)

-- | Wrong argument type: f x where f : A → A and x : B (different type)
test_wrong_arg_type = test "wrong argument type is rejected" $
  let ctx1 = bind emptyCtx (VU 0)          -- A : U 0
      ctx2 = bind ctx1 (VU 0)              -- B : U 0
      -- f : A → A
      fTy  = evalTerm (ctxEnv ctx2) (Pi (Var 1) (Var 2))
      ctx3 = bind ctx2 fTy                 -- f : A → A
      ctx4 = bind ctx3 (VNeutral (NVar 1)) -- x : B
      -- f x: f expects A but x : B. Should fail.
  in isLeft (infer ctx4 (App (Var 1) (Var 0)))

-- | Apply identity to U 0.
-- id : Π(A : U 1) . A → A  (need U 1 so U 0 : U 1 fits the domain)
-- App id (U 0) : U 0 → U 0
test_app_id_result = test "applying polymorphic id to U 0 gives U 0 -> U 0" $
  let idTy  = eval [] (Pi (U 1) (Pi (Var 0) (Var 1)))  -- Π(A:U1).A→A
      ctx1  = bind emptyCtx idTy           -- id : Π(A:U1).A→A
      -- App (Var 0) (U 0): apply id to U 0
      -- U 0 : U 1 ✓ (matches domain U 1)
      -- Result type: (A→A)[A↦U0] = U0 → U0
  in case infer ctx1 (App (Var 0) (U 0)) of
      Right ty -> quote (ctxLvl ctx1) ty == Pi (U 0) (U 0)
      Left _   -> False

-- | Check lambda against non-Pi type — must fail.
test_lam_check_nonpi = test "lambda checked against non-Pi type fails" $
  isLeft (check emptyCtx (Lam (Var 0)) (VU 0))

-- ============================================================
-- 2d. Conversion / NbE correctness (8 tests)
-- ============================================================

test_quote_lam, test_quote_pi, test_beta, test_beta_nested :: IO Bool
test_eta, test_noconv_U, test_noconv_var :: IO Bool
test_conv_refl_U, test_conv_refl_pi :: IO Bool

-- | eval then quote is identity on normal forms.
test_quote_lam = test "quote (eval (Lam (Var 0))) = Lam (Var 0)" $
  quote 0 (eval [] (Lam (Var 0))) == Lam (Var 0)

test_quote_pi = test "quote (eval (Pi (U 0) (Var 0))) = Pi (U 0) (Var 0)" $
  quote 0 (eval [] (Pi (U 0) (Var 0))) == Pi (U 0) (Var 0)

-- | Implements: Π-β (Section 4)
-- (λ . x) (U 0) ≡ U 0
test_beta = test "beta reduction: (lam x.x) (U 0) = U 0" $
  quote 0 (eval [] (App (Lam (Var 0)) (U 0))) == U 0

-- | Nested β: (λ . λ . Var 1) (U 0) applied to anything returns U 0.
test_beta_nested = test "nested beta: (lam.lam.Var1)(U0) applied to (U1) = U 0" $
  let v = eval [] (App (Lam (Lam (Var 1))) (U 0))
      -- v is a VLam; applying it to anything should give VU 0
      result = vApp v (VU 1)
  in quote 0 result == U 0

-- | Implements: Π-η (Section 4)
-- λ x . f x ≡ f  (where f is a neutral variable)
test_eta = test "eta: (lam x . f x) ≡ f" $
  let f    = VNeutral (NVar 0)
      -- Build VLam whose body applies f to its argument:
      -- Closure env=[f], body = App (Var 1) (Var 0)
      -- When instantiated with arg: eval [arg, f] (App (Var 1) (Var 0))
      --   = vApp f arg ✓
      lamF = VLam (Closure [f] (App (Var 1) (Var 0)))
  in conv 1 lamF f

-- | Non-conversion: different universe levels.
test_noconv_U = test "U 0 /= U 1" $
  not (conv 0 (VU 0) (VU 1))

-- | Non-conversion: different neutral variables.
test_noconv_var = test "NVar 0 /= NVar 1" $
  not (conv 2 (VNeutral (NVar 0)) (VNeutral (NVar 1)))

-- | Self-conversion (reflexivity).
test_conv_refl_U = test "conv reflexive: U 42 = U 42" $
  conv 0 (VU 42) (VU 42)

test_conv_refl_pi = test "conv reflexive: Pi type = itself" $
  let v = eval [] (Pi (U 0) (Var 0))
  in conv 0 v v

-- ============================================================
-- 2e. Negative tests — things that MUST be rejected (8 tests)
-- ============================================================

test_app_nonfunction, test_var_scope, test_var_scope2 :: IO Bool
test_pi_nontype_dom, test_lam_vs_universe :: IO Bool
test_deep_mismatch, test_universe_level, test_body_mismatch :: IO Bool

-- | Applying a non-function must fail.
test_app_nonfunction = test "applying non-function (U 0) (U 0) rejected" $
  case infer emptyCtx (App (U 0) (U 0)) of
    Left (NotAFunction _) -> True
    _                     -> False

-- | Variable out of scope in empty context.
test_var_scope = test "Var 0 out of scope in empty context" $
  case infer emptyCtx (Var 0) of
    Left (VariableOutOfScope _) -> True
    _                           -> False

test_var_scope2 = test "Var 5 out of scope in empty context" $
  case infer emptyCtx (Var 5) of
    Left (VariableOutOfScope _) -> True
    _                           -> False

-- | Pi with non-type domain.
-- Context: [A : U 0, f : A → A]
-- Pi (Var 0) (...): Var 0 = f : A → A, which is not a universe.
test_pi_nontype_dom = test "Pi with non-type domain rejected" $
  let ctx1 = bind emptyCtx (VU 0)
      fTy  = evalTerm (ctxEnv ctx1) (Pi (Var 0) (Var 1))
      ctx2 = bind ctx1 fTy                 -- f : A → A
      -- Pi (Var 0) (Var 0): domain is f, not a type
  in case infer ctx2 (Pi (Var 0) (Var 0)) of
      Left (NotAUniverse _) -> True
      _                     -> False

-- | Lambda checked against universe must fail.
test_lam_vs_universe = test "lambda checked against VU 0 fails" $
  isLeft (check emptyCtx (Lam (Var 0)) (VU 0))

-- | Deeply nested type error.
-- Π(A:U0).Π(B:U0).A→B with term λA.λB.λx.x
-- Body x has type A (Var 2) but expected B (Var 1). Should fail.
test_deep_mismatch = test "deep type mismatch in nested lambda" $
  let ty = Pi (U 0) (Pi (U 0) (Pi (Var 1) (Var 1)))
      -- This is Π(A:U0).Π(B:U0).A→B
      tm = Lam (Lam (Lam (Var 0)))
      -- λA.λB.λx.x : body returns x:A, but codomain says B
  in isLeft (check emptyCtx tm (eval [] ty))

-- | Universe level: U 0 : U 0 must fail (U 0 has type U 1, not U 0).
test_universe_level = test "U 0 checked against U 0 fails" $
  isLeft (check emptyCtx (U 0) (VU 0))

-- | Body mismatch: λ . U 1 against Π(_ : U 0) . U 0.
-- Body U 1 : U 2, but expected U 0. conv(VU 2, VU 0) = False.
test_body_mismatch = test "lambda body U 1 against Pi expecting U 0 fails" $
  isLeft (check emptyCtx (Lam (U 1)) (VPi (VU 0) (Closure [] (U 0))))

-- ============================================================
-- 2f. Stress tests (4 tests)
-- ============================================================

test_deep_id, test_large_universe, test_church_two, test_self_app_fail :: IO Bool

-- | 6-deep lambda: Π(A:U0).Π(B:U0).Π(C:U0).A→B→C→C
-- λ A B C x y z . z
-- After 6 binders [z,y,x,C,B,A]: z=Var0, y=Var1, x=Var2, C=Var3, B=Var4, A=Var5
-- Return type C = Var 3. Domain of each arrow: A=Var2, B=Var2, C=Var2 (shifts).
test_deep_id = test "6-deep lambda picks last argument" $
  let ty = Pi (U 0) (Pi (U 0) (Pi (U 0)
             (Pi (Var 2) (Pi (Var 2) (Pi (Var 2) (Var 3))))))
      tm = Lam (Lam (Lam (Lam (Lam (Lam (Var 0))))))
  in isRight (check emptyCtx tm (eval [] ty))

-- | Large universe level.
test_large_universe = test "U 999 : U 1000" $
  inferIsU emptyCtx (U 999) 1000

-- | Church numeral 2: Π(A:U0).(A→A)→A→A
-- λ A f x . f (f x)
test_church_two = test "Church numeral 2 type checks" $
  let -- Π(A:U0).(A→A)→A→A
      -- = Pi (U 0) (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2)))
      churchTy = Pi (U 0) (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2)))
      -- λ A . λ f . λ x . f (f x)
      -- Var 0 = x, Var 1 = f, Var 2 = A
      churchTm = Lam (Lam (Lam (App (Var 1) (App (Var 1) (Var 0)))))
  in isRight (check emptyCtx churchTm (eval [] churchTy))

-- | Self-application must fail.
-- Context: [A : U 0, f : A → A]
-- f f should fail: f expects A, but f : A → A ≠ A.
test_self_app_fail = test "self-application f f fails" $
  let ctx1 = bind emptyCtx (VU 0)
      fTy  = evalTerm (ctxEnv ctx1) (Pi (Var 0) (Var 1))
      ctx2 = bind ctx1 fTy
      -- App (Var 0) (Var 0): f applied to f
      -- f : A → A, but f expects argument of type A, not A → A
  in isLeft (infer ctx2 (App (Var 0) (Var 0)))

-- ============================================================
-- Phase 4: Cross-reference with elaboration-zoo (5 tests)
-- ============================================================
-- Adapted from AndrasKovacs/elaboration-zoo 02-typecheck-closures-debruijn.
-- That implementation uses type-in-type (U : U); we adjust for universe levels.

test_elab_nat_type, test_elab_church_five, test_elab_bool_true :: IO Bool
test_elab_bool_false, test_elab_compose :: IO Bool

-- | Church Nat = Π(N:U0).(N→N)→N→N lives in U 1.
-- elaboration-zoo tests this as the type of Church numerals.
-- In our system: quantifying over U 0 pushes the result into U 1.
test_elab_nat_type = test "[elab-zoo] Church Nat type : U 1" $
  let natTy = Pi (U 0) (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2)))
  in inferIsU emptyCtx natTy 1

-- | Church five: λN.λs.λz. s(s(s(s(sz)))) : Nat
-- elaboration-zoo defines five and uses it in arithmetic.
test_elab_church_five = test "[elab-zoo] Church five : Nat" $
  let natTy = Pi (U 0) (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2)))
      five  = Lam (Lam (Lam
                (App (Var 1) (App (Var 1) (App (Var 1)
                  (App (Var 1) (App (Var 1) (Var 0))))))))
  in isRight (check emptyCtx five (eval [] natTy))

-- | Church Bool = Π(B:U0).B→B→B, and true = λB.λt.λf. t
-- Tests checking against a 3-argument Church-encoded type.
test_elab_bool_true = test "[elab-zoo] Church true : Bool" $
  let boolTy = Pi (U 0) (Pi (Var 0) (Pi (Var 1) (Var 2)))
      true_  = Lam (Lam (Lam (Var 1)))
  in isRight (check emptyCtx true_ (eval [] boolTy))

-- | Church false = λB.λt.λf. f : Bool
test_elab_bool_false = test "[elab-zoo] Church false : Bool" $
  let boolTy = Pi (U 0) (Pi (Var 0) (Pi (Var 1) (Var 2)))
      false_ = Lam (Lam (Lam (Var 0)))
  in isRight (check emptyCtx false_ (eval [] boolTy))

-- | Polymorphic composition:
-- compose : Π(A:U0).Π(B:U0).Π(C:U0).(B→C)→(A→B)→A→C
-- compose = λA.λB.λC.λf.λg.λx. f(g x)
--
-- This is a key higher-order test from elaboration-zoo patterns.
-- De Bruijn for the type (verified by hand):
--   After A,B,C: Var 0=C, Var 1=B, Var 2=A
--   B→C at scope [C,B,A] = Pi (Var 1) (Var 1)
--     (domain = B, after binding: Var 1 = C)
--   A→B at scope [f,C,B,A] = Pi (Var 3) (Var 3)
--     (domain = A, after binding: Var 3 = B)
--   Domain A at scope [g,f,C,B,A] = Var 4
--   Return C at scope [x,g,f,C,B,A] = Var 3
test_elab_compose = test "[elab-zoo] compose function type checks" $
  let composeTy = Pi (U 0) (Pi (U 0) (Pi (U 0)
                    (Pi (Pi (Var 1) (Var 1))       -- f : B → C
                      (Pi (Pi (Var 3) (Var 3))     -- g : A → B
                        (Pi (Var 4)                -- x : A
                          (Var 3))))))             -- return C
      composeTm = Lam (Lam (Lam (Lam (Lam (Lam
                    (App (Var 2) (App (Var 1) (Var 0))))))))
  in isRight (check emptyCtx composeTm (eval [] composeTy))

-- ============================================================
-- All tests
-- ============================================================

allTests :: [IO Bool]
allTests =
  -- 2a. Universe rules (6)
  [ test_U0_type, test_U1_type, test_U5_type
  , test_U0_check_U1, test_U0_check_U0, test_U1_check_U1
  -- 2b. Pi-type formation (5)
  , test_pi_simple, test_pi_universe, test_pi_nested
  , test_pi_higher, test_pi_max_level
  -- 2c. Lambda + Application (10)
  , test_identity, test_const, test_lam_no_infer
  , test_var_lookup, test_app_simple, test_type_mismatch
  , test_double_app, test_wrong_arg_type
  , test_app_id_result, test_lam_check_nonpi
  -- 2d. Conversion / NbE (9)
  , test_quote_lam, test_quote_pi, test_beta, test_beta_nested
  , test_eta, test_noconv_U, test_noconv_var
  , test_conv_refl_U, test_conv_refl_pi
  -- 2e. Negative tests (8)
  , test_app_nonfunction, test_var_scope, test_var_scope2
  , test_pi_nontype_dom, test_lam_vs_universe
  , test_deep_mismatch, test_universe_level, test_body_mismatch
  -- 2f. Stress tests (4)
  , test_deep_id, test_large_universe, test_church_two, test_self_app_fail
  -- Phase 4: elaboration-zoo cross-reference (5)
  , test_elab_nat_type, test_elab_church_five
  , test_elab_bool_true, test_elab_bool_false
  , test_elab_compose
  ]
