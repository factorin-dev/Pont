-- | Property-based tests for the Pont kernel using QuickCheck.
-- Tests structural invariants that must hold for ALL well-scoped terms.
{-# OPTIONS_GHC -Wno-orphans #-}
module Properties (runPropertyTests) where

import Test.QuickCheck
import Kernel.Syntax
import Kernel.Value
import Kernel.Eval (eval)
import Kernel.Quote (quote)
import Kernel.Conv (conv)
import Kernel.Check
import Kernel.Context

-- ============================================================
-- Term generator: well-scoped random terms
-- ============================================================

-- | Generate a random well-scoped term.
-- depth: remaining depth budget (to prevent infinite terms)
-- scope: number of variables currently in scope
genTerm :: Int -> Int -> Gen Term
genTerm 0 scope = frequency $
  [(2, U <$> choose (0, 5))] ++
  [(3, Var <$> choose (0, scope - 1)) | scope > 0]
genTerm depth scope = frequency $
  [(2, U <$> choose (0, 5))] ++
  [(3, Var <$> choose (0, scope - 1)) | scope > 0] ++
  [(2, Pi <$> genTerm (depth-1) scope <*> genTerm (depth-1) (scope+1))] ++
  [(2, Lam <$> genTerm (depth-1) (scope+1))] ++
  [(2, App <$> genTerm (depth-1) scope <*> genTerm (depth-1) scope)] ++
  [(2, Sigma <$> genTerm (depth-1) scope <*> genTerm (depth-1) (scope+1))] ++
  [(2, Pair <$> genTerm (depth-1) scope <*> genTerm (depth-1) scope)] ++
  [(1, Fst <$> genTerm (depth-1) scope)] ++
  [(1, Snd <$> genTerm (depth-1) scope)] ++
  [(1, PathT <$> genTerm (depth-1) scope <*> genTerm (depth-1) scope <*> genTerm (depth-1) scope)] ++
  [(1, Refl <$> genTerm (depth-1) scope)] ++
  [(1, J <$> genTerm (depth-2) scope <*> genTerm (depth-2) scope
         <*> genTerm (depth-2) (scope+2) <*> genTerm (depth-2) scope
         <*> genTerm (depth-2) scope <*> genTerm (depth-2) scope) | depth >= 3] ++
  [(1, Ua <$> genTerm (depth-1) scope)] ++
  [(1, UaInv <$> genTerm (depth-1) scope)]

instance Arbitrary Term where
  arbitrary = sized $ \n -> genTerm (min n 5) 0
  shrink (Pi a b)    = [a, b] ++ [Pi a' b | a' <- shrink a] ++ [Pi a b' | b' <- shrink b]
  shrink (Lam t)     = [t] ++ [Lam t' | t' <- shrink t]
  shrink (App f a)   = [f, a] ++ [App f' a | f' <- shrink f] ++ [App f a' | a' <- shrink a]
  shrink (Sigma a b) = [a, b] ++ [Sigma a' b | a' <- shrink a] ++ [Sigma a b' | b' <- shrink b]
  shrink (Pair a b)  = [a, b] ++ [Pair a' b | a' <- shrink a] ++ [Pair a b' | b' <- shrink b]
  shrink (Fst t)     = [t] ++ [Fst t' | t' <- shrink t]
  shrink (Snd t)     = [t] ++ [Snd t' | t' <- shrink t]
  shrink (PathT a t u) = [a, t, u] ++ [PathT a' t u | a' <- shrink a] ++ [PathT a t' u | t' <- shrink t] ++ [PathT a t u' | u' <- shrink u]
  shrink (Refl t)    = [t] ++ [Refl t' | t' <- shrink t]
  shrink (J a b c d e f) = [a,b,c,d,e,f] ++ [J a' b c d e f | a' <- shrink a] ++ [J a b' c d e f | b' <- shrink b] ++ [J a b c' d e f | c' <- shrink c] ++ [J a b c d' e f | d' <- shrink d] ++ [J a b c d e' f | e' <- shrink e] ++ [J a b c d e f' | f' <- shrink f]
  shrink (Ua t)    = [t] ++ [Ua t' | t' <- shrink t]
  shrink (UaInv t) = [t] ++ [UaInv t' | t' <- shrink t]
  shrink (U n)       = [U n' | n' <- shrink n, n' >= 0]
  shrink (Var _)     = []

-- ============================================================
-- Helper: check all Var indices in a term are within scope
-- ============================================================

allVarsInScope :: Int -> Term -> Bool
allVarsInScope bound (Var ix)      = ix >= 0 && ix < bound
allVarsInScope _     (U _)         = True
allVarsInScope bound (Pi a b)      = allVarsInScope bound a && allVarsInScope (bound + 1) b
allVarsInScope bound (Lam t)       = allVarsInScope (bound + 1) t
allVarsInScope bound (App f a)     = allVarsInScope bound f && allVarsInScope bound a
allVarsInScope bound (Sigma a b)   = allVarsInScope bound a && allVarsInScope (bound + 1) b
allVarsInScope bound (Pair a b)    = allVarsInScope bound a && allVarsInScope bound b
allVarsInScope bound (Fst t)       = allVarsInScope bound t
allVarsInScope bound (Snd t)       = allVarsInScope bound t
allVarsInScope bound (PathT a t u) = allVarsInScope bound a && allVarsInScope bound t && allVarsInScope bound u
allVarsInScope bound (Refl t)      = allVarsInScope bound t
allVarsInScope bound (J a b c d e f) = allVarsInScope bound a && allVarsInScope bound b && allVarsInScope (bound+2) c && allVarsInScope bound d && allVarsInScope bound e && allVarsInScope bound f
allVarsInScope bound (Ua t)        = allVarsInScope bound t
allVarsInScope bound (UaInv t)     = allVarsInScope bound t

-- | Check if a term is well-typed in the empty context.
-- Used to guard properties that need well-typed terms (eval won't crash).
wellTyped :: Term -> Bool
wellTyped t = case infer emptyCtx t of
  Right _ -> True
  Left _  -> False

-- ============================================================
-- Property 1: eval-quote idempotence
-- For any well-typed closed term t:
--   quote 0 (eval [] (quote 0 (eval [] t))) == quote 0 (eval [] t)
-- i.e., normalizing twice gives the same result as normalizing once.
-- ============================================================

prop_eval_quote_roundtrip :: Property
prop_eval_quote_roundtrip = forAll (genTerm 4 0) $ \t ->
  wellTyped t ==>
    let v   = eval [] t
        nf  = quote 0 v
        v'  = eval [] nf
        nf' = quote 0 v'
    in nf == nf'

-- ============================================================
-- Property 2: conv is reflexive
-- For any well-typed term's value: conv lvl v v == True
-- ============================================================

prop_conv_reflexive :: Property
prop_conv_reflexive = forAll (genTerm 4 0) $ \t ->
  wellTyped t ==>
    let v = eval [] t
    in conv 0 v v

-- ============================================================
-- Property 3: conv is symmetric
-- For any two well-typed terms: conv v1 v2 == conv v2 v1
-- ============================================================

prop_conv_symmetric :: Property
prop_conv_symmetric = forAll (genTerm 3 0) $ \t1 ->
  forAll (genTerm 3 0) $ \t2 ->
    (wellTyped t1 && wellTyped t2) ==>
      let v1 = eval [] t1
          v2 = eval [] t2
      in conv 0 v1 v2 == conv 0 v2 v1

-- ============================================================
-- Property 4: infer is deterministic
-- Two calls to infer on the same term give the same result.
-- ============================================================

prop_infer_deterministic :: Property
prop_infer_deterministic = forAll (genTerm 4 0) $ \t ->
  let r1 = infer emptyCtx t
      r2 = infer emptyCtx t
  in case (r1, r2) of
      (Right v1, Right v2) -> quote 0 v1 == quote 0 v2
      (Left _, Left _)     -> True
      _                    -> False

-- ============================================================
-- Property 5: well-typed terms don't crash eval
-- If infer ctx t == Right _, then eval env t doesn't error.
-- ============================================================

prop_eval_no_crash :: Property
prop_eval_no_crash = forAll (genTerm 4 0) $ \t ->
  case infer emptyCtx t of
    Right _ ->
      let v = eval [] t
          nf = quote 0 v
      in length (show nf) >= 0  -- force evaluation
    Left _ -> True  -- skip ill-typed

-- ============================================================
-- Property 6: type of U is always VU (ℓ+1)
-- ============================================================

prop_type_of_type_is_universe :: Property
prop_type_of_type_is_universe = forAll (choose (0, 100)) $ \lvl ->
  case infer emptyCtx (U lvl) of
    Right (VU n) -> n == lvl + 1
    _            -> False

-- ============================================================
-- Property 7: quote produces well-scoped terms
-- For closed well-typed terms: quote at level 0 produces no free variables.
-- ============================================================

prop_quote_well_scoped :: Property
prop_quote_well_scoped = forAll (genTerm 4 0) $ \t ->
  wellTyped t ==>
    let v  = eval [] t
        nf = quote 0 v
    in allVarsInScope 0 nf

-- ============================================================
-- Runner
-- ============================================================

runPropertyTests :: IO Bool
runPropertyTests = do
  putStrLn "=== Property Tests (QuickCheck, 1000 inputs each) ==="
  putStrLn ""
  results <- mapM runOne tests
  let numPassed = length (filter id results)
      numTotal  = length results
  putStrLn ""
  putStrLn $ "  " ++ show numPassed ++ "/" ++ show numTotal ++ " property tests passed."
  return (and results)
  where
    tests =
      [ ("eval-quote roundtrip",       prop_eval_quote_roundtrip)
      , ("conv reflexive",             prop_conv_reflexive)
      , ("conv symmetric",             prop_conv_symmetric)
      , ("infer deterministic",        prop_infer_deterministic)
      , ("eval no crash (well-typed)", prop_eval_no_crash)
      , ("type of U is always VU",     prop_type_of_type_is_universe)
      , ("quote well-scoped",          prop_quote_well_scoped)
      ]

    runOne (name, prop) = do
      result <- quickCheckWithResult stdArgs{ maxSuccess = 1000, maxDiscardRatio = 100, chatty = False } prop
      case result of
        Success{} -> do
          putStrLn $ "  \x2713 " ++ name ++ " (1000 tests)"
          return True
        failure -> do
          putStrLn $ "  \x2717 " ++ name ++ ": " ++ output failure
          return False
