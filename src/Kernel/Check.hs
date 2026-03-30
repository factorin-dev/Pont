module Kernel.Check where

import Kernel.Syntax
import Kernel.Value
import Kernel.Conv (conv)
import Kernel.Context

-- | Type checking errors
data TypeError
  = NotAFunction Val
  | TypeMismatch Val Val        -- expected, got
  | NotAUniverse Val
  | VariableOutOfScope Ix
  | CannotInferLambda
  deriving (Show)

-- | Infer the type of a term (returns a value)
infer :: Ctx -> Term -> Either TypeError Val
infer ctx term = case term of
  Var ix ->
    if ix < length (ctxTypes ctx)
      then Right (ctxTypes ctx !! ix)
      else Left (VariableOutOfScope ix)

  U lvl -> Right (VU (lvl + 1))   -- U ℓ : U (ℓ+1)

  Pi a b -> do
    -- Check that `a` is a type (lives in some universe)
    aLvl <- inferUniverse ctx a
    let aVal = evalTerm (ctxEnv ctx) a
    -- Check that `b` is a type, under context extended with x : a
    bLvl <- inferUniverse (bind ctx aVal) b
    -- Π (x : A) . B : U (max ℓ₁ ℓ₂)
    Right (VU (max aLvl bLvl))

  App f a -> do
    fTy <- infer ctx f
    case fTy of
      VPi domTy codCl -> do
        check ctx a domTy
        let aVal = evalTerm (ctxEnv ctx) a
        Right (instantiate codCl aVal)
      ty -> Left (NotAFunction ty)

  Lam _ -> Left CannotInferLambda
    -- Cannot infer type of bare lambda.
    -- Lambdas are checked, not inferred.

-- | Check that a term has the given type
check :: Ctx -> Term -> Val -> Either TypeError ()
check ctx term ty = case (term, ty) of
  (Lam body, VPi domTy codCl) -> do
    -- Check body under extended context
    let ctx' = bind ctx domTy
    let codTy = instantiate codCl (VNeutral (NVar (ctxLvl ctx)))
    check ctx' body codTy

  _ -> do
    -- Fall back to inference + conversion
    inferredTy <- infer ctx term
    let lvl = ctxLvl ctx
    if conv lvl inferredTy ty
      then Right ()
      else Left (TypeMismatch ty inferredTy)

-- | Check that a term is a type, and return its universe level
inferUniverse :: Ctx -> Term -> Either TypeError ULvl
inferUniverse ctx t = do
  ty <- infer ctx t
  case ty of
    VU lvl -> Right lvl
    other  -> Left (NotAUniverse other)
