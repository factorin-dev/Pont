-- | Kernel.Check — Bidirectional type checker.
--
-- Implements: Typing judgment (Section 2 of KERNEL.md)
--   Γ ⊢ t : A    — t has type A in context Γ
-- Two modes:
--   infer : Ctx → Term → Either TypeError Val    (synthesize type)
--   check : Ctx → Term → Val → Either TypeError ()  (verify against given type)
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
  | NotASigma Val
  | CannotInferPair
  deriving (Show)

-- | Infer the type of a term (returns a value).
-- Implements the synthesis direction of bidirectional typing.
infer :: Ctx -> Term -> Either TypeError Val
infer ctx term = case term of

  -- | Variable lookup.
  -- Γ(x) = A  ⟹  Γ ⊢ x : A
  Var ix ->
    if ix < length (ctxTypes ctx)
      then Right (ctxTypes ctx !! ix)
      else Left (VariableOutOfScope ix)

  -- | Implements: U-Type (Section 3)
  -- ─────────────────────
  --  Γ ⊢ U ℓ : U (ℓ+1)
  U lvl -> Right (VU (lvl + 1))

  -- | Implements: Π-Form (Section 4)
  --   Γ ⊢ A : U ℓ₁    Γ, x : A ⊢ B : U ℓ₂
  --  ────────────────────────────────────────────
  --          Γ ⊢ Π (x : A) . B : U (max ℓ₁ ℓ₂)
  Pi a b -> do
    aLvl <- inferUniverse ctx a
    let aVal = evalTerm (ctxEnv ctx) a
    bLvl <- inferUniverse (bind ctx aVal) b
    Right (VU (max aLvl bLvl))

  -- | Implements: Π-Elim (Section 4)
  --   Γ ⊢ f : Π (x : A) . B    Γ ⊢ a : A
  --  ─────────────────────────────────────────
  --              Γ ⊢ f a : B[x ↦ a]
  App f a -> do
    fTy <- infer ctx f
    case fTy of
      VPi domTy codCl -> do
        check ctx a domTy
        let aVal = evalTerm (ctxEnv ctx) a
        Right (instantiate codCl aVal)
      ty -> Left (NotAFunction ty)

  -- | Implements: Σ-Form (Section 5)
  --   Γ ⊢ A : U ℓ₁    Γ, x : A ⊢ B : U ℓ₂
  --  ────────────────────────────────────────────
  --          Γ ⊢ Σ (x : A) . B : U (max ℓ₁ ℓ₂)
  Sigma a b -> do
    aLvl <- inferUniverse ctx a
    let aVal = evalTerm (ctxEnv ctx) a
    bLvl <- inferUniverse (bind ctx aVal) b
    Right (VU (max aLvl bLvl))

  -- | Implements: Σ-fst (Section 5)
  --   Γ ⊢ t : Σ (x : A) . B
  --  ────────────────────────
  --   Γ ⊢ fst t : A
  Fst t -> do
    tTy <- infer ctx t
    case tTy of
      VSigma a _ -> Right a
      other -> Left (NotASigma other)

  -- | Implements: Σ-snd (Section 5)
  --   Γ ⊢ t : Σ (x : A) . B
  --  ──────────────────────────────
  --   Γ ⊢ snd t : B[x ↦ fst t]
  Snd t -> do
    tTy <- infer ctx t
    case tTy of
      VSigma _ cl -> do
        let tVal = evalTerm (ctxEnv ctx) t
        Right (instantiate cl (vFst tVal))
      other -> Left (NotASigma other)

  -- | Lambda cannot be inferred — it must be checked against a known Π type.
  Lam _ -> Left CannotInferLambda

  -- | Pair cannot be inferred — it must be checked against a known Σ type.
  Pair _ _ -> Left CannotInferPair

-- | Check that a term has the given type.
-- Implements the checking direction of bidirectional typing.
check :: Ctx -> Term -> Val -> Either TypeError ()
check ctx term ty = case (term, ty) of

  -- | Implements: Π-Intro (Section 4)
  --       Γ, x : A ⊢ t : B
  --  ───────────────────────────────
  --   Γ ⊢ λ (x : A) . t : Π (x : A) . B
  --
  -- Check lambda body under extended context with domain type.
  (Lam body, VPi domTy codCl) -> do
    let ctx' = bind ctx domTy
    let codTy = instantiate codCl (VNeutral (NVar (ctxLvl ctx)))
    check ctx' body codTy

  -- | Implements: Σ-Intro (Section 5)
  --   Γ ⊢ a : A    Γ ⊢ b : B[x ↦ a]
  --  ──────────────────────────────────
  --   Γ ⊢ (a, b) : Σ (x : A) . B
  (Pair a b, VSigma domTy codCl) -> do
    check ctx a domTy
    let aVal = evalTerm (ctxEnv ctx) a
    check ctx b (instantiate codCl aVal)

  -- | Fallback: infer the type and check conversion.
  --
  -- Implements: Conversion (Section 9)
  --   Γ ⊢ t : A    Γ ⊢ A ≡ B
  --  ──────────────────────────
  --         Γ ⊢ t : B
  _ -> do
    inferredTy <- infer ctx term
    let lvl = ctxLvl ctx
    if conv lvl inferredTy ty
      then Right ()
      else Left (TypeMismatch ty inferredTy)

-- | Check that a term is a well-formed type, and return its universe level.
--
-- Implements: Γ ⊢ A type  (Section 2)
-- Which is sugar for: Γ ⊢ A : U ℓ  for some ℓ.
inferUniverse :: Ctx -> Term -> Either TypeError ULvl
inferUniverse ctx t = do
  ty <- infer ctx t
  case ty of
    VU lvl -> Right lvl
    other  -> Left (NotAUniverse other)
