-- | Kernel.Value — Semantic domain for Normalization by Evaluation (NbE).
--
-- Implements: Section 10 (NbE Sketch) of KERNEL.md
-- Values are the result of evaluating terms. Functions become closures.
-- A value is either a canonical form (VU, VPi, VLam, VSigma, VPair) or a neutral
-- (computation stuck on a free variable).
module Kernel.Value where

import Kernel.Syntax (Lvl, ULvl, Term(..))

-- | Environment: list of values, indexed by de Bruijn index.
-- The most recently bound variable is at the head (index 0).
type Env = [Val]

-- | Closure: a term body + the environment it was evaluated under.
-- Represents a binder waiting for an argument.
data Closure = Closure Env Term

-- We derive Show manually to avoid infinite loops
instance Show Closure where
  show (Closure _ t) = "Closure{" ++ show t ++ "}"

-- | Values (canonical forms or stuck computations)
--
-- Implements (value forms from Section 10):
--   VU ℓ           — Universe value
--   VPi A (x.B)    — Π type: domain value + closure for codomain
--   VLam (x.t)     — Lambda: closure for body
--   VNeutral n     — Stuck computation (blocked on a variable)
data Val
  = VU ULvl                    -- Universe value
  | VPi Val Closure            -- Π type: domain value + closure for codomain
  | VLam Closure               -- Lambda: closure for body
  | VSigma Val Closure         -- Σ type: domain value + closure for codomain
  | VPair Val Val              -- Pair value: (a, b)
  | VPathT Val Val Val         -- Path type value: VPathT A a b
  | VRefl Val                  -- Reflexivity value: refl a
  | VNeutral Neutral           -- Stuck computation
  deriving (Show)

-- | Neutral values (computations stuck on a variable)
--
-- Implements (neutral forms from Section 10):
--   NVar x         — A free variable (de Bruijn level)
--   NApp n v       — Application stuck on neutral function
data Neutral
  = NVar Lvl                   -- A free variable (de Bruijn level)
  | NApp Neutral Val           -- Application stuck on neutral function
  | NFst Neutral               -- fst stuck on neutral pair
  | NSnd Neutral               -- snd stuck on neutral pair
  | NJ Val Val Closure2 Val Val Neutral  -- J stuck: (A, a, motive-closure2, d, b, neutral-path)
  deriving (Show)

-- | A closure with 2 pending binders (used for J's motive).
-- The motive C lives in context Γ, y : A, p : Path A a y.
-- When instantiated: first arg = y (index 1), second arg = p (index 0).
data Closure2 = Closure2 Env Term

instance Show Closure2 where
  show (Closure2 _ t) = "Closure2{" ++ show t ++ "}"

-- | Instantiate a 2-binder closure with two values.
-- First arg binds to index 1 (y), second arg binds to index 0 (p).
instantiate2 :: Closure2 -> Val -> Val -> Val
instantiate2 (Closure2 env t) v1 v2 = evalTerm (v2 : v1 : env) t

-- | Instantiate a closure with a value.
-- Implements substitution: given closure (env, t) and value v,
-- evaluates t in the extended environment (v : env).
instantiate :: Closure -> Val -> Val
instantiate (Closure env t) v = evalTerm (v : env) t

-- | Apply a value to an argument.
--
-- Implements: Π-β (Section 4)
--   (λ (x : A) . t) u  ≡  t[x ↦ u]
-- For VLam: triggers β-reduction via closure instantiation.
-- For VNeutral: builds a stuck application NApp.
vApp :: Val -> Val -> Val
vApp (VLam cl)    arg = instantiate cl arg
vApp (VNeutral n) arg = VNeutral (NApp n arg)
vApp _            _   = error "vApp: not a function"

-- | First projection.
--
-- Implements: Σ-β₁ (Section 5)
--   fst (a, b) ≡ a
vFst :: Val -> Val
vFst (VPair a _) = a
vFst (VNeutral n) = VNeutral (NFst n)
vFst _ = error "vFst: not a pair"

-- | Second projection.
--
-- Implements: Σ-β₂ (Section 5)
--   snd (a, b) ≡ b
vSnd :: Val -> Val
vSnd (VPair _ b) = b
vSnd (VNeutral n) = VNeutral (NSnd n)
vSnd _ = error "vSnd: not a pair"

-- | J computation rule.
--
-- Implements: J-β (Section 6)
--   J A a C d a (refl a) ≡ d
-- On VRefl: reduces to base case d.
-- On VNeutral: stuck, produces NJ.
vJ :: Val -> Val -> Closure2 -> Val -> Val -> Val -> Val
vJ _tyA _a _c d _b (VRefl _) = d
vJ tyA a c d b (VNeutral n)  = VNeutral (NJ tyA a c d b n)
vJ _ _ _ _ _ _                = error "vJ: invalid path argument"

-- | Evaluate a term under an environment.
--
-- Implements: Evaluation (Section 10)
-- All β-reductions happen eagerly here. The key invariant:
-- a value is either canonical or neutral (stuck on a variable).
evalTerm :: Env -> Term -> Val
evalTerm env term = case term of
  Var ix  -> env !! ix    -- look up by de Bruijn index from head
  U lvl   -> VU lvl
  Pi a b  -> VPi (evalTerm env a) (Closure env b)
  Lam t   -> VLam (Closure env t)
  App f a   -> vApp (evalTerm env f) (evalTerm env a)
  Sigma a b -> VSigma (evalTerm env a) (Closure env b)
  Pair a b  -> VPair (evalTerm env a) (evalTerm env b)
  Fst t     -> vFst (evalTerm env t)
  Snd t     -> vSnd (evalTerm env t)
  PathT a t u -> VPathT (evalTerm env a) (evalTerm env t) (evalTerm env u)
  Refl t      -> VRefl (evalTerm env t)
  J tyA a c d b p -> vJ (evalTerm env tyA) (evalTerm env a)
                         (Closure2 env c) (evalTerm env d)
                         (evalTerm env b) (evalTerm env p)
