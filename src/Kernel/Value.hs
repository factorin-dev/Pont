module Kernel.Value where

import Kernel.Syntax (Lvl, ULvl, Term(..))

-- | Environment: list of values, indexed by de Bruijn index
-- The most recently bound variable is at the head (index 0).
type Env = [Val]

-- | Closure: a term body + the environment it was evaluated under
data Closure = Closure Env Term

-- We derive Show manually to avoid infinite loops
instance Show Closure where
  show (Closure _ t) = "Closure{" ++ show t ++ "}"

-- | Values (canonical forms or stuck computations)
data Val
  = VU ULvl                    -- Universe value
  | VPi Val Closure            -- Π type: domain value + closure for codomain
  | VLam Closure               -- Lambda: closure for body
  | VNeutral Neutral           -- Stuck computation
  deriving (Show)

-- | Neutral values (computations stuck on a variable)
data Neutral
  = NVar Lvl                   -- A free variable (de Bruijn level)
  | NApp Neutral Val           -- Application stuck on neutral function
  deriving (Show)

-- | Apply a closure to a value
instantiate :: Closure -> Val -> Val
instantiate (Closure env t) v = evalTerm (v : env) t

-- | Apply a value to an argument
vApp :: Val -> Val -> Val
vApp (VLam cl)    arg = instantiate cl arg
vApp (VNeutral n) arg = VNeutral (NApp n arg)
vApp _            _   = error "vApp: not a function"

-- | Evaluation function — defined here to avoid circular imports.
-- This is the core NbE evaluator.
evalTerm :: Env -> Term -> Val
evalTerm env term = case term of
  Var ix  -> env !! ix
  U lvl   -> VU lvl
  Pi a b  -> VPi (evalTerm env a) (Closure env b)
  Lam t   -> VLam (Closure env t)
  App f a -> vApp (evalTerm env f) (evalTerm env a)
