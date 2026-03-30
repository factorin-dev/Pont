-- | Kernel.Eval — Re-exports evaluation primitives from Value.
--
-- The actual evaluation logic lives in Value.hs to avoid circular
-- imports (Conv.hs needs vApp, which needs evalTerm).
module Kernel.Eval
  ( eval
  , vApp
  , instantiate
  ) where

import Kernel.Syntax (Term)
import Kernel.Value (Env, Val, vApp, instantiate, evalTerm)

-- | Evaluate a term under an environment.
-- See Value.hs evalTerm for the implementation.
eval :: Env -> Term -> Val
eval = evalTerm
