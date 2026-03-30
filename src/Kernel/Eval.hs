module Kernel.Eval
  ( eval
  , vApp
  , instantiate
  ) where

import Kernel.Syntax (Term)
import Kernel.Value (Env, Val, vApp, instantiate, evalTerm)

-- | Evaluate a term under an environment
eval :: Env -> Term -> Val
eval = evalTerm
