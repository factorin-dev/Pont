module Kernel.Context where

import Kernel.Syntax (Lvl)
import Kernel.Value (Val(..), Neutral(..), Env)

-- | Typing context
data Ctx = Ctx
  { ctxEnv   :: Env    -- Values of defined variables (for evaluation)
  , ctxTypes :: [Val]  -- Types of variables (for type checking)
  , ctxLvl   :: Lvl    -- Current de Bruijn level
  } deriving (Show)

-- | Empty context
emptyCtx :: Ctx
emptyCtx = Ctx [] [] 0

-- | Extend context with a new bound variable of the given type.
--   The variable itself becomes a fresh neutral.
bind :: Ctx -> Val -> Ctx
bind (Ctx env tys lvl) ty = Ctx
  { ctxEnv   = VNeutral (NVar lvl) : env
  , ctxTypes = ty : tys
  , ctxLvl   = lvl + 1
  }
