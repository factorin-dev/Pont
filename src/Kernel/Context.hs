-- | Kernel.Context — Typing contexts for the bidirectional type checker.
--
-- Implements: Context formation (Section 2 of KERNEL.md)
--   ⊢ Γ ctx    — Γ is a well-formed context
--   Γ ::= · | Γ, x : A
module Kernel.Context where

import Kernel.Syntax (Lvl)
import Kernel.Value (Val(..), Neutral(..), Env)

-- | Typing context.
-- Tracks: evaluation environment (for eval), types of variables (for checking),
-- and current de Bruijn level (for fresh variable generation).
data Ctx = Ctx
  { ctxEnv   :: Env    -- Values of defined variables (for evaluation)
  , ctxTypes :: [Val]  -- Types of variables (for type checking)
  , ctxLvl   :: Lvl    -- Current de Bruijn level
  } deriving (Show)

-- | Empty context.
-- Implements: · (empty context)
emptyCtx :: Ctx
emptyCtx = Ctx [] [] 0

-- | Extend context with a new bound variable of the given type.
--
-- Implements: Γ, x : A  (context extension)
-- Creates a fresh neutral variable at the current level and adds it to
-- both the environment (for evaluation) and the type list (for checking).
-- Increments ctxLvl.
bind :: Ctx -> Val -> Ctx
bind (Ctx env tys lvl) ty = Ctx
  { ctxEnv   = VNeutral (NVar lvl) : env
  , ctxTypes = ty : tys
  , ctxLvl   = lvl + 1
  }
