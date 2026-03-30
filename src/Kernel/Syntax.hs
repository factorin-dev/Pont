module Kernel.Syntax where

-- | De Bruijn index (bound variables in terms)
type Ix = Int

-- | De Bruijn level (free variables in values)
type Lvl = Int

-- | Universe level
type ULvl = Int

-- | Raw terms. This is the full syntax tree that the type checker operates on.
data Term
  = Var Ix              -- Variable (de Bruijn index)
  | U ULvl              -- Universe
  | Pi Term Term        -- Π (x : A) . B — first is domain, second is codomain (binds one var)
  | Lam Term            -- λ . t — the domain type is NOT stored here, only the body (binds one var)
  | App Term Term       -- Application
  deriving (Show, Eq)
