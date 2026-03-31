-- | Kernel.Syntax — Raw terms with de Bruijn indices.
--
-- Implements: Section 1 (Raw Syntax) of KERNEL.md
-- Milestone 1: U, Var, Π, λ, App.
-- Milestone 2: Σ, Pair, Fst, Snd.
-- Milestone 3: Path, Refl, J.
-- Milestone 4: Ua, UaInv (univalence).
--
-- Convention: de Bruijn index 0 = most recently bound variable.
-- Levels are used in the value domain (Value.hs); indices here.
module Kernel.Syntax where

-- | De Bruijn index (bound variables in terms)
type Ix = Int

-- | De Bruijn level (free variables in values)
type Lvl = Int

-- | Universe level
type ULvl = Int

-- | Raw terms. This is the full syntax tree that the type checker operates on.
--
-- Implements (term formers from Section 1):
--   U ℓ             → U ULvl
--   x               → Var Ix
--   Π (x : A) . B   → Pi Term Term
--   λ (x : A) . t   → Lam Term      (domain NOT stored; checked against Pi type)
--   t u              → App Term Term
--   Σ (x : A) . B   → Sigma Term Term
--   (a , b)          → Pair Term Term
--   fst t            → Fst Term
--   snd t            → Snd Term
data Term
  = Var Ix              -- Variable (de Bruijn index)
  | U ULvl              -- Universe
  | Pi Term Term        -- Π (x : A) . B — first is domain, second is codomain (binds one var)
  | Lam Term            -- λ . t — the domain type is NOT stored here, only the body (binds one var)
  | App Term Term       -- Application
  | Sigma Term Term     -- Σ (x : A) . B — dependent pair type (binds one var)
  | Pair Term Term      -- (a, b) — pair introduction
  | Fst Term            -- First projection
  | Snd Term            -- Second projection
  | PathT Term Term Term   -- Path A a b — path type (identity type)
  | Refl Term              -- refl a — reflexivity: Path A a a
  | J Term Term Term Term Term Term  -- J A a C d b p — path eliminator (C binds 2 vars)
  | Ua Term            -- ua e : (A ≃ B) → Path (U ℓ) A B
  | UaInv Term         -- ua⁻¹ p : Path (U ℓ) A B → (A ≃ B)
  deriving (Show, Eq)
