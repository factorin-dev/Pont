-- | Kernel.Conv — Conversion checking: decides definitional equality.
--
-- Implements: Section 9 (Definitional Equality / Conversion) of KERNEL.md
-- Two values are convertible if they reduce to the same normal form.
-- Since values are already evaluated (β-reduced), we compare structurally
-- with η-expansion for functions.
module Kernel.Conv where

import Kernel.Syntax (Lvl)
import Kernel.Value

-- | Check if two values are convertible (definitionally equal)
--   at the given de Bruijn level.
--
-- Implements: Conversion checking algorithm (Section 9)
--   1. Compare heads (canonical vs canonical, neutral vs neutral)
--   2. For binders, instantiate with fresh variable and recurse
--   3. Handle Π-η (Section 4): f ≡ λ x . f x
conv :: Lvl -> Val -> Val -> Bool
conv lvl v1 v2 = case (v1, v2) of
  -- | Implements: Universe comparison (structural)
  (VU l1, VU l2) -> l1 == l2

  -- | Implements: Congruence for Π types
  -- Two Π types are equal iff domains are equal and codomains are equal
  -- (under a fresh variable).
  (VPi a1 cl1, VPi a2 cl2) ->
    conv lvl a1 a2 &&
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl1 fresh) (instantiate cl2 fresh)

  -- | Implements: Congruence for λ (compare bodies under fresh variable)
  (VLam cl1, VLam cl2) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl1 fresh) (instantiate cl2 fresh)

  -- | Implements: Π-η (Section 4)
  --   f ≡ λ x . f x    (if f : Π (x : A) . B)
  -- A lambda is equal to a non-lambda if applying the non-lambda
  -- to a fresh variable gives the same result as the lambda body.
  (VLam cl, v) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl fresh) (vApp v fresh)

  -- | Implements: Π-η (symmetric case)
  (v, VLam cl) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (vApp v fresh) (instantiate cl fresh)

  -- | Neutral-neutral: compare structurally
  (VNeutral n1, VNeutral n2) -> convNeutral lvl n1 n2

  _ -> False

-- | Check if two neutral values are convertible.
-- Structural comparison: same head variable, same spine of arguments.
convNeutral :: Lvl -> Neutral -> Neutral -> Bool
convNeutral lvl n1 n2 = case (n1, n2) of
  (NVar x, NVar y)           -> x == y
  (NApp f1 a1, NApp f2 a2)   -> convNeutral lvl f1 f2 && conv lvl a1 a2
  _                           -> False
