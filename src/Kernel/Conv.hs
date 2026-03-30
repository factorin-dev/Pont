module Kernel.Conv where

import Kernel.Syntax (Lvl)
import Kernel.Value

-- | Check if two values are convertible (definitionally equal)
--   at the given de Bruijn level
conv :: Lvl -> Val -> Val -> Bool
conv lvl v1 v2 = case (v1, v2) of
  (VU l1, VU l2) -> l1 == l2

  (VPi a1 cl1, VPi a2 cl2) ->
    conv lvl a1 a2 &&
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl1 fresh) (instantiate cl2 fresh)

  (VLam cl1, VLam cl2) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl1 fresh) (instantiate cl2 fresh)

  -- η-expansion: f ≡ λ x . f x
  (VLam cl, v) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (instantiate cl fresh) (vApp v fresh)

  (v, VLam cl) ->
    let fresh = VNeutral (NVar lvl)
    in conv (lvl + 1) (vApp v fresh) (instantiate cl fresh)

  (VNeutral n1, VNeutral n2) -> convNeutral lvl n1 n2

  _ -> False

-- | Check if two neutral values are convertible
convNeutral :: Lvl -> Neutral -> Neutral -> Bool
convNeutral lvl n1 n2 = case (n1, n2) of
  (NVar x, NVar y)           -> x == y
  (NApp f1 a1, NApp f2 a2)   -> convNeutral lvl f1 f2 && conv lvl a1 a2
  _                           -> False
