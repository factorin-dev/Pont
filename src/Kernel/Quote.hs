module Kernel.Quote where

import Kernel.Syntax
import Kernel.Value

-- | Quote a value back to a normal-form term.
--   `lvl` is the current de Bruijn level (= number of binders we're under)
quote :: Lvl -> Val -> Term
quote lvl val = case val of
  VU ulvl        -> U ulvl
  VPi a cl       ->
    let va = quote lvl a
        -- Apply closure to a fresh variable at current level
        vb = quote (lvl + 1) (instantiate cl (VNeutral (NVar lvl)))
    in Pi va vb
  VLam cl        ->
    let body = quote (lvl + 1) (instantiate cl (VNeutral (NVar lvl)))
    in Lam body
  VNeutral n     -> quoteNeutral lvl n

-- | Quote a neutral value
quoteNeutral :: Lvl -> Neutral -> Term
quoteNeutral lvl neu = case neu of
  NVar x   -> Var (lvl - x - 1)   -- Convert level back to index
  NApp n v -> App (quoteNeutral lvl n) (quote lvl v)
