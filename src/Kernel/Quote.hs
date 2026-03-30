-- | Kernel.Quote — Quotation: reads values back into normal-form terms.
--
-- Implements: Quotation (Section 10 of KERNEL.md)
-- Part of the NbE pipeline: Term →(eval)→ Val →(quote)→ Term (normal form).
-- Used by conversion checking: to compare values, quote both and compare terms.
module Kernel.Quote where

import Kernel.Syntax
import Kernel.Value

-- | Quote a value back to a normal-form term.
--   `lvl` is the current de Bruijn level (= number of binders we're under).
--
-- Implements: Quotation (Section 10)
-- For each canonical form, recursively quotes subterms.
-- For binders (VPi, VLam), instantiates the closure with a fresh
-- variable at the current level, then quotes the body at lvl+1.
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
  VSigma a cl    ->
    let va = quote lvl a
        vb = quote (lvl + 1) (instantiate cl (VNeutral (NVar lvl)))
    in Sigma va vb
  VPair a b      -> Pair (quote lvl a) (quote lvl b)
  VPathT a t u   -> PathT (quote lvl a) (quote lvl t) (quote lvl u)
  VRefl t        -> Refl (quote lvl t)
  VNeutral n     -> quoteNeutral lvl n

-- | Quote a neutral value back to a term.
--
-- Implements: Quotation of neutrals (Section 10)
-- Key formula: NVar x → Var (lvl - x - 1)
-- This converts a de Bruijn level back to a de Bruijn index.
quoteNeutral :: Lvl -> Neutral -> Term
quoteNeutral lvl neu = case neu of
  NVar x   -> Var (lvl - x - 1)   -- Convert level back to index
  NApp n v -> App (quoteNeutral lvl n) (quote lvl v)
  NFst n   -> Fst (quoteNeutral lvl n)
  NSnd n   -> Snd (quoteNeutral lvl n)
  NJ tyA a c2 d b n ->
    let freshY = VNeutral (NVar lvl)
        freshP = VNeutral (NVar (lvl + 1))
        cVal   = instantiate2 c2 freshY freshP
        cTerm  = quote (lvl + 2) cVal
    in J (quote lvl tyA) (quote lvl a) cTerm (quote lvl d) (quote lvl b) (quoteNeutral lvl n)
