# Pont

A minimal type checker based on Homotopy Type Theory (HoTT), designed for verified DeFi quantitative finance.

## What is this?

Pont is a type checker — it takes a program and a type specification, and answers yes or no. The core idea: use HoTT's transport and univalence to carry proofs across equivalent DeFi protocols (cross-chain, cross-version, cross-fork).

## Status

**Kernel complete.** All four milestones implemented:

- **Milestone 1**: Π-types + Universes (dependent functions, universe hierarchy)
- **Milestone 2**: Σ-types (dependent pairs, projections, η-conversion)
- **Milestone 3**: Path types + J eliminator (identity types, transport, symmetry)
- **Milestone 4**: Univalence axiom + ua-β computation rule

Total: ~700 lines of trusted kernel code, ~115 tests.

Next steps:
- Parser + surface syntax
- Financial semantics layer (Token, Amount, bridge equivalences)
- Content hashing pipeline
- Compilation backend

## Build & Run

```bash
cabal build
cabal run pont
```

Expected output:
```
Pont type checker v0.1 — Milestone 1 (Π + Universe)

Checking: (λ A . λ x . x) : Π (A : U 0) . A → A
✓ Type check passed.

Checking: U 0 applied to U 0 (should fail)
✓ Correctly rejected: NotAFunction (VU 0)
```

## Architecture

All trusted code lives in `src/Kernel/`. The kernel is deliberately tiny (~500 lines for M1) — a bug here means the type checker accepts wrong proofs.

```
src/Kernel/
  Syntax.hs    -- Terms (de Bruijn indices)
  Value.hs     -- Values (NbE semantic domain)
  Eval.hs      -- Evaluation: Term → Val
  Quote.hs     -- Quotation: Val → Term
  Conv.hs      -- Conversion: Val ≡ Val?
  Check.hs     -- Bidirectional type checker
  Context.hs   -- Typing contexts
```

## Documentation

See [docs/KERNEL.md](docs/KERNEL.md) for the full kernel specification — the mathematical rules this type checker implements.

## License

MIT
