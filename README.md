# Pont

A minimal type checker based on Homotopy Type Theory (HoTT), designed for verified DeFi quantitative finance.

## What is this?

Pont is a type checker — it takes a program and a type specification, and answers yes or no. The core idea: use HoTT's **transport** and **univalence** to carry proofs across equivalent DeFi protocols (cross-chain, cross-version, cross-fork).

For example, if you prove a property about USDC on Ethereum and there is a verified bridge equivalence to Arbitrum, Pont can automatically transport that proof to the Arbitrum side. The forward function of the bridge is applied via the **ua-β** computation rule — no manual re-proving needed.

## Features

- **Dependent function types (Π)** — polymorphism, type-level computation
- **Dependent pair types (Σ)** — existential types, records, equivalences
- **Identity types (Path) + J eliminator** — equality proofs, transport, symmetry
- **Univalence axiom (ua + ua-β)** — equivalent types are equal; transport computes

The kernel is ~700 lines of Haskell. It uses Normalization by Evaluation (NbE) with de Bruijn indices, bidirectional type checking, and closure-based evaluation.

## Build & Run

```bash
cabal build
cabal run pont
cabal test
```

```
Pont type checker v0.4 — Complete HoTT kernel
  Π (dependent functions)
  Σ (dependent pairs)
  Path + J (identity types)
  ua + ua-β (univalence)

1. Identity function: (λ A x . x) : Π (A : U 0) . A → A
   ✓ Type check passed.
2. Reflexivity: refl (U 0) : Path (U 1) (U 0) (U 0)
   ✓ Inferred type: PathT (U 1) (U 0) (U 0)
3. ua-β: transport along ua(equiv) applies the forward function
   ✓ transport (ua id-equiv) (U 0) = U 0

Kernel complete. All 4 milestones implemented.
```

## Architecture

All trusted code lives in `src/Kernel/`. The kernel is deliberately tiny — a bug here means the type checker accepts wrong proofs. Keep it small, keep it auditable.

```
src/Kernel/
  Syntax.hs    -- Terms (de Bruijn indices)
  Value.hs     -- Values (NbE semantic domain, closures, evaluation)
  Eval.hs      -- Evaluation entry point
  Quote.hs     -- Quotation: Val → Term (read back normal forms)
  Conv.hs      -- Conversion checking (definitional equality)
  Check.hs     -- Bidirectional type checker (infer + check)
  Context.hs   -- Typing contexts
  Kernel.hs    -- Re-exports
```

115 tests validate the kernel: exhaustive hand-written tests for every typing rule, QuickCheck property tests (1000+ random inputs each), and cross-reference tests adapted from [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).

## Documentation

- [docs/KERNEL.md](docs/KERNEL.md) — Full kernel specification (the mathematical rules this type checker implements)
- [docs/VALIDATION.md](docs/VALIDATION.md) — Validation report (audit results, test coverage, known limitations)

## License

MIT
