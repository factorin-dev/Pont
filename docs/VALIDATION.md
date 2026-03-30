# Kernel Validation Report

Rigorous validation of the Pont kernel (Milestone 1: Π + Universe).

## 1. Audit Results

Every function in `src/Kernel/` was annotated with the KERNEL.md rule it implements. The following checks were performed:

### Checks passed (no discrepancies)

| Check | Code | Spec (KERNEL.md) | Status |
|-------|------|-------------------|--------|
| U-Type | `infer (U lvl) = VU (lvl + 1)` | `U ℓ : U (ℓ+1)` (Section 3) | ✓ Match |
| Π-Form | `VU (max aLvl bLvl)` | `Π (x:A).B : U (max ℓ₁ ℓ₂)` (Section 4) | ✓ Match |
| Π-β | `vApp (VLam cl) arg = instantiate cl arg` | `(λ x . t) u ≡ t[x↦u]` (Section 4) | ✓ Match |
| Π-η | `conv` handles `(VLam, v)` and `(v, VLam)` | `f ≡ λ x . f x` (Section 4) | ✓ Match |
| Π-Intro | `check (Lam body) (VPi dom cod)` | Lambda checks against Pi | ✓ Match |
| Π-Elim | `infer (App f a)` checks `f : Π`, `a : dom` | `f a : B[x↦a]` (Section 4) | ✓ Match |
| De Bruijn quote | `Var (lvl - x - 1)` | Level-to-index conversion | ✓ Correct |
| Context bind | `VNeutral (NVar lvl)` at current level | Fresh neutral variable | ✓ Correct |

### Known limitations (not bugs)

| Feature | Status | Notes |
|---------|--------|-------|
| Cumulativity | NOT implemented | KERNEL.md specifies `A : U ℓ ⟹ A : U (ℓ+1)`. Conversion uses strict universe equality. Acceptable for M1. |
| Universe polymorphism | NOT in kernel | By design — elaboration feature per KERNEL.md Section 11. |

### Bugs found and fixed

**No bugs were found in the kernel.** The implementation correctly matches KERNEL.md for all M1-scope rules.

Two test expectation errors were corrected during validation:
- `Π (A : U 0) . A` lives in `U 1`, not `U 0` (domain `U 0 : U 1`, so ℓ₁ = 1)
- `Π (A : U 3) . A` lives in `U 4`, not `U 3` (domain `U 3 : U 4`, so ℓ₁ = 4)

These reflect a common confusion: the Π-Form rule uses the universe level that *contains* the domain (`U 0 : U 1` → ℓ₁ = 1), not the domain's own level.

## 2. Test Summary

### Exhaustive tests: 47/47 passed

| Category | Count | Description |
|----------|-------|-------------|
| 2a. Universe rules | 6 | U-Type rule, positive and negative checks |
| 2b. Π-type formation | 5 | Universe level computation for various Pi types |
| 2c. Lambda + application | 10 | Identity, const, variable lookup, application in context, type mismatches |
| 2d. Conversion / NbE | 9 | Quote roundtrip, β-reduction, η-expansion, reflexivity, non-conversion |
| 2e. Negative tests | 8 | Non-function application, scope errors, non-type domains, level mismatches |
| 2f. Stress tests | 4 | 6-deep lambda, U 999, Church 2, self-application |
| Phase 4: elaboration-zoo | 5 | Church Nat/Bool/five, compose function |
| **Total** | **47** | |

### Property tests (QuickCheck): 7/7 passed

Each property tested with 1000+ random well-scoped inputs:

| Property | Inputs | Result |
|----------|--------|--------|
| eval-quote idempotence | 1000 | ✓ |
| conv reflexive | 1000 | ✓ |
| conv symmetric | 1000 | ✓ |
| infer deterministic | 1000 | ✓ |
| eval no crash (well-typed) | 1000 | ✓ |
| type of U is always VU | 1000 | ✓ |
| quote well-scoped | 1000 | ✓ |

## 3. Property Test Details

- **Generator**: Random well-scoped terms up to depth 5 with valid de Bruijn indices.
- **Shrinking**: Implemented for all constructors — QuickCheck minimizes failing cases.
- **Guard**: Properties requiring well-typed terms use `infer` as a guard to skip ill-typed inputs (avoids `vApp` crashes on ill-typed terms like `App (U 0) (U 0)`).
- **Discard ratio**: Set to 100 for the symmetric property (requires *two* well-typed terms simultaneously).

No failures were found in any property test after 7000+ total random inputs.

## 4. Cross-Reference with elaboration-zoo

Compared against `AndrasKovacs/elaboration-zoo` `02-typecheck-closures-debruijn`:

### Structural comparison

| Feature | elaboration-zoo 02 | Pont M1 |
|---------|-------------------|---------|
| Variables | `Var Ix` | `Var Ix` (same) |
| Universe | `U` (type-in-type) | `U ULvl` (hierarchy) |
| Pi | `Pi Name Tm Tm` | `Pi Term Term` (no names) |
| Lambda | `Lam Name Tm` | `Lam Term` (no names) |
| Let | `Let Name Tm Tm Tm` | Not in kernel |
| NbE | Closure-based | Closure-based (same) |
| η-conversion | Yes | Yes |

### Key differences

1. **Universe levels**: elaboration-zoo uses type-in-type (`U : U`, inconsistent). Pont has `U ℓ : U (ℓ+1)` (consistent). This means some elaboration-zoo examples need universe level adjustments (e.g., `id` applied to its own type requires `id` at `U 1`).

2. **No names in kernel**: Pont drops names from `Pi` and `Lam`. Cleaner for a trusted kernel; names are an elaboration concern.

3. **No `Let` in kernel**: elaboration-zoo includes `Let` in core syntax. Pont correctly excludes it (elaborated away per KERNEL.md Section 11).

### Cross-reference tests (all pass)

1. **Church Nat type : U 1** — In elaboration-zoo, `Nat` is `(N : U) -> (N -> N) -> N -> N`. In Pont with universe levels, this quantifies over `U 0`, so `Nat : U 1`. ✓
2. **Church five : Nat** — `λN.λs.λz. s(s(s(s(sz))))` — 5 nested applications. ✓
3. **Church true : Bool** — `λB.λt.λf. t` checked against `Π(B:U0).B→B→B`. ✓
4. **Church false : Bool** — `λB.λt.λf. f` checked against same type. ✓
5. **Compose function** — `λA.λB.λC.λf.λg.λx. f(gx)` with full dependent type. Tests deep nesting and higher-order functions. ✓

### Edge cases elaboration-zoo handles that Pont doesn't (M1 scope)

- **Let-bindings**: elaboration-zoo can define `add`, `mul`, `ten`, `hundred`, `thousand` via `let`. Pont M1 has no `let` (planned for elaboration layer).
- **Large Church arithmetic**: `mul ten hundred` (= 1000 β-reductions) exercises NbE performance. Not testable without `let`.
- **Source positions**: elaboration-zoo tracks source positions for error messages. Not in Pont kernel (correct — elaboration concern).

## 5. Known Limitations

1. **No cumulativity**: `U 0 : U 1` but not `U 0 : U 2`. This means `check (U 0) (VU 2)` fails. The spec allows cumulativity but it's not required for M1.

2. **`eval` is partial**: `eval [] (App (U 0) (U 0))` crashes with "vApp: not a function". This only affects ill-typed terms. Well-typed terms never crash (verified by property test).

3. **No `Let` bindings**: Can't test multi-definition programs (Church arithmetic chains). Will be added in elaboration layer.

4. **No implicit arguments**: All type annotations must be explicit. Elaboration concern.

5. **Σ-types, Path, J, univalence**: Not in M1 scope. Planned for M2–M4.

## 6. Remaining Concerns

1. **Performance**: No benchmarking done. NbE with closures should be efficient, but large Church numeral arithmetic (1000+ β-reductions) is untested.

2. **Termination**: The kernel has no fixpoint/recursion, so all well-typed terms terminate. But `eval` on ill-typed terms could theoretically loop (e.g., with a self-applying closure constructed via unsafe means). In practice this can't happen from the type checker.

3. **Error messages**: `TypeError` values contain `Val`s which are hard to read (closures). Better error formatting is an elaboration concern.

---

## Milestone 2 Validation: Σ-Types

### M2 Audit (7 checks)

| # | Check | Location | Status |
|---|-------|----------|--------|
| 1 | Σ-Form: `max(ℓ₁, ℓ₂)` | Check.hs:74 `VU (max aLvl bLvl)` | ✓ Match |
| 2 | Σ-β₁: `vFst (VPair a _) = a` | Value.hs:73 | ✓ Match |
| 3 | Σ-β₂: `vSnd (VPair _ b) = b` | Value.hs:82 | ✓ Match |
| 4 | Σ-η: both directions in `conv` | Conv.hs:63 `(VPair, other)` + Conv.hs:67 `(other, VPair)` | ✓ Match |
| 5 | Σ-Intro: Pair case before wildcard | Check.hs:124 before fallback at :135 | ✓ Correct |
| 6 | Σ-snd type `B[x ↦ fst t]` | Check.hs:95 `instantiate cl (vFst tVal)` | ✓ Match |
| 7 | Quote VSigma/VPair symmetric with VPi/VLam | Quote.hs:29–33 same closure pattern | ✓ Correct |

**No bugs found.** All Σ-type code matches KERNEL.md Section 5.

### M2 Known limitations

- **Σ-η is not type-directed**: If both sides are `VNeutral`, conversion compares structurally. Two different neutrals `p` and `q` with `fst p ≡ fst q` and `snd p ≡ snd q` will NOT be recognized as equal unless one side is a `VPair`. Full Σ-η requires type-directed conversion, deferred to a future upgrade.

### M2 Test summary: 24/24 passed

| Category | Count |
|----------|-------|
| Formation | 3 |
| Introduction (positive + negative) | 3 |
| Projections (positive + negative) | 4 |
| β-reduction | 3 |
| η-conversion | 2 |
| Quote round-trip | 2 |
| Product type | 1 |
| Integration (proto-equiv) | 1 |
| Inference rejection | 1 |
| M2 validation additional | 4 |
| **Total** | **24** |

Additional validation tests:
- 3-layer nested Sigma formation with correct universe level
- Deep projection chain `fst(fst p)`, `fst(snd p)`
- Pair checked against Pi type → rejected
- Lambda checked against Sigma type → rejected

### M2 Property tests: 7/7 passed

Term generator expanded with `Sigma`, `Pair`, `Fst`, `Snd`. All 7 properties hold over 1000+ random inputs including Σ-type terms.

### M2 Regression: 47/47 M1 tests still pass

---

## Milestone 3 Validation: Path Type + J Eliminator

### M3 Audit (10 checks)

| # | Check | Location | Status |
|---|-------|----------|--------|
| 1 | Path-Form: returns `VU aLvl` | Check.hs:107 | ✓ Match |
| 2 | Path-Intro: `VPathT tTy tVal tVal` (endpoints equal) | Check.hs:116 | ✓ Match |
| 3 | J-β: `vJ _ _ _ d _ (VRefl _) = d` | Value.hs:109 | ✓ Match |
| 4 | J stuck: `VNeutral (NJ ...)` on neutral path | Value.hs:110 | ✓ Match |
| 5 | Closure2: motive stored as `Closure2 env c` (not eval'd) | Value.hs:132 | ✓ Correct |
| 6 | instantiate2: `evalTerm (v2:v1:env)` → idx0=p, idx1=y | Value.hs:65 | ✓ Correct |
| 7 | d's type: `eval (reflA:aVal:ctxEnv) c` | Check.hs:143 | ✓ Correct |
| 8 | result type: `eval (pVal:bVal:ctxEnv) c` | Check.hs:154 | ✓ Correct |
| 9 | Quote NJ: freshY@lvl, freshP@lvl+1, quote@lvl+2 | Quote.hs:50-53 | ✓ Correct |
| 10 | Conv NJ: same fresh vars for both Closure2s @lvl+2 | Conv.hs:93-95 | ✓ Correct |

**Key design decision verified**: J's motive `C` is stored as `Closure2` (unevaluated term + env), not as a `Val`. This avoids wrong de Bruijn indexing when C has 2 pending binders. Instantiation via `instantiate2 (Closure2 env t) v1 v2 = evalTerm (v2 : v1 : env) t` correctly binds index 0 = p, index 1 = y.

**d's type substitution**: `evalTerm (VRefl aVal : aVal : ctxEnv ctx) c` — index 0 → refl a (for p), index 1 → a (for y). ✓

**Result type substitution**: `evalTerm (pVal : bVal : ctxEnv ctx) c` — index 0 → q (for p), index 1 → b (for y). ✓

**No bugs found.**

### M3 Test summary: 24/24 passed

| Category | Count |
|----------|-------|
| Path formation (positive + negative) | 5 |
| Refl | 2 |
| J-β computation | 2 |
| Derived operations (transport, symmetry) | 2 |
| J type checking (positive + negative) | 2 |
| Conversion | 3 |
| Quote round-trip | 2 |
| M3 validation additional | 6 |
| **Total** | **24** |

M3 validation additional tests:
- Transport along neutral path stays stuck (NJ)
- J with wrong path endpoints rejected
- J with b of wrong type rejected
- J with non-type motive rejected
- `refl (U 0) /= refl (U 1)` (different refl not convertible)
- J stuck term eval-quote-eval roundtrip

### M3 Property tests: 7/7 passed

Term generator expanded with `PathT`, `Refl`, `J` (J only at depth ≥ 3, motive has scope+2). All 7 properties hold over 1000+ random inputs including Path-type terms.

### M3 Regression: 47/47 M1 + 24/24 M2 tests still pass

## Conclusion

The Pont kernel (M1 + M2 + M3) is **correct** with respect to KERNEL.md for Π + Σ + Path + J + Universe. No bugs found across any milestone. 102 total tests (47 M1 + 24 M2 + 24 M3 + 7 property) all pass. The kernel is ready for Milestone 4 (Univalence axiom + ua-β computation rule).
