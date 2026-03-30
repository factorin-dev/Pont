# Kernel Specification

The minimal type-theoretic core. Everything else (financial semantics, elaboration, surface syntax) is built on top of this.

## 1. Raw Syntax

```
-- Terms and types live in the same syntactic category.
-- "Type" is just a term that happens to inhabit a universe.

t, u, A, B ::=
  | U ℓ                     -- Universe at level ℓ (ℓ = 0, 1, 2, ...)
  | x                       -- Variable
  | Π (x : A) . B           -- Dependent function type
  | λ (x : A) . t           -- Lambda abstraction
  | t u                     -- Application
  | Σ (x : A) . B           -- Dependent pair type
  | (t , u)                 -- Pair introduction
  | fst t                   -- First projection
  | snd t                   -- Second projection
  | Path A t u              -- Path type (identity type)
  | refl t                  -- Reflexivity: Path A t t
  | J A t C d u p           -- Path eliminator
  | ua e                    -- Univalence axiom (A ≃ B) → Path (U ℓ) A B
  | ua⁻¹ p                  -- Univalence inverse: Path (U ℓ) A B → (A ≃ B)

-- Contexts
Γ ::= · | Γ, x : A
```

That's it. No inductive types, no pattern matching, no recursion in the kernel. Those are elaborated away or added as a separate layer.

## 2. Judgments

Four judgments. The type checker implements exactly these.

```
Γ ⊢ t : A          -- t has type A in context Γ       (typing)
Γ ⊢ t ≡ u : A      -- t and u are definitionally equal  (conversion)
Γ ⊢ A type          -- A is a well-formed type          (type formation)
⊢ Γ ctx             -- Γ is a well-formed context       (context validity)
```

In practice, `Γ ⊢ A type` is sugar for `Γ ⊢ A : U ℓ` for some ℓ. The type checker is bidirectional: `infer` and `check` are the two modes.

## 3. Universes

```
                                   Γ ⊢ A : U ℓ
─────────────── (U-Type)      ─────────────────── (U-Cumul)
 Γ ⊢ U ℓ : U (ℓ+1)            Γ ⊢ A : U (ℓ+1)
```

Cumulativity: a type in `U ℓ` is also in `U (ℓ+1)`. This is essential — without it, even simple financial types would need manual universe annotations everywhere.

Implementation note: universe levels are natural numbers. Universe polymorphism is NOT in the kernel. If needed later, add as elaboration.

## 4. Π-Type (Dependent Functions)

```
  Γ ⊢ A : U ℓ₁    Γ, x : A ⊢ B : U ℓ₂
──────────────────────────────────────────── (Π-Form)
        Γ ⊢ Π (x : A) . B : U (max ℓ₁ ℓ₂)

      Γ, x : A ⊢ t : B
─────────────────────────────── (Π-Intro)
  Γ ⊢ λ (x : A) . t : Π (x : A) . B

  Γ ⊢ f : Π (x : A) . B    Γ ⊢ a : A
─────────────────────────────────────────── (Π-Elim)
           Γ ⊢ f a : B[x ↦ a]

────────────────────────────────────── (Π-β)
  (λ (x : A) . t) u  ≡  t[x ↦ u]

──────────────────────────────────────── (Π-η)
  f  ≡  λ (x : A) . f x    (if f : Π (x : A) . B)
```

Non-dependent function type is sugar: `A → B` means `Π (_ : A) . B`.

## 5. Σ-Type (Dependent Pairs)

```
  Γ ⊢ A : U ℓ₁    Γ, x : A ⊢ B : U ℓ₂
──────────────────────────────────────────── (Σ-Form)
        Γ ⊢ Σ (x : A) . B : U (max ℓ₁ ℓ₂)

  Γ ⊢ a : A    Γ ⊢ b : B[x ↦ a]
────────────────────────────────────── (Σ-Intro)
    Γ ⊢ (a , b) : Σ (x : A) . B

    Γ ⊢ t : Σ (x : A) . B
──────────────────────────────── (Σ-fst)     (Σ-snd)
  Γ ⊢ fst t : A                  Γ ⊢ snd t : B[x ↦ fst t]

──────────────────────── (Σ-β₁)      ──────────────────────── (Σ-β₂)
  fst (a , b)  ≡  a                    snd (a , b)  ≡  b

──────────────────────────────────────── (Σ-η)
  t  ≡  (fst t , snd t)    (if t : Σ (x : A) . B)
```

Product type is sugar: `A × B` means `Σ (_ : A) . B`.

## 6. Path Type (Identity)

This is where HoTT begins.

```
  Γ ⊢ A : U ℓ    Γ ⊢ a : A    Γ ⊢ b : A
──────────────────────────────────────────────── (Path-Form)
         Γ ⊢ Path A a b : U ℓ

         Γ ⊢ a : A
────────────────────────────── (Path-Intro)
  Γ ⊢ refl a : Path A a a
```

### J Eliminator (Path Elimination)

J is the fundamental elimination principle for paths. Everything else (transport, ap, path inversion, path composition) is derived from J.

```
  Γ ⊢ A : U ℓ
  Γ ⊢ a : A
  Γ, y : A, p : Path A a y ⊢ C : U ℓ'       -- motive
  Γ ⊢ d : C[y ↦ a, p ↦ refl a]              -- base case
  Γ ⊢ b : A
  Γ ⊢ q : Path A a b
──────────────────────────────────────── (J)
  Γ ⊢ J A a C d b q : C[y ↦ b, p ↦ q]

──────────────────────────────────────── (J-β)
  J A a C d a (refl a)  ≡  d
```

The computation rule (J-β) says: J on `refl` reduces to the base case `d`. This is the only computation rule for paths in Book HoTT. (In cubical type theory, paths compute more — that's a future upgrade.)

### Derived Operations

These are NOT in the kernel. They are defined in terms of J.

```
-- Transport: carry data along a path
transport : Π (P : A → U ℓ) . Path A a b → P a → P b
transport P p x = J A a (λ y _ . P y) x b p

-- ap: apply a function to a path
ap : Π (f : A → B) . Path A a b → Path B (f a) (f b)
ap f p = J A a (λ y _ . Path B (f a) (f y)) (refl (f a)) b p

-- Path symmetry
sym : Path A a b → Path A b a
sym p = J A a (λ y _ . Path A y a) (refl a) b p

-- Path transitivity
trans : Path A a b → Path A b c → Path A a c
trans p q = J A b (λ y _ . Path A a y) p c q
```

## 7. Equivalence

Equivalence is NOT a primitive. It's defined using Σ and Π.

```
-- A fiber of f over y
fiber : (A → B) → B → U ℓ
fiber f y = Σ (x : A) . Path B (f x) y

-- f is an equivalence if every fiber is contractible
isEquiv : (A → B) → U ℓ
isEquiv f = Π (y : B) . isContr (fiber f y)

-- where contractibility is:
isContr : U ℓ → U ℓ
isContr A = Σ (center : A) . Π (x : A) . Path A center x

-- The equivalence type
Equiv : U ℓ → U ℓ → U ℓ
A ≃ B = Σ (f : A → B) . isEquiv f
```

This is all definable from Π, Σ, Path. No new kernel primitives.

## 8. Univalence Axiom

Two new kernel primitives. This is the only place where we add something that doesn't compute.

```
  Γ ⊢ A : U ℓ    Γ ⊢ B : U ℓ    Γ ⊢ e : A ≃ B
──────────────────────────────────────────────────── (ua)
          Γ ⊢ ua e : Path (U ℓ) A B

  Γ ⊢ A : U ℓ    Γ ⊢ B : U ℓ    Γ ⊢ p : Path (U ℓ) A B
──────────────────────────────────────────────────────────── (ua⁻¹)
          Γ ⊢ ua⁻¹ p : A ≃ B
```

Computation rules:

```
────────────────────────────────────── (ua-β)
  transport (λ X . X) (ua e) a  ≡  (fst e) a

-- i.e., transporting along ua(e) computes to applying the forward function of e

────────────────────────── (ua-η)
  ua (ua⁻¹ p)  ≡  p

────────────────────────────── (ua-refl)
  ua (idEquiv A)  ≡  refl A

-- where idEquiv A : A ≃ A is the identity equivalence
```

**ua-β is the critical rule.** It says: if you have an equivalence `e : A ≃ B`, and you `transport` along the path `ua e`, the result is just applying the forward function of `e`. This is what makes univalence usable, not just a logical principle.

Without ua-β, `transport (ua e) x` would be stuck (no reduction). With it, the type checker can actually compute through transports along equivalences.

ua-η and ua-refl are optional for the prototype. ua-β is non-negotiable.

## 9. Definitional Equality (Conversion)

The type checker needs to decide when two terms are "the same." This is conversion checking.

```
-- Structural
──────────── (refl)       ────────────────────── (sym)       ─────────────────────────── (trans)
  t ≡ t                    t ≡ u → u ≡ t                     t ≡ u → u ≡ v → t ≡ v

-- Congruence (for each term constructor)
  t₁ ≡ t₂    u₁ ≡ u₂
────────────────────────── (cong-app)
    t₁ u₁ ≡ t₂ u₂

-- Computation (β-rules from sections 4-8)
-- These are the directed rewrite rules.

-- Conversion checking algorithm:
-- 1. Normalize both sides to weak head normal form (WHNF)
-- 2. Compare heads
-- 3. Recurse on subterms
-- 4. Handle η-expansion when heads differ
```

Implementation: Normalization by Evaluation (NbE). Terms are evaluated into a semantic domain (values), then read back into normal forms, then compared structurally.

## 10. NbE Sketch

```haskell
-- Semantic domain (values)
data Val
  = VU Level
  | VPi Val (Val -> Val)           -- closure
  | VLam Val (Val -> Val)          -- closure
  | VSigma Val (Val -> Val)        -- closure
  | VPair Val Val
  | VPath Val Val Val
  | VRefl Val
  | VNeutral Neutral               -- stuck computation

data Neutral
  = NVar Level                     -- de Bruijn level
  | NApp Neutral Val
  | NFst Neutral
  | NSnd Neutral
  | NJ Val Val Val Val Val Neutral -- J stuck on neutral path
  | NTransport Val Neutral Val     -- transport stuck on neutral path
  | NUa Neutral                    -- ua stuck on neutral equiv

-- Evaluation: Term → Val  (under an environment)
-- Quotation: Val → Term   (read back to normal form)
-- Conversion: Val → Val → Bool
```

The key invariant: evaluation applies all β-rules eagerly. A value is either a canonical form (VPi, VLam, VPair, VRefl, ...) or a neutral (computation stuck on a variable).

## 11. What Is NOT in the Kernel

Deliberately excluded. Each of these is a separate layer.

| Feature | Why excluded | Where it lives |
|---------|-------------|----------------|
| Inductive types | Complex, not needed for core demo | Layer 2: added as primitives or encoded |
| Pattern matching | Sugar over eliminators | Elaborator |
| Recursion / fixpoint | Needs termination checking | Layer 2 |
| Implicit arguments | Inference problem | Elaborator |
| Typed holes / sorry | Development aid | Elaborator |
| Tactics | Proof automation | Tactic engine (Layer 3) |
| Notation / syntax | Surface language | Parser + desugaring |
| Inductive families | Dependent pattern matching | Layer 2 |
| Higher inductive types | Need Path constructors | Layer 3 (post-cubical upgrade) |
| Universe polymorphism | Elaboration feature | Elaborator |
| Content hashing | Infrastructure | External pipeline |
| Compilation to executable | Backend | Separate compiler |

## 12. Implementation Skeleton (Haskell)

```
src/
  Kernel/
    Syntax.hs       -- Raw terms, de Bruijn indices     (~100 lines)
    Value.hs         -- Semantic domain for NbE          (~80 lines)
    Eval.hs          -- Evaluation (Term → Val)          (~150 lines)
    Quote.hs         -- Quotation (Val → Term)           (~100 lines)
    Conv.hs          -- Conversion checking (Val → Val → Bool)  (~100 lines)
    Check.hs         -- Bidirectional type checker        (~300 lines)
    Context.hs       -- Typing contexts                   (~50 lines)
    Axiom.hs         -- Univalence axiom + computation    (~80 lines)
    Kernel.hs        -- Re-exports                        (~10 lines)
  Main.hs            -- CLI entry point                   (~50 lines)
                                                    Total: ~1020 lines
```

This is the irreducible core. Everything in Kernel/ must be trusted — a bug here means the type checker accepts wrong proofs. Keep it small, keep it auditable.

## 13. Correctness Argument

Why should anyone trust this kernel?

1. **Metatheory is known.** Book HoTT (Martin-Löf type theory + univalence axiom) has well-studied metatheory. Consistency follows from the simplicial set model (Voevodsky) or the cubical set model (CCHM).

2. **Univalence as axiom is safe.** It doesn't compute fully (unlike cubical), but it doesn't introduce inconsistency. The ua-β rule gives enough computation to be useful. What we lose: some terms involving `ua` on non-canonical equivalences won't reduce. This is acceptable for the prototype.

3. **The kernel is small.** ~1000 lines of Haskell. Two people can audit it in a day. Compare: Lean 4 kernel is ~15,000 lines of C++, Coq kernel is ~10,000 lines of OCaml.

4. **No axiom beyond univalence.** No propositional resizing, no choice, no LEM. Every axiom is a potential unsoundness vector. We add exactly one, and it's the one we need.

## 14. The One Design Decision That Matters Most

**De Bruijn indices vs. names vs. locally nameless.**

- **De Bruijn indices**: no α-equivalence issues, conversion checking is structural. Harder to read, harder to debug. cubicaltt uses this.
- **Locally nameless**: bound variables are indices, free variables are names. pi-forall uses this.
- **Named with α-equivalence**: easiest to write, hardest to get right.

Recommendation: **de Bruijn indices internally, named terms in surface syntax.** The elaborator translates. The kernel never sees names.

## 15. What "Done" Looks Like

The kernel is done when this works:

```
-- Input (surface syntax, post-elaboration into kernel terms)

-- Two types
def A : U 0
def B : U 0

-- An equivalence between them
def e : Equiv A B

-- A property of A
def P : A → U 0
def proof_a : P a    -- for some a : A

-- Transport the property to B
def proof_b : P (transport (λ X . X) (ua e) a)
def proof_b = transport (λ x . P x) ... proof_a

-- Type checker says: OK
```

And this fails:

```
-- A function that is NOT an equivalence
def f : A → B          -- no inverse, no isEquiv proof
def bad : Path (U 0) A B
def bad = ua (f , ???)  -- can't construct isEquiv f

-- Type checker says: ERROR, hole ??? has type isEquiv f, unfilled
```

That's the kernel. Everything else is layers on top.
