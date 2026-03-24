# How a Lean 4 Kernel Typechecker Works

This document explains, from first principles, how to typecheck Lean 4 expressions.
It focuses on the **environment-based** (NbE / Krivine machine) approach used by our
three kernel implementations, contrasting it with the **substitution-based** approach
used by `lean4lean` and `nanoda_lib`.

### The Three Implementations

| Implementation | Language | File(s) | Notes |
|---|---|---|---|
| **Lean reference** | Lean 4 | `Ix/Kernel/*.lean` | Full-featured, ST-based thunks, pointer caching |
| **Rust reference** | Rust | `src/ix/kernel/*.rs` | Full-featured, RefCell thunks, extensive caching |
| **Aiur circuit** | Aiur (zkDSL) | `Ix/IxVM/Kernel.lean` | Minimal, no mutation, function-call caching |

The Lean and Rust implementations are feature-complete reference kernels. The Aiur
implementation is a work-in-progress circuit targeting zero-knowledge proof generation,
with significant constraints (no mutation, no dynamic indexing, no non-tail matches)
but with aggressive function-call caching that provides call-by-need semantics for free.

---

## Table of Contents

1. [The Big Picture](#1-the-big-picture)
2. [Expressions](#2-expressions)
3. [Universe Levels](#3-universe-levels)
4. [The Typing Judgments](#4-the-typing-judgments)
5. [Type Inference](#5-type-inference)
6. [Evaluation: From Expressions to Values](#6-evaluation-from-expressions-to-values)
7. [Weak Head Normal Form (WHNF)](#7-weak-head-normal-form-whnf)
8. [Definitional Equality](#8-definitional-equality)
9. [Declarations and the Environment](#9-declarations-and-the-environment)
10. [Inductive Types and Recursors](#10-inductive-types-and-recursors)
11. [Special Reductions](#11-special-reductions)
12. [Substitution-Based vs Environment-Based](#12-substitution-based-vs-environment-based)
13. [Caching and Performance](#13-caching-and-performance)
14. [Implementation Comparison](#14-implementation-comparison)
15. [Aiur TODOs and Disparities](#15-aiur-todos-and-disparities)

---

## 1. The Big Picture

A **kernel** (or **type checker**) is the trusted core of a proof assistant. Its job is
to verify that every definition and theorem in a Lean file is well-typed. If the kernel
accepts it, you can trust it — no matter how complicated the tactics or elaboration that
produced it.

The kernel does NOT:
- Parse syntax or run tactics
- Do elaboration, unification, or typeclass resolution
- Handle user-facing error messages

The kernel DOES:
- **Infer types** of expressions
- **Check definitional equality** of two expressions (are they "the same" by computation?)
- **Validate declarations** (definitions, theorems, inductives) one at a time

The core loop is: for each new declaration, check that its type is well-formed and (for
definitions/theorems) that its value has the claimed type. "Has the claimed type" means
the inferred type and the declared type are **definitionally equal**.

### The Three Core Operations

Everything reduces to three mutually recursive operations:

```
infer(e)        : Expr → Type        -- what is the type of e?
whnf(e)         : Expr → Expr        -- reduce e to weak head normal form
isDefEq(a, b)   : Expr × Expr → Bool -- are a and b definitionally equal?
```

These call each other. `infer` calls `isDefEq` to check that an argument's type matches
a function's domain. `isDefEq` calls `whnf` to peel away computation. `whnf` may call
`infer` to determine if something is a proposition (for proof irrelevance).

**Where to find these:**

| Operation | Lean | Rust | Aiur |
|-----------|------|------|------|
| `eval` | `Infer.lean` `eval` | `eval.rs` `eval` | `Kernel.lean` `k_eval` |
| `whnf` | `Infer.lean` `whnfVal` | `whnf.rs` `whnf_val` | `Kernel.lean` `k_whnf` |
| `isDefEq` | `Infer.lean` `isDefEq` | `def_eq.rs` `is_def_eq` | `Kernel.lean` `k_is_def_eq` |
| `infer` | `Infer.lean` `infer` | `infer.rs` `infer` | `Kernel.lean` `k_infer` |
| `check` | `Infer.lean` `check` | `infer.rs` `check` | `Kernel.lean` `k_check` |

---

## 2. Expressions

Lean's expression language is a dependently-typed lambda calculus. Here are the
constructors:

| Constructor | Notation | Meaning |
|-------------|----------|---------|
| `bvar i` | `#i` | Bound variable (de Bruijn index `i`) |
| `sort u` | `Sort u` | A universe / type of types |
| `const n [u₁..uₖ]` | `@List.map.{u,v}` | Named constant with universe arguments |
| `app f a` | `f a` | Function application |
| `lam x : A => b` | `fun x : A => b` | Lambda abstraction |
| `forallE x : A => B` | `(x : A) → B` | Dependent function type (Pi type) |
| `letE x : A := v; b` | `let x : A := v; b` | Let binding |
| `lit l` | `42`, `"hi"` | Nat or String literal |
| `proj T i s` | `s.i` | Structure field projection |

In the Aiur kernel, expressions are the `KExpr` enum (defined in `KernelTypes.lean`).
Binder info and names are stripped since the kernel operates on anonymous
(content-addressed) constants.

### De Bruijn Indices

Bound variables are nameless — instead of `fun x => fun y => x`, we write
`fun _ => fun _ => #1`. The index counts how many binders you cross to reach the
binding site: `#0` is the innermost binder, `#1` the next one out, etc.

```
fun (A : Type) => fun (x : A) => x
=  lam (Sort 1) (lam #0 #0)
       ^^^^^^^^       ^^  ^^
       binds #1       |   refers to x (0 binders crossed)
                      refers to A (1 binder crossed)
```

---

## 3. Universe Levels

Every type lives in a universe. `Nat : Type 0`, `Type 0 : Type 1`, `Type 1 : Type 2`,
and so on. Lean represents these symbolically:

| Level | Meaning |
|-------|---------|
| `zero` | 0 (also called `Prop` when used as `Sort 0`) |
| `succ u` | u + 1 |
| `max u v` | max(u, v) |
| `imax u v` | if v = 0 then 0 else max(u, v) |
| `param i` | Universe parameter (polymorphism) |

### Why `imax`?

`imax` is the key to **impredicativity** of `Prop`. Consider the type of a function
`(x : A) → B`. Its universe is `imax uA uB` where `A : Sort uA` and `B : Sort uB`.

If `B : Prop` (i.e., `uB = 0`), then `imax uA 0 = 0`, so the function type is also
in `Prop` — regardless of how large `A` is. This is what makes propositions
"impredicative": you can quantify over arbitrarily large types and still land in `Prop`.

If `B` is NOT in `Prop`, then `imax uA uB = max uA uB`, the standard predicative rule.

### Level Comparison

Two levels are equal if they evaluate to the same natural number under every assignment
of parameters. The Aiur kernel uses `level_equal(a, b) = level_leq(a, b) ∧ level_leq(b, a)`,
where `level_leq` is sound and complete.

#### Semantics

A *level assignment* σ maps parameter indices to natural numbers. Every level `l`
evaluates to a natural number ⟦l⟧σ:

- ⟦Zero⟧σ = 0
- ⟦Param(i)⟧σ = σ(i)
- ⟦Succ(l)⟧σ = 1 + ⟦l⟧σ
- ⟦Max(a, b)⟧σ = max(⟦a⟧σ, ⟦b⟧σ)
- ⟦IMax(a, b)⟧σ = if ⟦b⟧σ = 0 then 0 else max(⟦a⟧σ, ⟦b⟧σ)

We write `a ≤ b` to mean ⟦a⟧σ ≤ ⟦b⟧σ for all σ, and `a = b` to mean `a ≤ b ∧ b ≤ a`.
Let σ₀ denote the assignment mapping every parameter to 0.

#### Reduced levels

The functions `level_max` and `level_imax` produce levels in *reduced form*.
The key invariant:

> **(R)** If `IMax(a, b)` appears in a reduced level, then `level_is_not_zero(b) = 0`.

This holds because `level_imax(a, b)` returns `Zero` when `b = Zero`, returns
`level_max(a, b)` when `b = Succ(_)` or `level_is_not_zero(b) = 1`, and only
produces an `IMax` node otherwise.

All levels entering `level_leq` are reduced: the initial levels come from
`level_inst_params` / `level_reduce` (which build via `level_max`/`level_imax`),
and the case-split substitutions use `level_subst_reduce` (which also builds via
`level_max`/`level_imax`).

#### Monotonicity

**Lemma (Monotonicity).** All level expressions are monotone in their parameters:
if σ₁(i) ≤ σ₂(i) for all i, then ⟦l⟧σ₁ ≤ ⟦l⟧σ₂.

*Proof.* By induction on `l`. The Zero, Param, Succ, and Max cases are immediate.
For IMax(a, b): if ⟦b⟧σ₁ = 0, then ⟦IMax(a,b)⟧σ₁ = 0 ≤ ⟦IMax(a,b)⟧σ₂.
If ⟦b⟧σ₁ > 0, then by IH ⟦b⟧σ₂ ≥ ⟦b⟧σ₁ > 0, so
⟦IMax(a,b)⟧σ₁ = max(⟦a⟧σ₁, ⟦b⟧σ₁) ≤ max(⟦a⟧σ₂, ⟦b⟧σ₂) = ⟦IMax(a,b)⟧σ₂. ∎

#### Zero witness

**Lemma (Zero Witness).** `level_is_not_zero(l) = 0` if and only if ⟦l⟧₀ = 0
(where σ₀(i) = 0 for all i). Equivalently, `level_is_not_zero(l) = 1` if and only
if ⟦l⟧σ ≥ 1 for all σ.

*Proof.* (⇒) By induction: Zero and Param evaluate to 0 under σ₀. Succ returns 1,
so this case is excluded. Max(a,b) with both children returning 0 gives
max(⟦a⟧₀, ⟦b⟧₀) = max(0, 0) = 0. IMax(a,b) with `level_is_not_zero(b) = 0`
gives ⟦b⟧₀ = 0 by IH, so ⟦IMax(a,b)⟧₀ = 0.

(⇐) If `level_is_not_zero(l) = 1`, by induction: Succ(x) ≥ 1 always.
Max(a,b) with at least one child having `level_is_not_zero = 1`: that child is ≥ 1
for all σ (IH), so max ≥ 1. IMax(a,b) with `level_is_not_zero(b) = 1`:
⟦b⟧σ ≥ 1 for all σ (IH), so IMax = max(a,b) ≥ b ≥ 1. ∎

**Corollary.** For a reduced `IMax(a, b)` (invariant R), ⟦IMax(a, b)⟧₀ = 0.

#### Case-split soundness

The case-split technique substitutes a parameter `p` with `Zero` and `Succ(Param(p))`.
This is sound and complete for universal quantification over σ(p):

- Every σ has σ(p) = 0 or σ(p) ≥ 1.
- When σ(p) = 0: captured by the `p → Zero` substitution.
- When σ(p) ≥ 1: write σ(p) = 1 + σ'(p). Then ⟦l[p ↦ Succ(Param(p))]⟧σ' = ⟦l⟧σ,
  so the `p → Succ(Param(p))` substitution captures all σ(p) ≥ 1.

Hence `∀σ. ⟦a⟧σ ≤ ⟦b⟧σ` iff both `∀σ. ⟦a[p↦0]⟧σ ≤ ⟦b[p↦0]⟧σ` and
`∀σ. ⟦a[p↦S(p)]⟧σ ≤ ⟦b[p↦S(p)]⟧σ`.

#### Soundness and completeness of `level_leq`

**Theorem.** For reduced levels `a` and `b`, `level_leq(a, b) = 1` if and only if
`a ≤ b` (i.e., ⟦a⟧σ ≤ ⟦b⟧σ for all σ).

*Proof.* By case analysis on `level_leq`. In each case we show the return value is 1
iff the inequality holds universally.

**Case `a = Zero`:** Returns 1. Correct: 0 ≤ ⟦b⟧σ for all σ.

**Case `a = Max(a1, a2)`:** Returns `level_leq(a1, b) * level_leq(a2, b)`.
max(⟦a1⟧σ, ⟦a2⟧σ) ≤ ⟦b⟧σ iff ⟦a1⟧σ ≤ ⟦b⟧σ and ⟦a2⟧σ ≤ ⟦b⟧σ. ∎

**Case `a = Succ(Max(x, y))`:** Distributes to `level_leq(Succ(x), b) * level_leq(Succ(y), b)`.
Correct: 1 + max(⟦x⟧σ, ⟦y⟧σ) = max(1 + ⟦x⟧σ, 1 + ⟦y⟧σ), reducing to the Max case. ∎

**Case `a = Succ(a1)`, `a1` not Max, `b = Succ(b1)`:** Returns `level_leq(a1, b1)`.
1 + ⟦a1⟧σ ≤ 1 + ⟦b1⟧σ iff ⟦a1⟧σ ≤ ⟦b1⟧σ. ∎

**Case `a = Succ(a1)`, `a1` not Max, `b = Zero` or `Param(j)` or `IMax(_, _)`:**
Returns 0. Correct by Zero Witness: ⟦b⟧₀ = 0 (b = Zero is immediate; Param(j) gives
σ₀(j) = 0; IMax is 0 under σ₀ by the Corollary), but ⟦Succ(a1)⟧₀ ≥ 1. ∎

**Case `a = Succ(a1)`, `a1` not Max, `b = Max(b1, b2)`:** First tries
`level_leq(a, b1)` and `level_leq(a, b2)`. If either returns 1, the result is sound
(a ≤ bi implies a ≤ max(b1, b2)). If both return 0 and `b` has no params, returns 0
(b is a concrete number; the try-each-branch is complete for concrete values). If both
return 0 and `b` has params, case-splits on a param `p` from `b`. This is sound and
complete by Case-Split Soundness above — after substitution, `level_subst_reduce`
re-reduces the result, resolving any IMax whose conditioning variable was `p`.
The recursion terminates because each case-split strictly reduces the number of free
parameters. After all IMax nodes are resolved (finitely many case-splits), the levels
are tropical polynomials (max-plus over Succ chains and Params), for which the
try-each-branch heuristic IS complete:

> *Tropical completeness:* For tropical polynomials (no IMax), `Succ(a1) ≤ Max(b1, b2)`
> for all σ implies `Succ(a1) ≤ b1` for all σ or `Succ(a1) ≤ b2` for all σ.
>
> *Proof sketch:* Since ⟦Succ(a1)⟧₀ ≥ 1, we have max(⟦b1⟧₀, ⟦b2⟧₀) ≥ 1, so
> WLOG ⟦b1⟧₀ ≥ 1, hence `level_is_not_zero(b1) = 1` (Zero Witness). Since b1 is a
> tropical polynomial with `level_is_not_zero = 1`, it is Succ or Max (not IMax, not
> Param, not Zero). Being a tropical polynomial, b1 is of the form max(σ(pᵢ) + cᵢ)
> with all cᵢ ≥ 0. For any Param(q) appearing in a with Succ-offset k: ⟦a⟧σ grows as
> σ(q) + k, and for a ≤ Max(b1, b2) to hold universally as σ(q) → ∞, some branch must
> contain a term σ(q) + c with c ≥ k. Since b1 is tropical and always ≥ 1 (no IMax
> zeroing), all its terms are unconditional — any term σ(q) + c in b1 contributes
> b1 ≥ σ(q) + c for ALL σ. So if b1 contains the dominating terms for a, then a ≤ b1. ∎

**Case `a = Param(i)`, `b = Param(j)`:** Returns `eq_zero(i - j)`, i.e., 1 iff i = j.
Correct: σ(i) ≤ σ(j) for all σ iff i = j (otherwise set σ(i) > σ(j)). ∎

**Case `a = Param(i)`, `b = Succ(b1)`:** Returns `level_leq(Param(i), b1)`,
i.e., reduces `σ(i) ≤ 1 + ⟦b1⟧σ` to `σ(i) ≤ ⟦b1⟧σ`.

*Soundness:* If σ(i) ≤ ⟦b1⟧σ then σ(i) ≤ 1 + ⟦b1⟧σ. ∎

*Completeness:* Suppose σ(i) ≤ 1 + ⟦b1⟧σ for all σ. Fix all parameters except i and
define f(n) = ⟦b1⟧(σ[i ↦ n]). By monotonicity, f is non-decreasing. The premise gives
n ≤ 1 + f(n) for all n ≥ 0. We need n ≤ f(n) for all n.

For n > 0: every IMax in b1 whose second argument depends on Param(i) is resolved
(since n > 0 makes any monotone expression involving Param(i) positive, and
`level_subst_reduce` normalizes away such IMax nodes). So for n > 0, f(n) includes
an unconditional term n + c for some c ≥ 0 (from each Param(i) path in b1).
If such a term exists, f(n) ≥ n + c ≥ n. If no such term exists, f is eventually
constant, and n ≤ 1 + C fails for large n — contradicting the premise.

For n = 0: f(0) ≥ 0 trivially. ∎

**Case `a = Param(i)`, `b = Max(b1, b2)`:** Tries each branch. Sound (a ≤ bi
implies a ≤ max(b1, b2)). Complete: at σ₀, σ₀(i) = 0 ≤ max(⟦b1⟧₀, ⟦b2⟧₀),
which holds trivially — so the argument is subtler. Since σ(i) is unbounded, at least
one bk must contain Param(i) + c (c ≥ 0) unconditionally (not zeroed by IMax). That
branch satisfies bk ≥ σ(i), so Param(i) ≤ bk. If the only Param(i) terms are inside
IMax nodes, then at σ₀ (where IMax zeroes them), b = max(const₁, const₂), and
σ(i) ≤ max(const₁, const₂) fails for large σ(i) — contradicting the premise. ∎

**Case `a = Param(i)`, `b = IMax(b1, b2)`:** Case-splits on a param from b2.
Sound and complete by Case-Split Soundness. ∎

**Case `a = Param(i)`, `b = Zero`:** Returns 0. Correct: σ(i) ≤ 0 fails for σ(i) = 1. ∎

**Case `a = IMax(a1, a2)`, `level_is_not_zero(a2) = 1`:** Treats as Max(a1, a2):
returns `level_leq(a1, b) * level_leq(a2, b)`. Correct: a2 ≥ 1 for all σ (Zero Witness),
so IMax(a1, a2) = max(a1, a2). ∎

**Case `a = IMax(a1, a2)`, `level_is_not_zero(a2) = 0`:** Case-splits on a param
from a2. Sound and complete by Case-Split Soundness. Note: `level_is_not_zero(a2) = 0`
and `a` is reduced, so a2 has at least one param (otherwise a2 is Zero and
`level_imax` would have reduced the IMax away). ∎

#### Termination

Each case either reduces the structural size of the levels (Succ peeling, Max
distribution) or reduces the number of free parameters (case-split substitution).
Since both measures are bounded, the recursion terminates.

### Level Instantiation

When a polymorphic constant `C.{u, v}` is used at specific levels `[l₁, l₂]`, all
`Param(i)` in the type are replaced with the corresponding level. This happens in all
three implementations via an `inst_levels` / `expr_inst_levels` function that walks the
expression tree. The Aiur kernel simultaneously reduces the substituted levels to normal
form (`level_max`, `level_imax`).

---

## 4. The Typing Judgments

The kernel implements two core judgments:

**Type inference**: Γ ⊢ e : T
> "In context Γ, expression e has type T."

**Definitional equality**: Γ ⊢ a ≡ b
> "In context Γ, expressions a and b are computationally equal."

These are NOT the same as propositional equality (`a = b` as a Lean `Prop`).
Definitional equality is a judgment the kernel makes silently — it's the equality
that lets you write `2 + 2` where `4` is expected without an explicit proof.

### What Generates Definitional Equality?

| Rule | Example |
|------|---------|
| **β-reduction** | `(fun x => x + 1) 3 ≡ 3 + 1` |
| **δ-reduction** | `Nat.succ 0 ≡ 1` (unfolding a definition) |
| **ζ-reduction** | `let x := 5; x + 1 ≡ 5 + 1` |
| **ι-reduction** | Pattern matching on a constructor |
| **η-expansion** | `f ≡ fun x => f x` (for functions) |
| **Proof irrelevance** | `p ≡ q` whenever `p q : P` and `P : Prop` |
| **Structure η** | `s ≡ ⟨s.1, s.2, ...⟩` for structures |
| **Nat/String literals** | `2 ≡ Nat.succ (Nat.succ Nat.zero)` |

---

## 5. Type Inference

Given an expression, compute its type. Each constructor has a straightforward rule:

### Sort
```
infer(Sort u) = Sort (succ u)
```
The type of `Type u` is `Type (u+1)`.

### Bound Variable
```
infer(#i) = Γ[i]     -- look up the i-th binding in context
```
In the Lean/Rust kernels, the context is an array indexed by de Bruijn level
(`depth - 1 - i`). In Aiur, the `types` list is indexed directly by de Bruijn index
(front = most recent binder).

### Constant
```
infer(const c [u₁..uₖ]) = instantiate(env[c].type, [u₁..uₖ])
```
Look up the constant in the global environment, substitute its universe parameters.
The Lean/Rust kernels also validate universe arity and safety (unsafe/partial) here.
The Aiur kernel asserts level count matches but doesn't check safety.

### Application
```
infer(f a) where:
  infer(f) = (x : A) → B      -- must be a Pi type (after WHNF)
  infer(a) = A'
  isDefEq(A, A')               -- argument type must match domain
  result = B[x := a]            -- substitute a into the codomain
```
This is the critical step where `isDefEq` gets called during inference. In the
environment-based approach, "B[x := a]" is implemented as `eval(body, env ++ [a_val])`
— an O(1) environment push rather than a tree walk.

### Lambda
```
infer(fun (x : A) => b) where:
  infer(A) must be a Sort        -- domain must be a type
  extend context with (x : A)
  infer(b) = B                   -- infer body type in extended context
  result = (x : A) → B          -- Pi type
```
The Lean/Rust kernels extend the context via `with_binder(dom, |tc| tc.infer(body))`.
The Aiur kernel passes extended `types` and `env` lists explicitly, introducing an
`FVar(depth)` for the new variable.

### Pi / ForallE
```
infer((x : A) → B) where:
  infer(A) = Sort u              -- domain must be a type
  extend context with (x : A)
  infer(B) = Sort v              -- codomain must be a type
  result = Sort (imax u v)       -- note: imax, not max
```

### Let
```
infer(let x : A := v; b) where:
  infer(v) = A'
  isDefEq(A, A')                 -- check value has declared type
  result = infer(b[x := v])      -- substitute and infer body
```
In the Lean/Rust kernels, let bindings use `with_let_binder` which stores the value so
it can be used during delta-like reduction. In the Aiur kernel, the value is eagerly
pushed into the environment.

### Projection
```
infer(proj T i s) where:
  infer(s) = T args...           -- s must have the structure type
  result = the type of the i-th field, with params instantiated
```
All three implementations share the same strategy: look up the inductive's single
constructor, instantiate its type with the universe levels, walk past the parameters
(substituting from the inductive's spine), then walk past preceding fields
(substituting `Proj(T, j, s)` for field `j < i`), and extract the domain of the
resulting Pi type.

### Literal
```
infer(42)   = Nat
infer("hi") = String
```

### Bidirectional Checking

All three implementations use **bidirectional type checking** (`check`): when checking
a lambda against an expected Pi type, the expected codomain is pushed through the
lambda body, avoiding an expensive `infer` + `isDefEq`. This is implemented as
`k_check` in Aiur, `check` in Lean/Rust.

---

## 6. Evaluation: From Expressions to Values

This is where the environment-based and substitution-based approaches **diverge
fundamentally**.

### The Substitution-Based Approach (lean4lean, nanoda_lib)

In a substitution-based kernel, beta reduction physically rewrites the expression:

```
(fun x => body) arg   →   body[x := arg]
```

The `body[x := arg]` operation walks the entire body AST, replacing every occurrence of
`x` (i.e., `#0`) with `arg`, and adjusting de Bruijn indices as it goes. This is
O(|body|) per beta step.

### The Environment-Based Approach (Our Kernels)

Instead of rewriting expressions, we **evaluate** them into a **semantic domain** of
**values** (`Val`). The key idea is **closures**: a lambda doesn't substitute — it
captures its environment and waits.

#### The Value Type

Values are the "evaluated form" of expressions:

```
Val =
  | lam(dom, body_expr, env)          -- closure: body is still an Expr
  | pi(dom, body_expr, env)           -- pi-closure
  | sort(level)                       -- universe
  | neutral(head, spine)              -- stuck term (fvar or const)
  | ctor(name, levels, spine)         -- constructor with args
  | lit(literal)                      -- nat/string literal
  | proj(type, idx, struct, spine)    -- stuck projection
  | thunk(expr, env)                  -- [Aiur only] unevaluated closure
```

The Aiur kernel adds a `Thunk` variant to `KVal` since it cannot use mutable references
for call-by-need. Instead, Aiur's function-call caching ensures that
`k_eval(expr, env, top)` called with the same arguments returns the cached result.

A **closure** is `(body_expr, env)` where `env` is an array/list of `Val`. To apply a
closure to an argument `v`, you evaluate `body_expr` in `env ++ [v]`. No substitution
walk — just a push. **O(1) beta reduction.**

A **neutral** is a term stuck on something that can't be reduced further — either a
free variable (`fvar`) or an unresolved constant. Neutrals accumulate a **spine** of
arguments that couldn't be applied.

#### The `eval` Function

`eval` takes an `Expr` and an environment (array of `Val`) and produces a `Val`:

```
eval(#i, env) =
  if i < |env| then env[|env| - 1 - i]   -- look up in environment
  else mkFVar(...)                         -- free variable

eval(Sort u, env) = sort(u)

eval(const c [us], env) =
  if c is a constructor then ctor(c, us, [])
  else neutral(const(c, us), [])            -- NO eager unfolding

eval(app f a, env) =
  let vf = eval(f, env)
  match vf with
  | lam(_, body, lam_env) =>
      let va = eval(a, env)                -- eager beta
      eval(body, lam_env ++ [va])          -- O(1) beta!
  | _ =>
      let thunk = lazy(a, env)             -- don't evaluate yet
      apply_val_thunk(vf, thunk)

eval(lam A b, env) =
  let dom = eval(A, env)
  lam(dom, b, env)                         -- capture closure

eval(forallE A B, env) =
  let dom = eval(A, env)
  pi(dom, B, env)                          -- capture closure

eval(let A v b, env) =
  let val = eval(v, env)
  eval(b, env ++ [val])                    -- eager zeta-reduction

eval(proj T i s, env) =
  let sv = eval(s, env)
  if sv is ctor then extract field i (and force it)
  else create stuck proj
```

**Key design choice**: `eval` does NOT unfold definitions. A `const` always evaluates
to either a `ctor` (for constructors) or a `neutral(const(...), [])`. Definition
unfolding is deferred to WHNF. This is the "lazy" approach — constants are only
unfolded when the kernel actually needs to look inside them.

The **eager beta optimization** is important: when the head of an application is already
a lambda, we skip thunk creation and evaluate the argument directly. The Rust kernel
collects the full App spine and checks at each step; the Aiur kernel uses a tail match
on the evaluated function:

```
-- Aiur: k_eval App case
KExpr.App(&f, &a) =>
  let vf = k_eval(f, env, top);
  match vf {
    KVal.Lam(_, &body, &lam_env) =>
      let va = k_eval(a, env, top);           -- eager: skip thunk
      let env2 = KValEnv.Cons(store(va), store(lam_env));
      k_eval(body, env2, top),
    _ =>
      let thunk = KVal.Thunk(store(a), store(env));
      k_apply(vf, thunk, top),                -- lazy: store thunk
  }
```

#### De Bruijn Levels vs Indices

In the environment-based approach, **free variables** use de Bruijn **levels** (counting
from the bottom of the context), not indices (counting from the top). This is crucial:

- **Index** `#i` = "the variable `i` binders above me" — changes when you go under a binder
- **Level** `fvar(k)` = "the k-th variable ever introduced" — stable, never changes

When we push a new binding into the context at depth `d`, we create `fvar(d)`. Since
levels count up from the bottom, they never need adjustment when we enter new binders.
This eliminates the shifting/lifting operations that plague substitution-based approaches.

#### Thunk Representation

| Impl | Thunk type | Memoization |
|------|-----------|-------------|
| Lean | `ThunkId` (Nat index into `ST.Ref` table) | Explicit: mutates ref on force |
| Rust | `Rc<RefCell<ThunkEntry>>` | Explicit: mutates cell on force |
| Aiur | `KVal.Thunk(&KExpr, &KValEnv)` | Implicit: Aiur caches `k_eval(e, env, top)` calls |

In the Lean kernel, thunks are managed via `TypecheckM` which maintains an array of
`ST.Ref (Option (Val m))`. In the Rust kernel, `ThunkEntry` is either
`Unevaluated { expr, env }` or `Evaluated(Val)`. In Aiur, there is no mutation, but
the runtime's aggressive function-call caching means `k_force(thunk, top)` =
`k_eval(expr, env, top)` is automatically memoized.

---

## 7. Weak Head Normal Form (WHNF)

**Weak head normal form** means: reduce enough to see the outermost constructor.
We don't reduce under binders or inside arguments — just enough to know what shape
the expression has.

Examples:
```
whnf(Nat.add 2 3)     = 5                      -- δ + primitive
whnf(fun x => x + 1)  = fun x => x + 1         -- already WHNF (lambda)
whnf(let x := 5; x)   = 5                      -- ζ-reduction (done in eval)
whnf(Nat.rec m z s (Nat.succ n)) = s n (...)    -- ι-reduction
```

### The WHNF Loop

All three implementations structure WHNF as a loop:

1. **Force thunks** (Aiur: `KVal.Thunk` → `k_eval` → continue)
2. **Projection reduction**: if `proj(T, i, struct, spine)` and `struct` WHNFs to a
   constructor, extract field `i`, apply spine, and continue
3. **Iota reduction**: if `const(rec, spine)` and the major premise WHNFs to a
   constructor, fire the matching recursor rule
4. **Delta reduction**: if `const(defn, spine)` and the definition is unfoldable,
   evaluate its body, apply the spine, and continue
5. **Quotient reduction**: `Quot.lift f h (Quot.mk r a) → f a`
6. **Nat primitives** (Lean/Rust only): `Nat.add (lit 3) (lit 4) → lit 7`
7. Otherwise: return (already in WHNF)

The Lean/Rust kernels separate structural WHNF (`whnfCoreVal`/`whnf_core`) from delta
unfolding (`deltaStepVal`/`delta_step`), with the outer loop (`whnfVal`/`whnf_val`)
alternating between them. The Aiur kernel combines everything into a single `k_whnf`
function. The Lean/Rust kernels also cache WHNF results by pointer identity.

### Delta Reduction (Unfolding Definitions)

When we see a constant like `Nat.add`, we can **unfold** it to its definition. The
definition body is an `Expr`; we `eval` it (substituting universe parameters) and then
apply the accumulated spine of arguments.

Not all constants should be eagerly unfolded. Lean assigns **reducibility hints**:
- **Abbreviation**: Always unfold (e.g., type aliases)
- **Regular(n)**: Unfold with priority `n` (higher = unfold later)
- **Opaque**: Never unfold (axioms, opaque defs)

The Lean/Rust kernels use hints to decide **which side to unfold first** during lazy
delta in `isDefEq` (see §8). During WHNF, they unfold any non-opaque definition.
The Aiur kernel does the same in `k_whnf`.

### Iota Reduction (Recursor on Constructor)

When a recursor meets a constructor it can pattern-match:

```
Nat.rec motive zero_case succ_case (Nat.succ n)
  →  succ_case n (Nat.rec motive zero_case succ_case n)
```

The kernel detects that the **major premise** (the thing being matched on) is a
constructor, picks the corresponding **minor premise** (branch), and applies it to the
constructor's fields and (for recursive args) the recursive result.

The recursor's spine is laid out as:
```
[params..., motives..., minors..., indices..., major]
```

The major premise index is `nparams + nmotives + nminors + nindices`. After matching,
the result is `rhs_val` applied to `[params, motives, minors, ctor_fields, remaining]`.

All three implementations share this structure in `try_iota` / `tryIotaReduction`.
The Aiur kernel additionally handles:
- **Nat literals**: `Lit(0)` matches the zero rule; `Lit(n+1)` matches the succ rule
  with `Lit(n)` as the field
- **K-reduction**: for proof-irrelevant inductives (k_flag set), the minor premise is
  returned directly without inspecting the major premise's constructor

### Zeta Reduction (Let Bindings)

Let bindings are reduced eagerly during `eval` — the value is evaluated and pushed into
the environment. There is no `Val.let` constructor. This is simpler and avoids the need
to handle let-bindings in WHNF or definitional equality.

---

## 8. Definitional Equality

The most complex part of the kernel. Given two values, determine if they are
definitionally equal.

### The Algorithm (Layered)

Definitional equality uses a layered approach, trying cheap checks first:

```
isDefEq(a, b) =
  -- Layer 0: Trivial
  if a and b are pointer-equal → true       [Lean/Rust only]
  if cached as equal → true                 [Lean/Rust only]

  -- Layer 1: Quick syntactic
  if both sorts, compare levels
  if both literals, compare values

  -- Layer 2: Reduce to WHNF
  a' = whnf(a)
  b' = whnf(b)

  -- Layer 3: Proof irrelevance
  if both are proofs of Props, compare their types

  -- Layer 4: Structural comparison (isDefEqCore)
  if same head constant and levels, compare spines pairwise
  if both fvar at same level, compare spines
  if both ctor at same index, compare spines
  if both pi, compare domains and codomains (under binder)
  if both lambda, compare bodies (under binder)
  if both proj with same type/idx, compare structs and spines
  if one is lambda (eta): compare body with (other applied to fvar)
  if one/both are consts: try lazy delta

  -- Layer 5: Fallback rules
  try structure eta: s ≡ ⟨s.1, s.2, ...⟩
  try unit-like: if type has exactly one nullary ctor  [Lean/Rust only]

  -- Failed
  return false
```

### Lazy Delta Unfolding

A key design choice: don't unfold everything to normal form. Instead, unfold
**one step at a time**, alternating between the two sides based on reducibility hints.

If both sides have the same head constant `f`, first try comparing their arguments
directly (congruence). Only if that fails, unfold `f` on both sides.

If the sides have different head constants, unfold the one with the **smaller**
reducibility hint (i.e., the one that's "more reducible"). This heuristic tends to
converge quickly.

**Implementation differences:**
- **Lean/Rust** (`lazyDelta`/`lazy_delta`): Alternates unfolding based on
  `ReducibilityHints` comparison. Has a `MAX_LAZY_DELTA_ITERS` limit (10,002 in Rust).
  Unfolds one side at a time.
- **Aiur** (`k_lazy_delta`): Unfolds **both** sides via `try_delta_unfold`, checks if
  either changed, and retries. No hint-based alternation, no iteration limit. Simpler
  but less directed.

### Proof Irrelevance

If `a : P` and `b : P` and `P : Prop`, then `a ≡ b` — all proofs of the same
proposition are definitionally equal. The kernel checks this by inferring the type of
the value and asking if that type lives in `Sort 0`.

**Implementation differences:**
- **Lean/Rust**: `infer_type_of_val` handles all Val forms: FVar (has its type stored),
  Const/Ctor (looks up typed constant and walks Pi spine), Lam/Pi/Proj (quotes back to
  Expr and infers). Catches errors and returns `false` gracefully.
- **Aiur**: `k_infer_val_type` handles Srt, Lit, Const, Ctor, Proj. Returns `Sort 1`
  as a sentinel for FVar/Lam/Pi (which are never Prop). This means proof irrelevance
  cannot trigger for FVar-headed values in the Aiur kernel, which is conservative but
  safe.

### Eta Expansion

For functions: `f ≡ fun x => f x` always holds. If one side is a lambda and the other
isn't, eta-expand the other side and compare the bodies.

For structures (single-constructor inductives): if `S` has constructor `mk`, then
`s ≡ S.mk s.1 s.2 ...` always holds. If comparing two values of a structure type
and they don't match, try eta-expanding both to constructor form.

All three implementations handle both function eta and structure eta. The Aiur kernel's
`try_eta_struct_one` inlines the struct-like check (single constructor) and field
comparison into one function, avoiding redundant constant lookups.

### Nat Literal vs Constructor Equality

A special case: `Lit(0)` must be definitionally equal to `Nat.zero`, and `Lit(n+1)`
must equal `Nat.succ (Lit(n))`. All three implementations handle this in `isDefEqCore`
via a `nat_lit_eq_ctor` helper that checks the constructor's inductive is Nat, then
compares field counts and recursively checks the predecessor.

### Equiv Manager (Union-Find Cache)

The Lean and Rust kernels cache definitional equality results using a **union-find**
data structure keyed on pointer identity. When `isDefEq(a, b) = true`, they merge `a`
and `b` into the same equivalence class. Future comparisons involving either can
short-circuit by checking if they share a root. The Aiur kernel has no equiv manager
(Aiur's function-call caching provides some equivalent benefit).

---

## 9. Declarations and the Environment

The kernel processes declarations one at a time. Each declaration is added to the
**environment** — a map from names (or addresses) to their definitions and types.

### Declaration Kinds

| Kind | Has value? | Unfoldable? | Example |
|------|-----------|-------------|---------|
| **Axiom** | No | No | `Classical.choice` |
| **Definition** | Yes | Yes (with hints) | `Nat.add` |
| **Theorem** | Yes | Yes (needed for proof checking) | `Nat.add_comm` |
| **Opaque** | Yes | No | `native_decide` impl |
| **Inductive** | Generated | N/A | `Nat`, `List` |
| **Constructor** | Generated | N/A | `Nat.zero`, `Nat.succ` |
| **Recursor** | Generated | Has ι-rules | `Nat.rec` |
| **Quotient** | Special | Special rules | `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` |

### Checking a Definition

```
checkDefinition(name, type, value, univParams) =
  1. Check that `type` is well-typed: infer(type) must be a Sort
  2. Check that `value` has the declared type: check(value, type)
  3. (For safe defs) Ensure no unsafe constants are referenced
  4. Add to environment
```

The Lean/Rust kernels use `check` (bidirectional) for step 2 rather than
`infer` + `isDefEq`. The Aiur kernel also uses `k_check` for Defn/Thm/Opaque.

### Checking a Theorem

Same as a definition. Theorem values (proofs) are unfoldable during WHNF and delta
reduction — this is necessary because proof terms may need to reduce during type
checking (e.g., when checking that two proof terms are definitionally equal, or when
a proof is used as an argument whose type must match a Pi domain).

---

## 10. Inductive Types and Recursors

Inductive types are the most complex declarations. When you write:

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

The kernel generates and validates:
1. The **inductive type** itself (`Nat`)
2. Each **constructor** (`Nat.zero`, `Nat.succ`)
3. The **recursor** (`Nat.rec`) — the elimination principle

### The Recursor

`Nat.rec` has type:
```
Nat.rec : {motive : Nat → Sort u} →
          motive Nat.zero →
          ((n : Nat) → motive n → motive (Nat.succ n)) →
          (n : Nat) → motive n
```

It takes:
- A **motive**: what type you're producing, as a function of the Nat
- A case for **zero**
- A case for **succ** (which receives the predecessor AND the recursive result)
- The **major premise**: the Nat being matched on

### Iota Rules

Each constructor gets a reduction rule:
```
Nat.rec motive hz hs Nat.zero       →  hz
Nat.rec motive hz hs (Nat.succ n)   →  hs n (Nat.rec motive hz hs n)
```

The kernel validates that these rules are well-typed.

### Mutual and Nested Inductives

Mutual inductives (several types defined simultaneously) share a single recursor.
Nested inductives (an inductive that references itself inside another type constructor,
like `Expr` containing `List Expr`) require specialization — the kernel creates
temporary specialized versions for validation.

The Lean/Rust kernels handle mutual/nested inductives via `check_ind_block`. The Aiur
kernel does not validate inductive blocks — it trusts that the inductives, constructors,
and recursors provided in the environment are well-formed.

---

## 11. Special Reductions

### Nat Primitives

Instead of unfolding `Nat.add 1000000 1000000` by a million successor steps, the kernel
has built-in support for Nat arithmetic. When both arguments are **literals**, it
computes the result directly:

```
Nat.add (lit 3) (lit 4) → lit 7       -- O(1), not O(n) unfolding
```

Supported: `add`, `sub`, `mul`, `div`, `mod`, `pow`, `gcd`, `beq`, `ble`, `land`,
`lor`, `xor`, `shiftLeft`, `shiftRight`.

The Lean and Rust kernels implement these in their WHNF loops. The Aiur kernel does
**not** implement nat primitives — it relies entirely on iota reduction (Nat.rec) for
Nat computation. This works but is exponentially slower for large numbers.

### String Primitives

String literals can be compared and manipulated. When needed for definitional equality,
a string literal is expanded to its `List Char` constructor form.

The Lean/Rust kernels handle this. The Aiur kernel does not support string operations
(the `str_idx` is set to a sentinel value since String is not in the dependency
closure of the currently tested constants).

### Quotient Types

Lean has built-in support for quotient types:
- `Quot`: quotient type former
- `Quot.mk`: inject into quotient
- `Quot.lift`: eliminate from quotient (must respect the equivalence)
- `Quot.ind`: induction principle

These have special reduction rules:
```
Quot.lift f h (Quot.mk r a) → f a
```

All three implementations handle quotient reduction in WHNF. The Aiur kernel implements
`k_try_quot_reduction` which handles both `Quot.lift` (reduce_size=6, f_pos=3) and
`Quot.ind` (reduce_size=5, f_pos=3).

---

## 12. Substitution-Based vs Environment-Based

Here's a concrete comparison:

### Beta Reduction

**Substitution** (lean4lean, nanoda_lib):
```
(fun x => body) arg
  → body[#0 := arg]
  → walk entire body tree, replace #0 with arg, shift other indices
  → O(|body|) work
```

**Environment** (our kernels):
```
eval(app (lam A body) arg, env)
  → let va = eval(arg, env)
  → eval(body, env ++ [va])
  → O(1) work (just an array push)
```

### Going Under Binders (in isDefEq)

**Substitution**: To compare `fun x => a` with `fun x => b`, substitute a fresh
variable for `x` in both, then compare. Creating the fresh variable and substituting
it is O(|body|).

**Environment**: To compare `lam(domA, bodyA, envA)` with `lam(domB, bodyB, envB)`,
create a fresh `fvar(depth)`, push it onto both environments, eval both bodies, and
compare the resulting values. The "substitution" is just `env_push(env, fvar)`.

### Trade-offs

| Aspect | Substitution | Environment |
|--------|-------------|-------------|
| Beta reduction | O(\|body\|) | O(1) |
| Representing values | Expressions (familiar) | Values (new domain) |
| Sharing/caching | Expression-level | Pointer-identity on Vals |
| Implementation complexity | Simpler | More complex (thunks, closures) |
| Memory | May duplicate work | Thunks add overhead, but memoize |
| Readback | Not needed | Needed for some operations |

### Readback (Quote)

Sometimes the environment-based kernel needs to convert a `Val` back to an `Expr` —
this is called **readback** or **quotation**. It's needed when, e.g., we want to
instantiate universe parameters in an expression stored in the environment (which is
still an `Expr`), or when building the Pi type for a lambda's inferred type.

The readback converts de Bruijn levels back to indices:
```
quote(fvar(level), depth) = bvar(depth - level - 1)
quote(lam(dom, body, env), depth) =
  let x = fvar(depth)
  let body_val = eval(body, env ++ [x])
  lam(quote(dom, depth), quote(body_val, depth + 1))
```

In Aiur, `k_quote` also handles `KVal.Thunk` by forcing it first.

---

## 13. Caching and Performance

### Lean/Rust Kernels

The Lean and Rust kernels use aggressive caching at multiple levels:

| Cache | Key | Value | Purpose |
|-------|-----|-------|---------|
| **Inference** | `(Expr, context_ptrs)` | `(TypedExpr, Val)` | Avoid re-inferring shared subexpressions |
| **WHNF** | `Val` (pointer id) | `Val` | Skip re-reducing already-WHNF values |
| **DefEq success** | `(ptr_a, ptr_b)` | `bool` | Skip re-checking known equalities |
| **DefEq failure** | `(ptr_a, ptr_b)` | `bool` | Skip re-checking known non-equalities |
| **Equiv manager** | union-find on `ptr` | equivalence class | Transitive equality: a≡b ∧ b≡c ⇒ a≡c |
| **Typed constants** | `MetaId` | `TypedConst` | Never re-check a constant |
| **Thunk memoization** | thunk identity | `Val` | Never re-evaluate a forced thunk |

### Aiur Kernel

The Aiur kernel has **no explicit caches**. Instead, it relies on the Aiur runtime's
function-call caching (see `src/aiur/execute.rs`): every function call with the same
arguments returns the cached result. This means:

- `k_eval(expr, env, top)` with the same `expr`, `env`, `top` is automatically memoized
- `k_force(thunk, top)` = `k_eval(e, env, top)` benefits from the same caching
- `k_whnf(v, top)` on the same `v` is cached
- Even `k_is_def_eq(a, b, ...)` is cached when called with pointer-equal arguments

This makes the most naive Fibonacci implementation efficient in Aiur, and similarly
makes thunk re-evaluation free. The trade-off is that cache keys are structural
(not pointer-based), which may be slower for large values but is always correct.

### Heartbeats

The Lean/Rust kernels use a monotonic counter incremented on each major operation.
If it exceeds a limit, the kernel aborts. The Aiur kernel has no heartbeat mechanism —
termination relies on the well-foundedness of the input declarations.

---

## 14. Implementation Comparison

### Feature Matrix

| Feature | Lean | Rust | Aiur |
|---------|------|------|------|
| Lazy eval (thunks in spines) | ✅ ST.Ref | ✅ RefCell | ✅ KVal.Thunk |
| Eager beta optimization | ✅ | ✅ | ✅ |
| Delta unfolding (WHNF) | ✅ | ✅ | ✅ |
| Iota reduction (recursor) | ✅ | ✅ | ✅ |
| K-reduction (Prop recursors) | ✅ | ✅ | ✅ |
| Nat literal iota | ✅ | ✅ | ✅ |
| Quotient reduction | ✅ | ✅ | ✅ |
| Nat primitives (add, mul, ...) | ✅ | ✅ | ❌ |
| String primitives | ✅ | ✅ | ❌ |
| Proof irrelevance | ✅ full | ✅ full | ⚠️ partial (FVar sentinel) |
| Function eta | ✅ | ✅ | ✅ |
| Struct eta | ✅ | ✅ | ✅ |
| Unit-like types | ✅ | ✅ | ❌ |
| Lazy delta (hint-based) | ✅ | ✅ | ⚠️ unfolds both sides |
| Equiv manager (union-find) | ✅ | ✅ | ❌ (Aiur caching instead) |
| WHNF cache | ✅ | ✅ | ❌ (Aiur caching instead) |
| Inference cache | ✅ | ✅ | ❌ (Aiur caching instead) |
| Inductive block validation | ✅ | ✅ | ❌ (trusts input) |
| Safety checking (unsafe/partial) | ✅ | ✅ | ❌ |
| Error diagnostics | ✅ | ✅ | ❌ (assert only) |
| Delta step limit | ✅ | ✅ | ❌ |
| Bidirectional checking | ✅ | ✅ | ✅ |

### Context Management

| Aspect | Lean/Rust | Aiur |
|--------|-----------|------|
| Type context | `types: Vec<Val>` indexed by level | `types: KValList` indexed by de Bruijn index |
| Value environment | `Env = Rc<Vec<Val>>` (COW) | `KValEnv` (cons-list) |
| Let-bound values | Separate `let_values: Vec<Option<Val>>` | Pushed directly into env |
| Depth tracking | `depth()` method on TypeChecker | Explicit `depth: [G; 8]` parameter |
| Binder entry | `with_binder(dom, \|tc\| ...)` | Explicit `KValList.Cons(dom, types)` + `KValEnv.Cons(fvar, env)` |

---

## 15. Aiur TODOs and Disparities

### Missing Features (by priority)

1. **Nat primitives**: Built-in computation for `Nat.add`, `Nat.sub`, `Nat.mul`, etc.
   on literals. Without these, any theorem involving concrete arithmetic must unfold
   through `Nat.rec`, which is exponential for large numbers. The Lean/Rust kernels
   detect these by matching the constant's address against a `Primitives` table
   discovered during environment setup.

3. **Unit-like types**: In `isDefEq`, if both values have a type with exactly one
   nullary constructor, they are definitionally equal. The Lean/Rust kernels check this
   as a fallback after struct eta fails.

4. **Lazy delta with hint comparison**: The current `k_lazy_delta` unfolds both sides
   simultaneously. The Lean/Rust kernels unfold one side at a time, choosing based on
   `ReducibilityHints` comparison. This is more efficient when one side is "more
   reducible" than the other.

5. **String support**: String literals and primitives. Needed for any theorem that
   involves `String`.

### Potential Issues

1. **No delta step limit**: If two definitions are mutually recursive (shouldn't happen
   in well-typed code, but the kernel should be robust), `k_lazy_delta` →
   `try_delta_unfold` → `k_is_def_eq` → `k_lazy_delta` could diverge. The Lean/Rust
   kernels have `MAX_LAZY_DELTA_ITERS` / `MAX_DELTA_STEPS` limits.

2. **Proof irrelevance for FVar**: `k_infer_val_type` returns `Sort 1` (non-Prop) for
   `FVar`. This means if `x : P` where `P : Prop` and `x` is a free variable, proof
   irrelevance won't trigger. This is conservative (never unsound) but incomplete.
   The Lean/Rust kernels store the type in the FVar head and can inspect it directly.

---

## Appendix: Reading the Code

### Aiur implementation (`Ix/IxVM/`)

| File | What it does |
|------|-------------|
| `KernelTypes.lean` | `KExpr`, `KVal` (with `Thunk`), `KLevel`, `KConstantInfo`, all enums |
| `Kernel.lean` | All kernel logic: `k_eval`, `k_whnf`, `k_is_def_eq`, `k_infer`, `k_check` |
| `Convert.lean` | Ixon format → `KConstantInfo` conversion |
| `Ingress.lean` | Content-addressed constant loading from IO |

### Lean implementation (`Ix/Kernel/`)

| File | What it does |
|------|-------------|
| `Types.lean` | Core AST: `Expr`, `Level`, `ConstantInfo`, `Env`, `MetaMode` |
| `Value.lean` | `Val`, `Head`, closure/thunk types |
| `Infer.lean` | The big mutual block: `eval`, `whnf`, `isDefEq`, `infer` |
| `TypecheckM.lean` | Monad stack, thunk table management, runner |
| `Level.lean` | Universe level normalization and comparison |
| `Primitive.lean` | Validation of built-in Nat/Bool/Quot primitives |
| `Helpers.lean` | Nat extraction, projection reduction |
| `EquivManager.lean` | Union-find for def-eq caching |
| `Quote.lean` | Val → Expr readback |
| `ExprUtils.lean` | Level substitution, bvar shifting |
| `Datatypes.lean` | `TypedConst`, `TypeInfo` wrappers |
| `Convert.lean` | Ixon format → kernel types |

### Rust implementation (`src/ix/kernel/`)

| File | What it does |
|------|-------------|
| `types.rs` | `KExpr`, `KLevel`, `KConstantInfo`, `KEnv`, `Primitives` |
| `value.rs` | `Val`, `Head`, `Thunk`, `Env` (COW) |
| `eval.rs` | Krivine machine: `eval`, `apply_val_thunk`, `force_thunk` |
| `whnf.rs` | WHNF with delta/iota/quot/nat reductions |
| `infer.rs` | Type inference and checking |
| `def_eq.rs` | Definitional equality |
| `check.rs` | Per-declaration validation |
| `tc.rs` | `TypeChecker` state, context, caches |
| `level.rs` | Universe level operations |
| `helpers.rs` | Nat/projection helpers |
| `equiv.rs` | Union-find |
| `quote.rs` | Readback |
| `primitive.rs` | Primitive validation |
| `error.rs` | Error types |

### Reference implementations

| Codebase | Language | Approach | Notes |
|----------|----------|----------|-------|
| `lean4lean/` | Lean 4 | Substitution | Verified (has correctness proofs) |
| `nanoda_lib/` | Rust | Substitution | Clean, well-documented |
