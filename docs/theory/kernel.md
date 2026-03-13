# Formalizing the Correctness of Ix

This document describes the plan for proving the soundness of Ix's NbE-based
type checker, building on the existing `Ix/Theory/` specification and using
[lean4lean](https://github.com/digama0/lean4lean) as a reference.

## Architecture

The formalization has three layers:

```
┌──────────────────────────────────────────────────┐
│  Theory  (Ix/Theory/)                            │
│  Pure specification: SExpr, SVal, eval_s,        │
│  quote_s, isDefEq_s. Typing judgment.            │
│  All proofs in Lean, 0 sorries target.           │
├──────────────────────────────────────────────────┤
│  Verify  (Ix/Verify/)  [future]                  │
│  Bridge: Kernel2 implements Theory correctly.    │
│  TrExpr, TrVal translation relations.            │
├──────────────────────────────────────────────────┤
│  Implementation  (Ix/Kernel2/)                   │
│  NbE Krivine machine with lazy thunks.           │
│  Lean (~3K LOC) + Rust (~9K LOC).                │
└──────────────────────────────────────────────────┘
```

The key idea: define a logical typing judgment (`IsDefEq`) at the Theory
level, then prove that the NbE specification (`eval_s`, `quote_s`,
`isDefEq_s`) is sound with respect to it. This validates the NbE approach
itself. A future Verify layer can then connect the actual Kernel2
implementation to the Theory specification.


## Part I: What We Have

The `Ix/Theory/` directory contains 6341 lines of Lean across 22 files.
Phases 0–4 and 6–8 have **0 sorries** — every theorem is fully proven.
Phases 5 (NbESoundness), 9 (EvalSubst), and 10 (SimVal) have **19 sorries**
total; see Part V–V.C for details.

### Substitution Algebra (`Ix/Theory/Expr.lean`)

The syntactic foundation. `SExpr` is a de Bruijn indexed term language with
`liftN` (shift free variables) and `inst` (substitute a variable).

```
inductive SExpr where
  | bvar (idx : Nat)
  | sort (u : Nat)
  | const (id : Nat)
  | app (fn arg : SExpr)
  | lam (dom body : SExpr)
  | forallE (dom body : SExpr)
  | letE (ty val body : SExpr)
  | lit (n : Nat)
```

Key proven lemmas:
- `inst_liftN` — lifting then instantiating cancels
- `liftN_instN_lo/hi` — lifting commutes with substitution
- `inst_inst_hi` — double substitution composition
- `ClosedN` — well-scopedness predicate with monotonicity

These are ported from lean4lean's `VExpr.lean` and extended with `letE`
and `lit`.

### Semantic Domain (`Ix/Theory/Value.lean`)

```
mutual
inductive SVal where
  | lam (dom : SVal) (body : SExpr) (env : List SVal)
  | pi  (dom : SVal) (body : SExpr) (env : List SVal)
  | sort (u : Nat)
  | neutral (head : SHead) (spine : List SVal)
  | lit (n : Nat)

inductive SHead where
  | fvar (level : Nat)
  | const (id : Nat)
end
```

Closures capture `(body, env)`. Neutrals carry a head and a spine of
arguments. No thunks, no mutability — pure specification.

### Evaluation (`Ix/Theory/Eval.lean`)

`eval_s (fuel : Nat) (e : SExpr) (env : List SVal) : Option SVal`

Fueled evaluator. Environment is a list with bvar 0 at the head. O(1) beta
reduction via closure application. `letE` is zeta-reduced eagerly.

`apply_s (fuel : Nat) (fn arg : SVal) : Option SVal`

Beta for lambdas (evaluate closure body in extended env), spine accumulation
for neutrals.

### Quoting (`Ix/Theory/Quote.lean`)

`quote_s (fuel : Nat) (v : SVal) (d : Nat) : Option SExpr`

Read-back at binding depth `d`. Opens closures by applying a fresh
`fvar d`, then quotes the result at `d+1`. Converts de Bruijn levels to
indices via `levelToIndex d level = d - 1 - level`.

`nbe_s fuel e env d = eval_s fuel e env >>= quote_s fuel · d`

### Well-Formedness (`Ix/Theory/WF.lean`)

`ValWF v d` — all fvar levels in `v` are below `d`, closures are
well-scoped relative to their environments.

Mutual predicates: `ValWF`, `HeadWF`, `ListWF`, `EnvWF`.
Proven: monotonicity (depth increase preserves WF), environment lookup
preserves WF, spine append preserves WF.

### Eval Preserves WF (`Ix/Theory/EvalWF.lean`)

```
theorem eval_preserves_wf :
    eval_s fuel e env = some v →
    ClosedN e env.length → EnvWF env d → ValWF v d

theorem apply_preserves_wf :
    apply_s fuel fn arg = some v →
    ValWF fn d → ValWF arg d → ValWF v d
```

### Fuel Monotonicity (`Ix/Theory/Roundtrip.lean`)

More fuel never changes the result:

```
theorem eval_fuel_mono   : eval_s n e env = some v   → n ≤ m → eval_s m e env = some v
theorem apply_fuel_mono  : apply_s n fn arg = some v → n ≤ m → apply_s m fn arg = some v
theorem quote_fuel_mono  : quote_s n v d = some e    → n ≤ m → quote_s m v d = some e
```

### NbE Stability (`Ix/Theory/Roundtrip.lean`)

The corrected roundtrip theorem. NbE produces normal forms:

```
theorem nbe_stable :
    ValWF v d → quote_s fuel v d = some e →
    ∃ fuel', nbe_s fuel' e (fvarEnv d) d = some e
```

If a well-formed value quotes to `e`, then running NbE on `e` in the
standard fvar environment `[fvar(d-1), ..., fvar(0)]` returns `e`
unchanged.

### NbE Idempotence (`Ix/Theory/Roundtrip.lean`)

```
theorem nbe_idempotent :
    EnvWF env d → ClosedN e env.length →
    eval_s fuel e env = some v → quote_s fuel v d = some e' →
    ∃ fuel', nbe_s fuel' e' (fvarEnv d) d = some e'
```

Consequence of stability + eval preserves WF.

### Definitional Equality (`Ix/Theory/DefEq.lean`)

`isDefEq_s (fuel : Nat) (v1 v2 : SVal) (d : Nat) : Option Bool`

Structural comparison on values. Opens closures with shared fresh fvar.

Proven properties:
- **Fuel monotonicity**: `isDefEq_fuel_mono`
- **Symmetry**: `isDefEq_symm`
- **Reflexivity** (conditional on quotability): `isDefEq_refl`
- **Soundness**: `isDefEq_sound` — def-eq values produce the same normal
  form:

```
theorem isDefEq_sound :
    isDefEq_s fuel v1 v2 d = some true →
    ValWF v1 d → ValWF v2 d →
    ∃ f1 f2 e, quote_s f1 v1 d = some e ∧ quote_s f2 v2 d = some e
```


## Part II: Parameterizing SExpr for Universe Levels

The current `SExpr` uses `Nat` for sort levels and bare `Nat` for const
identifiers (no universe level arguments). For the typing judgment we need
proper universe levels and universe-polymorphic constants.

### The SLevel Type

Following lean4lean's `VLevel`:

```
inductive SLevel where
  | zero
  | succ (l : SLevel)
  | max (l r : SLevel)
  | imax (l r : SLevel)
  | param (idx : Nat)
```

With:
- `SLevel.WF (uvars : Nat)` — all param indices < uvars
- `SLevel.eval (ls : List Nat) : SLevel → Nat` — semantic evaluation
- `SLevel.Equiv (a b : SLevel) : Prop := a.eval = b.eval` — equivalence
- `SLevel.inst (ls : List SLevel) : SLevel → SLevel` — level substitution

### Parameterizing SExpr

Refactor `SExpr` to be generic over the level type:

```
inductive SExpr (L : Type) where
  | bvar (idx : Nat)
  | sort (u : L)
  | const (id : Nat) (levels : List L)
  | app (fn arg : SExpr L)
  | lam (dom body : SExpr L)
  | forallE (dom body : SExpr L)
  | letE (ty val body : SExpr L)
  | lit (n : Nat)
  | proj (typeName : Nat) (idx : Nat) (struct : SExpr L)
```

Two instantiations:
- `abbrev SExpr₀ := SExpr Nat` — for existing NbE proofs (backward compatible)
- `abbrev TExpr := SExpr SLevel` — for the typing judgment

The substitution algebra (`liftN`, `inst`, `ClosedN`) is level-agnostic:
`liftN` and `inst` never touch sorts or const levels. All existing proofs
should transfer to the parameterized version with minimal changes.

Similarly parameterize `SVal` and `SHead`:

```
mutual
inductive SVal (L : Type) where
  | lam (dom : SVal L) (body : SExpr L) (env : List (SVal L))
  | pi  (dom : SVal L) (body : SExpr L) (env : List (SVal L))
  | sort (u : L)
  | neutral (head : SHead L) (spine : List (SVal L))
  | lit (n : Nat)

inductive SHead (L : Type) where
  | fvar (level : Nat)
  | const (id : Nat) (levels : List L)
end
```

The `const` head gains level arguments to match universe-polymorphic
lookups.

### New Operations for Levels

Universe-level instantiation on expressions, following lean4lean's `instL`:

```
variable (ls : List SLevel) in
def SExpr.instL : TExpr → TExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL
  | .letE ty val body => .letE ty.instL val.instL body.instL
  | .lit n => .lit n
  | .proj t i s => .proj t i s.instL
```

Key lemmas to prove:
- `instL` commutes with `liftN` and `inst`
- `ClosedN` preserved by `instL`
- `instL_instL` — double instantiation composition

### Impact on Existing Files

| File | Change needed |
|------|---------------|
| `Expr.lean` | Parameterize `SExpr`. Add `L` type parameter. Proofs should transfer since `liftN`/`inst` ignore `L`. |
| `Value.lean` | Parameterize `SVal`, `SHead`. Add `L` parameter. |
| `Eval.lean` | Parameterize `eval_s`, `apply_s` over `L`. No logic changes. |
| `Quote.lean` | Parameterize `quote_s`, `nbe_s`. No logic changes. |
| `WF.lean` | Parameterize `ValWF` etc. No logic changes. |
| `EvalWF.lean` | Parameterize. No logic changes. |
| `Roundtrip.lean` | Parameterize. Proofs should transfer. |
| `DefEq.lean` | Parameterize. Proofs should transfer. |

The `BEq` instances on `SVal`/`SHead` (used for `#guard` checks) will need
`[BEq L]` constraints. The equation lemmas should still work since the
proofs are structural.

**Risk**: Lean's equation compiler may generate different equation lemmas
for parameterized mutual inductives. If so, proof scripts that reference
specific `eq_N` lemmas may need updating. This is the main risk of the
refactor.


## Part III: The Typing Judgment

### Context Lookup

```
inductive Lookup : List TExpr → Nat → TExpr → Prop where
  | zero : Lookup (ty :: Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A :: Γ) (n+1) ty.lift
```

Variable `i` in context `Γ` has type `Γ[i]` lifted appropriately (to
account for the bindings between the variable and the point of use).

### The IsDefEq Judgment

The core typing relation combining typing and definitional equality in a
single inductive, following lean4lean:

```
variable (env : SEnv) (uvars : Nat)

inductive IsDefEq : List TExpr → TExpr → TExpr → TExpr → Prop where
  -- Variable
  | bvar : Lookup Γ i A → IsDefEq Γ (.bvar i) (.bvar i) A

  -- Structural
  | symm  : IsDefEq Γ e e' A → IsDefEq Γ e' e A
  | trans : IsDefEq Γ e₁ e₂ A → IsDefEq Γ e₂ e₃ A → IsDefEq Γ e₁ e₃ A

  -- Sorts
  | sortDF :
      l.WF uvars → l'.WF uvars → l ≈ l' →
      IsDefEq Γ (.sort l) (.sort l') (.sort (.succ l))

  -- Constants (universe-polymorphic)
  | constDF :
      env.constants c = some ci →
      (∀ l ∈ ls, l.WF uvars) → (∀ l ∈ ls', l.WF uvars) →
      ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      IsDefEq Γ (.const c ls) (.const c ls') (ci.type.instL ls)

  -- Application
  | appDF :
      IsDefEq Γ f f' (.forallE A B) →
      IsDefEq Γ a a' A →
      IsDefEq Γ (.app f a) (.app f' a') (B.inst a)

  -- Lambda
  | lamDF :
      IsDefEq Γ A A' (.sort u) →
      IsDefEq (A :: Γ) body body' B →
      IsDefEq Γ (.lam A body) (.lam A' body') (.forallE A B)

  -- Pi (forallE)
  | forallEDF :
      IsDefEq Γ A A' (.sort u) →
      IsDefEq (A :: Γ) body body' (.sort v) →
      IsDefEq Γ (.forallE A body) (.forallE A' body')
              (.sort (.imax u v))

  -- Type conversion
  | defeqDF :
      IsDefEq Γ A B (.sort u) → IsDefEq Γ e₁ e₂ A →
      IsDefEq Γ e₁ e₂ B

  -- Beta reduction
  | beta :
      IsDefEq (A :: Γ) e e B → IsDefEq Γ e' e' A →
      IsDefEq Γ (.app (.lam A e) e') (e.inst e') (B.inst e')

  -- Eta expansion
  | eta :
      IsDefEq Γ e e (.forallE A B) →
      IsDefEq Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)

  -- Proof irrelevance
  | proofIrrel :
      HasType Γ p (.sort .zero) → HasType Γ h p → HasType Γ h' p →
      IsDefEq Γ h h' p

  -- Extra definitional equalities (delta, iota, etc.)
  | extra :
      env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
      IsDefEq Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)

  -- Let-expression (zeta reduction)
  | letDF :
      IsDefEq Γ ty ty' (.sort u) →
      IsDefEq Γ val val' ty →
      IsDefEq (ty :: Γ) body body' B →
      IsDefEq Γ (.letE ty val body) (.letE ty' val' body') (B.inst val)

  | letZeta :
      HasType Γ ty (.sort u) → HasType Γ val ty →
      IsDefEq (ty :: Γ) body body B →
      IsDefEq Γ (.letE ty val body) (body.inst val) (B.inst val)

  -- Literals
  | litDF :
      IsDefEq Γ (.lit n) (.lit n) litType

  -- Projection
  | projDF :
      HasType Γ s sType →
      IsDefEq Γ (.proj t i s) (.proj t i s) (projType t i s sType)
```

### Abbreviations

```
def HasType env U Γ e A := IsDefEq env U Γ e e A
def IsType  env U Γ A   := ∃ u, HasType env U Γ A (.sort u)
def IsDefEqU env U Γ e₁ e₂ := ∃ A, IsDefEq env U Γ e₁ e₂ A
```

### Differences from lean4lean

| Feature | lean4lean | Ix |
|---------|-----------|-----|
| `letE` | Absent from VExpr (desugared) | Included with `letDF` + `letZeta` rules |
| `lit` | Absent (elaborated to ctors) | Included with `litDF` rule |
| `proj` | Absent | Included with `projDF` rule |
| `const` levels | `Name × List VLevel` | `Nat × List SLevel` |

Including these in the judgment means the verification bridge (Phase 9) is
more direct — no desugaring step required between Kernel2 and Theory.

### Environment and Declarations

```
structure SConstant where
  uvars : Nat
  type : TExpr

structure SDefEq where
  uvars : Nat
  lhs : TExpr
  rhs : TExpr
  type : TExpr

structure SEnv where
  constants : Nat → Option SConstant
  defeqs : SDefEq → Prop
```

With `SEnv.addConst`, `SEnv.addDefEq`, and monotonicity (`SEnv.LE`).


## Part IV: Basic Typing Lemmas

These follow lean4lean's `Theory/Typing/Lemmas.lean` and rely heavily on
the substitution algebra already proven in `Expr.lean`.

### Weakening

```
theorem IsDefEq.weakening :
    IsDefEq env U Γ e₁ e₂ A →
    IsDefEq env U (B :: Γ) e₁.lift e₂.lift A.lift
```

Under one additional binder, all terms shift by 1. Uses `liftN`
composition lemmas from `Expr.lean`.

### Substitution

```
theorem IsDefEq.substitution :
    IsDefEq env U (A :: Γ) e₁ e₂ B →
    HasType env U Γ a A →
    IsDefEq env U Γ (e₁.inst a) (e₂.inst a) (B.inst a)
```

The substitution lemma. Uses `inst` composition lemmas (`inst_liftN`,
`inst_inst_hi`) from `Expr.lean`.

### Context Conversion

```
theorem IsDefEq.ctxConv :
    IsDefEq env U Γ A A' (.sort u) →
    IsDefEq env U (A :: Γ) e₁ e₂ B →
    IsDefEq env U (A' :: Γ) e₁ e₂ B
```

If two types are definitionally equal, we can substitute one for the other
in the context.

### Environment Monotonicity

```
theorem IsDefEq.envMono :
    IsDefEq env U Γ e₁ e₂ A → env ≤ env' →
    IsDefEq env' U Γ e₁ e₂ A
```


## Part V: NbE Soundness — The Novel Contribution

This is where Ix's formalization diverges from lean4lean. We connect the
*computational* NbE specification to the *logical* typing judgment directly.

### The Key Insight

In lean4lean, reduction is defined by head-reduction rules, and confluence
requires a complex parallel reduction argument. In Ix, NbE *computes*
normal forms directly, and we already have:

1. **NbE stability** (`nbe_stable`): normal forms are fixed points of NbE
2. **DefEq soundness** (`isDefEq_sound`): def-eq values quote to the same
   expression

These give us the raw material for:

### NbE Type Preservation

```
theorem nbe_type_preservation :
    HasType env U Γ e A →
    eval_s fuel e env_val = some v →
    quote_s fuel' v d = some e' →
    -- (where env_val is the evaluation of Γ, d = |Γ|)
    IsDefEq env U Γ e e' A
```

Evaluating a well-typed expression and quoting back yields a term
definitionally equal to the original. The judgment's `beta`, `letZeta`,
and `extra` rules account for the reductions that NbE performs.

### Computational DefEq Reflects Typing

```
theorem isDefEq_s_reflects_typing :
    isDefEq_s fuel v₁ v₂ d = some true →
    ValTyped env U Γ v₁ A → ValTyped env U Γ v₂ A →
    ∃ e₁ e₂, IsDefEq env U Γ e₁ e₂ A
```

If the computational `isDefEq_s` returns `true`, then the values are
definitionally equal in the typing judgment. This bridges the executable
checker to the logical specification.

### Proof Strategy

The proof proceeds by:

1. **Define `ValTyped`**: a relation connecting `SVal` to the typing
   judgment — "value `v` at depth `d` has type `A` in context `Γ`".
   This is the semantic analogue of `HasType`.

2. **Prove eval preserves typing**: if `HasType Γ e A` and
   `eval_s fuel e env_val = some v`, then `ValTyped Γ v A`.

3. **Prove quote reflects typing**: if `ValTyped Γ v A` and
   `quote_s fuel v d = some e`, then `HasType Γ e A`.

4. **Combine**: NbE (eval + quote) preserves typing, and `isDefEq_s`
   soundness follows from `isDefEq_sound` (same normal form) plus
   the typing connection.

The existing proofs (`eval_preserves_wf`, `nbe_stable`, `isDefEq_sound`)
provide the well-formedness backbone. The new work is lifting from
well-formedness (`ValWF`) to typing (`ValTyped`).


### Part V.A: Current State of NbE Soundness (Phase 5)

**`Ix/Theory/NbESoundness.lean`** (~570 lines, 7 sorries)

The actual implementation uses a doubly-conditional predicate `NbEProp`:
if eval AND quote both succeed, then the resulting expression is
`IsDefEq` to the original. This avoids requiring `eval_succeeds` and
`quote_succeeds` lemmas upfront — those are deferred to when the
predicate is instantiated.

The proof is by induction on `IsDefEq` (17 constructors). Current
status:

| Constructor | Status |
|-------------|--------|
| bvar, symm, trans, sortDF, constDF | Proved |
| litDF, projDF, defeqDF, proofIrrel | Proved |
| lamDF, forallEDF, extra | Proved |
| appDF (neutral sub-case) | Proved |
| appDF (lambda sub-case) | **Sorry** — needs `nbe_subst` |
| beta | **Sorry** — needs `nbe_subst` |
| eta (right direction) | Proved |
| eta (left direction) | **Sorry** — needs `eval_lift_quoteEq` |
| letDF | **Sorry** — needs `nbe_subst` |
| letZeta | **Sorry** — needs `nbe_subst` |

All 7 sorries are blocked on a single axiom, `nbe_subst`, which states:

```
nbe_subst : eval body (va :: fenv) quotes to bodyE.inst ea
```

This connects semantic substitution (closure environment extension) to
syntactic substitution (`SExpr.inst`). It is the output of Phase 9.


### Part V.B: Eval-Subst Correspondence (Phase 9)

**`Ix/Theory/EvalSubst.lean`** (~445 lines, 6 sorries)

Introduces `QuoteEq v1 v2 d` — two values are QuoteEq if they quote to
the same expression at depth `d`, regardless of fuel. The main theorem
`eval_inst_quoteEq` is proved by structural induction on `e`, with all
cases filled — but it relies on 6 sorry'd axioms.

**The core circularity**: The `app` case of `eval_inst_quoteEq` needs
`apply_quoteEq`. But `apply_quoteEq` for lambda closures needs
`nbe_subst`, which IS `eval_inst_quoteEq` at `k=0`:

```
eval_inst_quoteEq (app case) → needs apply_quoteEq
apply_quoteEq (lam case)     → needs nbe_subst ≈ eval_inst_quoteEq at k=0
```

Breaking this circularity is the hardest problem in the formalization.
The planned approach is fuel-based mutual induction (see plan at
`.claude/plans/keen-zooming-babbage.md`).


### Part V.C: SimVal Design Findings (Phase 10)

**`Ix/Theory/SimVal.lean`** (~932 lines, 6 sorries)

Step-indexed value simulation `SimVal n v1 v2 d` provides closure
bisimulation infrastructure. It compiles and many downstream theorems
are proved, but deep analysis revealed critical design flaws:

**Finding 1: `eval_simval` at a fixed step is mathematically false for
app/letE.** `SimEnv 1` can relate environments containing
differently-bodied lambdas (since `SimVal 1 lam = True` for the closure
condition at step 0). Evaluating `app (.bvar 0) (.bvar 1)` in such
environments gives different results that are NOT `SimVal 1` equal.
The sorries at lines 466, 564, 568 are **unfillable**.

**Finding 2: `SimVal.mono` for closures is unprovable.** The closure at
step `n+1` takes `SimVal n` inputs and produces `SimVal n` outputs.
Monotonicity from step `n` to step `m ≤ n` requires lifting `SimVal m`
inputs to `SimVal n` inputs (going UP in step), but `SimVal.mono` only
goes DOWN.

**What works:** `eval_simval_inf` (the `∀n` version) has app/letE cases
fully proved — the step loss is absorbed by the universal quantifier.
The `simval_implies_quoteEq` bridge from `SimVal_inf` to `QuoteEq` is
also proved (modulo a mechanical `decreasing_by` obligation).

**Planned fix:** Redesign SimVal definition to match on `n` first
(SimVal 0 = True for all constructors), use `∀ j ≤ n'` in the closure
condition, and use well-founded recursion via `termination_by`. This
makes `SimVal.mono` provable and eliminates the false step-0 case.


## Part VI: Confluence via NbE

### Why This Is Simpler

lean4lean proves Church-Rosser via parallel reduction with a `Params`
typeclass abstracting over the reduction rules. This requires
standardization (Kashima 2000) and has 2 sorries.

Ix gets confluence from NbE stability:

```
theorem confluence :
    IsDefEq env U Γ e₁ e₂ A →
    ∃ f e, nbe_s f e₁ (fvarEnv d) d = some e ∧
           nbe_s f e₂ (fvarEnv d) d = some e
```

Def-eq terms have the same normal form under NbE. This follows from:
1. `isDefEq_sound` — computational def-eq gives same normal form
2. NbE type preservation — well-typed terms can be evaluated
3. `nbe_stable` — the normal form is a fixed point

No parallel reduction, no diamond lemma, no standardization. The NbE
machinery does the work.

### What This Buys Us

Confluence is the key lemma for:
- **Unique typing** (Phase 7): types are unique up to def-eq
- **Decidability**: the typing judgment is decidable (the computational
  `isDefEq_s` is a decision procedure)
- **Consistency**: the type system does not equate all types


## Part VII: Phased Roadmap

### Phase 0: Universe Levels
- **File**: `Ix/Theory/Level.lean` (~300 LOC)
- `SLevel` type, `WF`, `eval`, `Equiv`, `inst`
- Equivalence relation properties
- Reference: `lean4lean/Lean4Lean/Theory/VLevel.lean`

### Phase 1: Parameterize SExpr
- **Files**: all of `Ix/Theory/` (~1700 LOC refactor)
- `SExpr L`, `SVal L`, `SHead L`
- Add `instL` for `TExpr := SExpr SLevel`
- Verify all existing proofs still compile

### Phase 2: Environment & Declarations
- **File**: `Ix/Theory/Env.lean` (~200 LOC)
- `SConstant`, `SDefEq`, `SEnv`
- Reference: `lean4lean/Lean4Lean/Theory/VEnv.lean`

### Phase 3: Typing Judgment
- **File**: `Ix/Theory/Typing.lean` (~300 LOC)
- `IsDefEq` inductive, `HasType`, `IsType`, `Lookup`
- Reference: `lean4lean/Lean4Lean/Theory/Typing/Basic.lean`

### Phase 4: Basic Typing Lemmas
- **File**: `Ix/Theory/TypingLemmas.lean` (~800 LOC)
- Weakening, substitution, context conversion
- Reference: `lean4lean/Lean4Lean/Theory/Typing/Lemmas.lean`

### Phase 5: NbE Soundness Bridge — **7 sorries**
- **File**: `Ix/Theory/NbESoundness.lean` (~570 LOC)
- `NbEProp` conditional preservation predicate, `nbe_preservation` by
  induction on `IsDefEq` (11/17 constructors fully proved)
- `nbe_type_preservation` corollary (proved modulo sorry'd `nbe_subst`)
- **7 sorry cases**: all blocked on `nbe_subst` axiom from Phase 9
  - appDF lam left/right, beta, eta left, letDF, letZeta

### Phase 6: Confluence — **0 sorries**
- **File**: `Ix/Theory/Confluence.lean` (~178 LOC)
- `confluence_defeq`, `nbe_normal_form`, `confluence_syntactic`
- `isDefEq_s_reflects_typing` — computational def-eq reflects typing

### Phase 7: Inductive Types — **0 sorries**
- **File**: `Ix/Theory/Inductive.lean` (~370 LOC)
- Well-formed inductive declarations, constructors, recursors

### Phase 8: Quotient Types — **0 sorries**
- **File**: `Ix/Theory/Quotient.lean` (~210 LOC)
- Well-formed quotient types (Quot.mk/lift/ind axioms)

### Phase 9: Eval-Subst Correspondence — **6 sorries**
- **File**: `Ix/Theory/EvalSubst.lean` (~445 LOC)
- `QuoteEq v1 v2 d` — fuel-agnostic value equivalence via quoting
- `eval_inst_quoteEq` — main theorem (all cases filled using sorry'd axioms)
- **6 sorry'd axioms** (closure bisimulation, to be filled by SimVal):
  - `apply_quoteEq` — **hard**, circular with `nbe_subst`
  - `quoteEq_lam`, `quoteEq_pi` — **easy**, direct quote unfolding
  - `InstEnvCond.prepend` quoteEq — **medium**, needs eval_lift
  - `eval_env_quoteEq` — **medium**, needs apply_quoteEq
  - `quotable_of_wf` — **medium**, needs eval_succeeds helper

### Phase 10: Step-Indexed Simulation (SimVal) — **6 sorries**
- **File**: `Ix/Theory/SimVal.lean` (~932 LOC)
- Step-indexed value simulation `SimVal n v1 v2 d` for closure bisimulation
- `simval_implies_quoteEq` — bridge from SimVal_inf to QuoteEq
- `apply_simval`, `eval_simval_inf` — semantic preservation
- **6 sorries**: 3 are **mathematically false** (see Part V.C), 2 are
  unprovable with current definition, 1 is mechanical
- **Status**: compiles, but definition needs redesign before further progress

### Dependency Graph

```
Phase 0 (Levels)
   │
Phase 1 (Parameterize SExpr)
   │
Phase 2 (Env) ──→ Phase 3 (Typing) ──→ Phase 4 (Lemmas)
                                              │
                      Phase 10 (SimVal) ──→ Phase 9 (EvalSubst)
                                              │
                                        Phase 5 (NbE Soundness)
                                              │
                                        Phase 6 (Confluence)
                                        Phase 7 (Inductives)
                                        Phase 8 (Quotients)
```

### Future Phases (deferred)

- **Phase 11: Strong & unique typing** — stratified induction. (~2500 LOC)
- **Phase 12: Verification bridge** — `Ix/Verify/` connecting Kernel2 to
  Theory via `TrExpr`/`TrVal` translation relations. (~4000 LOC)
- **Phase 13: Declaration checking** — end-to-end `addDecl` soundness.


## Part VIII: Comparison with lean4lean

| Aspect | lean4lean | Ix |
|--------|-----------|-----|
| Reduction engine | Substitution-based head reduction | NbE eval-quote |
| Confluence | Church-Rosser via parallel reduction (2 sorries) | Via NbE stability (target: 0 sorries) |
| Typing judgment | `IsDefEq` on `VExpr` (no let/lit/proj) | `IsDefEq` on `TExpr` (includes let/lit/proj) |
| Expr type | `VExpr` with `VLevel` and `Name` | `SExpr SLevel` with `SLevel` and `Nat` |
| Value domain | N/A (substitution kernel) | `SVal SLevel` with closures and spines |
| Thunks | N/A | Specification has none; Kernel2 has lazy thunks |
| Verify bridge | `TrExprS`/`TrExpr` (Lean.Expr → VExpr) | `TrExpr`/`TrVal` (Kernel2.Expr → TExpr, Val → SVal) |
| sorry count (Theory) | ~9 | 19 (target: 0) |
| sorry count (Verify) | ~15 | TBD |

### What Ix Gains from NbE

1. **Simpler confluence**: no parallel reduction machinery needed
2. **Direct soundness**: prove NbE is sound, get type checking correctness
3. **Shared specification**: the same `eval_s`/`quote_s` used for both
   normalization proofs and the typing connection
4. **Executable specification**: `isDefEq_s` is a decision procedure that
   can be tested against concrete examples via `#guard`

### What lean4lean Has That Ix Needs

1. **Inductive types metatheory** (`Lean4Lean/Theory/Inductive.lean`)
2. **Strong typing** (`Lean4Lean/Theory/Typing/Strong.lean`)
3. **Unique typing** (`Lean4Lean/Theory/Typing/UniqueTyping.lean`)
4. **Full verify bridge** (`Lean4Lean/Verify/`)


## Part IX: Beyond Basic NbE — The Full Reduction Landscape

The Theory specification (`eval_s`, `quote_s`, `isDefEq_s`) covers only
the pure lambda calculus fragment: beta reduction, zeta reduction (let),
and structural comparison. The actual Kernel2 implementation has **20+
reduction strategies** that all need to be accounted for.

### What Kernel2 Actually Does

The main mutual block in `Ix/Kernel2/Infer.lean` (lines 59–1986) contains
42 functions. The full algorithm for `isDefEq` is:

```
1. Quick pre-check (pointer eq, sort eq, lit eq)
2. EquivManager transitive check (union-find cache)
3. Pointer success/failure cache lookup
4. whnfCore (NO delta):
   a. Projection reduction (struct.field → field value)
   b. Iota reduction (recursor on constructor → rule RHS)
   c. K-reduction (Prop inductive with single ctor)
   d. Struct eta iota (eta-expand major via projections)
   e. Quotient reduction (Quot.lift/Quot.ind on Quot.mk)
5. Proof irrelevance (both Prop → compare types only)
6. Lazy delta (hint-guided, single-step unfolding)
   a. isDefEqOffset (Nat.succ chain comparison)
   b. Nat primitive reduction
   c. Native reduction (reduceBool/reduceNat)
   d. Same-head short-circuit with failure cache
7. Full WHNF (whnfCore + delta + native + nat prims, cached)
8. isDefEqCore (structural comparison in WHNF):
   a. Sorts (level equivalence)
   b. Literals (value equality)
   c. Neutrals (head match → spine comparison)
   d. Constructors (addr/levels match → spine comparison)
   e. Lambdas (domain eq, bodies under fresh binder)
   f. Pis (domain eq, codomains under fresh binder)
   g. Eta (lam vs non-lam: eta-expand one side)
   h. Projections (addr/idx match → struct/spine)
   i. Nat lit ↔ ctor expansion
   j. String lit ↔ ctor expansion
   k. Structure eta (mk(proj₀,...,projₙ) ≡ struct)
   l. Unit-like types (0-field single-ctor → types only)
9. Cache result (union-find on success, content key on failure)
```

### Reduction Strategies That Need Formalization

Each reduction strategy must be proven sound — i.e., if Kernel2 considers
two terms definitionally equal via this strategy, they must be related by
`IsDefEq` in the typing judgment.

#### 1. Delta Reduction (definition unfolding)

`deltaStepVal` (Infer.lean:428) unfolds a constant to its definition body.
Soundness: the `extra` rule in `IsDefEq` handles this — each definition
`c := body : type` adds a defeq `c ≡ body : type` to `env.defeqs`.

**Formal requirement**: `SEnv.addDefn` must record the appropriate `SDefEq`.
Lazy delta's hint-guided strategy (reducibility hints: regular,
semireducible, irreducible) is a completeness optimization, not a soundness
concern — it chooses *which* side to unfold first but cannot introduce
unsound equalities.

#### 2. Iota Reduction (recursor on constructor)

`tryIotaReduction` (Infer.lean:203) fires when a recursor is applied to a
constructor. It selects the matching minor premise by constructor index and
applies it to the constructor's fields.

**Formal requirement**: The `extra` rule must encode iota: for each
recursor rule, `rec.{us} params motive minors (ctor.{us} params fields)`
≡ `rule params motive minors fields`. This requires:
- Well-formed inductive declarations (`SInductDecl`)
- Recursor type construction
- Iota rule: `rec (ctor fields) ≡ minor fields`
- Special case: Nat literal 0 treated as `Nat.zero`

#### 3. K-Reduction

`tryKReductionVal` (Infer.lean:278) applies to Prop inductives with a
single constructor that has no fields (e.g., `Eq.refl`). The recursor
returns the minor premise directly without needing the major premise to
be a constructor.

**Formal requirement**: K-axiom for qualifying inductives:
`rec motive minor major ≡ minor` when the inductive is subsingleton
(K-like). The `validateKFlag` function (Infer.lean:1672) checks the
preconditions.

#### 4. Projection Reduction

Projection of a structure field: `s.fieldᵢ` reduces when `s` is a
constructor application. `proj typeName i (ctor args) ≡ args[numParams + i]`.

**Formal requirement**: Projection reduction rule as an `extra` defeq.
Must validate that the type is a single-constructor inductive and the
field index is in range.

#### 5. Quotient Reduction

`tryQuotReduction` (Infer.lean:340) handles:
- `Quot.lift f h (Quot.mk r a) ≡ f a`
- `Quot.ind p h (Quot.mk r a) ≡ h a`

**Formal requirement**: Quotient axioms as `extra` defeqs. The quotient
computation rule is: lift applied to mk produces the function applied to
the argument.

#### 6. Eta Reduction

Two forms:
- **Lambda eta**: `(λ x. f x) ≡ f` when `x ∉ FV(f)`. Already in `IsDefEq`
  as the `eta` rule.
- **Structure eta**: `⟨s.1, s.2, ...⟩ ≡ s` for structure types. Handled
  by `tryEtaStructCoreVal` (Infer.lean:1378).

**Formal requirement**: Lambda eta is in the judgment. Structure eta needs
an `extra` defeq or a dedicated judgment rule encoding
`mk (proj₀ s) ... (projₙ s) ≡ s` for single-constructor inductives.

#### 7. Proof Irrelevance

`isDefEqProofIrrel` (Infer.lean:1328): if the type is `Prop` (Sort 0),
any two proofs are definitionally equal.

**Formal requirement**: Already in `IsDefEq` as the `proofIrrel` rule.

#### 8. Nat Primitive Reduction

`tryReduceNatVal` (Infer.lean:451) reduces closed Nat arithmetic:
`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.mod`, `Nat.div`, `Nat.gcd`,
`Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`.

**Formal requirement**: Each primitive reduction must be proven sound.
The `validatePrimitive` function (Infer.lean:1479, Primitive.lean) checks
that primitive definitions have the correct recursive structure. The
computation rules (e.g., `Nat.add a (Nat.succ b) ≡ Nat.succ (Nat.add a b)`)
are `extra` defeqs derived from the definition.

#### 9. Literal ↔ Constructor Expansion

`natLitToCtorThunked` (Infer.lean:1301): converts `natVal n` to
`Nat.succ^n(Nat.zero)`. `strLitToCtorThunked` (Infer.lean:1312): converts
string literals to `List Char` constructor form.

**Formal requirement**: `extra` defeqs relating each literal to its
constructor encoding.

#### 10. Unit-Like Reduction

`isDefEqUnitLikeVal` (Infer.lean:1402): for types with a single
zero-field non-recursive constructor, any two values of that type are
defeq (compare types only).

**Formal requirement**: This is a consequence of proof irrelevance +
the fact that unit-like types are subsingletons. Needs: unique typing
for the single constructor, proof that all values equal the constructor.

#### 11. Native Reduction

`reduceNativeVal` (Infer.lean:478): reduces `@[reduceBool]` and
`@[reduceNat]` marked constants by evaluating them and extracting the
literal result.

**Formal requirement**: Trusted reduction — the native evaluator must
produce the correct result. This is an axiom in the formalization:
native reduction is sound if the native evaluator agrees with the
definitional reduction.

### How `extra` Defeqs Encode Reductions

The `extra` rule in `IsDefEq` is the catch-all for reductions beyond
beta/zeta/eta/proof-irrel. The `SEnv.defeqs` predicate must be populated
with:

| Reduction | LHS | RHS |
|-----------|-----|-----|
| Delta | `c.{us}` | `body.{us}` (definition body) |
| Iota | `rec.{us} params motive minors (ctor fields)` | `minor fields` |
| K | `rec.{us} motive minor major` | `minor` (for K-inductives) |
| Projection | `proj typeName i (ctor args)` | `args[numParams + i]` |
| Quot.lift | `Quot.lift f h (Quot.mk r a)` | `f a` |
| Quot.ind | `Quot.ind p h (Quot.mk r a)` | `h a` |
| Struct eta | `mk (proj₀ s) ... (projₙ s)` | `s` |
| Nat prim | `Nat.add (natVal m) (natVal n)` | `natVal (m + n)` |
| Lit↔ctor | `natVal n` | `Nat.succ^n(Nat.zero)` |

The `Params` typeclass in lean4lean abstracts over `extra_pat` — patterns
for which extra reductions fire. Ix can use the same mechanism, with the
`SEnv` populated by `addDefn`, `addInduct`, `addQuot`, etc.


## Part X: Declaration Checking

Beyond expression-level type checking, Kernel2 validates declarations.
This is where inductives, constructors, and recursors are checked.

### What `checkIndBlock` Does (Infer.lean:1817)

1. **Check inductive type**: type must be a well-formed sort-returning
   telescope.
2. **Check constructors**: each constructor's type must:
   - Return the correct inductive applied to the right parameters
   - Satisfy strict positivity (the inductive doesn't appear in negative
     positions in constructor argument types)
   - Satisfy universe constraints (field universes ≤ inductive universe)
3. **Build recursor type**: the recursor's type is derived from the
   inductive's structure (motive, minors, major).
4. **Check recursor rules**: each rule must type-check and match its
   constructor.
5. **Validate K-flag**: K-reduction is only enabled for Prop inductives
   with a single zero-field constructor.
6. **Check elimination level**: the recursor's universe must be compatible
   with the inductive's universe (large elimination restrictions).

### Formal Requirements

- `SInductDecl` with well-formedness predicate
- Positivity checker formalization (or axiomatize it)
- Recursor type construction proven correct
- Universe constraint checking
- `SEnv.addInduct` that adds the inductive, constructors, and recursor
  to the environment with all necessary `defeqs`

lean4lean's `Theory/Inductive.lean` is heavily sorry'd (2 main sorries for
`VInductDecl.WF` and `VEnv.addInduct`). This is the hardest part of the
formalization for both projects.


## Part XI: Cache and Thunk Correctness

### Thunk Semantics

Kernel2 uses call-by-need thunks (`ThunkEntry` in `TypecheckM.lean`).
Each thunk is either unevaluated `(expr, env)` or evaluated `val`.
`forceThunk` memoizes: on first force, evaluate and replace; on subsequent
forces, return cached value.

**Invariant**: Forcing a thunk always produces the same value. Since
`eval` is deterministic (given sufficient fuel), this holds as long as
the expression and environment don't change between forces.

**Formalization approach**: The Theory specification uses strict evaluation
(no thunks). The Verify bridge defines:

```
inductive TrThunk (table : ThunkTable) (am : AddrMap) : Nat → SVal → Prop
  | evaluated : table[id] = .evaluated v → TrVal am v sv → TrThunk table am id sv
  | unevaluated : table[id] = .unevaluated e env →
      TrExpr am e se → TrVals am env senv →
      (∃ fuel, eval_s fuel se senv = some sv) →
      TrThunk table am id sv
```

A thunk translates to the `SVal` that forcing it would produce.

### EquivManager (Union-Find)

`EquivManager.lean` implements union-find on pointer addresses. After
`isDefEq v₁ v₂` succeeds, the pointers of `v₁` and `v₂` are merged.
Future `isDefEq` queries check the union-find first for transitivity.

**Invariant**: If two pointers are in the same equivalence class, their
values are definitionally equal.

**Formalization approach** (following lean4lean's `EquivManager.WF`):

```
structure EquivManager.WF (m : EquivManager) where
  defeq : m.isEquiv ptr₁ ptr₂ → IsDefEq env U Γ (deref ptr₁) (deref ptr₂) A
```

### Pointer-Based Caches

Kernel2 maintains three caches:
- **ptrSuccessCache**: `(ptr₁, ptr₂) → ()` — these pointers were proven
  def-eq.
- **ptrFailureCache**: `(ptr₁, ptr₂) → (val₁, val₂)` — these were proven
  NOT def-eq, with the actual values stored for validation (since pointers
  could be reused after GC).
- **whnfCache**: `ptr → (whnf_val, type_val)` — WHNF result cached by
  input pointer.

**Formalization concern**: Pointer identity is not value identity in
general. Within a single `ST` session, `Rc` pointers are stable (no GC
during type checking). The `σ` type parameter in `TypecheckM σ m` ensures
this via ST's region discipline.

For the formalization, caches must be proven correct: a cache hit must
return the same answer as recomputation would. A false positive in the
success cache would be unsound (claiming def-eq when it isn't). The
content-based failure cache mitigates pointer reuse by storing the actual
values and re-validating on hit.


## Part XII: The Verification Bridge

### lean4lean's Pattern

lean4lean uses a **monadic WF predicate** approach:

```
-- "If action succeeds, postcondition holds"
def M.WF (ctx : VContext) (state : VState) (action : M α)
         (post : α → VState → Prop) : Prop :=
  state.WF ctx →
  ∀ a s', action ctx.toContext state.toState = .ok (a, s') →
    ∃ vs', vs'.toState = s' ∧ state ≤ vs' ∧ vs'.WF ctx ∧ post a vs'
```

Key elements:
- **VContext**: logical context (env + local context + translation)
- **VState**: imperative state (caches, name generator, equiv manager)
- **VState.WF**: caches are consistent, name generator is fresh
- **Monotonicity**: `state ≤ vs'` — state only grows

For each function `f`, prove `f.WF` — if `f` returns successfully, the
result satisfies the postcondition and the state remains well-formed.
Chain these with `M.WF.bind` (monadic composition preserves WF).

### Adapting for Ix/Kernel2

Ix's `TypecheckM σ m` is `ReaderT (TypecheckCtx σ m) (StateT (TypecheckState σ m) (EST σ TcError))`.

The Verify bridge would define:

```
structure VCtx (σ : Type) (m : MetaMode) where
  ctx : TypecheckCtx σ m
  senv : SEnv                        -- logical environment
  trenv : TrEnv ctx.kenv senv        -- env translation
  vlctx : VLCtx                      -- logical local context
  vlctx_eq : TrLCtx ctx.types vlctx  -- context translation

def TypecheckM.WF (vctx : VCtx σ m) (state : TypecheckState σ m)
    (action : TypecheckM σ m α) (post : α → TypecheckState σ m → Prop) : Prop :=
  state.WF vctx →
  ∀ a s', action vctx.ctx state = .ok (a, s') →
    state ≤ s' ∧ s'.WF vctx ∧ post a s'
```

Then prove WF lemmas for each function in the mutual block:

```
theorem eval.WF : TrExprS am e se → TrVals am env senv →
    TypecheckM.WF vctx state (eval e env) fun v s' =>
      ∃ sv, TrVal am v sv ∧ (∃ fuel, eval_s fuel se senv = some sv)

theorem isDefEq.WF : TrVal am v₁ sv₁ → TrVal am v₂ sv₂ →
    TypecheckM.WF vctx state (isDefEq v₁ v₂) fun b s' =>
      b → ∃ e₁ e₂, IsDefEq senv U Γ e₁ e₂ A

theorem infer.WF : TrExprS am e se →
    TypecheckM.WF vctx state (infer e) fun (ty, _) s' =>
      ∃ sty, TrVal am ty sty ∧ HasType senv U Γ se sty
```

### Challenges Specific to Ix

1. **Partial functions**: Kernel2's mutual block is `partial`. Cannot do
   structural induction. Must use the fuel-based Theory spec as the
   induction backbone, then show the `partial` implementation agrees.

2. **42-function mutual block**: lean4lean's verify proofs are organized
   per-function but the mutual block makes dependencies circular. Need
   careful staging (e.g., prove eval.WF before isDefEq.WF, since isDefEq
   calls eval but not vice versa at the base level).

3. **Thunk indirection**: Every spine element is a thunk ID, not a value.
   Translation relations must thread through the thunk table.

4. **Constructor/projection values**: Kernel2's `Val` has `ctor` and
   `proj` variants that `SVal` lacks. The translation must map these:
   - `Val.ctor addr lvls name cidx nParams nFields iAddr spine` →
     `SVal.neutral (.const addr lvls) (params ++ fields)` (or a dedicated
     `SCtor` in an extended `SVal`)
   - `Val.proj typeAddr idx struct spine` → evaluated via projection
     reduction or remains neutral

5. **MetaMode erasure**: Kernel2 has `MetaMode` (`.meta` vs `.anon`).
   The `.anon` mode erases names/binder info. The translation must
   handle both modes (verify `.anon` suffices for soundness).


## Part XIII: What's Needed for Real Confidence

Summarizing everything, here is the full picture of what must be proven
for high confidence in Kernel2's correctness:

### Tier 1: Core Type Theory (Phases 0–6)

This validates the NbE approach itself:

- [ ] Universe level algebra (`SLevel`, equivalence, instantiation)
- [ ] Parameterized `SExpr`/`SVal` with level polymorphism
- [ ] Well-formed environments and declarations
- [ ] Typing judgment (`IsDefEq` inductive)
- [ ] Weakening, substitution, context conversion
- [ ] **NbE soundness**: eval preserves typing, quote reflects typing
- [ ] **Confluence via NbE**: def-eq terms have same normal form

### Tier 2: Reduction Soundness (extends Tier 1)

Each reduction strategy proven sound w.r.t. the typing judgment:

- [ ] Delta reduction (definition unfolding)
- [ ] Iota reduction (recursor on constructor)
- [ ] K-reduction (subsingleton elimination)
- [ ] Projection reduction (structure field extraction)
- [ ] Quotient reduction (Quot.lift/Quot.ind computation)
- [ ] Structure eta (mk(proj₀,...,projₙ) ≡ struct)
- [ ] Nat primitive operations (14 operations)
- [ ] Literal ↔ constructor expansion
- [ ] Unit-like subsingleton reduction

### Tier 3: Inductive Types (extends Tier 2)

- [ ] Well-formed inductive declarations
- [ ] Strict positivity checking
- [ ] Constructor type validation
- [ ] Recursor type construction and soundness
- [ ] Universe constraint checking (large elimination)
- [ ] K-flag validation
- [ ] Mutual inductive blocks

### Tier 4: Metatheory (extends Tier 3)

- [ ] Strong typing (all sub-derivations have types)
- [ ] Unique typing (types unique up to defeq)
- [ ] Subject reduction (reduction preserves typing)
- [ ] Consistency (not all types are equal)

### Tier 5: Verification Bridge (extends Tier 4)

Connect Kernel2 implementation to Theory specification:

- [ ] Translation relations (`TrExpr`, `TrVal`, `TrThunk`, `TrEnv`)
- [ ] `eval.WF` — Kernel2 eval agrees with `eval_s`
- [ ] `isDefEq.WF` — Kernel2 isDefEq implies `IsDefEq`
- [ ] `infer.WF` — Kernel2 infer implies `HasType`
- [ ] `whnfVal.WF` — WHNF preserves meaning
- [ ] `checkConst.WF` — declaration checking is sound
- [ ] Cache correctness (EquivManager, pointer caches)
- [ ] Thunk determinism (forcing is idempotent)

### Tier 6: End-to-End (extends Tier 5)

- [ ] `checkIndBlock` — inductive block validation is sound
- [ ] `addDecl` — adding a declaration preserves env well-formedness
- [ ] Top-level: if Ix accepts an environment, it is well-typed

### Estimated Effort

| Tier | LOC | Sorries target | Confidence gain |
|------|-----|----------------|-----------------|
| 1 | ~3,000 | 0 | NbE approach is sound |
| 2 | ~2,000 | 0 | All reductions are sound |
| 3 | ~2,000 | 2–4 | Inductives are sound |
| 4 | ~3,000 | 0–2 | Full metatheory |
| 5 | ~5,000 | 5–10 | Implementation matches spec |
| 6 | ~1,000 | 0–2 | End-to-end correctness |

Tiers 1–2 give strong confidence that the *theory* is right. Tiers 1–4
match lean4lean's coverage. Tiers 1–6 give full implementation
verification (beyond lean4lean, which has ~15 sorries in its verify
layer).


## Part XIV: Key References

- `Ix/Theory/Roundtrip.lean` — `nbe_stable`, `nbe_idempotent`, fuel monotonicity
- `Ix/Theory/DefEq.lean` — `isDefEq_sound`, symmetry, reflexivity
- `Ix/Theory/EvalWF.lean` — `eval_preserves_wf`, `apply_preserves_wf`
- `Ix/Theory/Expr.lean` — substitution algebra (`liftN`, `inst`, `ClosedN`)
- `Ix/Theory/WF.lean` — `ValWF`, `EnvWF`, monotonicity
- `lean4lean/Lean4Lean/Theory/VLevel.lean` — `VLevel`, `WF`, `Equiv`
- `lean4lean/Lean4Lean/Theory/VEnv.lean` — `VConstant`, `VDefEq`, `VEnv`
- `lean4lean/Lean4Lean/Theory/Typing/Basic.lean` — `IsDefEq` judgment
- `lean4lean/Lean4Lean/Theory/Typing/Lemmas.lean` — weakening, substitution
- `lean4lean/Lean4Lean/Theory/VExpr.lean` — `VExpr`, `instL`, substitution algebra
