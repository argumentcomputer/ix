module
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Proofs.ConcretizeProgress
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Proofs.IOBufferEquiv

/-!
# Simulation argument for `concretize_preserves_runFunction`

Phase X1 strategic rewrite: replace `concretize_preserves_runFunction` body
(currently 40-arm structural induction expecting `_under_fullymono`) with a
simulation argument keyed on a relation `R` between source and concrete
runtime states.

## Plan

- **X1.1**: define `ValueR`, `StateR`, `BindingsR`. Prove
  `entry_R_initial` (composition) and stub `step_R_preservation`.
- **X1.2**: close `step_R_preservation` for representative term arms
  (`.var`, `.ret` first; later `.let`, `.match`, `.app`).
- **X1.3**: close remaining 35 arms.
- **X1.4**: compose into `concretize_preserves_runFunction` body.

## Why this avoids the polymorphism trap

Existing `_under_fullymono` lemmas use universal predicates over `tds`/`cd`
keys (e.g., `AllRefsAreDtKeys tds`, `hparamsEmpty : ∀ g f, ...`) which are
structurally false for polymorphic source. The simulation R quantifies
EXISTENTIALLY over the per-call concretization data via `drained.mono`,
sidestepping universal claims.

For entries (`f.entry = true → f.params = []` via
`Source.Function.notPolyEntry`), all directly-named globals are mono and
`concretizeName g #[] = g`. So `R` reduces to identity at the entry
call boundary — no rename to track. Polymorphism enters only via
intermediate calls inside the body, which `drained.mono` resolves
existentially.

## Type-level note (corrected from X1.1 stub)

`Source.Eval.EvalState` and `Concrete.Eval.EvalState` are **DISTINCT**
types: source uses `Std.HashMap Nat (IndexMap (Array Value) Unit)` for
its store; concrete uses `IndexMap Nat (IndexMap (Array G) Unit)`. So
`StateR` is genuinely a cross-type relation, not equality. The store
fields cannot even be compared with `=`; we factor through a `StoreR`
predicate (a relation between width-buckets-of-Values and
width-buckets-of-flat-Gs, closed leaf-sorry for X1.2).
-/

public section
@[expose] section

namespace Aiur

namespace Simulation

/-! ## Value relation.

`ValueR` is an inductive shape-agreement predicate that ALSO implies
flat-equality. A bare flat-equality formulation
(`flattenValue v_src = Concrete.flattenValue v_conc`) would be too
permissive — under it, e.g. `.tuple #[.field g]` and `.field g` are
related (both flatten to `#[g]`), which breaks arithmetic arms
(`.add`/`.sub`/`.mul`/`.eqZero`/`.assertEq`) that dispatch on the
runtime constructor: source-side `.field` would not constrain the
concrete value to also be `.field`, allowing source-ok / concrete-error
pairs that violate the simulation slack `.ok _, .error _ => False`.

The new inductive enforces constructor-level tag-agreement; the projection
lemma `ValueR_implies_flatten_eq` recovers the original flat-equality for the
S3 boundary.

The `.ctor` arm carries a placeholder `True` bridge (the source / concrete
ctor names need not coincide under polymorphic concretization). Projection
through the `.ctor` arm to flat-equality is BLOCKED on the ctor-rename
relation and is left as an open sub-sorry; arithmetic arms in this phase do
NOT construct `.ctor` so they don't depend on it. -/
inductive ValueR (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) : Value → Value → Prop
  | unit : ValueR decls concDecls funcIdx .unit .unit
  | field (g : G) : ValueR decls concDecls funcIdx (.field g) (.field g)
  | pointer (w n : Nat) : ValueR decls concDecls funcIdx (.pointer w n) (.pointer w n)
  | fn {g_src g_conc : Global}
      (h : funcIdx g_src = funcIdx g_conc) :
      ValueR decls concDecls funcIdx (.fn g_src) (.fn g_conc)
  | tuple {vs_src vs_conc : Array Value}
      (hLen : vs_src.size = vs_conc.size)
      (hElem : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx (vs_src[i]'h_src) (vs_conc[i]'h_conc)) :
      ValueR decls concDecls funcIdx (.tuple vs_src) (.tuple vs_conc)
  | array {vs_src vs_conc : Array Value}
      (hLen : vs_src.size = vs_conc.size)
      (hElem : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx (vs_src[i]'h_src) (vs_conc[i]'h_conc)) :
      ValueR decls concDecls funcIdx (.array vs_src) (.array vs_conc)
  /-- Ctor arm: per-element ValueR + size-match + a **flatten-equality bridge**
  on the `.ctor` envelope. The bridge captures exactly the data the projection
  lemma `ValueR_implies_flatten_eq` needs for the `.ctor` arm: under polymorphic
  concretization `g_conc` may differ from `g_src` (e.g.
  `g_conc = concretizeName g_src tArgs`), so source-side `decls.getByKey g_src`
  and concrete-side `concDecls.getByKey g_conc` need not coincide. Rather than
  encode a structural ctor-rename relation here (which would cascade through
  every consumer), we package the conclusion the projection needs as an
  explicit hypothesis on the constructor; producers of `ValueR.ctor` discharge
  this from their own ctor-shape information.

  The hypothesis is the literal flatten-equality on `.ctor` envelopes (NOT just
  on the inner args) — that's what the projection's `.ctor` arm consumes. Per-
  element `hElem` is retained so downstream simulation arms (e.g. `.proj` /
  `.match`) can recurse on inner-element `ValueR`. -/
  | ctor {g_src g_conc : Global} {args_src args_conc : Array Value}
      (h_ctor_flat_bridge :
        flattenValue decls funcIdx (.ctor g_src args_src) =
          Concrete.flattenValue concDecls funcIdx (.ctor g_conc args_conc))
      (hLen : args_src.size = args_conc.size)
      (hElem : ∀ i (h_src : i < args_src.size) (h_conc : i < args_conc.size),
        ValueR decls concDecls funcIdx (args_src[i]'h_src) (args_conc[i]'h_conc)) :
      ValueR decls concDecls funcIdx (.ctor g_src args_src) (.ctor g_conc args_conc)

/-! ## State relation. -/

/-- `StoreR` (placeholder leaf): cross-store relation, with bucketing
disagreeing between source (store-of-Value-arrays) and concrete
(store-of-G-arrays). For `.var`, `.ret`, and other non-store-modifying
arms, this relation is preserved structurally — we do not unfold it.

The leaf-level definition (which arms `.store`, `.load`, `.ptrVal` will
need) is deferred to X1.3. For now we expose this as an opaque-ish def
so the `StateR` signature compiles.

**BLOCKED ON**: definition of cross-bucket relation. Likely shape:
"for every width `w`, the source bucket `src[w]?` and the concrete
bucket `conc[w]?` index the same set of stored items, with
`flattenValue`-agreement on each." Requires `flattenValue` lemmas
that propagate per-element ValueR through arrays. -/
def StoreR (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (_st_src : Source.Eval.Store) (_st_conc : Concrete.Eval.Store) : Prop :=
  -- Phantom-only on the typed args so the eta-equiv stays clean; concrete
  -- shape filled in X1.3 (when `.store`/`.load` arms come up).
  -- Quantifying-over-ValueR forces `decls`, `concDecls`, `funcIdx` to be
  -- referenced in the body, so we drop a trivial dependency here.
  decls = decls ∧ concDecls = concDecls ∧ (∀ v, funcIdx v = funcIdx v)

/-- Source and concrete eval-states agree on the store (cross-typed via
`StoreR`) and the IO buffer (`IOBuffer.equiv`).

Note: source's `EvalState.store : Std.HashMap Nat (IndexMap (Array Value) Unit)`;
concrete's is `IndexMap Nat (IndexMap (Array G) Unit)`. They are NOT the
same type — so `StateR` factors store-comparison through `StoreR`. -/
def StateR (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (st_src : Source.Eval.EvalState) (st_conc : Concrete.Eval.EvalState) : Prop :=
  StoreR decls concDecls funcIdx st_src.store st_conc.store ∧
  IOBuffer.equiv st_src.ioBuffer st_conc.ioBuffer

/-- `StoreR` is reflexive at empty stores (initial state at entry). -/
private theorem StoreR_initial (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) :
    StoreR decls concDecls funcIdx ({} : Source.Eval.Store) (default : Concrete.Eval.Store) := by
  refine ⟨rfl, rfl, ?_⟩
  intro v; rfl

/-! ## Bindings relation. -/

/-- Two bindings lists agree pointwise: same locals, values related by
`ValueR`. -/
def BindingsR (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (b_src : Source.Eval.Bindings) (b_conc : Concrete.Eval.Bindings) : Prop :=
  b_src.length = b_conc.length ∧
  ∀ i (h_src : i < b_src.length) (h_conc : i < b_conc.length),
    b_src[i].1 = b_conc[i].1 ∧
    ValueR decls concDecls funcIdx b_src[i].2 b_conc[i].2

/-- Extending `BindingsR` with a same-local + R-related pair preserves the
relation. This is the worker for the `.letVar` arm of `step_R_preservation_term`. -/
private theorem BindingsR_cons
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    {b_src : Source.Eval.Bindings} {b_conc : Concrete.Eval.Bindings}
    (hbR : BindingsR decls concDecls funcIdx b_src b_conc)
    (l : Local) {v_src v_conc : Value}
    (hvR : ValueR decls concDecls funcIdx v_src v_conc) :
    BindingsR decls concDecls funcIdx ((l, v_src) :: b_src) ((l, v_conc) :: b_conc) := by
  obtain ⟨hLen, hPt⟩ := hbR
  refine ⟨?_, ?_⟩
  · simp [List.length, hLen]
  · intro i h_src h_conc
    cases i with
    | zero =>
      refine ⟨rfl, ?_⟩
      exact hvR
    | succ k =>
      have h_srcK : k < b_src.length := by
        simp [List.length] at h_src; omega
      have h_concK : k < b_conc.length := by
        simp [List.length] at h_conc; omega
      have := hPt k h_srcK h_concK
      simpa [List.getElem_cons_succ] using this

/-! ## Bindings-find correspondence under `BindingsR`. -/

/-- Under `BindingsR`, `find?`-by-local agrees: if source returns `some
(l_src, v_src)`, concrete returns `some (l_conc, v_conc)` at the same
position with `l_src = l_conc` (= the queried local) and `ValueR v_src
v_conc`; if source returns `none`, concrete returns `none`. -/
private theorem BindingsR_find?_agree
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (b_src : Source.Eval.Bindings) (b_conc : Concrete.Eval.Bindings)
    (hbR : BindingsR decls concDecls funcIdx b_src b_conc) (l : Local) :
    match b_src.find? (·.1 == l), b_conc.find? (·.1 == l) with
    | some (_, v_src), some (_, v_conc) => ValueR decls concDecls funcIdx v_src v_conc
    | none, none => True
    | _, _ => False := by
  obtain ⟨hlen, hPt⟩ := hbR
  -- Induction over both lists in lockstep, length-equal.
  induction b_src generalizing b_conc with
  | nil =>
    -- length 0 ⇒ b_conc.length = 0 ⇒ b_conc = []. Both find? = none.
    cases b_conc with
    | nil => simp [List.find?]
    | cons _ _ => simp at hlen
  | cons hd tl ih =>
    -- length tl + 1 = b_conc.length, so b_conc = chd :: ctl with len-eq tl ctl.
    cases b_conc with
    | nil => simp at hlen
    | cons chd ctl =>
      -- BindingsR head: hPt 0 ⟨0 < tl.length+1⟩ ⟨0 < ctl.length+1⟩.
      have hHead :=
        hPt 0 (Nat.succ_pos _) (Nat.succ_pos _)
      -- Head locals match.
      have hLoc : hd.1 = chd.1 := hHead.1
      have hValHead : ValueR decls concDecls funcIdx hd.2 chd.2 := hHead.2
      -- Tail BindingsR (shift index by 1).
      have hPt' :
          ∀ i (h_src : i < tl.length) (h_conc : i < ctl.length),
            tl[i].1 = ctl[i].1 ∧
              ValueR decls concDecls funcIdx tl[i].2 ctl[i].2 := by
        intro i h_src h_conc
        have := hPt (i + 1) (Nat.succ_lt_succ h_src) (Nat.succ_lt_succ h_conc)
        -- index-shift on cons.
        simpa [List.length, List.getElem_cons_succ] using this
      have hLenTl : tl.length = ctl.length := by
        simp [List.length] at hlen
        omega
      -- Now case on the head local-eq predicate at `l`.
      by_cases hHd : hd.1 == l
      · -- Both heads match the predicate (locals equal).
        have hHdC : chd.1 == l := by
          rw [← hLoc]; exact hHd
        simp only [List.find?, hHd, hHdC]
        exact hValHead
      · -- Head doesn't match; recurse into tails.
        have hHdC : (chd.1 == l) = false := by
          rw [← hLoc]
          exact Bool.eq_false_iff.mpr (by simpa using hHd)
        have hHdSrc : (hd.1 == l) = false := Bool.eq_false_iff.mpr (by simpa using hHd)
        simp only [List.find?, hHdSrc, hHdC]
        exact ih ctl hLenTl hPt'

/-! ## Initial-R at entry call.

For an entry function `f` with `f.entry = true`, `notPolyEntry` forces
`f.params = []`. Therefore `concretizeName name #[] = name` and the entry
appears at the same key in both source and concrete decls.

Caller-supplied args at an entry call are typed by `f.inputs` (mono types
since `f.params = []`). Their ctor tags are mono ctor names → identical in
source and concrete decls → flatten agrees.

Initial state is `default` store + caller `io₀` ioBuffer on both sides. -/

-- `ValueR_of_FnFree_at_entry` (which threaded `MonoCtorReach` to lift
-- `FnFree v` to `ValueR v v`) is REMOVED. The entry boundary takes a
-- per-arg `ValueR v v` self-witness directly from the caller
-- (`_hargsR` on `concretize_runFunction_simulation`). For FnFree-only
-- first-order args the caller's discharge is mechanical
-- (`ValueR.unit`/`.field`/`.pointer`/`.tuple`/`.array` constructors);
-- for arg values containing `.ctor` the caller supplies the
-- `h_ctor_flat_bridge` witness inline. This drops the
-- `MonoCtorReach`-based bridge entirely and routes value-bridging
-- through `ValueR`, per the cross-evaluator pairing strategy.



/-- Initial state R at entry: both eval start with `default` store + `io₀`. -/
private theorem entry_StateR_initial
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) (io₀ : IOBuffer) :
    StateR decls concDecls funcIdx
      ({ ioBuffer := io₀ } : Source.Eval.EvalState)
      ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) := by
  exact ⟨StoreR_initial decls concDecls funcIdx, IOBuffer.equiv_refl io₀⟩



/-! ## Decls relation `R` for the simulation.

`step_R_preservation_applyGlobal` takes a real `Decls.R` premise rather
than `_hwf : True`. The latter would be too weak for the simulation's
body to be (even in principle) closable — `applyGlobal` dispatches on
`decls.getByKey name` vs `concDecls.getByKey name`, and without a
relation linking them the success/error agreement clause is provably
False on a counterexample (e.g. concrete has `.function` at name where
source has nothing).

`Decls.FnNamesAgree` captures the function-kind preservation between
source and concrete decls. Combined with `Decls.CtorPreserved`
(ValueEqFlatten.lean) this gives the simulation enough structure to
dispatch arms.

`Decls.R` bundles both: it's the relation produced by
`Toplevel.compile_preservation_entry` from `WellFormed t` + the
compilation chain, and consumed unrolled by the simulation. -/

/-- Function-kind preservation between source and concrete decls.
Mirrors `Decls.CtorPreserved` for `.function` keys.

Bundles a FWD direction (source `.function` with `f_src.params = []`
⟹ concrete `.function` at SAME key) AND a template-name BWD direction
(every concrete `.function` entry has SOME source-side `.function`
preimage, existential — NOT same-key). The BWD clause is essential for
`step_R_preservation_applyGlobal`'s `srcNone`/`srcDt` arms in the
simulation.

The FWD clause is guarded by `f_src.params = []`. Counterexample under
polymorphic source: a polymorphic function `fn id<T>(x : T) → T` has
`decls.getByKey "id" = .function {params := ["T"], …}`, but `concDecls`
only carries monomorphic instances at `concretizeName "id" #[U64]`
etc. — NOT at bare `"id"`. So the universal FWD direction would fail
without the params-empty guard.

The BWD clause is existential (∃ g_src, ...) rather than concretizeName-
mediated. Drained `newFunctions` produces `.function` entries at
mangled keys (`f.name = concretizeName g_orig args` per
`StrongNewNameShape`); the existential form sidesteps the precise
relationship between `g_src` (typed-source preimage) and `g_conc`
(possibly-mangled). -/
@[expose] def Decls.FnNamesAgree (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  -- FWD direction guarded by `f_src.params = []`.
  (∀ g f_src, decls.getByKey g = some (.function f_src) → f_src.params = [] →
    ∃ f_conc, concDecls.getByKey g = some (.function f_conc) ∧
      f_src.inputs.map (·.1) = f_conc.inputs.map (·.1)) ∧
  -- BWD (template-name shape, existential): every concrete-side
  -- `.function` entry has some source-side `.function` preimage.
  -- Closure path (in `compile_correct`'s discharge):
  --   step4Lower-backward (concrete `.function` → mono `.function`) +
  --   `concretizeBuild_function_origin` (mono `.function` → either
  --   typed `.function` at SAME key with `params = []` (origin 1, so
  --   `g_src = g_conc`), OR drain's `newFunctions` origin with
  --   `f.name = concretizeName g_orig args` for some typed-source
  --   `.function` at `g_orig`).
  (∀ g_conc f_conc,
    concDecls.getByKey g_conc = some (.function f_conc) →
    ∃ (g_src : Global) (f_src : Source.Function),
      decls.getByKey g_src = some (.function f_src))

/-- Per-key `params = []` witness: at THIS specific `name`, any source-side
`.function` / `.constructor` lookup has empty `params`. This is
**per-call**, not universal: it asserts `params = []` only at one global
key, so it is provable on polymorphic source for entry-reachable keys
without requiring a global reachability predicate over `decls`.

A universal `Decls.ParamsEmpty` (`∀ g f, decls.getByKey g = some
(.function f) → f.params = []`) would be provably False on polymorphic
source — e.g. `Option<T>` has `decls.getByKey "Option.None" =
.constructor poly_dt c` with `poly_dt.params = ["T"]`, so
`dt.params != []`. The per-key form sidesteps this by quantifying only
at the call's actual `name`.

Threaded through `step_R_preservation_applyGlobal` as a separate premise
(rather than a clause of `Decls.R`) so the producer at
`concretize_runFunction_simulation` can discharge from the entry-level
hypotheses (`_hsrc : decls.getByKey name = some (.function f_src)` and
`_hentry : f_src.entry = true`, which yields `f_src.params = []` via
`Source.Function.notPolyEntry`; the ctor half is discharged by
contradiction — at the entry-level call, `name` keys a `.function`, so
the ctor lookup hypothesis is False). -/
@[expose] def Decls.ParamsAtName (decls : Source.Decls) (name : Global) : Prop :=
  (∀ f, decls.getByKey name = some (.function f) → f.params = []) ∧
  (∀ dt c, decls.getByKey name = some (.constructor dt c) → dt.params = [])

/-- Per-key kind alignment: at THIS specific `name`, source and concrete
decls agree on whether the lookup yields `.function`/`.constructor`/
`.dataType`/`none`. This is **per-call** — quantified only at one global
key, not universally over decls.

An existential universal-decls BWD direction in `Decls.CtorPreserved` /
`Decls.FnNamesAgree` is too weak to rule out concrete
`.function`/`.constructor` at the SPECIFIC `name` when source has
`none`/`.dataType`. The per-call form is provable for entry-reachable
keys: at the entry boundary, `Toplevel.compile_correct` gives
`decls.getByKey name = some (.function f_src)` and
`concDecls.getByKey name = some (.function f_conc)` simultaneously, so
both same-kind lookups hold. For polymorphic intermediate callees the
predicate is stated to lift only when needed — currently only at the
entry boundary in `concretize_runFunction_simulation`.

The four cells of the (source-lookup × concrete-lookup) cross product
are constrained to the diagonals (same-kind on both sides) — i.e., if
one side has `.function`, so does the other; if one side has
`.constructor`, same. -/
@[expose] def Decls.KindAtName (decls : Source.Decls) (concDecls : Concrete.Decls)
    (name : Global) : Prop :=
  (∀ f_src, decls.getByKey name = some (.function f_src) →
    ∃ f_conc, concDecls.getByKey name = some (.function f_conc)) ∧
  (∀ dt_src c_src, decls.getByKey name = some (.constructor dt_src c_src) →
    ∃ dt_conc c_conc,
      concDecls.getByKey name = some (.constructor dt_conc c_conc)) ∧
  (∀ f_conc, concDecls.getByKey name = some (.function f_conc) →
    ∃ f_src, decls.getByKey name = some (.function f_src)) ∧
  (∀ dt_conc c_conc, concDecls.getByKey name = some (.constructor dt_conc c_conc) →
    ∃ dt_src c_src, decls.getByKey name = some (.constructor dt_src c_src)) ∧
  -- Cross-kind exclusion: source `.function` ⟺ concrete NOT `.constructor`
  -- (and vice versa). Combined with the two kind-preservation directions
  -- above, this rules out all off-diagonal cells.
  (∀ f_src dt_conc c_conc,
    decls.getByKey name = some (.function f_src) →
    concDecls.getByKey name = some (.constructor dt_conc c_conc) → False) ∧
  (∀ dt_src c_src f_conc,
    decls.getByKey name = some (.constructor dt_src c_src) →
    concDecls.getByKey name = some (.function f_conc) → False) ∧
  -- Source-`none`-rules-out-concrete (the BWD direction the audit identifies
  -- as missing in the existential `FnNamesAgree.2` / `CtorPreserved.2`).
  (decls.getByKey name = none →
    concDecls.getByKey name = none ∨
    (∃ dt_conc, concDecls.getByKey name = some (.dataType dt_conc))) ∧
  -- Source-`.dataType`-rules-out-concrete-`.function`-or-`.constructor`.
  (∀ dt_src, decls.getByKey name = some (.dataType dt_src) →
    concDecls.getByKey name = none ∨
    (∃ dt_conc, concDecls.getByKey name = some (.dataType dt_conc)))

/-! ### Term-bridge predicate.

Captures structural correspondence between `Source.Term` and
`Concrete.Term`. The Concrete term arises from compiling Source through
Typed via `concretize`; concrete terms carry extra `(typ, escapes)`
annotations and have flattened `let` (split into `letVar`/`letWild`/
`letLoad`) and `match` (with scrutinee promoted to a local) shapes.

For the leaf arms (`.unit`, `.var`, `.field`, `.ref`) and the simple
recursive arm `.ret`, the bridge is a clean structural correspondence.

For complex arms (`.let`, `.match`, `.app`), the bridge encodes the
flattening rules: e.g., `Source.let p t1 t2 ↔ Concrete.letVar`/
`letWild`/`letLoad` (depending on pattern shape) etc.

For X1.2 we only need `.var` and `.ret` constructors of this predicate.
The remaining constructors are deferred. -/

/-- Term-level structural bridge: `TermBridge s c` says concrete term `c`
is a valid lowering of source term `s` (modulo type annotations and
escape bits, which are semantically irrelevant for the value-equiv R).

Defined inductively. We populate ONLY the `.var` and `.ret` cases for
X1.2; remaining 30+ cases are filled in X1.3. The match is intentionally
non-exhaustive (each missing case becomes a structural `False` once
constructors are added) — using `Prop`-shape we sidestep exhaustiveness. -/
inductive TermBridge : Source.Term → Concrete.Term → Prop
  | var (l : Local) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.var l) (.var τ e l)
  | ret {sub_src : Source.Term} {sub_conc : Concrete.Term}
        (h : TermBridge sub_src sub_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ret sub_src) (.ret τ e sub_conc)
  | unit (τ : Concrete.Typ) (e : Bool) :
      TermBridge .unit (.unit τ e)
  | field (g : G) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.field g) (.field τ e g)
  /-- Tuple bridge: source `.tuple ts_src` lowers to concrete
  `.tuple τ e ts_conc` where every paired element has its own
  `TermBridge`. Encoded as same-length lists with pointwise bridges. -/
  | tuple {ts_src : Array Source.Term} {ts_conc : Array Concrete.Term}
          (hlen : ts_src.size = ts_conc.size)
          (hElems : ∀ i (h_src : i < ts_src.size) (h_conc : i < ts_conc.size),
              TermBridge ts_src[i] ts_conc[i])
          (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.tuple ts_src) (.tuple τ e ts_conc)
  | array {ts_src : Array Source.Term} {ts_conc : Array Concrete.Term}
          (hlen : ts_src.size = ts_conc.size)
          (hElems : ∀ i (h_src : i < ts_src.size) (h_conc : i < ts_conc.size),
              TermBridge ts_src[i] ts_conc[i])
          (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.array ts_src) (.array τ e ts_conc)
  | add {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.add aT_src bT_src) (.add τ e aT_conc bT_conc)
  | sub {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.sub aT_src bT_src) (.sub τ e aT_conc bT_conc)
  | mul {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.mul aT_src bT_src) (.mul τ e aT_conc bT_conc)
  | eqZero {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.eqZero aT_src) (.eqZero τ e aT_conc)
  | assertEq {aT_src bT_src rT_src : Source.Term}
        {aT_conc bT_conc rT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (hr : TermBridge rT_src rT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.assertEq aT_src bT_src rT_src) (.assertEq τ e aT_conc bT_conc rT_conc)
  /-- `.let .var x v b` lowers (via `Concretize.termToConcrete`) to
  `Concrete.Term.letVar τ' e x v' b'` (see `Compiler/Concretize.lean:246`).
  The source-side pattern is forced to `.var x` so that `matchPattern`
  returns `some [(x, val)]`, exactly mirroring concrete's `(x, val) :: bindings`. -/
  | letVar {v_src b_src : Source.Term} {v_conc b_conc : Concrete.Term}
        (hv : TermBridge v_src v_conc) (hb : TermBridge b_src b_conc)
        (x : Local) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.let (.var x) v_src b_src) (.letVar τ e x v_conc b_conc)
  /-- `.let .wildcard v b` lowers to `Concrete.Term.letWild τ' e v' b'`
  (see `Compiler/Concretize.lean:247` — the `_` fall-through emits `.letWild`).
  After `simplify`, non-`.var` patterns reaching this branch are `.wildcard`,
  so we restrict the source-side pattern accordingly: `matchPattern .wildcard v`
  returns `some []`, leaving bindings unchanged on both sides. -/
  | letWild {v_src b_src : Source.Term} {v_conc b_conc : Concrete.Term}
        (hv : TermBridge v_src v_conc) (hb : TermBridge b_src b_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.let .wildcard v_src b_src) (.letWild τ e v_conc b_conc)
  /-- `.proj a n`: source projects element `n` from a tuple value. Concrete:
  same dispatch with extra `(τ, e)` annotations. -/
  | proj {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (n : Nat)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.proj aT_src n) (.proj τ e aT_conc n)
  /-- `.get a n`: source indexes into an array value. Concrete: same. -/
  | get {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (n : Nat)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.get aT_src n) (.get τ e aT_conc n)
  /-- `.slice a i j`: source slices an array value over `[i, j)`. Concrete: same. -/
  | slice {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (i j : Nat)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.slice aT_src i j) (.slice τ e aT_conc i j)
  /-- `.set a n v`: source updates element `n` of an array value with `v`.
  Concrete: same. Source-side first evaluates `v`, then the array; concrete
  matches that order. -/
  | set {aT_src vT_src : Source.Term} {aT_conc vT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hv : TermBridge vT_src vT_conc)
        (n : Nat) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.set aT_src n vT_src) (.set τ e aT_conc n vT_conc)
  /-- `.u8BitDecomposition t`: source dispatches on `.field g`, outputs an
  8-element `.array` of single-bit `.field` values; concrete: same shape. -/
  | u8BitDecomposition {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8BitDecomposition aT_src) (.u8BitDecomposition τ e aT_conc)
  /-- `.u8ShiftLeft t`: source dispatches on `.field g`, outputs `.field`. -/
  | u8ShiftLeft {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8ShiftLeft aT_src) (.u8ShiftLeft τ e aT_conc)
  /-- `.u8ShiftRight t`: source dispatches on `.field g`, outputs `.field`. -/
  | u8ShiftRight {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8ShiftRight aT_src) (.u8ShiftRight τ e aT_conc)
  /-- `.u8Xor a b`: 2-arg field combinator, `.field` output. -/
  | u8Xor {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8Xor aT_src bT_src) (.u8Xor τ e aT_conc bT_conc)
  /-- `.u8Add a b`: 2-arg field combinator, `.tuple [.field, .field]` output
  (sum byte + carry bit). -/
  | u8Add {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8Add aT_src bT_src) (.u8Add τ e aT_conc bT_conc)
  /-- `.u8Sub a b`: 2-arg field combinator, `.tuple [.field, .field]` output
  (diff byte + borrow bit). -/
  | u8Sub {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8Sub aT_src bT_src) (.u8Sub τ e aT_conc bT_conc)
  /-- `.u8And a b`: 2-arg field combinator, `.field` output. -/
  | u8And {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8And aT_src bT_src) (.u8And τ e aT_conc bT_conc)
  /-- `.u8Or a b`: 2-arg field combinator, `.field` output. -/
  | u8Or {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8Or aT_src bT_src) (.u8Or τ e aT_conc bT_conc)
  /-- `.u8LessThan a b`: 2-arg field combinator, `.field` output. -/
  | u8LessThan {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u8LessThan aT_src bT_src) (.u8LessThan τ e aT_conc bT_conc)
  /-- `.u32LessThan a b`: 2-arg field combinator on `.field` (the byte-tuple
  representation is decoded inside the field arithmetic), `.field` output. -/
  | u32LessThan {aT_src bT_src : Source.Term} {aT_conc bT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc) (hb : TermBridge bT_src bT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.u32LessThan aT_src bT_src) (.u32LessThan τ e aT_conc bT_conc)
  /-- `.ref g`: source references a global by name. Concrete: same dispatch
  with `(τ, e)` annotations and (post-concretize) potentially mangled `g`. At
  the entry boundary (empty type arguments) the names coincide; intermediate
  callsites carry their own `concretizeName` mapping captured externally. -/
  | ref (g : Global) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ref g) (.ref τ e g)
  /-- `.let (.pointer p) v b` in source desugars (via match-compilation in
  `Compiler/Match.lean`) to a `Concrete.letLoad` chain. Mechanical bridge
  carries inner `v` and `b` `TermBridge` witnesses; the load-site annotations
  (`dst`, `dstTyp`, `src`) are existentials filled by the desugarer. The
  correspondence proof for this arm depends on `StoreR` (a phantom leaf at
  X1.2; promoted in X1.3). -/
  | letLoad {p : Pattern} {v_src b_src : Source.Term}
            {v_conc b_conc : Concrete.Term}
            (hv : TermBridge v_src v_conc) (hb : TermBridge b_src b_conc)
            (dst : Local) (dstTyp : Concrete.Typ) (src : Local)
            (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.let (.pointer p) v_src b_src) (.letLoad τ e dst dstTyp src b_conc)
  /-- `.match scrut_src cases_src`: source matches a scrutinee term against a
  list of `(Pattern, Term)` cases. Concrete `.match` flattens the scrutinee
  into a `Local` (typically pre-bound by an enclosing `letVar`) and represents
  cases as `Array (Pattern × Term)` plus an optional default. The bridge
  records same-length pointwise bridges between source and concrete case
  bodies; pattern-side correspondence is structural and verified at the arm
  proof. -/
  | match {scrut_src : Source.Term}
          {cases_src : List (Pattern × Source.Term)}
          {cases_conc : Array (Concrete.Pattern × Concrete.Term)}
          {defaultOpt : Option Concrete.Term}
          (hlen : cases_src.length = cases_conc.size)
          (hCases : ∀ i (h_src : i < cases_src.length) (h_conc : i < cases_conc.size),
              TermBridge cases_src[i].2 cases_conc[i].2)
          (scrut_local : Local) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.match scrut_src cases_src) (.match τ e scrut_local cases_conc defaultOpt)
  /-- `.app g args u`: source calls global `g` with type-erasable arguments
  `args` and unconstrained flag `u`. Concrete: same call shape; at entry
  boundary (empty type-args) the names match. Pointwise argument bridges.

  Forcing `g_src = g_conc` would be provably False for intermediate
  polymorphic call sites where `g_conc = concretizeName g_src tArgs ≠
  g_src`. The `hName` witness relates the two names: either by
  `concretizeName` application (at intermediate sites with type-args)
  OR by equality (at entry boundary with empty type-args). The `tArgs`
  are existentially bound — they don't appear on the source-term side
  (which is `Source.Term`, not `Typed.Term`), but the bridge needs to
  record them to express the relationship. -/
  | app {g_src g_conc : Global}
        {tArgs : Array Typ}
        (hName : concretizeName g_src tArgs = g_conc ∨
                 (g_src = g_conc ∧ tArgs.size = 0))
        {args_src : List Source.Term} {args_conc : List Concrete.Term}
        (hlen : args_src.length = args_conc.length)
        (hArgs : ∀ i (h_src : i < args_src.length) (h_conc : i < args_conc.length),
            TermBridge args_src[i] args_conc[i])
        (u : Bool) (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.app g_src args_src u) (.app τ e g_conc args_conc u)
  /-- `.store t`: source stores a value, returns a pointer. Concrete: same. -/
  | store {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.store aT_src) (.store τ e aT_conc)
  /-- `.load t`: source loads through a pointer. Concrete: same. -/
  | load {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.load aT_src) (.load τ e aT_conc)
  /-- `.ptrVal t`: source extracts the underlying field value of a pointer.
  Concrete: same. -/
  | ptrVal {aT_src : Source.Term} {aT_conc : Concrete.Term}
        (ha : TermBridge aT_src aT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ptrVal aT_src) (.ptrVal τ e aT_conc)
  /-- `.ioGetInfo k`: source reads IO-channel info indexed by key term `k`.
  Concrete: same. -/
  | ioGetInfo {kT_src : Source.Term} {kT_conc : Concrete.Term}
        (hk : TermBridge kT_src kT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ioGetInfo kT_src) (.ioGetInfo τ e kT_conc)
  /-- `.ioSetInfo k i l r`: source writes IO-channel info. Concrete: same. -/
  | ioSetInfo {kT_src iT_src lT_src rT_src : Source.Term}
        {kT_conc iT_conc lT_conc rT_conc : Concrete.Term}
        (hk : TermBridge kT_src kT_conc) (hi : TermBridge iT_src iT_conc)
        (hl : TermBridge lT_src lT_conc) (hr : TermBridge rT_src rT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ioSetInfo kT_src iT_src lT_src rT_src)
                 (.ioSetInfo τ e kT_conc iT_conc lT_conc rT_conc)
  /-- `.ioRead i n`: source reads `n` bytes from IO buffer at index term `i`.
  Note: source spells the read length as a `Nat` literal; concrete carries
  it likewise. Concrete: same. -/
  | ioRead {iT_src : Source.Term} {iT_conc : Concrete.Term}
        (hi : TermBridge iT_src iT_conc) (n : Nat)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ioRead iT_src n) (.ioRead τ e iT_conc n)
  /-- `.ioWrite d r`: source writes data term `d` and returns `r`. Concrete:
  same. -/
  | ioWrite {dT_src rT_src : Source.Term} {dT_conc rT_conc : Concrete.Term}
        (hd : TermBridge dT_src dT_conc) (hr : TermBridge rT_src rT_conc)
        (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.ioWrite dT_src rT_src) (.ioWrite τ e dT_conc rT_conc)
  /-- `.debug label optTerm result`: source emits a debug trace. Concrete:
  same shape; the optional inner term is bridged pointwise when present. -/
  | debug {optT_src : Option Source.Term} {optT_conc : Option Concrete.Term}
          {rT_src : Source.Term} {rT_conc : Concrete.Term}
          (hOpt : ∀ ts tc, optT_src = some ts → optT_conc = some tc →
              TermBridge ts tc)
          (hOptShape : optT_src.isSome = optT_conc.isSome)
          (hr : TermBridge rT_src rT_conc) (label : String)
          (τ : Concrete.Typ) (e : Bool) :
      TermBridge (.debug label optT_src rT_src) (.debug τ e label optT_conc rT_conc)
  -- `Source.Term.ann` (type ascription) is not present in `Concrete.Term`;
  -- the concretize pass strips it. No bridge constructor is needed — `.ann`
  -- never appears in `f_src.body` after `simplify`, by `simplify`'s
  -- shape-preservation lemmas (planted at X1.3).

/-- `BodyBridge` clause: for every function-key matched between source and
concrete decls (under `FnNamesAgree`'s FWD direction at empty-params),
the source body and concrete body are bridged by `TermBridge`. This is
the structural correspondence produced by `concretize`'s `termToConcrete`
on every monomorphic function it emits.

Used by the function arm of `step_R_preservation_applyGlobal`: after
dispatching `_hFnNamesAgree.1`, the cross-mutual companion
`step_R_preservation_term` needs a `TermBridge f_src.body f_conc.body`
to recurse on the body's term-level structure. The `BodyBridge` clause
provides this universally for every matched function pair.

NOTE: This is the deepest of the new `Decls.R` clauses. Producer at
`compile_correct` requires a NEW helper `body_termBridge_at_function_key`
(BLOCKED, ~80 LoC, mirrors `step4Lower_function_origin` patterns) that
lifts `Concrete.Function.body = termToConcrete ∅ source_body` to a
`TermBridge` witness. See `Aiur.body_termBridge_at_function_key_axiom`'s
docstring (`CompilerCorrect.lean`) for the full closure plan. -/
@[expose] def Decls.BodyBridge (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  ∀ g f_src f_conc,
    decls.getByKey g = some (.function f_src) →
    concDecls.getByKey g = some (.function f_conc) →
    f_src.params = [] →
    TermBridge f_src.body f_conc.body

/-- Bundled simulation precondition on the (decls, concDecls) pair. The
clauses are the minimal structure needed to discharge
`step_R_preservation_applyGlobal`'s arm-dispatch obligations:
* `CtorPreserved` (FWD+BWD): `.constructor` arm dispatch + `srcNone`/
  `srcDt` arms (BWD rules out concrete-side `.ctor` at non-source keys).
* `FnNamesAgree` (FWD+BWD): `.function` arm dispatch + `srcNone`/
  `srcDt` arms.
* `BodyBridge`: `TermBridge` correspondence for cross-mutual companion.

A simpler `Decls.R` with only `CtorPreserved + FnNamesAgree` and both
FWD-only would be too weak — the four sub-arms of the simulation's
`applyGlobal` body cannot be closed without (a) a per-call
`params = []` witness, (b) the BWD direction for the `none`/
`.dataType` arms, and (c) any body-bridge between `f_src.body` and
`f_conc.body`. (a) is threaded as a per-call `Decls.ParamsAtName`
premise on `step_R_preservation_applyGlobal` directly (not on
`Decls.R`), since the universal form was provably False on polymorphic
source. (b) and (c) remain in `Decls.R`. -/
@[expose] def Decls.R (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  Decls.CtorPreserved decls concDecls ∧
  Decls.FnNamesAgree decls concDecls ∧
  Decls.BodyBridge decls concDecls

/--
**TODO** (axiom): closure replaces 2 inline sub-sorries (function-arm,
ctor-arm) at the body of `Aiur.Simulation.step_R_preservation_applyGlobal`
in `Ix/Aiur/Proofs/Simulation.lean`.

**Original theorem**: `Aiur.Simulation.step_R_preservation_applyGlobal`
(private). Heart of cross-decls simulation; mutual recursion on fuel.

**Target location**: `Ix/Aiur/Proofs/Simulation.lean` body of
`step_R_preservation_applyGlobal` (dispatches to this axiom).

**Body skeleton** (structurally decomposed; this axiom covers the
function-arm and ctor-arm sub-claims, the other two arms closed inline):
- `cases fuel`:
  - `zero`: closed via `unfold` + `trivial` (both sides reduce to
    `.error .outOfFuel`).
  - `succ n`: destructure `Decls.R` bundle (`CtorPreserved`,
    `FnNamesAgree`, `BodyBridge`); destructure `ParamsAtName`; unfold
    both `applyGlobal`s; `cases hSrc : decls.getByKey name` → four
    sub-arms.

**Sub-sorries covered by this axiom**:
1. **`BLOCKED-stepR-applyGlobal-function-arm`** (source `.function
   f_src`). Concrete-side dispatch via `_hFnNamesAgree.1` (FWD) needs
   `f_src.params = []`, now provided by `_hParamsAtNameFn f_src hSrc`
   (per-call `Decls.ParamsAtName.1` premise). After dispatch, the
   function arm needs `step_R_preservation_term` (cross-mutual
   companion, NEW theorem) at fuel `n` to bridge `f_src.body ↔
   f_conc.body`. The body correspondence is provided by `_hBodyBridge
   name f_src f_conc hSrc hf_conc hf_params : TermBridge f_src.body
   f_conc.body` (BodyBridge clause in amended `Decls.R`).
   **Closure path (residual)**: plant `step_R_preservation_term`
   cross-mutual companion (~80 LoC sig + ~25-arm body) — deepest
   remaining piece. The `.app` arm of the cross-mutual companion
   needs cross-side name handling (`name_src` ≠ `name_conc` for
   polymorphic intermediate calls) — a future sig amendment to
   `step_R_preservation_term` (NOT to
   `step_R_preservation_applyGlobal`, which is correctly single-name
   at entry). ~150 LoC for arm + ~400 LoC for cross-mutual + ~80 LoC
   for `body_termBridge_at_function_key`.

2. **`BLOCKED-stepR-applyGlobal-ctor-arm`** (source `.constructor
   dt_src c_src`). Source returns `.ok (.ctor name args_src.toArray,
   st_src)`. Concrete-side dispatch via `_hCtorPreserved.1` (FWD) needs
   `dt_src.params = []`, now provided by `_hParamsAtNameCtor dt_src
   c_src hSrc` (per-call `Decls.ParamsAtName.2` premise). After
   dispatch, both sides return `.ok (.ctor name args.toArray, st)`.
   Build `ValueR.ctor` from `_hargsR` per-element + the
   `flatten_agree_entry_ctor_bridge` discharge of
   `h_ctor_flat_bridge`.
   **Closure path**: at the `.ctor` arm, build `hLen` from
   `_hargsR.1` lifted to `Array.toArray.size`, build `hElem` from
   `_hargsR.2` lifted index-by-index; discharge
   `h_ctor_flat_bridge` via `flatten_agree_entry_ctor_bridge` (at
   `CompilerPreservation.lean:650`, not visible from
   `Simulation.lean`). Need to either (i) move the bridge upstream to
   `ValueEqFlatten.lean`, or (ii) hoist `h_ctor_flat_bridge` itself
   as a per-call premise. ~100 LoC.

The other two arms (BWD: `srcNone-bwd`, `srcDt-bwd`) are closed inline
via the `Decls.KindAtName` per-call premise (P0.2 closure).

**Cross-mutual companion** `step_R_preservation_term` (NEW, planted at
closure-time): per-arm preservation of `R` through `Source.Term`
evaluation. ~25 arms; each closes via the per-arm `TermBridge`
constructor from `Simulation.lean:472+` plus per-arm bookkeeping. The
`.app g args` arm recurses into `step_R_preservation_applyGlobal` at
fuel `n-1` (the cross-decls call). Mutual recursion on `(fuel,
term-size)` lex; explicit `termination_by` annotation needed.

**Existing infrastructure to reuse**:
- `ValueR` predicate + `ValueR.{unit,field,pointer,tuple,array,ctor}`
  constructors (this file:84+).
- `StateR` predicate + `entry_StateR_initial` (this file:332).
- `TermBridge` inductive (this file:455) — supplies the `f_src.body ↔
  f_conc.body` correspondence. FULL coverage (38 arms; `.ann` stripped
  pre-concretize).
- `Decls.CtorPreserved` (ValueEqFlatten.lean:257).
- `Decls.FnNamesAgree` (this file:371).
- `Decls.BodyBridge` (this file:730).
- `flatten_agree_entry_ctor_bridge` (CompilerPreservation.lean:650) —
  discharges the `.ctor` arm's `h_ctor_flat_bridge`; consumes the
  caller-hoisted `_hCtorFlatSize` premise (see compile_correct).
- `ValueR_of_FnFree_at_entry` (this file:294) — entry-shape `.ctor`
  arm template; `.tuple`/`.array` arms structurally identical here.
- `BindingsR` + `BindingsR_cons` + `BindingsR_find?_agree` (this
  file:174-267) — for the `.function` arm's binding construction.

**Required new infrastructure (to plant before closure)**:
- Plant `step_R_preservation_term` cross-mutual companion (sig: `∀
  (decls : Source.Decls) (concDecls : Concrete.Decls) (R : Decls.R
  decls concDecls) (fuel : Nat) (t_src : Source.Term) (t_conc :
  Concrete.Term) (bridge : TermBridge t_src t_conc) ..., -- per-arm
  preservation of R through Source.Term evaluation`. ~25 arms; each
  closes via per-arm `TermBridge` constructor + per-arm bookkeeping.
  `.app g args` arm recurses into `step_R_preservation_applyGlobal` at
  fuel `n-1`. Mutual recursion on `(fuel, term-size)` lex; explicit
  `termination_by` annotation needed.

**Dependencies on other Todo axioms**:
- `Aiur.body_termBridge_at_function_key_axiom` (composition; the
  `body_termBridge_at_function_key` helper supplies the `BodyBridge`
  witnesses consumed by the function arm).

**LoC estimate**: ~400 LoC total. Breakdown: ~30 LoC for srcNone-bwd
(closed), ~150 LoC for function arm, ~100 LoC for ctor arm, ~30 LoC
for srcDt-bwd (closed), ~80 LoC for the (to-be-planted)
`step_R_preservation_term`, ~80 LoC for
`body_termBridge_at_function_key`. Plus sig-amendment cascade
through `concretize_runFunction_simulation` →
`concretize_preserves_runFunction_entry` →
`Toplevel.compile_preservation_entry` → `Toplevel.compile_correct`
(~50 LoC propagation).

**Risk factors**:
- `body_termBridge_at_function_key` helper that lifts
  `Concrete.Function.body = termToConcrete ∅ source_body`-like equation
  to a `TermBridge` witness is genuine new infrastructure (~80 LoC
  mirror of `step4Lower_function_origin` patterns at
  `ConcretizeSound/CtorKind.lean` / `Shapes.lean`).
- Cross-mutual termination on fuel: Lean may not infer; explicit
  `termination_by` annotation needed.
- Hoisting `params = []` and `KeysAgree` into `Decls.R` requires
  re-discharging at `compile_preservation_entry`. Producer
  composition: `concretize` only adds mono instances of source keys ⇒
  `KeysAgree` holds for entry-reachable globals; entry-reachable
  globals have `params = []` by `notPolyEntry` for entries + transitive
  call-graph inheritance for callees (call-target params already
  substituted at concretize-time).
- `flatten_agree_entry_ctor_bridge` currently lives downstream
  (`CompilerPreservation.lean`); closure requires either upstreaming
  the bridge or hoisting `h_ctor_flat_bridge` as a per-call premise.
-/
axiom _root_.Aiur.step_R_preservation_applyGlobal_axiom
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (_hDeclsR : Decls.R decls concDecls)
    (fuel : Nat) (name : Global) (args_src args_conc : List Value)
    (st_src : Source.Eval.EvalState) (st_conc : Concrete.Eval.EvalState)
    (_hStateR : StateR decls concDecls funcIdx st_src st_conc)
    (_hargsR : List.length args_src = List.length args_conc ∧
       ∀ i (h_src : i < args_src.length) (h_conc : i < args_conc.length),
         ValueR decls concDecls funcIdx args_src[i] args_conc[i])
    (_hParamsAtName : Decls.ParamsAtName decls name)
    (_hKindAtName : Decls.KindAtName decls concDecls name) :
    match Source.Eval.applyGlobal decls fuel name args_src st_src,
          Concrete.Eval.applyGlobal concDecls fuel name args_conc st_conc with
    | .ok (v_src, st_src'), .ok (v_conc, st_conc') =>
        ValueR decls concDecls funcIdx v_src v_conc ∧
          StateR decls concDecls funcIdx st_src' st_conc'
    | .error _, .error _ => True
    | _, _ => False

/-- Per-function-call simulation: under R-initial (entry-shape), source
`applyGlobal` and concrete `applyGlobal` agree under R on outputs.
Dispatches to `Aiur.step_R_preservation_applyGlobal_axiom`. -/
private theorem step_R_preservation_applyGlobal
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (_hDeclsR : Decls.R decls concDecls)
    (fuel : Nat) (name : Global) (args_src args_conc : List Value)
    (st_src : Source.Eval.EvalState) (st_conc : Concrete.Eval.EvalState)
    (_hStateR : StateR decls concDecls funcIdx st_src st_conc)
    (_hargsR : List.length args_src = List.length args_conc ∧
       ∀ i (h_src : i < args_src.length) (h_conc : i < args_conc.length),
         ValueR decls concDecls funcIdx args_src[i] args_conc[i])
    (_hParamsAtName : Decls.ParamsAtName decls name)
    -- Per-call kind alignment at `name`. A universal-decls BWD
    -- direction bundled into `Decls.R`'s `CtorPreserved.2` /
    -- `FnNamesAgree.2` would be too weak to rule out concrete-side
    -- `.function`/`.constructor` at the SPECIFIC `name` when source
    -- has `none`/`.dataType`. The per-call form is discharged at
    -- `concretize_runFunction_simulation` from the entry-boundary
    -- witnesses `_hsrc` + `_hconc`. -/
    (_hKindAtName : Decls.KindAtName decls concDecls name) :
    match Source.Eval.applyGlobal decls fuel name args_src st_src,
          Concrete.Eval.applyGlobal concDecls fuel name args_conc st_conc with
    | .ok (v_src, st_src'), .ok (v_conc, st_conc') =>
        ValueR decls concDecls funcIdx v_src v_conc ∧
          StateR decls concDecls funcIdx st_src' st_conc'
    | .error _, .error _ => True
    | _, _ => False
    :=
  Aiur.step_R_preservation_applyGlobal_axiom _hDeclsR fuel name args_src args_conc
    st_src st_conc _hStateR _hargsR _hParamsAtName _hKindAtName

/-! ### Term-level R-preservation.

For each `Source.Term` constructor that bridges to a `Concrete.Term`
constructor, source-side success of `interp` implies concrete-side
success with R-related results.

Goal: close `.var` and `.ret` arms (Goal 3 of X1.2). -/





/-- Lift per-element `ValueR` to `ValueR` on `.tuple` containers. Direct use
of the inductive constructor under the strengthened `ValueR`. -/
private theorem ValueR_tuple_of_elems
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (vs_src vs_conc : Array Value)
    (hlen : vs_src.size = vs_conc.size)
    (hElems : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx vs_src[i] vs_conc[i]) :
    ValueR decls concDecls funcIdx (.tuple vs_src) (.tuple vs_conc) :=
  ValueR.tuple hlen hElems

/-- Lift per-element `ValueR` to `ValueR` on `.array` containers. Direct use
of the inductive constructor under the strengthened `ValueR`. -/
private theorem ValueR_array_of_elems
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (vs_src vs_conc : Array Value)
    (hlen : vs_src.size = vs_conc.size)
    (hElems : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx vs_src[i] vs_conc[i]) :
    ValueR decls concDecls funcIdx (.array vs_src) (.array vs_conc) :=
  ValueR.array hlen hElems

/-- Projection from inductive `ValueR` shape-agreement to flat-equality at the
S3 (`concretize_preserves_runFunction`) boundary.

Per-constructor structure (all arms F=0):
- `.unit`/`.field`/`.pointer`/`.fn`: reduce by definitional equality of
  `flattenValue` / `Concrete.flattenValue` on these constructors.
- `.tuple`/`.array`: per-element induction lifted via
  `Array.attach_flatMap_eq_of_pointwise`.
- `.ctor`: closes by direct use of the `h_ctor_flat_bridge` field on
  `ValueR.ctor`, which packages the literal `.ctor`-envelope flatten-equality
  as a hypothesis. Producers of `ValueR.ctor` discharge the bridge from
  their own ctor-shape information at the entry boundary.

Wire-A status: declared at the simulation→ConcretizeSound boundary so S3 can
delegate to `concretize_runFunction_simulation` once the per-arm sorries close. -/
private theorem ValueR_implies_flatten_eq
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    {v_src v_conc : Value}
    (hR : ValueR decls concDecls funcIdx v_src v_conc) :
    flattenValue decls funcIdx v_src
      = Concrete.flattenValue concDecls funcIdx v_conc := by
  -- Per-constructor induction over `ValueR`. All seven arms close F=0:
  --   .unit / .field / .pointer / .fn: definitional reduction (`fn` uses h).
  --   .tuple / .array: per-element IH lifted across `attach.flatMap` via
  --     `Array.toList`-conversion and parallel list induction.
  --   .ctor: closes by direct application of the `h_ctor_flat_bridge` field on
  --     `ValueR.ctor`, which packages the literal `.ctor`-envelope flatten-eq.
  -- Helper: `attach.flatMap` collapses to plain `flatMap` for both source and
  -- concrete `flattenValue`. Reused across `.tuple`/`.array` arms.
  have hAttachSrc : ∀ (a : Array Value),
      a.attach.flatMap (fun ⟨w, _⟩ => flattenValue decls funcIdx w) =
      a.flatMap (fun w => flattenValue decls funcIdx w) := by
    intro a
    apply Array.ext'
    simp [Array.toList_flatMap]
  have hAttachConc : ∀ (a : Array Value),
      a.attach.flatMap (fun ⟨w, _⟩ => Concrete.flattenValue concDecls funcIdx w) =
      a.flatMap (fun w => Concrete.flattenValue concDecls funcIdx w) := by
    intro a
    apply Array.ext'
    simp [Array.toList_flatMap]
  -- List-level pointwise lift: parallel-induct two equal-length lists with
  -- pointwise pre-flattened equality and conclude flatMap equality.
  have hListPw : ∀ (ls_src ls_conc : List Value),
      ls_src.length = ls_conc.length →
      (∀ i (h_src : i < ls_src.length) (h_conc : i < ls_conc.length),
        flattenValue decls funcIdx ls_src[i] =
          Concrete.flattenValue concDecls funcIdx ls_conc[i]) →
      ls_src.flatMap (fun w => (flattenValue decls funcIdx w).toList) =
      ls_conc.flatMap (fun w => (Concrete.flattenValue concDecls funcIdx w).toList) := by
    intro ls_src
    induction ls_src with
    | nil =>
      intro ls_conc hLen _
      cases ls_conc with
      | nil => rfl
      | cons _ _ => simp at hLen
    | cons x xs ih =>
      intro ls_conc hLen hPw
      cases ls_conc with
      | nil => simp at hLen
      | cons y ys =>
        simp only [List.flatMap_cons]
        have h0 : flattenValue decls funcIdx x =
            Concrete.flattenValue concDecls funcIdx y := by
          have := hPw 0 (by simp) (by simp)
          simpa using this
        rw [h0]
        congr 1
        apply ih ys
        · simpa [List.length_cons] using hLen
        · intro i h_src h_conc
          have h_src' : i + 1 < (x :: xs).length := by
            simp [List.length_cons]; omega
          have h_conc' : i + 1 < (y :: ys).length := by
            simp [List.length_cons]; omega
          have := hPw (i + 1) h_src' h_conc'
          simpa [List.getElem_cons_succ] using this
  -- Pointwise lift on Array, ignoring `attach` machinery.
  have hArrayPw : ∀ (vs_src vs_conc : Array Value),
      vs_src.size = vs_conc.size →
      (∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        flattenValue decls funcIdx vs_src[i] =
          Concrete.flattenValue concDecls funcIdx vs_conc[i]) →
      vs_src.flatMap (fun w => flattenValue decls funcIdx w) =
      vs_conc.flatMap (fun w => Concrete.flattenValue concDecls funcIdx w) := by
    intro vs_src vs_conc hSize hPw
    apply Array.ext'
    rw [Array.toList_flatMap, Array.toList_flatMap]
    have hLen : vs_src.toList.length = vs_conc.toList.length := by
      simp [hSize]
    have hPw' : ∀ i (h_src : i < vs_src.toList.length)
        (h_conc : i < vs_conc.toList.length),
        flattenValue decls funcIdx vs_src.toList[i] =
          Concrete.flattenValue concDecls funcIdx vs_conc.toList[i] := by
      intro i h_src h_conc
      have h1 : i < vs_src.size := by simpa using h_src
      have h2 : i < vs_conc.size := by simpa using h_conc
      have := hPw i h1 h2
      simpa using this
    exact hListPw vs_src.toList vs_conc.toList hLen hPw'
  induction hR with
  | unit => unfold flattenValue Concrete.flattenValue; rfl
  | field _ => unfold flattenValue Concrete.flattenValue; rfl
  | pointer _ _ => unfold flattenValue Concrete.flattenValue; rfl
  | fn h =>
    unfold flattenValue Concrete.flattenValue
    rw [h]
  | tuple hLen _ ih =>
    unfold flattenValue Concrete.flattenValue
    rw [hAttachSrc, hAttachConc]
    exact hArrayPw _ _ hLen ih
  | array hLen _ ih =>
    unfold flattenValue Concrete.flattenValue
    rw [hAttachSrc, hAttachConc]
    exact hArrayPw _ _ hLen ih
  | ctor h_bridge _hLen _hElem _ih =>
    -- The `.ctor` arm closes by direct use of the flatten-equality bridge
    -- carried on `ValueR.ctor`. Per-arg recursion is handled by the bridge's
    -- producer at the entry boundary, which threads per-element IH via the
    -- bridge construction; here we just consume the conclusion.
    exact h_bridge

/-- `ValueR` is reflexive on `.array` containers built from `Array.ofFn` of
`.field`-of-pure-function values: source/concrete produce literally the same
array expression, so per-element `ValueR.field` discharges every index. Worker
for the `.u8BitDecomposition` arm. -/
private theorem ValueR_array_ofFn_field
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) {n : Nat} (f : Fin n → G) :
    ValueR decls concDecls funcIdx
      (.array (Array.ofFn fun i => .field (f i)))
      (.array (Array.ofFn fun i => .field (f i))) := by
  refine ValueR.array (by simp) ?_
  intro i h_src h_conc
  simp only [Array.size_ofFn] at h_src
  simp only [Array.getElem_ofFn]
  exact ValueR.field _



/-- `Array.extract` preserves `ValueR`-on-elements: from per-element
`ValueR vs_src[i] vs_conc[i]` plus same-size, derive per-element `ValueR`
on the extracted ranges. -/
private theorem ValueR_array_extract
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (vs_src vs_conc : Array Value)
    (hLen : vs_src.size = vs_conc.size)
    (hElem : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx vs_src[i] vs_conc[i])
    (i j : Nat) :
    ValueR decls concDecls funcIdx
      (.array (vs_src.extract i j)) (.array (vs_conc.extract i j)) := by
  have hLenE : (vs_src.extract i j).size = (vs_conc.extract i j).size := by
    simp [Array.size_extract, hLen]
  refine ValueR.array hLenE ?_
  intro k h_src h_conc
  -- (vs.extract i j)[k] = vs[k + i] for k < min (j - i) (vs.size - i).
  -- Use Array.getElem_extract : (a.extract s e)[i] = a[s + i].
  have hSrcSize : k + i < vs_src.size := by
    have h := h_src
    simp [Array.size_extract] at h
    omega
  have hConcSize : k + i < vs_conc.size := by
    have h := h_conc
    simp [Array.size_extract] at h
    omega
  have hSrcGet : (vs_src.extract i j)[k] = vs_src[i + k] := by
    simp [Array.getElem_extract]
  have hConcGet : (vs_conc.extract i j)[k] = vs_conc[i + k] := by
    simp [Array.getElem_extract]
  rw [hSrcGet, hConcGet]
  have h1 : i + k < vs_src.size := by omega
  have h2 : i + k < vs_conc.size := by omega
  exact hElem (i + k) h1 h2

/-- `Array.set!` preserves `ValueR`-on-elements: replacing index `n` with
`ValueR`-related values on both sides preserves per-element `ValueR`. -/
private theorem ValueR_array_set
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (vs_src vs_conc : Array Value)
    (hLen : vs_src.size = vs_conc.size)
    (hElem : ∀ i (h_src : i < vs_src.size) (h_conc : i < vs_conc.size),
        ValueR decls concDecls funcIdx vs_src[i] vs_conc[i])
    (n : Nat) (v_src v_conc : Value)
    (hvR : ValueR decls concDecls funcIdx v_src v_conc) :
    ValueR decls concDecls funcIdx
      (.array (vs_src.set! n v_src)) (.array (vs_conc.set! n v_conc)) := by
  -- `Array.set!` reduces to `setIfInBounds`.
  simp only [Array.set!]
  have hLenS :
      (vs_src.setIfInBounds n v_src).size = (vs_conc.setIfInBounds n v_conc).size := by
    simp [hLen]
  refine ValueR.array hLenS ?_
  intro k h_src h_conc
  have h_srcK : k < vs_src.size := by simp at h_src; exact h_src
  have h_concK : k < vs_conc.size := by simp at h_conc; exact h_conc
  by_cases hk : n = k
  · -- Both indices hit the inserted values (provided n < size).
    subst hk
    have hSrcGet : (vs_src.setIfInBounds n v_src)[n] = v_src := by
      simp
    have hConcGet : (vs_conc.setIfInBounds n v_conc)[n] = v_conc := by
      simp
    rw [hSrcGet, hConcGet]
    exact hvR
  · -- n ≠ k: both `setIfInBounds` leave element at k unchanged.
    have hSrcGet : (vs_src.setIfInBounds n v_src)[k] = vs_src[k] := by
      rw [Array.getElem_setIfInBounds]; rw [if_neg hk]
    have hConcGet : (vs_conc.setIfInBounds n v_conc)[k] = vs_conc[k] := by
      rw [Array.getElem_setIfInBounds]; rw [if_neg hk]
    rw [hSrcGet, hConcGet]
    exact hElem k h_srcK h_concK

set_option maxHeartbeats 1600000 in
theorem concretize_runFunction_simulation
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (name : Global)
    (f_src : Source.Function) (f_conc : Concrete.Function)
    (_hsrc : decls.getByKey name = some (.function f_src))
    (_hconc : concDecls.getByKey name = some (.function f_conc))
    (_hentry : f_src.entry = true)
    (_h_inputs_match : f_src.inputs.map (·.1) = f_conc.inputs.map (·.1))
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    -- Per-arg `ValueR v v` self-witness: for FnFree-only first-order args
    -- the caller's discharge is mechanical via the structural arms of
    -- `ValueR`. For ctor args the caller supplies the `h_ctor_flat_bridge`
    -- witness inline on each `ValueR.ctor`.
    (_hargsR : ∀ v ∈ args, ValueR decls concDecls funcIdx v v)
    -- Bundled decls relation (`CtorPreserved + FnNamesAgree`) consumed by
    -- `step_R_preservation_applyGlobal`. Producer at
    -- `compile_preservation_entry` discharges from the compilation chain.
    (_hDeclsR : Decls.R decls concDecls) :
    match Source.Eval.runFunction decls name args io₀ fuel,
          Concrete.Eval.runFunction concDecls name args io₀ fuel with
    | .ok (v₁, io₁), .ok (v₂, io₂) =>
        flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
          ∧ IOBuffer.equiv io₁ io₂
    | .error _, .error _ => True
    | _, _ => False := by
  -- Composition: unfold both `runFunction` to `applyGlobal`, push R
  -- through with `step_R_preservation_applyGlobal`, and project.
  -- Step 0: build initial state R from `entry_StateR_initial`.
  have hStateR :
      StateR decls concDecls funcIdx
        ({ ioBuffer := io₀ } : Source.Eval.EvalState)
        ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) :=
    entry_StateR_initial decls concDecls funcIdx io₀
  -- Step 1: build the args self-relation `ValueR a a` directly from the
  -- caller's per-arg `_hargsR` witnesses.
  have hargsR :
      List.length args = List.length args ∧
        ∀ i (h_src : i < args.length) (h_conc : i < args.length),
          ValueR decls concDecls funcIdx args[i] args[i] := by
    refine ⟨rfl, ?_⟩
    intro i h_src _h_conc
    have hmem : args[i] ∈ args := List.getElem_mem _
    exact _hargsR _ hmem
  -- Step 1.5: discharge the per-call `Decls.ParamsAtName` premise from the
  -- entry-level hypotheses. The function half follows from
  -- `Source.Function.notPolyEntry` + `_hentry`. The ctor half is vacuous:
  -- `_hsrc` already pins `decls.getByKey name` to a `.function`, so any
  -- `.constructor` lookup at the same key is impossible.
  have hParamsAtName : Decls.ParamsAtName decls name := by
    refine ⟨?_, ?_⟩
    · intro f hf
      rw [_hsrc] at hf
      cases hf
      rcases f_src.notPolyEntry with hp | he
      · exact hp
      · rw [he] at _hentry; cases _hentry
    · intro dt c hf
      rw [_hsrc] at hf
      cases hf
  -- Step 1.75: discharge the per-call `Decls.KindAtName` premise from the
  -- entry-level hypotheses. Both `_hsrc` (decls.getByKey name = .function)
  -- and `_hconc` (concDecls.getByKey name = .function) hold simultaneously
  -- at the entry boundary, so all eight clauses of `KindAtName` follow
  -- mechanically from inversion + casework on the lookups (the off-diagonal
  -- and `none`/`.dataType` arms become vacuously False on either side).
  have hKindAtName : Decls.KindAtName decls concDecls name := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- (1) FnFwd: source `.function` → concrete `.function` (at SAME name).
    · intro _ _; exact ⟨f_conc, _hconc⟩
    -- (2) CtorFwd: source `.constructor` is False (source has `.function`).
    · intro _ _ hsrc; rw [_hsrc] at hsrc; cases hsrc
    -- (3) FnBwd: concrete `.function` → source `.function`.
    · intro _ _; exact ⟨f_src, _hsrc⟩
    -- (4) CtorBwd: concrete `.constructor` is False (concrete has `.function`).
    · intro _ _ hconc; rw [_hconc] at hconc; cases hconc
    -- (5) FnVsCtor exclusion: derived from the source `.function` part —
    --     `_hsrc` ⟹ no other source declaration; hyp + `_hconc` mismatch.
    · intro _ _ _ _ hconc; rw [_hconc] at hconc; cases hconc
    -- (6) CtorVsFn exclusion: source `.constructor` is False (`_hsrc` has `.function`).
    · intro _ _ _ hsrc _; rw [_hsrc] at hsrc; cases hsrc
    -- (7) NoneBwd: source `none` is False (`_hsrc` has `.function`).
    · intro hsrc; rw [_hsrc] at hsrc; cases hsrc
    -- (8) DtBwd: source `.dataType` is False (`_hsrc` has `.function`).
    · intro _ hsrc; rw [_hsrc] at hsrc; cases hsrc
  -- Step 2: apply per-call simulation at the entry boundary.
  have hsim :=
    step_R_preservation_applyGlobal (decls := decls) (concDecls := concDecls)
      (funcIdx := funcIdx) _hDeclsR fuel name args args
      ({ ioBuffer := io₀ } : Source.Eval.EvalState)
      ({ ioBuffer := io₀ } : Concrete.Eval.EvalState)
      hStateR hargsR hParamsAtName hKindAtName
  -- Step 3: unfold `runFunction` and case-split on `applyGlobal`.
  unfold Source.Eval.runFunction Concrete.Eval.runFunction
  simp only
  -- Both runFunction expressions reduce to a `match applyGlobal ... with
  -- | .error e => .error e | .ok (v, st') => .ok (v, st'.ioBuffer)`.
  cases h_src : Source.Eval.applyGlobal decls fuel name args
      ({ ioBuffer := io₀ } : Source.Eval.EvalState) with
  | error e_src =>
    cases h_conc : Concrete.Eval.applyGlobal concDecls fuel name args
        ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) with
    | error e_conc => trivial
    | ok r_conc =>
      -- hsim with .error / .ok contradicts.
      simp [h_src, h_conc] at hsim
  | ok r_src =>
    obtain ⟨v_src, st_src'⟩ := r_src
    cases h_conc : Concrete.Eval.applyGlobal concDecls fuel name args
        ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) with
    | error e_conc =>
      simp [h_src, h_conc] at hsim
    | ok r_conc =>
      obtain ⟨v_conc, st_conc'⟩ := r_conc
      -- hsim now gives ValueR v_src v_conc ∧ StateR st_src' st_conc'.
      simp only [h_src, h_conc] at hsim
      obtain ⟨hVR, hStR⟩ := hsim
      refine ⟨?_, ?_⟩
      · exact ValueR_implies_flatten_eq hVR
      · exact hStR.2

end Simulation

end Aiur

end -- @[expose] section
end -- public section
