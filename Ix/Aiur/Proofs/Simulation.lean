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

Phase X1.2 sig-fix (2026-04-28): `ValueR` strengthened from bare flat-equality
(`flattenValue v_src = Concrete.flattenValue v_conc`) to an inductive shape-
agreement predicate that ALSO implies flat-equality. The flat-equality
formulation was too permissive — under it, e.g. `.tuple #[.field g]` and
`.field g` were related (both flatten to `#[g]`), which broke arithmetic arms
(`.add`/`.sub`/`.mul`/`.eqZero`/`.assertEq`) that dispatch on the runtime
constructor: source-side `.field` could not constrain the concrete value to
also be `.field`, allowing source-ok / concrete-error pairs that violate the
simulation slack `.ok _, .error _ => False`.

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

/-- Caller args at entry are FnFree (no first-class function values inside).
For FnFree mono-ctor values, source and concrete flatten agree.

The `.ctor` arm's flat-bridge is discharged by the explicit `h_flat_agree`
parameter — a per-FnFree-value flatten-agreement witness. Callers supply
this from `flatten_agree_entry` (CompilerPreservation.lean). Threading the
witness here (rather than reproving it inline) keeps this lemma free of
`WellFormed t`/stage-witness hypotheses, and lets us share work with A.5
(`flatten_agree_entry`): closing A.5's `.ctor` arm immediately closes both
this consumer and A.5 itself, since the two were duplicate obligations.

The other arms (`.unit/.field/.pointer/.tuple/.array`) close F=0
structurally; `h_flat_agree` is only consumed in `.ctor`. -/
private theorem ValueR_of_FnFree_at_entry
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    -- Sig amendment 2026-05-03: `h_flat_agree` now consumes BOTH `FnFree`
    -- AND `MonoCtorReach`. Mirrors `flatten_agree_entry`'s strengthened sig.
    -- Producer at `compile_preservation_entry` discharges `MonoCtorReach`
    -- via `runFunction_preserves_MonoCtorReach`.
    (h_flat_agree : ∀ (v : Value), Value.FnFree v →
      Value.MonoCtorReach decls concDecls v →
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v) :
    ∀ (v : Value), Value.FnFree v → Value.MonoCtorReach decls concDecls v →
      ValueR decls concDecls funcIdx v v
  | .unit, _, _ => ValueR.unit
  | .field g, _, _ => ValueR.field g
  | .pointer w n, _, _ => ValueR.pointer w n
  | .fn _, h, _ => nomatch h
  | .tuple vs, .tuple hfn, hreach =>
    ValueR.tuple rfl (fun i h_src _ =>
      ValueR_of_FnFree_at_entry h_flat_agree (vs[i]'h_src)
        (hfn _ (vs.getElem_mem h_src))
        (hreach.tuple_inv _ (vs.getElem_mem h_src)))
  | .array vs, .array hfn, hreach =>
    ValueR.array rfl (fun i h_src _ =>
      ValueR_of_FnFree_at_entry h_flat_agree (vs[i]'h_src)
        (hfn _ (vs.getElem_mem h_src))
        (hreach.array_inv _ (vs.getElem_mem h_src)))
  | .ctor g args, hfree@(.ctor _ hfn), hreach =>
    -- `h_flat_agree` discharges the ctor-flat-bridge directly. The per-element
    -- ValueR is built recursively from `hfn` + the IH.
    ValueR.ctor (h_flat_agree (.ctor g args) hfree hreach) rfl (fun i h_src _ =>
      ValueR_of_FnFree_at_entry h_flat_agree (args[i]'h_src)
        (hfn _ (args.getElem_mem h_src))
        (hreach.ctor_args _ (args.getElem_mem h_src)))
termination_by v _ _ => sizeOf v



/-- Initial state R at entry: both eval start with `default` store + `io₀`. -/
private theorem entry_StateR_initial
    (decls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat) (io₀ : IOBuffer) :
    StateR decls concDecls funcIdx
      ({ ioBuffer := io₀ } : Source.Eval.EvalState)
      ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) := by
  exact ⟨StoreR_initial decls concDecls funcIdx, IOBuffer.equiv_refl io₀⟩



/-! ## Decls relation `R` for the simulation.

Sig amendment 2026-05-03 (Invariant 3, Defect 1): `step_R_preservation_applyGlobal`
previously took `_hwf : True`, which is too weak for the simulation's body
to be (even in principle) closable — `applyGlobal` dispatches on
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

/-- Function-kind preservation between source and concrete decls
(FWD-only). Mirrors `Decls.CtorPreserved` for `.function` keys.

Sig amendment 2026-05-04 (architectural-defect closure): predicate is
FWD-ONLY. The previously paired BWD direction is provably False on
polymorphic source (drained `newFunctions` produces concrete `.function`
entries at MANGLED keys with no source preimage at the same key).
Keeping it as a biconditional hid an unprovable obligation behind a
phantom `BLOCKED-FnNamesAgree-BWD` sub-sorry that no real consumer
actually used. -/
@[expose] def Decls.FnNamesAgree (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  -- FWD direction guarded by `f_src.params = []`. Counterexample under
  -- polymorphic source: a polymorphic function `fn id<T>(x : T) → T`
  -- has `decls.getByKey "id" = .function {params := ["T"], …}`, but
  -- `concDecls` only carries monomorphic instances at
  -- `concretizeName "id" #[U64]` etc. — NOT at bare `"id"`. So the
  -- universal FWD direction would fail without the params-empty guard.
  ∀ g f_src, decls.getByKey g = some (.function f_src) → f_src.params = [] →
    ∃ f_conc, concDecls.getByKey g = some (.function f_conc) ∧
      f_src.inputs.map (·.1) = f_conc.inputs.map (·.1)

/-- Bundled simulation precondition on the (decls, concDecls) pair. The
two clauses are the minimal structure needed to discharge
`step_R_preservation_applyGlobal`'s arm-dispatch obligations:
`CtorPreserved` for the `.constructor` arm of `applyGlobal`; `FnNamesAgree`
for the `.function` arm (input-name agreement lets bindings carry over
under `BindingsR`). -/
@[expose] def Decls.R (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  Decls.CtorPreserved decls concDecls ∧
  Decls.FnNamesAgree decls concDecls

/-- Per-function-call simulation: under R-initial (entry-shape), source
`applyGlobal` and concrete `applyGlobal` agree under R on outputs.

Direction: source/concrete must agree on success-vs-error. Both succeed
with R-related outputs, or both error. This is the tightened-arm form
suitable for direct composition into `concretize_runFunction_simulation`
without weakening its top-level guarantee.

Sig amendment 2026-05-03 (Invariant 3, Defect 1): `_hwf : True`
replaced with a proper hypothesis package (`Decls.R decls concDecls`).
The previous placeholder was provably False as a sig (no relation between
decls ⇒ no way to discharge `.error vs .ok ⇒ False` clause). The bundle
factors through `Decls.CtorPreserved + FnNamesAgree`; producers at the
caller (`concretize_runFunction_simulation`) discharge it from the
compilation chain witnesses.

**BLOCKED ON**: actual proof body still needs cross-call-cross-decls
reasoning; this is the X1.2 ⇒ X1.3 / X1.4 milestone. The proof will
recurse on the term-level simulation (`step_R_preservation_term` below)
inside `f.body` at fuel `n`, with the `applyGlobal`-decrement cited at
fuel boundaries. -/
private theorem step_R_preservation_applyGlobal
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (_hDeclsR : Decls.R decls concDecls)
    (fuel : Nat) (name : Global) (args_src args_conc : List Value)
    (st_src : Source.Eval.EvalState) (st_conc : Concrete.Eval.EvalState)
    (_hStateR : StateR decls concDecls funcIdx st_src st_conc)
    (_hargsR : List.length args_src = List.length args_conc ∧
       ∀ i (h_src : i < args_src.length) (h_conc : i < args_conc.length),
         ValueR decls concDecls funcIdx args_src[i] args_conc[i]) :
    match Source.Eval.applyGlobal decls fuel name args_src st_src,
          Concrete.Eval.applyGlobal concDecls fuel name args_conc st_conc with
    | .ok (v_src, st_src'), .ok (v_conc, st_conc') =>
        ValueR decls concDecls funcIdx v_src v_conc ∧
          StateR decls concDecls funcIdx st_src' st_conc'
    | .error _, .error _ => True
    | _, _ => False
    := by
  -- BLOCKED ON: cross-call cross-decls simulation. The proof recurses on
  -- term-level simulation inside `f.body` at fuel `n`. Requires
  -- `f_src.body`-level term-bridge plus `decls.getByKey name`-resolution
  -- compatibility (mono ctors agree by `concretizeName g #[] = g`;
  -- poly-call sites resolve via `drained.mono`). This is the X1.4
  -- abort-or-proceed signal.
  -- Sig (X1.4 wiring 2026-04-28): tightened from prior `.error, .ok => True`
  -- slack to `_, _ => False` so the public `concretize_runFunction_simulation`
  -- can compose without weakening its top-level guarantee. The slack was
  -- documented as "bytecode-may-overshoot" but is unneeded at this layer:
  -- `applyGlobal` operates on Value-level inputs (not on flat G arrays), so
  -- the bytecode-overflow rationale (which lives at the bytecode lowering
  -- layer) doesn't bite here.
  sorry

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
  -- Other constructors deferred to X1.3:
  -- | ref, letLoad, match, app, ...
  -- `letLoad` arises from match-compilation of `.pointer` patterns
  -- (`Compiler/Match.lean`), NOT from a direct Source `.let`. Its bridge
  -- and arm need StoreR (currently a phantom leaf) so are BLOCKED until X1.3.
  -- See `Ix/Aiur/Compiler/Concretize.lean:227 termToConcrete` for the
  -- structural correspondence we'll mirror constructor-by-constructor.

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
  as a hypothesis. Producers of `ValueR.ctor` (currently
  `ValueR_of_FnFree_at_entry`) discharge the bridge from their own ctor-shape
  information.

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
  -- concrete `flattenValue`. Reused across `.tuple`/`.array`/`.ctor` arms.
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
    -- producer (e.g. `ValueR_of_FnFree_at_entry`), which threads per-element
    -- IH via the bridge construction; here we just consume the conclusion.
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
    -- Sig amendment 2026-05-03: args carry `MonoCtorReach` (entry-call
    -- invariant — first-order entry args trivially satisfy this).
    (_hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    -- Sig amendment 2026-05-03 (Defect 1): bundled decls relation
    -- (`CtorPreserved + FnNamesAgree`) replaces the placeholder `True`
    -- consumed by `step_R_preservation_applyGlobal`. Producer at
    -- `compile_preservation_entry` discharges from the compilation chain.
    (_hDeclsR : Decls.R decls concDecls)
    (h_flat_agree : ∀ (v : Value), Value.FnFree v →
      Value.MonoCtorReach decls concDecls v →
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v) :
    match Source.Eval.runFunction decls name args io₀ fuel,
          Concrete.Eval.runFunction concDecls name args io₀ fuel with
    | .ok (v₁, io₁), .ok (v₂, io₂) =>
        flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
          ∧ IOBuffer.equiv io₁ io₂
    | .error _, .error _ => True
    | _, _ => False := by
  -- Composition (X1.4 wiring 2026-04-28): unfold both `runFunction` to
  -- `applyGlobal`, push R through with `step_R_preservation_applyGlobal`,
  -- and project. The `args_self_ValueR` lemma is built locally from
  -- `ValueR_of_FnFree_at_entry`.
  -- Step 0: build initial state R from `entry_StateR_initial`.
  have hStateR :
      StateR decls concDecls funcIdx
        ({ ioBuffer := io₀ } : Source.Eval.EvalState)
        ({ ioBuffer := io₀ } : Concrete.Eval.EvalState) :=
    entry_StateR_initial decls concDecls funcIdx io₀
  -- Step 1: build the args self-relation `ValueR a a` from FnFree.
  have hargsR :
      List.length args = List.length args ∧
        ∀ i (h_src : i < args.length) (h_conc : i < args.length),
          ValueR decls concDecls funcIdx args[i] args[i] := by
    refine ⟨rfl, ?_⟩
    intro i h_src _h_conc
    have hmem : args[i] ∈ args := List.getElem_mem _
    exact ValueR_of_FnFree_at_entry h_flat_agree args[i]
      (_hargsFnFree _ hmem) (_hargsReach _ hmem)
  -- Step 2: apply per-call simulation at the entry boundary.
  have hsim :=
    step_R_preservation_applyGlobal (decls := decls) (concDecls := concDecls)
      (funcIdx := funcIdx) _hDeclsR fuel name args args
      ({ ioBuffer := io₀ } : Source.Eval.EvalState)
      ({ ioBuffer := io₀ } : Concrete.Eval.EvalState)
      hStateR hargsR
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
