module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Semantics.Compatible
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.ConcreteInvariants
public import Ix.Aiur.Proofs.ValueEqFlatten

/-!
Shared infrastructure for the `Lower` proofs.

`IsCore` — a syntactic predicate carving out the straight-line subset of
`Concrete.Term`: no `.ret`, no `.match`, no function call (`.app`), no raw
`.store` / `.load`, no IO, no u8/u32. Also excludes `.letLoad`, the collection
forms (`.tuple`, `.array`), arithmetic (`.add`/`.sub`/`.mul`/`.eqZero`), and
the tuple/array accessors (`.proj`/`.get`/`.slice`/`.set`) for now — those
require either a width-1 subterm invariant (arithmetic) or a layout/shape
side-condition that is cleaner to introduce alongside the preservation proof
for the full-term extension. Extending `IsCore` to cover them is the first
step of that extension.

`CompileInv` — a structure capturing the `CompilerState` delta produced by a
successful `toIndex` call (valIdx growth = output width, ops/degrees grow
monotonically). Not needed by the progress proof but staged here for the
preservation proof, which is currently blocked (see `LowerSoundCore`).

Coordination note: `IsCore` is keyed on `LayoutMap`, which is a `Lower`
artifact. If the concretize worktree wants to express an `IsCore`-shaped
post-condition of `concretize`, it should live here (or be lifted to a
pre-`Lower` location).
-/

public section

namespace Aiur

open Concrete

/-- Syntactic predicate identifying the straight-line subset of
`Concrete.Term` on which `toIndex` provably does not throw.

The constructors are restricted to those whose `toIndex` arm is either
pure or a `pushOp` / `modify` followed by recursion on an already-covered
subterm. Every reference to a global symbol carries a proof that the symbol
is mapped in the current `LayoutMap` to a function or constructor layout —
`.dataType` layouts cause `toIndex` to `throw` on the `.ref` arm. -/
inductive IsCore (layoutMap : LayoutMap) : Term → Prop
  | unit {t e} : IsCore layoutMap (.unit t e)
  | var {t e l} : IsCore layoutMap (.var t e l)
  | field {t e g} : IsCore layoutMap (.field t e g)
  | ref {t e g} :
      ((∃ fl, layoutMap[g]? = some (.function fl)) ∨
       (∃ cl, layoutMap[g]? = some (.constructor cl))) →
      IsCore layoutMap (.ref t e g)
  | letVar {t e l v b} :
      IsCore layoutMap v → IsCore layoutMap b →
      IsCore layoutMap (.letVar t e l v b)
  | letWild {t e v b} :
      IsCore layoutMap v → IsCore layoutMap b →
      IsCore layoutMap (.letWild t e v b)
  | ptrVal {t e a} :
      IsCore layoutMap a → IsCore layoutMap (.ptrVal t e a)
  | assertEq {t e a b r} :
      IsCore layoutMap a → IsCore layoutMap b → IsCore layoutMap r →
      IsCore layoutMap (.assertEq t e a b r)
  | debug {t e label tOpt r} :
      (∀ x, tOpt = some x → IsCore layoutMap x) →
      IsCore layoutMap r →
      IsCore layoutMap (.debug t e label tOpt r)

/-- Typed-Value invariant: `v` has the typed shape `τ` (`Concrete.Typ`).

Carried by `IsCoreExtended` arms that access typed positions (`.proj`/
`.get`/`.slice`/`.set`/`.letLoad`/`.load`). The interpreter does not
type-check at runtime, so the lower-pass preservation theorem needs an
explicit invariant linking the source-side `Value` to the typed shape
the compiler-side `toIndex` consults via `arg.typ` / `dstTyp`.

For `.proj` we need `ValueHasTyp (.tuple typs) (.tuple vs)` — i.e. the
value at the projected position is a tuple whose element values track the
component types. Likewise `.get` / `.slice` / `.set` need
`ValueHasTyp (.array τ k) (.array vs)`, and `.letLoad` / `.load` need
`ValueHasTyp (.pointer τ) (.pointer w n)`.

The flat-size correspondence
`flattenValue v = typSize layoutMap τ` (under the appropriate decls /
funcIdx correspondence) is the key downstream consumer.

The predicate is parameterized by `concDecls : Concrete.Decls` so the
`.ref` arm can record the datatype + constructor it inhabits. Without the
parameterization the `.ref` arm would be unconstrained — see audit SD-A. -/
inductive ValueHasTyp (concDecls : Concrete.Decls) : Concrete.Typ → Value → Prop
  | unit : ValueHasTyp concDecls .unit .unit
  | field {g : G} : ValueHasTyp concDecls .field (.field g)
  | pointer {τ : Concrete.Typ} {w n : Nat} :
      ValueHasTyp concDecls (.pointer τ) (.pointer w n)
  | function {ins : List Concrete.Typ} {out : Concrete.Typ} {g : Global} :
      ValueHasTyp concDecls (.function ins out) (.fn g)
  | tuple {τs : Array Concrete.Typ} {vs : Array Value} :
      τs.size = vs.size →
      (∀ i (h₁ : i < τs.size) (h₂ : i < vs.size),
        ValueHasTyp concDecls (τs[i]'h₁) (vs[i]'h₂)) →
      ValueHasTyp concDecls (.tuple τs) (.tuple vs)
  | array {τ : Concrete.Typ} {n : Nat} {vs : Array Value} :
      vs.size = n →
      (∀ i (h : i < vs.size), ValueHasTyp concDecls τ (vs[i]'h)) →
      ValueHasTyp concDecls (.array τ n) (.array vs)
  /-- A `.ref g`-typed value is a constructor application of one of the
  constructors registered for the datatype keyed at `g` in `concDecls`.
  The witness carries:
  - `hdt` : `g` resolves to a registered datatype `cdt` in `concDecls`.
  - `hcc` : `cc` is one of `cdt`'s constructors.
  - `hargs` : the value carries exactly `cc.argTypes.length` arguments.
  - `h_per_arg` : each argument value is itself well-typed at the
    constructor's declared per-argument type.

  The constructor-name of the value is `g.pushNamespace cc.nameHead`,
  matching the layout-map key produced by `Concrete.Decls.layoutMap`. -/
  | ref {g cdt cc} {args : Array Value}
      (hdt : concDecls.getByKey g = some (.dataType cdt))
      (hcc : cc ∈ cdt.constructors)
      (hargs : args.size = cc.argTypes.length)
      (h_per_arg : ∀ i (h₁ : i < args.size) (h₂ : i < cc.argTypes.length),
        ValueHasTyp concDecls (cc.argTypes[i]'h₂) (args[i]'h₁)) :
      ValueHasTyp concDecls (.ref g) (.ctor (g.pushNamespace cc.nameHead) args)





/-- Side-condition predicate: `toIndex` on `term` produces a width-1
result from any starting state. This is exactly the precondition under
which `expectIdx` succeeds — required by every arithmetic, u8/u32, and
width-1-IO arm of `toIndex` (the `expectIdx` call sites). -/
@[expose] def WidthOne (layoutMap : LayoutMap) (term : Term) : Prop :=
  ∀ (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (st₀ : CompilerState),
    ∃ idxs st, (toIndex layoutMap bindings term).run st₀ = .ok idxs st ∧
      idxs.size = 1

/-- **Extension scaffold.** Carves out the FULL `toIndex`-valid subset of
`Concrete.Term`, i.e. everything except `.ret` and `.match` (both throw
inside `toIndex` and only ever appear at the `Term.compile` block level).
Used by the extended progress / preservation lemmas in `LowerSoundCore`.

Each arm tracks the side-conditions `toIndex`'s arm needs in order to avoid
throwing:
- `.letLoad` / `.proj` / `.get` / `.slice` / `.set` / `.load` carry a
  `typSize lm _ = .ok n` witness for every consulted `Typ`;
- `.app` carries `layoutMap[g]? = some (.function _)` or `.constructor _`
  — never `.dataType` or `none`;
- arithmetic / u8 / u32 arms require the operand subterms to produce a
  width-1 result (tracked via `WidthOne` carriers);
- IO arms recurse on subterms covered by `IsCoreExtended`.

The arms inherited from `IsCore` are listed for completeness so the predicate
is closed under all `Concrete.Term` constructors `toIndex` may legitimately
encounter. `.ret` and `.match` are intentionally absent — every
`Term.compile` invocation either rewrites them in tail position (handled by
the block-level proof in `LowerSoundControl`) or guarantees they never occur
in a value position.

BLOCKED on per-arm extension proofs in `LowerSoundCore`; see
`toIndex_progress_core_extended` / `toIndex_preservation_core_extended`. -/
inductive IsCoreExtended (layoutMap : LayoutMap) : Term → Prop
  -- Inherited core arms.
  | unit {t e} : IsCoreExtended layoutMap (.unit t e)
  | var {t e l} : IsCoreExtended layoutMap (.var t e l)
  | field {t e g} : IsCoreExtended layoutMap (.field t e g)
  | ref {t e g} :
      ((∃ fl, layoutMap[g]? = some (.function fl)) ∨
       (∃ cl, layoutMap[g]? = some (.constructor cl))) →
      IsCoreExtended layoutMap (.ref t e g)
  | letVar {t e l v b} :
      IsCoreExtended layoutMap v → IsCoreExtended layoutMap b →
      IsCoreExtended layoutMap (.letVar t e l v b)
  | letWild {t e v b} :
      IsCoreExtended layoutMap v → IsCoreExtended layoutMap b →
      IsCoreExtended layoutMap (.letWild t e v b)
  | ptrVal {t e a} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap (.ptrVal t e a)
  | assertEq {t e a b r} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      IsCoreExtended layoutMap r →
      IsCoreExtended layoutMap (.assertEq t e a b r)
  | debug {t e label tOpt r} :
      (∀ x, tOpt = some x → IsCoreExtended layoutMap x) →
      IsCoreExtended layoutMap r →
      IsCoreExtended layoutMap (.debug t e label tOpt r)
  -- New (extended) arms.
  | tuple {t e ts} :
      (∀ a ∈ ts, IsCoreExtended layoutMap a) →
      IsCoreExtended layoutMap (.tuple t e ts)
  | array {t e ts} :
      (∀ a ∈ ts, IsCoreExtended layoutMap a) →
      IsCoreExtended layoutMap (.array t e ts)
  | letLoad {t e dst dstTyp src bod} :
      (∃ n, typSize layoutMap dstTyp = .ok n) →
      IsCoreExtended layoutMap bod →
      IsCoreExtended layoutMap (.letLoad t e dst dstTyp src bod)
  | proj {t e a n} :
      IsCoreExtended layoutMap a →
      (∃ typs, a.typ = .tuple typs ∧
        ∀ τ ∈ typs.toList, ∃ k, typSize layoutMap τ = .ok k) →
      IsCoreExtended layoutMap (.proj t e a n)
  | get {t e a n} :
      IsCoreExtended layoutMap a →
      (∃ τ k, a.typ = .array τ k ∧ ∃ m, typSize layoutMap τ = .ok m) →
      IsCoreExtended layoutMap (.get t e a n)
  | slice {t e a i j} :
      IsCoreExtended layoutMap a →
      (∃ τ k, a.typ = .array τ k ∧ ∃ m, typSize layoutMap τ = .ok m) →
      IsCoreExtended layoutMap (.slice t e a i j)
  | set {t e a n v} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap v →
      (∃ τ k, a.typ = .array τ k ∧ ∃ m, typSize layoutMap τ = .ok m) →
      IsCoreExtended layoutMap (.set t e a n v)
  | store {t e a} :
      IsCoreExtended layoutMap a →
      IsCoreExtended layoutMap (.store t e a)
  | load {t e a} :
      IsCoreExtended layoutMap a →
      WidthOne layoutMap a →
      (∃ τ, a.typ = .pointer τ ∧ ∃ n, typSize layoutMap τ = .ok n) →
      IsCoreExtended layoutMap (.load t e a)
  -- Function call: layout must resolve to a function-or-constructor entry,
  -- and every argument must be `IsCoreExtended`.
  | app {t e g args u} :
      ((∃ fl, layoutMap[g]? = some (.function fl)) ∨
       (∃ cl, layoutMap[g]? = some (.constructor cl))) →
      (∀ a ∈ args, IsCoreExtended layoutMap a) →
      IsCoreExtended layoutMap (.app t e g args u)
  -- Arithmetic: operand subterms must `expectIdx`-succeed (width-1).
  | add {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.add t e a b)
  | sub {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.sub t e a b)
  | mul {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.mul t e a b)
  | eqZero {t e a} :
      IsCoreExtended layoutMap a →
      WidthOne layoutMap a →
      IsCoreExtended layoutMap (.eqZero t e a)
  -- IO ops.
  | ioGetInfo {t e k} :
      IsCoreExtended layoutMap k →
      IsCoreExtended layoutMap (.ioGetInfo t e k)
  | ioSetInfo {t e k i l r} :
      IsCoreExtended layoutMap k → IsCoreExtended layoutMap i →
      IsCoreExtended layoutMap l → IsCoreExtended layoutMap r →
      WidthOne layoutMap i → WidthOne layoutMap l →
      IsCoreExtended layoutMap (.ioSetInfo t e k i l r)
  | ioRead {t e i n} :
      IsCoreExtended layoutMap i →
      WidthOne layoutMap i →
      IsCoreExtended layoutMap (.ioRead t e i n)
  | ioWrite {t e d r} :
      IsCoreExtended layoutMap d → IsCoreExtended layoutMap r →
      IsCoreExtended layoutMap (.ioWrite t e d r)
  -- u8/u32 ops.
  | u8BitDecomposition {t e a} :
      IsCoreExtended layoutMap a →
      WidthOne layoutMap a →
      IsCoreExtended layoutMap (.u8BitDecomposition t e a)
  | u8ShiftLeft {t e a} :
      IsCoreExtended layoutMap a →
      WidthOne layoutMap a →
      IsCoreExtended layoutMap (.u8ShiftLeft t e a)
  | u8ShiftRight {t e a} :
      IsCoreExtended layoutMap a →
      WidthOne layoutMap a →
      IsCoreExtended layoutMap (.u8ShiftRight t e a)
  | u8Xor {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8Xor t e a b)
  | u8Add {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8Add t e a b)
  | u8Sub {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8Sub t e a b)
  | u8And {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8And t e a b)
  | u8Or {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8Or t e a b)
  | u8LessThan {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u8LessThan t e a b)
  | u32LessThan {t e a b} :
      IsCoreExtended layoutMap a → IsCoreExtended layoutMap b →
      WidthOne layoutMap a → WidthOne layoutMap b →
      IsCoreExtended layoutMap (.u32LessThan t e a b)

/-- Global-uniqueness side-condition on a `Local` `outerLocal`: every
`.letVar`-bound `l''` reachable in some `IsCore` term differs from
`outerLocal`. This is the SSA-freshness invariant that the concretize pass
produces — it lets us extend an `env` with `(outerLocal, val)` without
colliding with any other `.letVar` binder. -/
abbrev LetVarBinderNeq (layoutMap : LayoutMap) (outerLocal : Local) : Prop :=
  ∀ {t'' : Concrete.Typ} {e'' : Bool} {l'' : Local} {v'' b'' : Concrete.Term},
    IsCore layoutMap (.letVar t'' e'' l'' v'' b'') →
    l'' ≠ outerLocal

/-- Compatibility hypothesis linking `concDecls.getByKey g` (which drives the
interpreter's `.ref` arm) with `layoutMap[g]?` (which drives `toIndex`'s
`.ref` arm) and the flattening info coming from `sourceDecls`/`funcIdx`.

* Function branch: `layoutMap` and `concDecls` both see `g` as a function
  (interp returns `.fn g`, `toIndex` emits a width-1 array, and
  `flattenValue` on a function value is width 1).
* Constructor branch: both agree `g` is a zero-arg constructor (otherwise
  `interp` errors on `.ref`), and the width produced by `toIndex` matches
  `flattenValue` on `.ctor g #[]`. -/
@[expose] def RefCompat (sourceDecls : Source.Decls) (concDecls : Concrete.Decls)
    (funcIdx : Global → Option Nat)
    (layoutMap : LayoutMap) (g : Global) : Prop :=
  match layoutMap[g]? with
  | some (.function _) =>
      (∃ f, concDecls.getByKey g = some (.function f)) ∧
      (flattenValue sourceDecls funcIdx (.fn g)).size = 1
  | some (.constructor cl) =>
      (∃ dt ctor, concDecls.getByKey g = some (.constructor dt ctor)
                   ∧ ctor.argTypes.isEmpty = true) ∧
      (flattenValue sourceDecls funcIdx (.ctor g #[])).size = cl.size ∧
      cl.size ≥ 1
  | _ => False

/-- The `CompilerState` delta after a successful `toIndex` call.

Staged for the preservation proof: every successful `toIndex` invocation
increments `valIdx` by the flattened output width, never shrinks `ops`
or `degrees`, and keeps `degrees.size = valIdx`. -/
structure CompileInv (st st' : CompilerState) (outputSize : Nat) : Prop where
  valIdx_growth : st'.valIdx = st.valIdx + outputSize
  ops_monotone : st.ops.size ≤ st'.ops.size
  degrees_monotone : st.degrees.size ≤ st'.degrees.size

/-! ## Proof infrastructure — state-threading reductions for `CompileM`

These lemmas rewrite `.run` on common `CompileM` building blocks into explicit
`EStateM.Result.ok (value, new_state)` form. They let proofs about `toIndex`
proceed via `simp [pushOp_run, modify_run, ...]` without unfolding the
`EStateM` monad internals at every call site. -/

/-- `pushOp op size` on input state `s` produces `(Array.range' s.valIdx size,
post-state)` where `post-state` has `valIdx` bumped, `ops.push op`, and
`pushOpDegree`-updated `degrees`. -/
@[simp]
theorem pushOp_run (s : CompilerState) (op : Bytecode.Op) (size : Nat) :
    pushOp op size s =
    .ok (Array.range' s.valIdx size)
         { s with valIdx := s.valIdx + size,
                  ops := s.ops.push op,
                  degrees := pushOpDegree s.degrees op size } := by
  simp [pushOp, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `modify f` on input state `s` produces `((), f s)`. -/
@[simp]
theorem compileM_modify_run (s : CompilerState) (f : CompilerState → CompilerState) :
    (modify f : CompileM _).run s = .ok () (f s) := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.run]

/-- `pure x` on input state `s` produces `(x, s)` — `.ok` leaves state unchanged. -/
@[simp]
theorem compileM_pure_run {α : Type} (s : CompilerState) (x : α) :
    (pure x : CompileM α).run s = .ok x s := by
  simp [pure, EStateM.pure, EStateM.run]

/-- `bind` of an `.ok` step: unfolds the match to the continuation. -/
theorem compileM_bind_ok {α β : Type} (s : CompilerState)
    (ma : CompileM α) (a : α) (s' : CompilerState)
    (ha : ma.run s = .ok a s')
    (f : α → CompileM β) :
    (ma >>= f).run s = (f a).run s' := by
  simp only [bind, EStateM.bind, EStateM.run] at *
  rw [ha]

/- `Value.FnFree` and its transport helpers (`attach_flatMap_eq`,
`flattenValue_funcIdx_irrelevant_of_fnFree`, `ValueEq.funcIdx_irrelevant_of_fnFree`,
`Flatten.args_transport_remap_of_fnFree`, `InterpResultEq.transport_remap_of_src_fnFree`)
moved to `Ix/Aiur/Proofs/ValueEqFlatten.lean` — the natural home for
`ValueEq ↔ flattenValue` machinery. -/

/-! ## Post-conditions of `Concrete.Decls.toBytecode` (sorried)

The two top-level theorems project from a single consolidated fold-invariant
lemma `toBytecode_fold_invariant`. Supporting `List.foldlM_except_invariant`
is a generic reusable invariant-propagation principle. -/

/-- Equational unfold of `Concrete.Decls.toBytecode`. (`@[expose]` is now
on the definition, so this lemma could be inlined; kept for readability.) -/
theorem Concrete.Decls.toBytecode_unfold (decls : Concrete.Decls) :
    decls.toBytecode = (do
      let layout ← decls.layoutMap
      let initMemSizes : Lean.RBTree Nat compare := .empty
      let (functions, memSizes, nameMap) ← decls.foldlM
        (init := ((#[] : Array Bytecode.Function), initMemSizes,
                  ({} : Std.HashMap Global Bytecode.FunIdx)))
        fun acc@(functions, _memSizes, nameMap) (_, decl) => match decl with
          | .function function => do
            let (body, layoutMState) ← function.compile layout
            let nameMap := nameMap.insert function.name functions.size
            let function : Bytecode.Function :=
              ⟨body, layoutMState.functionLayout, function.entry, false⟩
            let memSizes := layoutMState.memSizes.fold (·.insert ·) acc.2.1
            pure (functions.push function, memSizes, nameMap)
          | _ => pure acc
      pure (⟨functions, memSizes.toArray⟩, nameMap)) := by
  rfl

/-! ### Infrastructure for dual-fold counting (toBytecode + layoutMap).

The `toBytecode` fold and the `layoutMap` fold each iterate `cd.pairs.toList`.
Both increment a function counter by 1 per `.function` decl and by 0 otherwise.
We extract explicit step functions, show each equals `countFunctions` of the
processed prefix, then bridge `layout[g]? = .function fl` to
`fl.index < countFunctions` via a per-step invariant. -/

private abbrev BCAcc :=
  Array Bytecode.Function × Lean.RBTree Nat compare ×
    Std.HashMap Global Bytecode.FunIdx

private abbrev bytecodeStep (lm : LayoutMap) (acc : BCAcc)
    (x : Global × Concrete.Declaration) : Except String BCAcc :=
  match x.2 with
  | .function function => do
    let (body, layoutMState) ← Concrete.Function.compile lm function
    let nameMap := acc.2.2.insert function.name acc.1.size
    let function' : Bytecode.Function :=
      ⟨body, layoutMState.functionLayout, function.entry, false⟩
    let memSizes := layoutMState.memSizes.fold
      (fun s n => (s : Lean.RBTree Nat compare).insert n) acc.2.1
    pure (acc.1.push function', memSizes, nameMap)
  | _ => pure acc

private theorem toBytecode_eq_aux (cd : Concrete.Decls) (lm : LayoutMap)
    (hlm : cd.layoutMap = .ok lm) :
    cd.toBytecode = (do
      let r ← cd.pairs.toList.foldlM (bytecodeStep lm)
        ((#[], (Lean.RBTree.empty : Lean.RBTree Nat compare),
          ({} : Std.HashMap Global Bytecode.FunIdx)) : BCAcc)
      pure (⟨r.1, r.2.1.toArray⟩, r.2.2)) := by
  unfold Concrete.Decls.toBytecode
  simp only [bind, Except.bind, hlm]
  simp only [IndexMap.foldlM]
  rw [← Array.foldlM_toList]
  rfl

/-- Whole-fold `toBytecode` progress given per-function progress.

Migrated 2026-04-30 from `Scratch.lean:6446` (orphan helper) so that
`Lower.compile_progress_entry` (CompilerProgress.lean) can compose through it.
The hypothesis `hfn` packages per-function `Function.compile` progress on every
`.function` pair; the fold then succeeds since `.dataType` and `.constructor`
arms are pure pass-throughs. -/
theorem toBytecode_fold_progress
    {cd : Concrete.Decls} (lm : LayoutMap)
    (hlm : cd.layoutMap = .ok lm)
    (hfn : ∀ name f, cd.getByKey name = some (.function f) →
      ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms)) :
    ∃ result, cd.toBytecode = .ok result := by
  rw [toBytecode_eq_aux cd lm hlm]
  have hstep : ∀ (acc : BCAcc) (x : Global × Concrete.Declaration),
      x ∈ cd.pairs.toList →
      ∃ acc', bytecodeStep lm acc x = .ok acc' := by
    rintro acc ⟨xname, decl⟩ hmem
    cases hdecl : decl with
    | function function =>
      subst hdecl
      have hgbk : cd.getByKey xname = some (Concrete.Declaration.function function) :=
        IndexMap.getByKey_of_mem_pairs cd xname _ hmem
      obtain ⟨body, lms, hcomp⟩ := hfn xname function hgbk
      refine ⟨(acc.1.push
        ⟨body, lms.functionLayout, function.entry, false⟩,
        lms.memSizes.fold
          (fun (s : Lean.RBTree Nat compare) n => s.insert n) acc.2.1,
        acc.2.2.insert function.name acc.1.size), ?_⟩
      unfold bytecodeStep
      simp only [bind, Except.bind, hcomp, pure, Except.pure]
    | dataType dt =>
      refine ⟨acc, ?_⟩
      unfold bytecodeStep
      simp only [pure, Except.pure]
    | «constructor» dt c =>
      refine ⟨acc, ?_⟩
      unfold bytecodeStep
      simp only [pure, Except.pure]
  obtain ⟨r, hfold⟩ := List.foldlM_except_ok' cd.pairs.toList
    ((#[], (Lean.RBTree.empty : Lean.RBTree Nat compare),
      ({} : Std.HashMap Global Bytecode.FunIdx)) : BCAcc) hstep
  refine ⟨(⟨r.1, r.2.1.toArray⟩, r.2.2), ?_⟩
  rw [hfold]; rfl


/-- `countFunctions xs` counts `.function` declarations in `xs`. -/
private def countFunctions : List (Global × Concrete.Declaration) → Nat
  | [] => 0
  | (_, .function _) :: xs => countFunctions xs + 1
  | (_, .dataType _) :: xs => countFunctions xs
  | (_, .constructor _ _) :: xs => countFunctions xs

private theorem bytecodeStep_preserves_size_plus_count
    (lm : LayoutMap) :
    ∀ (xs : List (Global × Concrete.Declaration))
      (init result : BCAcc),
      xs.foldlM (bytecodeStep lm) init = .ok result →
      result.1.size = init.1.size + countFunctions xs := by
  intro xs
  induction xs with
  | nil =>
    intro init result h
    simp only [List.foldlM_nil, pure, Except.pure] at h
    cases h; simp [countFunctions]
  | cons x rest ih =>
    intro init result h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by intro heq; cases heq)
    rename_i acc' hstep
    obtain ⟨xname, decl⟩ := x
    unfold bytecodeStep at hstep
    simp only at hstep
    cases decl with
    | function function =>
      simp only [bind, Except.bind] at hstep
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, lms⟩ := res
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_size : acc'.1.size = init.1.size + 1 := by
        rw [← hacc']; simp [Array.size_push]
      have ih_res := ih acc' result h
      rw [ih_res, hacc_size, countFunctions]
      omega
    | dataType dt =>
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_size : acc'.1.size = init.1.size := by
        rw [← hacc']
      have ih_res := ih acc' result h
      rw [ih_res, hacc_size, countFunctions]
    | «constructor» dt c =>
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_size : acc'.1.size = init.1.size := by
        rw [← hacc']
      have ih_res := ih acc' result h
      rw [ih_res, hacc_size, countFunctions]

private theorem toBytecode_functions_size_eq_countFunctions
    {cd : Concrete.Decls} {lm : LayoutMap}
    {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hlm : cd.layoutMap = .ok lm)
    (hbc : cd.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    bytecodeRaw.functions.size = countFunctions cd.pairs.toList := by
  rw [toBytecode_eq_aux cd lm hlm] at hbc
  simp only [bind, Except.bind] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  rename_i r hfold
  simp only [pure, Except.pure] at hbc
  have hEq := Prod.mk.inj (Except.ok.inj hbc)
  have hBC :
    (⟨r.1, r.2.1.toArray⟩ : Bytecode.Toplevel) = bytecodeRaw := hEq.1
  have : bytecodeRaw.functions = r.1 := by cases hBC; rfl
  rw [this]
  have h := bytecodeStep_preserves_size_plus_count lm cd.pairs.toList _ _ hfold
  rw [h]; simp

private abbrev LMAcc := LayoutMap × Nat

private abbrev layoutMapStep (decls : Concrete.Decls) (acc : LMAcc)
    (x : Global × Concrete.Declaration) : Except String LMAcc :=
  match x.2 with
  | .dataType dataType => do
    let dataTypeSize ← dataType.size decls
    let layoutMap := acc.1.insert dataType.name (.dataType dataTypeSize)
    let pass := fun (acc : LayoutMap × Nat) constructor => do
      let offsets ← constructor.argTypes.foldlM (init := (#[0] : Array Nat))
        fun (offsets : Array Nat) typ => do
          let typSyze ← typ.size decls
          pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
      let decl : Layout := .constructor
        { size := dataTypeSize, offsets, index := acc.2 }
      let name := dataType.name.pushNamespace constructor.nameHead
      pure (acc.1.insert name decl, acc.2 + 1)
    let (layoutMap, _) ← dataType.constructors.foldlM pass (layoutMap, 0)
    pure (layoutMap, acc.2)
  | .function function => do
    let inputSize ← function.inputs.foldlM (init := 0) fun acc (_, typ) => do
      let typSize ← typ.size decls
      pure $ acc + typSize
    let outputSize ← function.output.size decls
    let offsets ← function.inputs.foldlM (init := (#[0] : Array Nat)) fun offsets (_, typ) => do
      let typSyze ← typ.size decls
      pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
    let layoutMap := acc.1.insert function.name $
      .function { index := acc.2, inputSize, outputSize, offsets }
    pure (layoutMap, acc.2 + 1)
  | .constructor .. => pure acc

private theorem layoutMap_eq_aux (cd : Concrete.Decls) :
    cd.layoutMap = (do
      let r ← cd.pairs.toList.foldlM (layoutMapStep cd) (({}, 0) : LMAcc)
      pure r.1) := by
  unfold Concrete.Decls.layoutMap
  simp only [bind, Except.bind]
  simp only [IndexMap.foldlM]
  rw [← Array.foldlM_toList]
  rfl

private theorem layoutMap_preserves_function_bound
    (decls : Concrete.Decls) :
    ∀ (xs : List (Global × Concrete.Declaration))
      (init result : LMAcc),
      (∀ (g' : Global) (fl' : FunctionLayout),
          init.1[g']? = some (Layout.function fl') → fl'.index < init.2) →
      xs.foldlM (layoutMapStep decls) init = .ok result →
      (∀ (g' : Global) (fl' : FunctionLayout),
        result.1[g']? = some (Layout.function fl') →
        fl'.index < init.2 + countFunctions xs) := by
  intro xs
  induction xs with
  | nil =>
    intro init result hinit h g' fl' hget
    simp only [List.foldlM_nil, pure, Except.pure] at h
    cases h
    simp [countFunctions]
    exact hinit g' fl' hget
  | cons x rest ih =>
    intro init result hinit h g' fl' hget
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by intro heq; cases heq)
    rename_i acc' hstep
    obtain ⟨xname, decl⟩ := x
    unfold layoutMapStep at hstep
    simp only at hstep
    cases decl with
    | function function =>
      simp only [bind, Except.bind] at hstep
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i inputSize hinp
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i outputSize hout
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i offsets hoff
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_snd : acc'.2 = init.2 + 1 := by rw [← hacc']
      have hacc_fst : acc'.1 =
        init.1.insert function.name
          (Layout.function { index := init.2, inputSize, outputSize, offsets }) := by
        rw [← hacc']
      have hinit' : ∀ (g' : Global) (fl' : FunctionLayout),
          acc'.1[g']? = some (Layout.function fl') → fl'.index < acc'.2 := by
        intro g'' fl'' hget''
        rw [hacc_fst] at hget''
        rw [Std.HashMap.getElem?_insert] at hget''
        split at hget''
        · have hi : (Layout.function { index := init.2, inputSize, outputSize, offsets }) =
              (Layout.function fl'') := Option.some.inj hget''
          have heq : fl'' =
              { index := init.2, inputSize, outputSize, offsets : FunctionLayout } := by
            cases hi; rfl
          rw [heq, hacc_snd]; exact Nat.lt_succ_self _
        · rw [hacc_snd]
          exact Nat.lt_succ_of_lt (hinit g'' fl'' hget'')
      have ih_res := ih acc' result hinit' h g' fl' hget
      rw [hacc_snd] at ih_res
      rw [countFunctions]; omega
    | dataType dt =>
      simp only [bind, Except.bind] at hstep
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i dataTypeSize hsize
      split at hstep
      · exact absurd hstep (by intro heq; cases heq)
      rename_i lmPair hpass
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_snd : acc'.2 = init.2 := by rw [← hacc']
      have hacc_fst : acc'.1 = lmPair.1 := by rw [← hacc']
      have hcons_preserve :
        ∀ (cs : List Concrete.Constructor) (initPair resultPair : LayoutMap × Nat),
          cs.foldlM (fun (acc : LayoutMap × Nat) (constructor : Concrete.Constructor) =>
            (do
              let offsets ← constructor.argTypes.foldlM (init := (#[0] : Array Nat))
                fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                  let typSyze ← Concrete.Typ.size decls {} typ
                  pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
              let decl : Layout := .constructor
                { size := dataTypeSize, offsets, index := acc.2 }
              let name := dt.name.pushNamespace constructor.nameHead
              pure (acc.1.insert name decl, acc.2 + 1) : Except String (LayoutMap × Nat)))
            initPair = .ok resultPair →
          ∀ (gx : Global) (flx : FunctionLayout),
            resultPair.1[gx]? = some (Layout.function flx) →
            initPair.1[gx]? = some (Layout.function flx) := by
        intro cs
        induction cs with
        | nil =>
          intro initPair resultPair hf gx flx hg
          simp only [List.foldlM_nil, pure, Except.pure] at hf
          cases hf; exact hg
        | cons c rest' ih' =>
          intro initPair resultPair hf gx flx hg
          simp only [List.foldlM_cons, bind, Except.bind] at hf
          split at hf
          · exact absurd hf (by intro heq; cases heq)
          rename_i acc'' hcstep
          split at hcstep
          · exact absurd hcstep (by intro heq; cases heq)
          rename_i offsets hoff'
          simp only [pure, Except.pure] at hcstep
          have hacc'' := Except.ok.inj hcstep
          have := ih' acc'' resultPair hf gx flx hg
          rw [← hacc''] at this
          rw [Std.HashMap.getElem?_insert] at this
          split at this
          · cases this
          · exact this
      have hinit' : ∀ (g' : Global) (fl' : FunctionLayout),
          acc'.1[g']? = some (Layout.function fl') → fl'.index < acc'.2 := by
        intro g'' fl'' hget''
        rw [hacc_fst] at hget''
        have hf :=
          hcons_preserve dt.constructors _ _ hpass g'' fl'' hget''
        rw [Std.HashMap.getElem?_insert] at hf
        split at hf
        · cases hf
        · rw [hacc_snd]; exact hinit g'' fl'' hf
      have ih_res := ih acc' result hinit' h g' fl' hget
      rw [hacc_snd] at ih_res
      rw [countFunctions]; exact ih_res
    | «constructor» dt c =>
      simp only [pure, Except.pure] at hstep
      have hacc' := Except.ok.inj hstep
      have hacc_snd : acc'.2 = init.2 := by rw [← hacc']
      have hacc_fst : acc'.1 = init.1 := by rw [← hacc']
      have hinit' : ∀ (g' : Global) (fl' : FunctionLayout),
          acc'.1[g']? = some (Layout.function fl') → fl'.index < acc'.2 := by
        rw [hacc_fst, hacc_snd]; exact hinit
      have ih_res := ih acc' result hinit' h g' fl' hget
      rw [hacc_snd] at ih_res
      rw [countFunctions]; exact ih_res

private theorem layoutMap_funcIdx_lt_countFunctions
    {cd : Concrete.Decls} {layout : LayoutMap}
    (hlm : cd.layoutMap = .ok layout)
    (g : Global) (fl : FunctionLayout)
    (hfl : layout[g]? = some (Layout.function fl)) :
    fl.index < countFunctions cd.pairs.toList := by
  rw [layoutMap_eq_aux cd] at hlm
  simp only [bind, Except.bind] at hlm
  split at hlm
  · exact absurd hlm (by intro heq; cases heq)
  rename_i r hfold
  simp only [pure, Except.pure] at hlm
  have hLayout : r.1 = layout := Except.ok.inj hlm
  have hbase : ∀ (g' : Global) (fl' : FunctionLayout),
      (({} : LayoutMap))[g']? = some (Layout.function fl') →
      fl'.index < 0 := by
    intro g' fl' hget; simp at hget
  have hp := layoutMap_preserves_function_bound cd cd.pairs.toList _ _ hbase hfold
  have := hp g fl (by rw [hLayout]; exact hfl)
  simpa using this

/- `Concrete.Function.compile_inputSize` moved to `Ix/Aiur/Compiler/Lower.lean`
(next to the definition it constrains). -/

/-- Every layout-map function index is < `bytecodeRaw.functions.size`. -/
theorem layout_funcIdx_lt_bytecode_size
    {decls : Concrete.Decls} {layout : LayoutMap}
    {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hlayout : decls.layoutMap = .ok layout)
    (hbc : decls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (g : Global) (fl : FunctionLayout)
    (hfl : layout[g]? = some (.function fl)) :
    fl.index < bytecodeRaw.functions.size := by
  have h1 := layoutMap_funcIdx_lt_countFunctions hlayout g fl hfl
  have h2 := toBytecode_functions_size_eq_countFunctions hlayout hbc
  rw [h2]; exact h1

/- `compile_callees_from_layout` and its downstream users
(`function_compile_callees_lt_final_size`, `toBytecode_fold_invariant`,
`preNameMap_in_range`, `toBytecode_callees_in_range`) live in
`Ix/Aiur/Proofs/LowerCalleesFromLayout.lean` to avoid bloating this file
with ~1200 lines of per-arm structural recursion. That file imports this one. -/

-- `function_compile_callees_lt_final_size` + `toBytecode_fold_invariant`
-- moved to `Ix/Aiur/Proofs/LowerCalleesFromLayout.lean`.

/-- `toBytecode`'s layout-map prerequisite succeeds whenever `toBytecode` does. -/
theorem toBytecode_layoutMap_ok
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hbc : cd.toBytecode = .ok (bytecode, preNameMap)) :
    ∃ lm, cd.layoutMap = .ok lm := by
  simp only [Concrete.Decls.toBytecode, bind, Except.bind] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  · exact ⟨_, by assumption⟩

-- `IndexMap.getByKey_of_indices_eq` + `toBytecode_function_extract`
-- moved to `LowerCalleesFromLayout.lean`.











/-- IndexMap key-uniqueness at value level: two pairs with BEq-equal keys have
equal values. Proof via `pairsIndexed` + `HashMap.getElem?_congr`. -/
private theorem indexMap_key_unique
    {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : _root_.IndexMap α β) {k₁ k₂ : α} {v₁ v₂ : β}
    (h₁ : (k₁, v₁) ∈ m.pairs.toList) (h₂ : (k₂, v₂) ∈ m.pairs.toList)
    (hbeq : (k₁ == k₂) = true) : v₁ = v₂ := by
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem h₂
  rw [Array.length_toList] at hi hj
  have hgeti : m.pairs[i]'hi = (k₁, v₁) := by rw [← hi_eq, Array.getElem_toList]
  have hgetj : m.pairs[j]'hj = (k₂, v₂) := by rw [← hj_eq, Array.getElem_toList]
  have hpi : m.indices[k₁]? = some i := by
    have := m.pairsIndexed i hi; rw [hgeti] at this; exact this
  have hpj : m.indices[k₂]? = some j := by
    have := m.pairsIndexed j hj; rw [hgetj] at this; exact this
  have hcong : m.indices[k₁]? = m.indices[k₂]? :=
    Std.HashMap.getElem?_congr hbeq
  rw [hpi, hpj] at hcong
  have hij : i = j := Option.some.inj hcong
  subst hij
  have : (k₁, v₁) = (k₂, v₂) := by rw [← hgeti, hgetj]
  exact (Prod.mk.inj this).2

/-- Inner ctor-fold preservation: given no pushed ctor-name equals `nm`, the
inner `foldlM` preserves existing `.function` entries at `nm`. -/
private theorem ctor_fold_preserves_function
    (decls : Concrete.Decls) (dt : Concrete.DataType) (dataTypeSize : Nat)
    (nm : Global) (layout : FunctionLayout) :
    ∀ (cs : List Concrete.Constructor) (initPair resultPair : LayoutMap × Nat),
      (∀ c ∈ cs, (dt.name.pushNamespace c.nameHead == nm) = false) →
      cs.foldlM (fun (acc : LayoutMap × Nat) (constructor : Concrete.Constructor) =>
        (do
          let offsets ← constructor.argTypes.foldlM (init := (#[0] : Array Nat))
            fun (offsets : Array Nat) (typ : Concrete.Typ) => do
              let typSyze ← Concrete.Typ.size decls {} typ
              pure $ offsets.push ((offsets[offsets.size - 1]?.getD 0) + typSyze)
          let decl : Layout := .constructor
            { size := dataTypeSize, offsets, index := acc.2 }
          let name := dt.name.pushNamespace constructor.nameHead
          pure (acc.1.insert name decl, acc.2 + 1) : Except String (LayoutMap × Nat)))
        initPair = .ok resultPair →
      initPair.1[nm]? = some (Layout.function layout) →
      resultPair.1[nm]? = some (Layout.function layout) := by
  intro cs
  induction cs with
  | nil =>
    intro initPair resultPair _ hf hinit
    simp only [List.foldlM_nil, pure, Except.pure] at hf
    cases hf; exact hinit
  | cons c rest ih =>
    intro initPair resultPair hne hf hinit
    simp only [List.foldlM_cons, bind, Except.bind] at hf
    split at hf
    · exact absurd hf (by intro heq; cases heq)
    rename_i acc' hcstep
    split at hcstep
    · exact absurd hcstep (by intro heq; cases heq)
    rename_i offsets hoff
    simp only [pure, Except.pure] at hcstep
    have hacc' := Except.ok.inj hcstep
    have hne_c : (dt.name.pushNamespace c.nameHead == nm) = false :=
      hne c (List.Mem.head _)
    have hne_rest : ∀ c' ∈ rest, (dt.name.pushNamespace c'.nameHead == nm) = false :=
      fun c' hc' => hne c' (List.Mem.tail _ hc')
    have hacc'_get : acc'.1[nm]? = some (Layout.function layout) := by
      rw [← hacc']
      simp only
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i hbeq; rw [hne_c] at hbeq; cases hbeq
      · exact hinit
    exact ih acc' resultPair hne_rest hf hacc'_get



namespace T3Private

open Concrete.Bytecode

/-- `m` is "input-size preserving" if running it doesn't change inputSize. -/
private def PreservesInputSize {α : Type} (m : LayoutM α) : Prop :=
  ∀ (s : LayoutMState), (m s).2.functionLayout.inputSize = s.functionLayout.inputSize

private theorem pure_preserves {α : Type} (a : α) : PreservesInputSize (pure a : LayoutM α) :=
  fun _ => rfl
private theorem bumpAuxiliaries_preserves (n : Nat) : PreservesInputSize (bumpAuxiliaries n) :=
  fun _ => rfl
private theorem pushDegrees_preserves (ds : Array Nat) : PreservesInputSize (pushDegrees ds) :=
  fun _ => rfl
private theorem setDegrees_preserves (ds : Array Nat) : PreservesInputSize (setDegrees ds) :=
  fun _ => rfl
private theorem setSharedData_preserves (sd : SharedData) : PreservesInputSize (setSharedData sd) :=
  fun _ => rfl
private theorem getSharedData_preserves : PreservesInputSize getSharedData :=
  fun _ => rfl
private theorem getDegrees_preserves : PreservesInputSize getDegrees :=
  fun _ => rfl
private theorem getDegree_preserves (v : Aiur.Bytecode.ValIdx) : PreservesInputSize (getDegree v) :=
  fun _ => rfl

private theorem bind_preserves {α β : Type} (m : LayoutM α) (k : α → LayoutM β)
    (hm : PreservesInputSize m) (hk : ∀ a, PreservesInputSize (k a)) :
    PreservesInputSize (m >>= k) := by
  intro s
  have h1 : ((m >>= k) s).2.functionLayout.inputSize =
            (k (m s).1 (m s).2).2.functionLayout.inputSize := rfl
  rw [h1, hk (m s).1, hm s]

private theorem opLayout_preserves_inputSize (op : Aiur.Bytecode.Op) :
    PreservesInputSize (opLayout op) := by
  cases op with
  | const _ => exact fun _ => rfl
  | add _ _ => intro s; rfl
  | sub _ _ => intro s; rfl
  | mul a b =>
    apply bind_preserves (getDegree a)
    · exact getDegree_preserves _
    · intro ad
      apply bind_preserves (getDegree b)
      · exact getDegree_preserves _
      · intro bd
        intro s'
        by_cases hd : ad + bd < 2
        · rw [if_pos hd]; rfl
        · rw [if_neg hd]; rfl
  | eqZero a =>
    apply bind_preserves (getDegree a)
    · exact getDegree_preserves _
    · intro d
      intro s'
      by_cases hd : d = 0
      · rw [if_pos hd]; rfl
      · rw [if_neg hd]; rfl
  | call _ _ outputSize unconstrained =>
    apply bind_preserves (pushDegrees _)
    · exact pushDegrees_preserves _
    · intro _
      apply bind_preserves (bumpAuxiliaries _)
      · exact bumpAuxiliaries_preserves _
      · intro _
        intro s'
        by_cases hu : !unconstrained
        · rw [if_pos hu]; rfl
        · rw [if_neg hu]; rfl
  | store _ => intro s; rfl
  | load _ _ => intro s; rfl
  | assertEq _ _ => intro s; rfl
  | ioGetInfo _ => intro s; rfl
  | ioSetInfo _ _ _ => intro s; rfl
  | ioRead _ _ => intro s; rfl
  | ioWrite _ => intro s; rfl
  | u8BitDecomposition _ => intro s; rfl
  | u8ShiftLeft _ => intro s; rfl
  | u8ShiftRight _ => intro s; rfl
  | u8Xor _ _ => intro s; rfl
  | u8And _ _ => intro s; rfl
  | u8Or _ _ => intro s; rfl
  | u8Add _ _ => intro s; rfl
  | u8Sub _ _ => intro s; rfl
  | u8LessThan _ _ => intro s; rfl
  | u32LessThan _ _ => intro s; rfl
  | debug _ _ => intro s; rfl

private theorem list_foldlM_preserves {α β : Type} (l : List α)
    (f : β → α → LayoutM β)
    (hf : ∀ b a, PreservesInputSize (f b a)) :
    ∀ (init : β), PreservesInputSize (l.foldlM f init) := by
  induction l with
  | nil => intro init s; rfl
  | cons x xs ih =>
    intro init s
    have heq : (x :: xs).foldlM f init = f init x >>= fun b => xs.foldlM f b := rfl
    show (((x :: xs).foldlM f init : LayoutM β) s).2.functionLayout.inputSize = _
    rw [heq]
    exact bind_preserves (f init x) (fun b => xs.foldlM f b) (hf init x) (fun b => ih b) s

private theorem array_foldlM_preserves {α β : Type} (arr : Array α)
    (f : β → α → LayoutM β)
    (hf : ∀ b a, PreservesInputSize (f b a)) :
    ∀ (init : β), PreservesInputSize (arr.foldlM f init) := by
  intro init s
  have hfold : arr.foldlM f init = arr.toList.foldlM f init := (Array.foldlM_toList).symm
  show ((arr.foldlM f init : LayoutM β) s).2.functionLayout.inputSize = _
  rw [hfold]
  exact list_foldlM_preserves arr.toList f hf init s

private theorem array_forM_preserves {α : Type} (arr : Array α) (f : α → LayoutM Unit)
    (hf : ∀ a, PreservesInputSize (f a)) :
    PreservesInputSize (arr.forM f) := by
  have heq : arr.forM f = arr.foldlM (fun (_ : Unit) a => f a) () := rfl
  intro s
  show ((arr.forM f : LayoutM Unit) s).2.functionLayout.inputSize = _
  rw [heq]
  exact array_foldlM_preserves arr (fun _ a => f a)
    (fun _ a => hf a) () s

mutual
private theorem ctrlLayout_preserves_inputSize (c : Aiur.Bytecode.Ctrl) :
    PreservesInputSize (ctrlLayout c) := by
  match hc : c with
  | .return _ _ =>
    intro s
    show ((ctrlLayout _ : LayoutM Unit) s).2.functionLayout.inputSize = _
    simp only [ctrlLayout]; rfl
  | .yield _ _ =>
    intro s
    show ((ctrlLayout _ : LayoutM Unit) s).2.functionLayout.inputSize = _
    simp only [ctrlLayout]; rfl
  | .match v branches defaultBranch =>
    intro s
    show ((ctrlLayout _ : LayoutM Unit) s).2.functionLayout.inputSize = _
    simp only [ctrlLayout]
    have hfold_body : ∀ (initSharedData : SharedData) (degrees : Array Nat)
        (curMax : SharedData) (ab : {x // x ∈ branches}),
        PreservesInputSize (do
          setSharedData initSharedData
          blockLayout ab.val.2
          let blockSharedData ← getSharedData
          setDegrees degrees
          pure (curMax.maximals blockSharedData)) := by
      intro initSharedData degrees curMax ⟨⟨_, block⟩, _⟩
      exact bind_preserves _ _ (setSharedData_preserves _) (fun _ =>
        bind_preserves _ _ (blockLayout_preserves_inputSize block) (fun _ =>
          bind_preserves _ _ getSharedData_preserves (fun _ =>
            bind_preserves _ _ (setDegrees_preserves _) (fun _ =>
              pure_preserves _))))
    have hfold : ∀ (initSharedData : SharedData) (degrees : Array Nat),
        PreservesInputSize (branches.attach.foldlM (init := initSharedData)
          fun curMax ⟨(_, block), _⟩ => do
            setSharedData initSharedData
            blockLayout block
            let blockSharedData ← getSharedData
            setDegrees degrees
            pure (curMax.maximals blockSharedData)) := by
      intro initSharedData degrees
      apply array_foldlM_preserves _ _ _ initSharedData
      intro b ab
      exact hfold_body initSharedData degrees b ab
    have hdefault_set : ∀ (initSharedData : SharedData) (degrees : Array Nat)
        (maximalSharedData : SharedData),
        PreservesInputSize (match defaultBranch with
          | none => do let y ← pure maximalSharedData; setSharedData y
          | some defaultBlock => do
              setSharedData initSharedData
              bumpAuxiliaries branches.size
              blockLayout defaultBlock
              let defaultBlockSharedData ← getSharedData
              setDegrees degrees
              let y ← pure (maximalSharedData.maximals defaultBlockSharedData)
              setSharedData y) := by
      intro initSharedData degrees maximalSharedData
      cases defaultBranch with
      | none =>
        exact bind_preserves _ _ (pure_preserves _) (fun _ => setSharedData_preserves _)
      | some defaultBlock =>
        exact bind_preserves _ _ (setSharedData_preserves _) (fun _ =>
          bind_preserves _ _ (bumpAuxiliaries_preserves _) (fun _ =>
            bind_preserves _ _ (blockLayout_preserves_inputSize defaultBlock) (fun _ =>
              bind_preserves _ _ getSharedData_preserves (fun _ =>
                bind_preserves _ _ (setDegrees_preserves _) (fun _ =>
                  bind_preserves _ _ (pure_preserves _) (fun _ =>
                    setSharedData_preserves _))))))
    exact bind_preserves _ _ getSharedData_preserves (fun initSharedData =>
      bind_preserves _ _ getDegrees_preserves (fun degrees =>
        bind_preserves _ _ (hfold initSharedData degrees) (fun maximalSharedData =>
          hdefault_set initSharedData degrees maximalSharedData))) s
  | .matchContinue v branches defaultBranch outputSize sharedAux sharedLookups continuation =>
    intro s
    show ((ctrlLayout _ : LayoutM Unit) s).2.functionLayout.inputSize = _
    simp only [ctrlLayout]
    have hfold_body : ∀ (initSharedData : SharedData) (degrees : Array Nat)
        (curMax : SharedData) (ab : {x // x ∈ branches}),
        PreservesInputSize (do
          setSharedData initSharedData
          blockLayout ab.val.2
          let blockSharedData ← getSharedData
          setDegrees degrees
          pure (curMax.maximals blockSharedData)) := by
      intro initSharedData degrees curMax ⟨⟨_, block⟩, _⟩
      exact bind_preserves _ _ (setSharedData_preserves _) (fun _ =>
        bind_preserves _ _ (blockLayout_preserves_inputSize block) (fun _ =>
          bind_preserves _ _ getSharedData_preserves (fun _ =>
            bind_preserves _ _ (setDegrees_preserves _) (fun _ =>
              pure_preserves _))))
    have hfold : ∀ (initSharedData : SharedData) (degrees : Array Nat),
        PreservesInputSize (branches.attach.foldlM (init := initSharedData)
          fun curMax ⟨(_, block), _⟩ => do
            setSharedData initSharedData
            blockLayout block
            let blockSharedData ← getSharedData
            setDegrees degrees
            pure (curMax.maximals blockSharedData)) := by
      intro initSharedData degrees
      apply array_foldlM_preserves _ _ _ initSharedData
      intro b ab
      exact hfold_body initSharedData degrees b ab
    have hcont : ∀ (initSharedData : SharedData) (degrees : Array Nat)
        (maximalSharedData : SharedData),
        PreservesInputSize (
          let __do_jp := fun finalMax => do
            setSharedData finalMax
            bumpAuxiliaries outputSize
            pushDegrees (Array.replicate outputSize 1)
            blockLayout continuation
          (match defaultBranch with
          | none => do let y ← pure maximalSharedData; __do_jp y
          | some defaultBlock => do
              setSharedData initSharedData
              bumpAuxiliaries branches.size
              blockLayout defaultBlock
              let defaultBlockSharedData ← getSharedData
              setDegrees degrees
              let y ← pure (maximalSharedData.maximals defaultBlockSharedData)
              __do_jp y)) := by
      intro initSharedData degrees maximalSharedData
      have hjp : ∀ (finalMax : SharedData), PreservesInputSize (do
          setSharedData finalMax
          bumpAuxiliaries outputSize
          pushDegrees (Array.replicate outputSize 1)
          blockLayout continuation) := by
        intro finalMax
        exact bind_preserves _ _ (setSharedData_preserves _) (fun _ =>
          bind_preserves _ _ (bumpAuxiliaries_preserves _) (fun _ =>
            bind_preserves _ _ (pushDegrees_preserves _) (fun _ =>
              blockLayout_preserves_inputSize continuation)))
      cases defaultBranch with
      | none =>
        exact bind_preserves _ _ (pure_preserves _) (fun y => hjp y)
      | some defaultBlock =>
        exact bind_preserves _ _ (setSharedData_preserves _) (fun _ =>
          bind_preserves _ _ (bumpAuxiliaries_preserves _) (fun _ =>
            bind_preserves _ _ (blockLayout_preserves_inputSize defaultBlock) (fun _ =>
              bind_preserves _ _ getSharedData_preserves (fun _ =>
                bind_preserves _ _ (setDegrees_preserves _) (fun _ =>
                  bind_preserves _ _ (pure_preserves _) (fun y => hjp y))))))
    exact bind_preserves _ _ getSharedData_preserves (fun initSharedData =>
      bind_preserves _ _ getDegrees_preserves (fun degrees =>
        bind_preserves _ _ (hfold initSharedData degrees) (fun maximalSharedData =>
          hcont initSharedData degrees maximalSharedData))) s
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind

private theorem blockLayout_preserves_inputSize (b : Aiur.Bytecode.Block) :
    PreservesInputSize (blockLayout b) := by
  intro s
  show ((blockLayout b : LayoutM Unit) s).2.functionLayout.inputSize = _
  simp only [blockLayout]
  exact bind_preserves _ _
    (array_forM_preserves b.ops opLayout opLayout_preserves_inputSize)
    (fun _ => ctrlLayout_preserves_inputSize b.ctrl) s
termination_by (sizeOf b, 1)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left
       rcases b with ⟨ops, ctrl⟩
       show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl
       omega)
end

private theorem inputs_foldlM_reaches_sum
    (layoutMap : LayoutMap) :
    ∀ (inputs : List (Local × Concrete.Typ))
      (initVal : Nat) (initBind : Std.HashMap Local (Array Bytecode.ValIdx))
      (finalVal : Nat) (finalBind : Std.HashMap Local (Array Bytecode.ValIdx)),
      inputs.foldlM (m := Except String) (init := (initVal, initBind))
        (fun (valIdx, bindings) (arg, typ) => do
          let len ← match typSize layoutMap typ with
            | .error e => throw e
            | .ok len => pure len
          let indices := Array.range' valIdx len
          pure (valIdx + len, bindings.insert arg indices)) = .ok (finalVal, finalBind) →
      finalVal = initVal + (inputs.map Prod.snd).foldl
        (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  intro inputs
  induction inputs with
  | nil =>
    intro iv ib fv fb hfold
    simp only [List.foldlM_nil, pure, Except.pure] at hfold
    cases hfold
    simp
  | cons x rest ih =>
    intro iv ib fv fb hfold
    obtain ⟨arg, typ⟩ := x
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hts : typSize layoutMap typ with
    | error e =>
      rw [hts] at hfold
      cases hfold
    | ok len =>
      rw [hts] at hfold
      simp only [pure, Except.pure] at hfold
      have hih := ih (iv + len) (ib.insert arg (Array.range' iv len)) fv fb hfold
      rw [hih]
      have hle : (typSize layoutMap typ).toOption.getD 0 = len := by
        rw [hts]; rfl
      simp only [List.map_cons, List.foldl_cons]
      rw [Nat.zero_add]
      rw [hle]
      have hdispl : ∀ (n : Nat) (xs : List (Concrete.Typ)),
          xs.foldl (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) n
          = n + xs.foldl (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
        intro n xs
        induction xs generalizing n with
        | nil => simp
        | cons y ys ih' =>
          simp only [List.foldl_cons]
          rw [ih' (n + _)]
          rw [ih' (0 + _)]
          rw [Nat.zero_add]
          omega
      rw [hdispl len (rest.map Prod.snd)]
      omega

private theorem blockLayout_run_new_inputSize (body : Aiur.Bytecode.Block) (valIdx : Nat) :
    (Concrete.Bytecode.blockLayout body
      (Concrete.Bytecode.LayoutMState.new valIdx)).snd.functionLayout.inputSize = valIdx := by
  have h := blockLayout_preserves_inputSize body (Concrete.Bytecode.LayoutMState.new valIdx)
  exact h.trans rfl

end T3Private

/-- Structural post-condition of `Concrete.Function.compile`: the compiled
`functionLayout.inputSize` equals the sum of `typSize layoutMap t` over the
input types. -/
theorem Concrete.Function.compile_inputSize
    {layoutMap : LayoutMap} {f : Concrete.Function}
    {body : Bytecode.Block} {lms : Concrete.Bytecode.LayoutMState}
    (hcomp : Concrete.Function.compile layoutMap f = .ok (body, lms)) :
    lms.functionLayout.inputSize =
      (f.inputs.map Prod.snd).foldl
        (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  unfold Concrete.Function.compile at hcomp
  simp only [bind, Except.bind] at hcomp
  split at hcomp
  all_goals (try exact absurd hcomp (by intro heq; cases heq))
  rename_i layout hfnLayout
  simp only [pure, Except.pure] at hcomp
  split at hcomp
  · exact absurd hcomp (by intro heq; cases heq)
  rename_i foldResult hfold
  obtain ⟨valIdx, bindings⟩ := foldResult
  split at hcomp
  · exact absurd hcomp (by intro heq; cases heq)
  rename_i bodyResult lms_inner hbody
  have hpair := Prod.mk.inj (Except.ok.inj hcomp)
  obtain ⟨hbody_eq, hlms_eq⟩ := hpair
  rw [← hlms_eq]
  show (Concrete.Bytecode.blockLayout bodyResult
          (Concrete.Bytecode.LayoutMState.new valIdx)).snd.functionLayout.inputSize = _
  rw [T3Private.blockLayout_run_new_inputSize]
  have := T3Private.inputs_foldlM_reaches_sum layoutMap f.inputs 0 default valIdx bindings hfold
  rw [this]
  omega

end Aiur

end -- public section
