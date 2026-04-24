module
public import Ix.Aiur.Proofs.LowerSoundCore
public import Ix.Aiur.Proofs.LowerCalleesFromLayout
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.BytecodeEval
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.Relation

/-!
Lower proof, full.

Extends the straight-line core to:
- `.match` in tail position.
- Non-tail `.match` via `Ctrl.matchContinue`, only for the let-RHS form matching
  `findNonTailMatch`. Matches in other positions are excluded by the
  `Concrete.Term` shape.
- `.ret` / `Ctrl.return` / `Ctrl.yield`.
- Function calls (`Op.call`); the `unconstrained` flag is semantically
  equivalent in both branches.
- `.store` / `.load` with width-bucketed memory.
- IO operations — the `IOBuffer` clause of the main theorem is discharged here.
- u8/u32 ops — `bv_decide` or a library of bitvector lemmas.
-/

public section

namespace Aiur

open Concrete

/-! ## Aux lemmas local to the full-term Lower proof. -/

/--
**TODO** (axiom): closure replaces the dispatch at the body of
`Aiur.interp_preserves_ValueHasTyp` in
`Ix/Aiur/Proofs/LowerSoundControl.lean`.

**Original theorem**: `Aiur.interp_preserves_ValueHasTyp` (was sub-leaf
of `Function_body_preservation_succ_fuel`, F=1).

**Target location**: `Ix/Aiur/Proofs/LowerSoundControl.lean` body of
`interp_preserves_ValueHasTyp` (dispatches to this axiom).

**Closure path**:
Full 36-arm structural induction over `Concrete.Term`, mirroring
`Concrete.Eval.interp` definition.
- Mutual induction with `evalList` for `.tuple` / `.array` arms.
- Cross-recursion with `Concrete.Eval.runFunction` for `.app` arm at
  `fuel - 1` (depends on `runFunction`-side typing invariant from S1
  via `runFunction_preserves_FnFree` chain).
- `.letLoad` / `.load` arms need `unflattenValue_preserves_ValueHasTyp`
  aux lemma (memory-layout vs typed-value roundtrip).
- `.ref g` arm depends on `RefClosed cd` chasing through to the
  matching datatype + constructor.

The `_hCtx` premise (per-binding typed-context shape) gives the
`.var l` arm the type information needed to discharge the term
annotation; an existential `∀ l v', ∃ τ, ValueHasTyp τ v'` form would
be too weak for the `.var l` arm (which needs `τ = term.typ`).

**Existing infrastructure to reuse**:
- `Concrete.Decls.RefClosed` predicate.
- `ValueHasTyp` predicate from `Semantics/ConcreteEval.lean`.
- Note: `flattenValue_size_of_ValueHasTyp` and `flattenValue_slice_at_offset`
  were deleted with `Scratch.lean`. Reintroduce upstream when consumer
  access arms are decomposed.

**Dependencies on other Todo axioms**: None (this is a sub-leaf used by
`Function_body_preservation_succ_fuel`).

**LoC estimate**: ~500-1000 LoC for the full induction.

**Risk factors**:
- Currently a monolithic axiom; subsequent decomposition into per-arm
  granular axioms (one per `Concrete.Term` constructor) would be
  cleaner.
- The `.app` arm's cross-recursion ordering vs `runFunction` may force
  termination annotations.
- `unflattenValue_preserves_ValueHasTyp` (memory roundtrip lemma) is
  itself non-trivial new infrastructure (~50-100 LoC).
-/
axiom _root_.Aiur.interp_preserves_ValueHasTyp_axiom
    {concDecls : Concrete.Decls} {fuel : Nat}
    {env : Concrete.Eval.Bindings} {term : Concrete.Term}
    {evalSt evalSt' : Concrete.Eval.EvalState} {v : Value}
    -- Pin `concDecls`/`term` to a real compilation pair. Without this,
    -- premises do not constrain `term`'s type annotation to match its
    -- actual eval result (counterexample: `term = .field .unit false 0`
    -- evaluates to `.field 0` value with `term.typ = .unit` ≠ `.field`,
    -- yielding `ValueHasTyp ∅ .unit (.field 0)` False). The real
    -- compilation pipeline guarantees term annotations match eval
    -- results via the typing-soundness invariant (separate future
    -- theorem).
    (_hCompChain : ∃ (t : Source.Toplevel) (tds : Typed.Decls),
      t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls ∧
      ∃ (lm : LayoutMap) (g : Global) (cf : Concrete.Function),
        concDecls.layoutMap = .ok lm ∧
        concDecls.getByKey g = some (.function cf) ∧
        cf.body = term)
    (_hRefClosed : Concrete.Decls.RefClosed concDecls)
    (_hCtx : Local → Concrete.Typ)
    (_hEnvTyped : ∀ l v', (l, v') ∈ env → ValueHasTyp concDecls (_hCtx l) v')
    (_hTermCtx : ∀ l, term = .var (_hCtx l) term.escapes l → term.typ = _hCtx l)
    (_hrun : Concrete.Eval.interp concDecls fuel env term evalSt
      = .ok (v, evalSt')) :
    ValueHasTyp concDecls term.typ v

theorem interp_preserves_ValueHasTyp
    {concDecls : Concrete.Decls} {fuel : Nat}
    {env : Concrete.Eval.Bindings} {term : Concrete.Term}
    {evalSt evalSt' : Concrete.Eval.EvalState} {v : Value}
    -- Compilation chain witness. Forwarded verbatim to the axiom;
    -- caller supplies from `compile_correct` context.
    (_hCompChain : ∃ (t : Source.Toplevel) (tds : Typed.Decls),
      t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls ∧
      ∃ (lm : LayoutMap) (g : Global) (cf : Concrete.Function),
        concDecls.layoutMap = .ok lm ∧
        concDecls.getByKey g = some (.function cf) ∧
        cf.body = term)
    (_hRefClosed : Concrete.Decls.RefClosed concDecls)
    -- `_hEnv` is a per-binding typed-context premise. An existential
    -- form `∀ l v', (l, v') ∈ env → ∃ τ, ValueHasTyp concDecls τ v'`
    -- is too weak for the `.var l` arm: that arm needs `ValueHasTyp τ
    -- v_loc` where `τ` is the term's annotation (`term.typ`), not just
    -- SOME type. The current form takes a typing context
    -- `_hCtx : Local → Typ` that maps each bound local to its declared
    -- concrete type, plus a per-binding typing premise that the env
    -- value at `l` has the ctx-declared type. The `.var l` arm
    -- dispatches: `term.typ = _hCtx l` (caller-provided well-typed-ness
    -- of the term in the ctx) and the env lookup yields a value with
    -- the same type.
    (_hCtx : Local → Concrete.Typ)
    (_hEnvTyped : ∀ l v', (l, v') ∈ env → ValueHasTyp concDecls (_hCtx l) v')
    -- Per-term well-typedness against the ctx. The `.var l` arm needs
    -- `term.typ = _hCtx l`; structural arms recursively need the IH at
    -- sub-terms with the same ctx (or extended ctx for `.let`-style binders).
    (_hTermCtx : ∀ l, term = .var (_hCtx l) term.escapes l → term.typ = _hCtx l)
    (_hrun : Concrete.Eval.interp concDecls fuel env term evalSt
      = .ok (v, evalSt')) :
    ValueHasTyp concDecls term.typ v :=
  Aiur.interp_preserves_ValueHasTyp_axiom _hCompChain _hRefClosed _hCtx
    _hEnvTyped _hTermCtx _hrun

/-! ### Decomposition of `Function_body_preservation`. -/

/-- Zero-fuel case. Trivial under the asymmetric `InterpResultEq`: concrete
side is `.error .outOfFuel` unconditionally at `fuel = 0`, and
`InterpResultEq (.error _) _ = True`. -/
private theorem Function_body_preservation_zero_fuel
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (name : Global) (f : Concrete.Function)
    (_hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (_hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ 0)
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ 0) := by
  simp only [Concrete.Eval.runFunction, Concrete.Eval.applyGlobal, InterpResultEq]
  split <;> trivial

/--
**TODO** (axiom): closure replaces the dispatch at the body of
`Aiur.Function_body_preservation_succ_fuel` in
`Ix/Aiur/Proofs/LowerSoundControl.lean`.

**Original theorem**: `Aiur.Function_body_preservation_succ_fuel`.

**Target location**: `Ix/Aiur/Proofs/LowerSoundControl.lean` body of
`Function_body_preservation_succ_fuel` (dispatches to this axiom).

**Closure category**: Per-block dispatch + per-arm
`toIndex_preservation_core_extended` cascade.

**Closure path** (precise, step-by-step):
1. **Reduce both runners to per-block evaluators**: `unfold
   Concrete.Eval.runFunction` on LHS to expose
   `Concrete.Eval.applyGlobal` then `Concrete.Eval.interpBlock` on
   `f.body` with empty bindings + `args` populated by
   `f.inputs.zip args`. `unfold Bytecode.Eval.runFunction` on RHS to
   expose the `Bytecode.Eval.interpFunction` over
   `bytecode.functions[funIdx]`.
2. **Extract bytecode function from cd**: apply
   `toBytecode_function_extract _hbc _hname _hfi` (already F=0 in
   `LowerShared.lean`) to obtain `bf : Bytecode.Function` with
   `bytecode.functions[funIdx] = bf` and
   `Concrete.Function.compile lm f = .ok (bf.body, lms)`.
3. **Establish input-bindings agreement**: invoke `inputs_foldlM_ok`
   (`CompilerProgress.lean`, F=0) to produce `bindings_conc` matching
   `f.inputs.zip args` and bytecode flat slot range agreement via
   `Flatten.args decls funcIdx args` width-bucket. Agreement comes
   from `typSize_ok_of_refClosed_lm` (`ConcretizeSound/SizeBound.lean`)
   per input.
4. **Dispatch to body bridge**: invoke
   `toIndex_preservation_core_extended` (LowerSoundCore.lean) with
   witness package `{ hbc, hlm, hctxR := bindings agreement from (3),
   hStateR := init, hargsR := from (3) }`. This bridge handles all 25
   source-term arms and recursively calls
   `Function_body_preservation_succ_fuel` at `fuel'` for `.app` arms
   (cross-recursion fuel decrement).
5. **`.app` arm cross-call**: when
   `toIndex_preservation_core_extended` hits the `.app` arm, it builds
   args via `flattenValue` per-input agreement and calls
   `Function_body_preservation_succ_fuel _hbc _hlm callee_g callee_f
   hcallee fc.idx hfi_callee args' io' fuel'-1 retTyp_callee`.
   Termination is on `fuel'`.
6. **Tail-position handling for `.match`/`.ret`/`Ctrl.matchContinue`/
   `Ctrl.return`/`Ctrl.yield`**: NEW `Block.compile_preservation`
   helper (~150 LoC), currently fused into the body. Plant as a
   separate F=1 theorem with documented arm-by-arm closure: each tail
   arm reduces to `toIndex_preservation_core_extended` on its
   scrutinee/value-position term, then constructs
   `Bytecode.Block.match`/`.return`/`.yield` to discharge.
7. **IO clause**: `Bytecode.Eval.runFunction` returns `(_, io_final)`;
   agreement comes from threading `IOBuffer.equiv` through every
   IO-touching arm (`.printChar`, etc.) — already F=0 in those arms of
   `toIndex_preservation_core_extended`.

**Existing infrastructure to reuse**:
- `toBytecode_function_extract` (`LowerShared.lean`) — F=0 cd-key →
  bytecode-function lookup.
- `toBytecode_layoutMap_ok` (`LowerShared.lean`) — derives `lm` from
  `_hbc` (already used at the caller `Function_body_preservation`,
  line 127).
- `toIndex_preservation_core_extended` (`LowerSoundCore.lean`) — main
  per-arm bridge, currently decomposed into 25 sub-sorries (status: 9
  inherited + 4 arith + 10 u8/u32 + 4 IO + 1 store at F=0; 6 access
  arms F=1 needing `interp_preserves_ValueHasTyp`; `.app` arm at F=1,
  see Step 5).
- `inputs_foldlM_ok` (`CompilerProgress.lean`, F=0) +
  `typSize_ok_of_refClosed_lm` (`ConcretizeSound/SizeBound.lean`) for
  Step 3.
- `interp_preserves_ValueHasTyp` (`LowerSoundControl.lean`, F=1 stub) —
  needed by the 6 access arms in
  `toIndex_preservation_core_extended`.

**Required new infrastructure (to plant before closure)**:
- Plant new helper `toIndex_preservation_core_extended : ∀ (lm :
  LayoutMap) (rc : Concrete.Decls.RefClosed cd) (t : Concrete.Term)
  (state state' : CompilerState) (idxs : ...) (bindings : ...),
    t.toIndex bindings ... |>.run state = .ok idxs state' →
    -- For each of the 25 Concrete.Term arms, a per-arm preservation
    -- bridge showing that the bytecode result matches the source
    -- evaluator result under InterpResultEq.`
  Decomposition: 9 inherited core arms + 4 arith + 10 u8/u32 + 4 IO + 1
  store at F=0; 6 access arms (F=1) blocked behind
  `interp_preserves_ValueHasTyp`; `.app` arm at F=1 requires the
  cross-call to `step_R_preservation_applyGlobal`. Sibling to the
  future `toIndex_progress_core_extended` planted alongside the
  progress proof.

**Dependencies on other Todo axioms**:
- `Aiur.interp_preserves_ValueHasTyp_axiom` (consumed in the 6
  access arms of the future `toIndex_preservation_core_extended`).
- `Aiur.step_R_preservation_applyGlobal_axiom` (consumed in the
  `.app` arm of the future bridge for cross-call simulation; closure
  of #12 unblocks the `.app` arm).

**LoC estimate**: ~400 LoC for the headline body + per-block dispatch
+ tail handling, **plus** ~500-1000 LoC of
`interp_preserves_ValueHasTyp` (separate piece, blocks 6 access arms
inside `toIndex_preservation_core_extended`).

**Risk factors**:
- `interp_preserves_ValueHasTyp` is itself axiomatized (F=1) — needs
  closure before this axiom's 6 access arms are dischargeable.
- `Block.compile_preservation` (Step 6) is un-extracted; body-fusion
  in `toIndex_preservation_core_extended` may not cleanly factor
  without a sig refactor.
- Termination on `fuel'` may require explicit `termination_by` if Lean
  cannot infer the cross-call recursion structure; check by mirroring
  `Function_body_preservation_zero_fuel` at line 40 (which does have a
  termination annotation when called at higher fuel).
-/
axiom _root_.Aiur.Function_body_preservation_succ_fuel_axiom
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls} {lm : LayoutMap}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (_hlm : cd.layoutMap = .ok lm)
    (name : Global) (f : Concrete.Function)
    (_hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (_hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (fuel' : Nat) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ (fuel'+1))
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ (fuel'+1))

/-- Successor-fuel case: reduces both sides to their per-block evaluators and
appeals to the (extended) `toIndex_preservation_core`. -/
private theorem Function_body_preservation_succ_fuel
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls} {lm : LayoutMap}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (_hlm : cd.layoutMap = .ok lm)
    (name : Global) (f : Concrete.Function)
    (_hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (_hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (fuel' : Nat) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ (fuel'+1))
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ (fuel'+1)) := by
  -- BLOCKED ON:
  -- (1) `toIndex_preservation_core_extended` (LowerSoundCore.lean) is
  --     **decomposed** into per-arm sorries; current closure status:
  --       - 9 inherited core arms — **F=0**.
  --       - 4 arithmetic arms (.add/.sub/.mul/.eqZero) — **F=0**.
  --       - 10 u8/u32 arms — **F=0**.
  --       - 4 IO arms — **F=0**.
  --       - 1 `.store` arm — **F=0**.
  --       - `.tuple`/`.array` arms — F=0 modulo a width-distribution
  --         tail equation.
  --       - 6 collection/access arms (letLoad/proj/get/slice/set/load) —
  --         F=1; closure path is now decomposed using
  --         `interp_preserves_ValueHasTyp` (NEW witness producer, F=1
  --         in LowerShared.lean) + `flattenValue_size_of_ValueHasTyp` /
  --         `flattenValue_slice_at_offset` (S18/S19, F=1). Each arm has
  --         a 4-5-step blocked path documented inline.
  --       - 1 `.app` arm — central recursive obligation; Phase 4.
  -- (2) Tail-position handling for `.match` / `.ret` / `Ctrl.matchContinue` /
  --     `Ctrl.return` / `Ctrl.yield` — these never appear inside `toIndex`
  --     (it throws); they are produced by `Term.compile`'s block-level
  --     dispatch and need a separate `Block.compile_preservation` lemma
  --     (currently fused into this proof's body).
  -- (3) Input-bindings-agreement helper: `Flatten.args decls funcIdx args`
  --     vs the per-input `bindings` emitted by the input-foldlM in
  --     `Function.compile` (`inputs_foldlM_ok` already covers progress;
  --     preservation needs the layout/width parity at every input).
  -- (4) Threading `Concrete.Decls.RefClosed concDecls` and an env-typing
  --     hypothesis through `toIndex_preservation_core_extended`'s
  --     signature so the access arms can invoke
  --     `interp_preserves_ValueHasTyp`. Caller-side discharge of these
  --     hypotheses comes from
  --     `concretize_produces_refClosed` (already F=0) and the
  --     input-args typing invariant (NEW; needed in Function_compile
  --     entry).
  -- Keepalive for `interp_preserves_ValueHasTyp` (F=1 sorry). Consumed
  -- by the 6 access arms (.proj/.get/.slice/.set/.letLoad/.load) of
  -- `toIndex_preservation_core_extended` once the access arms are
  -- threaded with `Concrete.Decls.RefClosed concDecls` + env-typing.
  let _ := @interp_preserves_ValueHasTyp
  exact Aiur.Function_body_preservation_succ_fuel_axiom _hbc _hlm
    name f _hname funIdx _hfi args io₀ fuel' retTyp

/-- Per-function preservation: `Concrete.Eval.runFunction` and the
compiled-bytecode evaluator agree on shared names. -/
theorem Function_body_preservation
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    -- Structural invariant on `cd`: `.function` pairs store their key as
    -- `f.name`. Passes through to `toBytecode_function_extract`.
    (_hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ fuel)
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ fuel) := by
  obtain ⟨lm, hlm⟩ := toBytecode_layoutMap_ok hbc
  cases fuel with
  | zero =>
    exact Function_body_preservation_zero_fuel hbc name f hname funIdx hfi args io₀ retTyp
  | succ fuel' =>
    exact Function_body_preservation_succ_fuel hbc hlm name f hname funIdx hfi
      args io₀ fuel' retTyp

/-! ### Decomposition of `Function_compile_progress`. -/


end Aiur

end -- public section
