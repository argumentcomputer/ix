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
  sorry

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
