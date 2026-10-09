import Compilatrix.Cfg.Rc.Proof.Native.ConsumedCursor

/-! Actual call entry, including the optional forward entry jump inserted
when the first Cfg block has predecessors. The result retains the exact
parameter-binding receipt for dynamic register relations. Memory and caller
frames stay identical throughout this zero-charge entry fragment. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Rt.Lower Compilatrix.Rt.Proof

theorem Cursor.enter {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {f : Nat} {fd : Cfg.Fun} {block : Cfg.Block} {function : Lir.Func}
    {starts : Src.NatMap Nat}
    (sourceLookup : P.fun? f = some fd) (targetLookup : lp.funcs[f]? = some function)
    (layout : Lowered T f fd function starts) (blockLookup : fd.blocks[0]? = some block)
    (sourceEnv : Own.Env) (words : List Lir.Word) (arity : words.length = block.params.length)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    ∃ callee prior targetEnv offset,
      Lir.enter lp f words = some callee ∧
      Lir.bindParams prior (block.params.map Prod.fst) words = some targetEnv ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := callee :: callers} 0
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      Cursor T P lp {fn := f, blk := 0, rest := block.body, env := sourceEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv} := by
  obtain ⟨offset, start, entry⟩ := layout.entry blockLookup
  rcases entry with ⟨merged, rfl, params⟩ | ⟨merged, firstBlock, positive, distinct, _, paramsLength⟩
  · obtain ⟨targetEnv, binding⟩ := bindParams_some ({} : Lir.Env)
      (ps := function.params) (ws := words) (by rw [params]; simpa using arity.symm)
    have entered : Lir.enter lp f words = some {fn := f, label := 0, pos := 0, env := targetEnv} := by
      simp [Lir.enter, targetLookup, binding]
    refine ⟨_, {}, targetEnv, 0, entered, ?_, .refl _, ?_⟩
    · rw [params] at binding
      exact binding
    · exact Cursor.head sourceLookup targetLookup layout blockLookup start sourceEnv targetEnv
  · obtain ⟨initialEnv, binding⟩ := bindParams_some ({} : Lir.Env)
      (ps := function.params) (ws := words) (by rw [paramsLength, arity])
    have entered : Lir.enter lp f words = some {fn := f, label := 0, pos := 0, env := initialEnv} := by
      simp [Lir.enter, targetLookup, binding]
    obtain ⟨targetBlock, targetBlockLookup, targetParams⟩ := layout.head blockLookup start
    have parameters : targetBlock.params = block.params.map Prod.fst := by
      rw [targetParams]
      simp [headParams, merged]
    obtain ⟨targetEnv, targetBinding⟩ := bindParams_some initialEnv
      (ps := block.params.map Prod.fst) (ws := words) (by simpa using arity.symm)
    have step := Lir.jump_at (p := lp) (mem := mem) (ctx := context) (rest := callers)
      (pos := 0) (ρ := initialEnv) (e := {target := offset, args := function.params.map .v})
      (vals := words) (ρ' := targetEnv) targetLookup firstBlock rfl rfl
      (evalArgs_bindParams distinct binding) targetBlockLookup (by rw [parameters]; exact targetBinding)
    have forward : decide (offset ≤ 0) = false := by simp; omega
    rw [forward] at step
    exact ⟨_, initialEnv, targetEnv, offset, entered, targetBinding, Lir.star_of_step step,
      Cursor.head sourceLookup targetLookup layout blockLookup start sourceEnv targetEnv⟩

/-- Entry from the actual admitted source and lowering receipts. Neither
native entry success nor its optional jump execution is a premise. -/
theorem ConsumedCursor.enter {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {f : Nat} (range : f < P.base.size)
    {fd : Cfg.Fun} {block : Cfg.Block} (lookup : P.base.fun? f = some fd)
    (blockLookup : fd.blocks[0]? = some block)
    (sourceEnv : Own.Env) (words : List Lir.Word) (arity : words.length = block.params.length)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    ∃ callee prior targetEnv offset,
      Lir.enter lp f words = some callee ∧
      Lir.bindParams prior (block.params.map Prod.fst) words = some targetEnv ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := callee :: callers} 0
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      ConsumedCursor P pairs lp {fn := f, blk := 0, rest := block.body, env := sourceEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv} := by
  obtain ⟨original, consumedFd, starts, originalLookup, receipt, consumedLookup, targetLookup, layout⟩ :=
    Public.Spec.source_raw_layout consuming lowered main range
  rw [lookup] at originalLookup
  cases originalLookup
  obtain ⟨body, consumedBody, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨callee, prior, targetEnv, offset, enter, binding, trace, cursor⟩ :=
    Cursor.enter consumedLookup targetLookup layout targetBlock sourceEnv words arity mem context callers
  exact ⟨callee, prior, targetEnv, offset, enter, binding, trace, body, consumedBody, cursor⟩



end Compilatrix.Cfg.Rc.Native.Spec
