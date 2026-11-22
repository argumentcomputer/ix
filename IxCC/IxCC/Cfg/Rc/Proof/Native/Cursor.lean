import IxCC.Cfg.Rc.Proof.Native.RawSource
import IxCC.Rt.Proof.StepInstr

/-! A table-parameterized raw lowering position. RC overrides the runtime
procedure IDs, so this relation records the actual tables rather than using
the immortal compiler's default table constructor. No heap simulation is
stored as a field. In particular, call statement and return-position facts
are derived from the completed lowering receipt below. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Lower IxCC.Rt.Proof

def Cursor (T : Tables) (P : Cfg.Program) (lp : Lir.Program)
    (source : Cfg.Frame) (target : Lir.Frame) : Prop :=
  ∃ (fd : Cfg.Fun) (block : Cfg.Block) (function : Lir.Func)
    (starts : Src.NatMap Nat) (off : Nat) (chunk : List PBlock) (state final : St),
    P.fun? source.fn = some fd ∧ fd.blocks[source.blk]? = some block ∧
    lp.funcs[source.fn]? = some function ∧ Lowered T source.fn fd function starts ∧
    starts.get? source.blk = some off ∧ Holds source.fn function off starts chunk ∧
    (restAct source.fn T (useCounts fd) source.blk block source.rest).run state = .ok ((), final) ∧
    Ext chunk final ∧ Labels state ∧ Open state ∧ supOf fd ≤ state.fresh ∧
    (∃ pre, pre ++ source.rest = block.body) ∧
    target.fn = source.fn ∧ target.label = off + state.cur ∧ target.pos = state.acc.length

theorem Cursor.withEnvs {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    (sourceEnv : Own.Env) (targetEnv : Lir.Env) (destinations : List Nat) :
    Cursor T P lp {source with env := sourceEnv}
      {target with env := targetEnv, dsts := destinations} := cursor

theorem Cursor.head {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {f i offset : Nat} {fd : Cfg.Fun} {block : Cfg.Block}
    {function : Lir.Func} {starts : Src.NatMap Nat}
    (sourceLookup : P.fun? f = some fd) (targetLookup : lp.funcs[f]? = some function)
    (layout : Lowered T f fd function starts)
    (blockLookup : fd.blocks[i]? = some block) (start : starts.get? i = some offset)
    (sourceEnv : Own.Env) (targetEnv : Lir.Env) :
    Cursor T P lp {fn := f, blk := i, rest := block.body, env := sourceEnv}
      {fn := f, label := offset, pos := 0, env := targetEnv} := by
  obtain ⟨off, chunk, fresh, final, hoff, held, supply, lowering, extension, _⟩ := layout.chunk blockLookup
  rw [start] at hoff
  cases hoff
  refine ⟨fd, block, function, starts, offset, chunk, openSt fresh (headParams fd i block), final,
    sourceLookup, blockLookup, targetLookup, layout, start, held, ?_, extension,
    labels_openSt _ _, open_openSt _ _, supply, ⟨[], rfl⟩, rfl, ?_, ?_⟩
  · rw [restAct_body]
    exact lowering
  · simp [openSt]
  · simp [openSt]

/-- Every real call expansion supplies the concrete instruction and a cursor
for the suspended/resumed caller. Unrepresentable operands instead produce
the actual target resource branch; no successful operand premise is needed. -/
theorem Cursor.call {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {x callee : Nat} {args : List Fir.Arg} {tail : List Cfg.Instr}
    (instruction : source.rest = .bind x (.fir (.call callee args)) :: tail)
    (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ operands function block,
      Rt.Lower.operands source.fn args = .ok (some operands) ∧
      lp.funcs[target.fn]? = some function ∧ function.blocks[target.label]? = some block ∧
      ∃ position : target.pos < block.body.size,
        block.body[target.pos] = .call [x] callee operands ∧
        Cursor T P lp {source with rest := tail} {target with pos := target.pos + 1}) ∨
    Sem.Fails (Lir.semStep lp)
      (Lir.atState mem context target.fn target.label target.pos target.env callers) := by
  obtain ⟨fd, block, function, starts, off, chunk, state, final, sourceLookup, blockLookup,
    targetLookup, layout, start, held, lowering, extension, labeled, opened, supply,
    ⟨pre, body⟩, fn, label, pos⟩ := cursor
  rw [instruction] at lowering body
  have unfused : (fusable T (useCounts fd) block).isSome = true → tail ≠ [] := by
    intro someFused empty
    subst tail
    obtain ⟨⟨init, cond, left, right⟩, fused⟩ := Option.isSome_iff_exists.1 someFused
    obtain ⟨y, op, _, _, equal, _⟩ := fused_last fused body
    simp only [Cfg.Instr.bind.injEq] at equal
    cases equal.2
  obtain ⟨continues, after, lowered, ⟨rfl, rest⟩ | ⟨rfl, rfl⟩⟩ := rest_cons lowering unfused
  · obtain ⟨grows, labeled', opened'⟩ := instr_mono lowered labeled opened
    have afterExt : Ext chunk after := (rest_grows rest labeled' opened').ext extension
    rcases withOperands_run lowered with ⟨operands, hop, _, emitted⟩ | ⟨_, impossible, _⟩
    · rw [emit_run] at emitted
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at emitted
      subst after
      obtain ⟨output, suffix, lookup, _, statements⟩ :=
        holds_open held [Lir.Stmt.call [x] callee operands] state.fresh afterExt opened
      have position : state.acc.length < output.body.size := by
        rw [← Array.length_toList, statements]
        simp
      have statement : output.body[state.acc.length] = .call [x] callee operands := by
        rw [← Array.getElem_toList (h := position)]
        simp only [statements]
        rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
        simp
      refine .inl ⟨operands, function, output, hop, ?_, ?_, ?_, ?_, ?_⟩
      · rw [fn]
        exact targetLookup
      · rw [label]
        exact lookup
      · simpa [pos] using position
      · simpa [pos] using statement
      · refine ⟨fd, block, function, starts, off, chunk,
          {state with acc := Lir.Stmt.call [x] callee operands :: state.acc}, final,
          sourceLookup, blockLookup, targetLookup, layout, start, held, rest, extension,
          labeled', opened', supply, ⟨pre ++ [.bind x (.fir (.call callee args))], ?_⟩,
          fn, label, ?_⟩
        · simpa using body
        · simp [pos]
    · cases impossible
  · right
    rw [fn, label, pos]
    exact instr_fails targetLookup held lowered extension opened mem target.env callers




end IxCC.Cfg.Rc.Native.Spec
