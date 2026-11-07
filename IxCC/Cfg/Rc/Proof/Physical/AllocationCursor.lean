import IxCC.Cfg.Rc.Proof.Physical.AllocationConsumed
import IxCC.Rt.Proof.Term

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt IxCC.Rt.Proof

/-- An unrepresentable literal closes the actual caller block before either
allocation call is emitted. This is Nat overflow, independently of heap room. -/
theorem lower_allocation_overflow {f wrapper x : Nat} {args : List Fir.Arg}
    (tables : Lower.Tables) (state : Lower.St)
    (overflow : Lower.operands f args = .ok none) :
    (Lower.instr f tables (.bind x (.fir (.call wrapper args)))).run state =
      .ok (false, closeSt state (.fail .natOverflow)) := by
  simp only [Lower.instr, Lower.withOperands, overflow]
  rfl

/-- Invert successful instruction lowering, retaining both the emitted call
and the literal-overflow block. No operand-success premise is required. -/
theorem allocation_lowering_cases {f wrapper x : Nat} {args : List Fir.Arg}
    {tables : Lower.Tables} {state final : Lower.St} {continues : Bool}
    (lowered : (Lower.instr f tables (.bind x (.fir (.call wrapper args)))).run state =
      .ok (continues, final)) :
    (∃ operands, Lower.operands f args = .ok (some operands) ∧ continues = true ∧
      final = {state with acc := Lir.Stmt.call [x] wrapper operands :: state.acc}) ∨
    (Lower.operands f args = .ok none ∧ continues = false ∧
      final = closeSt state (.fail .natOverflow)) := by
  rcases withOperands_run lowered with ⟨operands, hop, hc, emitted⟩ | failed
  · have emission : (Lower.emit (Lir.Stmt.call [x] wrapper operands)).run state =
        .ok ((), {state with acc := Lir.Stmt.call [x] wrapper operands :: state.acc}) := rfl
    rw [emission] at emitted
    exact .inl ⟨operands, hop, hc, (congrArg Prod.snd (Except.ok.inj emitted)).symm⟩
  · exact .inr failed

/-- The actual closed chunk reaches Nat overflow for every source of heap
state and every clock, with its memory and suspended caller stack untouched. -/
theorem allocation_overflow_cursor {P : Lir.Program} {fn f off : Nat}
    {function : Lir.Func} {starts : Src.NatMap Nat} {blocks : List Lower.PBlock}
    (functionLookup : P.funcs[fn]? = some function)
    (layout : Holds f function off starts blocks)
    {state : Lower.St}
    (extension : Ext blocks (closeSt state (.fail .natOverflow)))
    (mem : X86.Memory) (context : Lir.Word) (env : Lir.Env) (callers : List Lir.Frame)
    (clock : Nat) :
    Sem.Reaches (Lir.semStep P)
      (Lir.atState mem context fn (off + state.cur) state.acc.length env callers)
      clock (.resource .natOverflow) := by
  have closed : ClosedAt function off state (.fail .natOverflow) :=
    closedAt_of layout (Grows.refl _) extension rfl
  obtain ⟨block, lookup, size, term⟩ := closed
  have failed := Lir.fail_at (mem := mem) (ctx := context) (ρ := env) (rest := callers)
    functionLookup lookup size.symm term
  apply Sem.Reaches.final
  rw [Lir.semStep_fail.mpr failed]
  exact .fail

/-- The lowering receipt yields either the actual publishing-call cursor or
actual Nat overflow. The latter never invokes the allocator and must not be
merged with its separately proved heap-exhaustion outcome. -/
theorem allocation_cursor_cases {P : Lir.Program} {fn f off wrapper x : Nat}
    {function : Lir.Func} {starts : Src.NatMap Nat} {blocks : List Lower.PBlock}
    (functionLookup : P.funcs[fn]? = some function)
    (layout : Holds f function off starts blocks)
    {state final : Lower.St} {continues : Bool} {tables : Lower.Tables} {args : List Fir.Arg}
    (lowered : (Lower.instr f tables (.bind x (.fir (.call wrapper args)))).run state =
      .ok (continues, final))
    (extension : Ext blocks final) (opened : Open state)
    (mem : X86.Memory) (context : Lir.Word) (env : Lir.Env) (callers : List Lir.Frame) :
    (∃ operands block suffix, Lower.operands f args = .ok (some operands) ∧
      continues = true ∧ function.blocks[off+state.cur]? = some block ∧
      block.params = state.params ∧
      block.body.toList = state.acc.reverse ++ [.call [x] wrapper operands] ++ suffix) ∨
    (continues = false ∧ ∀ clock,
      Sem.Reaches (Lir.semStep P)
        (Lir.atState mem context fn (off+state.cur) state.acc.length env callers)
        clock (.resource .natOverflow)) := by
  rcases allocation_lowering_cases lowered with ⟨operands, hop, hc, equal⟩ | ⟨_, hc, equal⟩
  · subst final
    obtain ⟨block, suffix, lookup, params, body⟩ :=
      holds_open layout [Lir.Stmt.call [x] wrapper operands] state.fresh extension opened
    exact .inl ⟨operands, block, suffix, hop, hc, lookup, params, body⟩
  · subst final
    exact .inr ⟨hc, allocation_overflow_cursor functionLookup layout extension mem context env callers⟩





end IxCC.Cfg.Rc.Native
