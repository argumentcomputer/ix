import IxCC.Cfg.Rc.Proof.Native.CallEntry
import IxCC.Rt.Proof.StepTerm

/-! The concrete return terminator follows from the actual raw cursor and
source operand. Dynamic values use valueWord; the proof needs no immortal
heap invariant and includes the emitted Nat-overflow branch. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Lower IxCC.Rt.Proof
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs

theorem Cursor.ret {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.fun? source.fn = some fd) (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {arg : Fir.Arg} (terminal : block.term = .ret arg)
    {addresses : AddressMap} {bound : Nat} {sourceEnv : Own.Env}
    (registers : FusedWords addresses (Fused T fd) bound sourceEnv target.env)
    {value : Own.RVal} (argument : Own.evalArg sourceEnv arg = some value)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    (∃ word, valueWord addresses value = some word ∧ RetAt lp target word) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨fd', block', function, starts, off, chunk, state, final, sourceLookup', blockLookup',
    functionLookup, layout, start, held, lowering, extension, labeled, opened, supply,
    body, fn, label, pos⟩ := cursor
  have sameFd : fd' = fd := Option.some.inj (sourceLookup'.symm.trans sourceLookup)
  subst fd'
  have sameBlock : block' = block := Option.some.inj (blockLookup'.symm.trans blockLookup)
  subst block'
  rw [finished] at lowering
  have code := rest_nil lowering
  have unfused : fusable T (useCounts fd) block = none := by
    cases fused : fusable T (useCounts fd) block with
    | none => rfl
    | some row =>
      obtain ⟨init, condition, left, right⟩ := row
      obtain ⟨x, op, alts, default, _, _, switch, _⟩ := fusable_some fused
      rw [terminal] at switch
      cases switch
  simp only [unfused, terminal] at code
  obtain ⟨_, ⟨operand, lowered, rfl⟩ | rfl⟩ := term_ret code opened
  · have live : LiveArg (Fused T fd) arg :=
      fused_term_live blockLookup (args := [arg]) (fun y member => by
        simp only [otherUses, terminal, List.mem_append]
        exact .inr (by simpa [Cfg.Check.termVars] using argVars_of_mem member)) arg (by simp)
    obtain ⟨word, evaluated, represented, _⟩ := fused_operand_word registers lowered live argument
    obtain ⟨output, outputLookup, size, term⟩ :=
      closedAt_of held (Grows.refl _) extension (t := .ret operand) rfl
    refine .inl ⟨word, represented, running, function, output, operand, ?_, ?_, ?_, term, evaluated⟩
    · rw [fn]
      exact functionLookup
    · rw [label]
      exact outputLookup
    · exact pos.trans size.symm
  · have failed := fails_closed functionLookup
      (closedAt_of held (Grows.refl _) extension rfl) mem context target.env callers
    have same : Lir.atState mem context source.fn (off + state.cur) state.acc.length target.env callers =
        {mem, ctx := context, stack := target :: callers} := by
      rw [← fn, ← label, ← pos]
      cases target
      simp_all [Lir.atState]
    exact .inr (same ▸ failed)

/-- Recover the current consumed return block from accepted consumption.
The source terminator is preserved even when its body contains RC markers. -/
theorem ConsumedCursor.ret {P : Program} {pairs : List (Nat × Cfg.Fun)}
    (consuming : consumeAll P = .ok pairs) {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : ConsumedCursor P pairs lp source target)
    (range : source.fn < P.base.size) {fd actual : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.base.fun? source.fn = some fd)
    (actualLookup : (consumed P pairs).fun? source.fn = some actual)
    (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {arg : Fir.Arg} (terminal : block.term = .ret arg)
    {addresses : AddressMap} {bound : Nat} {sourceEnv : Own.Env}
    (registers : FusedWords addresses (Fused (tablesOf P pairs) actual) bound sourceEnv target.env)
    {value : Own.RVal} (argument : Own.evalArg sourceEnv arg = some value)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    (∃ word, valueWord addresses value = some word ∧ RetAt lp target word) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨original, consumedFd, originalLookup, receipt, consumedLookup⟩ := consumed_entry consuming range
  have sourceSame : original = fd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  have targetSame : consumedFd = actual := Option.some.inj (consumedLookup.symm.trans actualLookup)
  subst consumedFd
  obtain ⟨body, _, targetBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
  obtain ⟨rest, consumeRest, position⟩ := cursor
  rw [finished] at consumeRest
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
  subst rest
  apply Cursor.ret position actualLookup targetBlock rfl terminal registers argument running mem context callers



end IxCC.Cfg.Rc.Native.Spec
