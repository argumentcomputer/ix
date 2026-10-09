import Compilatrix.Cfg.Rc.Proof.Native.FrameState
import Compilatrix.Rt.Proof.StepTerm

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Rc.Procs Compilatrix.Rt.Proof Compilatrix.Rt.Lower

/-- A real finished raw cursor yields the actual tail-call terminator and
dynamic argument words, or follows the emitted Nat-overflow failure. -/
theorem Cursor.tail_receipt {T : Tables} {P : Cfg.Program} {lp : Lir.Program}
    {source : Cfg.Frame} {target : Lir.Frame} (cursor : Cursor T P lp source target)
    {fd : Cfg.Fun} {block : Cfg.Block}
    (sourceLookup : P.fun? source.fn = some fd) (blockLookup : fd.blocks[source.blk]? = some block)
    (finished : source.rest = []) {f : Nat} {args : List Fir.Arg}
    (terminal : block.term = .tcall f args)
    {addresses : AddressMap} {bound : Nat}
    (registers : FusedWords addresses (Fused T fd) bound source.env target.env)
    {values : List Own.RVal} (arguments : Own.evalArgs source.env args = some values)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    (∃ words function output operands,
      ListRel (fun value word => valueWord addresses value = some word) values words ∧
      lp.funcs[target.fn]? = some function ∧ function.blocks[target.label]? = some output ∧
      target.pos = output.body.size ∧ output.term = .tail f operands ∧
      Lir.evalArgs target.env operands = some words) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨fd', block', function, starts, off, chunk, state, final, sourceLookup', blockLookup',
    functionLookup, layout, start, held, lowering, extension, labels, opened, supply,
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
  obtain ⟨_, ⟨operands, lowered, rfl⟩ | rfl⟩ := term_tcall code opened
  · have live : ∀ arg ∈ args, LiveArg (Fused T fd) arg :=
      term_live blockLookup (fun y member => by
        simp only [otherUses, terminal, List.mem_append]
        exact .inr (by simpa [Cfg.Check.termVars] using argVars_of_mem member))
    obtain ⟨words, evaluated, represented, _⟩ := fused_operands_words registers lowered live arguments
    obtain ⟨output, outputLookup, size, term⟩ :=
      closedAt_of held (Grows.refl _) extension (t := .tail f operands) rfl
    refine .inl ⟨words, function, output, operands, represented, ?_, ?_, ?_, term, evaluated⟩
    · rw [fn]; exact functionLookup
    · rw [label]; exact outputLookup
    · exact pos.trans size.symm
  · have failed := fails_closed functionLookup
      (closedAt_of held (Grows.refl _) extension rfl) mem context target.env callers
    have same : Lir.atState mem context source.fn (off+state.cur) state.acc.length target.env callers =
        {mem, ctx := context, stack := target :: callers} := by
      rw [← fn, ← label, ← pos]
      cases target
      simp_all [Lir.atState]
    exact .inr (same ▸ failed)

/-- Tail entry replaces the active native frame and retains every older
caller literally. Entry and the optional forward trampoline are executed,
so a successful native enter is not a caller-supplied premise. -/
theorem FrameState.tail {config : Rt.Config} {P : Program}
    {pairs : List (Nat × Cfg.Fun)} {funcs : List Lir.Func}
    (consuming : consumeAll P = .ok pairs)
    (lowered : Rt.Lower.functions (tablesOf P pairs) (consumed P pairs) (rootsOf config P)
      (List.range P.base.size) = .ok funcs)
    (main : Nat) {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    {source : Cfg.Frame} {target : Lir.Frame}
    (before : FrameState P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
      addresses heapSize bound function source target)
    (sourceRange : source.fn < P.base.size) {sourceFd : Cfg.Fun} {sourceBlock : Cfg.Block}
    (sourceLookup : P.base.fun? source.fn = some sourceFd)
    (sourceBlockLookup : sourceFd.blocks[source.blk]? = some sourceBlock)
    (finished : source.rest = []) {f : Nat} {args : List Fir.Arg}
    (terminal : sourceBlock.term = .tcall f args)
    {values : List Own.RVal} (arguments : Own.evalArgs source.env args = some values)
    (range : f < P.base.size) {fd : Cfg.Fun} {block : Cfg.Block}
    (lookup : P.base.fun? f = some fd) (blockLookup : fd.blocks[0]? = some block)
    {calleeBound : Nat} (arity : block.params.length = values.length)
    (real : ∀ x ∈ block.params.map Prod.fst, x < calleeBound)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word)
    (callers : List Lir.Frame) :
    let lp := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main
    let calleeEnv := Own.bindAll .leaf (block.params.map Prod.fst) values
    (∃ consumedFd targetEnv offset,
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} 1
        (Lir.atState mem context f offset 0 targetEnv callers) ∧
      FrameState P pairs lp addresses heapSize calleeBound consumedFd
        {fn := f, blk := 0, rest := block.body, env := calleeEnv}
        {fn := f, label := offset, pos := 0, env := targetEnv}) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  dsimp only
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming sourceRange
  have sameSource : original = sourceFd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  have sameActual : actual = function := Option.some.inj (actualLookup.symm.trans before.lookup)
  subst actual
  obtain ⟨body, _, actualBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 sourceBlockLookup
  obtain ⟨rest, consumeRest, position⟩ := before.cursor
  rw [finished] at consumeRest
  simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at consumeRest
  subst rest
  have live : ∀ arg ∈ args, LiveArg (Fused (tablesOf P pairs) function) arg :=
    term_live actualBlock (fun y member => by
      simp only [otherUses, terminal, List.mem_append]
      exact .inr (by simpa [Cfg.Check.termVars] using argVars_of_mem member))
  have compatible := before.compatible.args live arguments
  have bounded := before.bounded.args args arguments
  rcases position.tail_receipt before.lookup actualBlock rfl terminal before.words arguments
      running mem context callers with success | failed
  · obtain ⟨words, lirFunction, output, operands, represented, functionLookup,
      outputLookup, pos, term, evaluated⟩ := success
    obtain ⟨consumedFd, callee, targetEnv, offset, consumedLookup, entered, entryTrace,
      entryCursor, entryWords⟩ := consumed_entry_words consuming lowered main range lookup
      blockLookup represented arity real mem context callers
    have called := Lir.step_tail (mem := mem) (ctx := context) (rest := callers)
      functionLookup outputLookup pos term evaluated entered
    refine .inl ⟨consumedFd, targetEnv, offset, ?_, consumedLookup, entryCursor, entryWords,
      (Own.Plain.envBounded_empty heapSize).bindAll _ bounded,
      FusedCtorOk.empty.bindAll _ _ compatible⟩
    simpa using (Lir.star_of_step called).trans entryTrace
  · exact .inr failed



end Compilatrix.Cfg.Rc.Native.Spec
