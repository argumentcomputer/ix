import IxCC.Cfg.Rc.Proof.Physical.CaseLayout
import IxCC.Cfg.Rc.Proof.Physical.ConsumedSwitch

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Proof
open IxCC.Rt.Rc.Procs

theorem case_entry {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    (consuming : consumeAll P = .ok pairs) (switches : Rt.checkSwitches P.base = .ok ())
    {source : Cfg.Frame} {target : Lir.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {x : Fir.Var} {alts : List Own.Plain.Alt} {default : Option Own.Plain.Code}
    {key : Key.CtorKey} {body : Own.Plain.Code}
    (sourceState : At F P source ρ saved (.case x alts default))
    (selected : ownCase key alts default = some body)
    {addresses : AddressMap} {heap : Own.Heap} {bound : Nat} {function : Cfg.Fun}
    (frame : FrameState P pairs lp addresses heap.size bound function source target)
    (range : source.fn < P.base.size) (real : bound ≤ supOf function)
    (done : ∀ block, function.blocks[source.blk]? = some block →
      FusedDone (tablesOf P pairs) function block source)
    {value : Own.RVal} (lookup : ρ.get? x = some value) {fields : List Own.RVal}
    (constructor : value.asCtor (tablesOf P pairs).known heap = some (key, fields))
    {mem : X86.Memory} (liveHeap : Gen.HeapLive heap addresses mem)
    (compatibleHeap : HeapCtorOk (tablesOf P pairs) heap)
    (running : target.dsts = []) (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ after final cost,
      At F P after ρ saved body ∧ FrameState P pairs lp addresses heap.size bound function after final ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem, ctx := context, stack := final :: callers} ∧
      final.dsts = [] ∧ after.fn = source.fn ∧
      (∀ block, function.blocks[after.blk]? = some block →
        FusedDone (tablesOf P pairs) function block after)) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  have lexical : EnvSub ρ source.env := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sub, _⟩ := sourceState
    exact sub
  obtain ⟨fd, block, edges, fallback, edge, targetBlock, sourceLookup, blockLookup,
    finished, terminal, choice, noArgs, forward, targetLookup, noParams, enteredLayout⟩ :=
    case_layout sourceState selected
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming range
  have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans sourceLookup)
  subst original
  have actualEqual : actual = function := Option.some.inj (actualLookup.symm.trans frame.lookup)
  subst actual
  have member : edge ∈ block.term.edges := by
    rw [terminal]
    simp only [Cfg.Term.edges, List.mem_append, List.mem_map, Option.mem_toList]
    rw [selectEdge_dflt] at choice
    cases initial : Cfg.selectEdge key edges none with
    | some chosen =>
      rw [initial] at choice
      cases choice
      exact .inl (selectEdge_mem initial)
    | none => rw [initial] at choice; exact .inr choice
  have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
      ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
    cases target
    simp_all [Lir.atState]
  rcases ConsumedCursor.switch_reaches consuming switches frame range sourceLookup blockLookup
      finished terminal liveHeap compatibleHeap real done (lexical x value lookup) constructor choice
      context callers with reached | failure
  · obtain ⟨native, starts, off, chunks, low, pe, le, targetEnv, nativeLookup, layout, start,
      held, lower, edgeOk, back, resolved, reached, words⟩ := reached
    have arguments : Own.evalArgs ρ edge.args = some [] := by simp [noArgs, Own.evalArgs]
    rcases consumed_take_edge receipt frame.lookup blockLookup nativeLookup layout start held lower
        member targetLookup edgeOk resolved lexical lexical words arguments
        (by simp [noParams]) (by simp [noParams]) reached with failure | success
    · exact .inr (same ▸ failure)
    · obtain ⟨offset, charges, currentLabel, values, finalEnv, targetStart, labelLower, represented,
        binding, trace, actualBack, costBound, charged, entered, savedEnv, registers, lexicalRegisters⟩ := success
      simp only [noParams, List.map_nil, Own.bindAll] at entered registers
      let after : Cfg.Frame := {source with blk := edge.target, rest := targetBlock.body}
      let final : Lir.Frame := {fn := source.fn, label := offset, pos := 0, env := finalEnv}
      rw [same] at trace
      refine .inl ⟨after, final, charges + (decide (offset ≤ currentLabel)).toNat, enteredLayout,
        ⟨frame.lookup, entered, registers, frame.bounded, frame.compatible⟩,
        trace, rfl, rfl, ?_⟩
      intro consumedTarget foundTarget
      obtain ⟨targetBody, mapping, actualTarget⟩ := (consumeFunction_parts receipt).2.2.2.2.2 targetLookup
      rw [foundTarget] at actualTarget
      cases actualTarget
      intro init condition left right fused empty
      have originalEmpty : targetBlock.body = [] := empty
      have actualEmpty : targetBody = [] := by
        simpa only [originalEmpty, List.mapM_nil, pure, Except.pure, Except.ok.injEq] using mapping.symm
      obtain ⟨x, op, alts, default, nonempty, _⟩ := fusable_some fused
      simp [actualEmpty] at nonempty
  · exact .inr (same ▸ failure)


end IxCC.Cfg.Rc.Native
