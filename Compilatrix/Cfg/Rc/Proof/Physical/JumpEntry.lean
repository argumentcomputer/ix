import Compilatrix.Cfg.Rc.Proof.Physical.Jump
import Compilatrix.Cfg.Rc.Proof.Native.FrameState
import Compilatrix.Cfg.Rc.Proof.JumpStep

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Spec Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Rt.Proof
open Cfg.Proof (Impl spine)
open Compilatrix.Rt.Rc.Procs

/-- Enter the actual selected join body from its original RC syntax cursor.
The completed native lowering derives its edge and binding, and the saved
layout reconstructs all source join environments. Register coverage remains
over the entire actual Cfg map. -/
theorem jump_entry
    {F : Fir.Program} {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
    (consuming : consumeAll P = .ok pairs)
    {source : Cfg.Frame} {target : Lir.Frame} {ρ : Own.Env} {saved rest : List Own.Plain.JEntry}
    {j : Fir.JoinId} {args : List Fir.Arg} {entry : Own.Plain.JEntry}
    (sourceState : At F P source ρ saved (.jmp j args))
    (found : Own.Plain.lookupJ j saved = some (entry, rest))
    {values : List Own.RVal} (arguments : Own.evalArgs ρ args = some values)
    (arity : values.length = entry.params.length)
    {addresses : AddressMap} {heapSize bound : Nat} {function : Cfg.Fun}
    (frame : FrameState P pairs lp addresses heapSize bound function source target)
    (range : source.fn < P.base.size)
    (paramsReal : ∀ fd, P.base.fun? source.fn = some fd →
      ∀ (label : Nat) (block : Cfg.Block), fd.blocks[label]? = some block →
        ∀ x ∈ block.params.map Prod.fst, x < bound)
    (running : target.dsts = []) (mem : X86.Memory) (context : Lir.Word) (callers : List Lir.Frame) :
    (∃ after final cost,
      At F P after (Own.bindAll entry.env entry.params values) (entry.after rest) entry.body ∧
      FrameState P pairs lp addresses heapSize bound function after final ∧
      Sem.Star (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} cost
        {mem, ctx := context, stack := final :: callers} ∧
      entry.charged.toNat ≤ cost ∧ final.dsts = [] ∧
      after.fn = source.fn ∧
      (∀ block, function.blocks[after.blk]? = some block →
        FusedDone (tablesOf P pairs) function block after)) ∨
    Sem.Fails (Lir.semStep lp) {mem, ctx := context, stack := target :: callers} := by
  obtain ⟨fd, scope, params, acc, next, first, lo, lookup, sourceRange, sourceLayout, cursor,
    sub, below, scopedNames, joins⟩ := sourceState
  obtain ⟨bj, scope', ps, loEntry, loBody, bodyFirst, label, idEq, previous, lower,
    paramsEq, chargeRec, bodyLayout, savedSub, savedBelow, psLower, bodyLower, psUpper, bodyNames⟩ :=
    joins.lookup found
  let edge : Cfg.Edge := {target := bj, args, back := entry.charged}
  let block : Cfg.Block := {params, body := acc.reverse, term := .jump edge}
  have blockLookup : fd.blocks[source.blk]? = some block := by
    simpa only [skeleton, Impl, Cfg.Proof.jumpTerm, Cfg.Fun.block?, label, edge, block] using sourceLayout
  have finished : source.rest = [] := by simpa only [skeleton, spine] using cursor
  obtain ⟨terminal, targetLookup⟩ := Cfg.Proof.impl_head bodyLayout
  let targetBlock : Cfg.Block := {
    params := ps
    body := spine (skeleton P.base.size bodyFirst entry.body)
    term := terminal }
  have targetLookup' : fd.blocks[bj]? = some targetBlock := by
    simpa only [Cfg.Fun.block?, List.reverse_nil, List.nil_append] using targetLookup
  obtain ⟨original, actual, originalLookup, receipt, actualLookup⟩ := consumed_entry consuming range
  have originalEqual : original = fd := Option.some.inj (originalLookup.symm.trans lookup)
  subst original
  have actualEqual : actual = function := Option.some.inj (actualLookup.symm.trans frame.lookup)
  subst actual
  have member : edge ∈ block.term.edges := by simp [block, Cfg.Term.edges]
  obtain ⟨native, starts, off, chunks, low, pe, le, nativeLookup, layout, start, held,
      nativeLower, edgeOk, back, resolved, reached⟩ :=
    frame.cursor.jump_reaches consuming range lookup frame.lookup blockLookup finished
      (show block.term = .jump edge from rfl) mem context callers
  have length : targetBlock.params.length = values.length := by
    dsimp only [targetBlock]
    rw [arity, paramsEq]
    simp
  have real := paramsReal fd lookup bj targetBlock targetLookup'
  rcases consumed_take_edge receipt frame.lookup blockLookup nativeLookup layout start held nativeLower
      member targetLookup' edgeOk resolved sub savedSub frame.words arguments length real reached with failure | success
  · right
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at failure
    exact failure
  · obtain ⟨offset, charges, currentLabel, words, targetEnv, targetStart, labelLower, represented,
      binding, trace, actualBack, costBound, charged, entered, savedEnv, registers, lexicalRegisters⟩ := success
    let after : Cfg.Frame := { source with
      blk := bj
      rest := targetBlock.body
      env := Own.bindAll source.env (ps.map Prod.fst) values }
    let final : Lir.Frame := {fn := source.fn, label := offset, pos := 0, env := targetEnv}
    have restored : At F P after (Own.bindAll entry.env entry.params values) (entry.after rest) entry.body := by
      refine ⟨fd, _, ps, [], bj+1, bodyFirst, loBody, lookup, sourceRange, bodyLayout, rfl, ?_, ?_, bodyNames, ?_⟩
      · rw [paramsEq]
        exact Cfg.Proof.Sub.bindAll savedSub _ _
      · apply Cfg.Proof.below_bindAll
          (fun y value hy => Nat.lt_of_lt_of_le (savedBelow y value hy) bodyLower) ?_ values
        intro y hy
        rw [paramsEq] at hy
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact psUpper p hp
      · have agree : ∀ y, y < loEntry →
            (Own.bindAll source.env (ps.map Prod.fst) values).get? y = source.env.get? y := by
          intro y hy
          apply Cfg.Proof.bindAll_get_notin
          intro member
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
          exact (Nat.not_lt_of_ge (psLower p hp)) hy
        have tail := (previous.agree agree).mono bodyLower
        unfold Own.Plain.JEntry.after
        cases recCase : entry.isRec with
        | false => simpa [recCase] using tail
        | true =>
          simp only [↓reduceIte]
          have self := Joins.cons (e := {entry with charged := true}) (ps := ps) (bj := bj)
            (previous.agree agree) bodyLower paramsEq (fun _ => recCase)
            (by simpa [recCase] using bodyLayout)
            (fun y value hy => by rw [agree y (savedBelow y value hy)]; exact savedSub y value hy)
            savedBelow psLower bodyLower psUpper bodyNames
          simpa [recCase] using self
    have frameArgs : Own.evalArgs source.env args = some values := Cfg.Proof.evalArgs_sub sub arguments
    obtain ⟨body, _, consumedBlock⟩ := (consumeFunction_parts receipt).2.2.2.2.2 blockLookup
    have compatible := frame.compatible.args (edge_live consumedBlock member) frameArgs
    have bounded := frame.bounded.args args frameArgs
    have same : Lir.atState mem context target.fn target.label target.pos target.env callers =
        ({mem, ctx := context, stack := target :: callers} : Lir.State) := by
      cases target
      simp_all [Lir.atState]
    rw [same] at trace
    refine .inl ⟨after, final, charges + (decide (offset ≤ currentLabel)).toNat, restored,
      ⟨frame.lookup, entered, registers, frame.bounded.bindAll _ bounded,
        frame.compatible.bindAll _ _ compatible⟩,
      trace, costBound, rfl, rfl, ?_⟩
    intro consumedTarget foundTarget
    obtain ⟨targetBody, mapping, actualTarget⟩ := (consumeFunction_parts receipt).2.2.2.2.2 targetLookup'
    rw [foundTarget] at actualTarget
    cases actualTarget
    intro init condition left right fused empty
    have originalEmpty : targetBlock.body = [] := empty
    have actualEmpty : targetBody = [] := by
      simpa only [originalEmpty, List.mapM_nil, pure, Except.pure, Except.ok.injEq] using mapping.symm
    obtain ⟨x, op, alts, default, nonempty, _⟩ := fusable_some fused
    simp [actualEmpty] at nonempty


end Compilatrix.Cfg.Rc.Native
