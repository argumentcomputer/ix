import IxCC.Recheck.Rc.Proof.ReleaseCore
import IxCC.Cfg.Rc.Proof.Physical.DropStep
import IxCC.Cfg.Rc.Proof.Physical.PublicRoot

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Own IxCC.Own.Rc IxCC.Rt.Rc.Procs

private theorem suffix_at {α : Type} (before after : List α) (i : Nat) :
    (before ++ after)[before.length + i]? = after[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem accepted_drop_index {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered) :
    lowered.drop = (layoutOf P).init + 3 + (reuseProcs (layoutOf P)).length := by
  obtain ⟨original, native, rfl, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, length, program, _⟩ := Native.Spec.lower_parts native
  change original.program.funcs.size = _
  rw [program]
  simp only [Lir.Program.splitCriticalEdges, Array.size_map, inlinedProgram,
    Prune.pruneUnusedReuse, Inline.inlineProgram,
    Array.size_mapIdx, rawProgram, List.size_toArray,
    List.length_append, List.length_cons, List.length_nil, length, wrappers_length, procedures_length]
  simp [layoutOf, Layout.init, Layout.incProc]
  omega

theorem source_stage_drop (P : Program) (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).init + 3 + (reuseProcs (layoutOf P)).length]? =
      some (Public.dropWrapper (layoutOf P).decProc) := by
  have beyond : ¬ (layoutOf P).init + 3 + (reuseProcs (layoutOf P)).length < P.base.size := by
    simp only [layoutOf, Layout.init, Layout.incProc]
    omega
  have index : (layoutOf P).init + 3 + (reuseProcs (layoutOf P)).length - P.base.size =
      (wrappers (layoutOf P)).length + ((procedures (layoutOf P)).length +
        (([Rt.Procs.cxInit, Rt.Procs.natPow, Rt.Procs.natGcd] : List Lir.Func).length +
          ((reuseProcs (layoutOf P)).length + 0))) := by
    rw [wrappers_length, procedures_length]
    simp only [layoutOf, Layout.init, Layout.incProc, List.length_cons, List.length_nil]
    omega
  rw [Public.Spec.sourceStage_get, ite_eq_right (fun h => absurd h beyond), index]
  simp only [Public.Spec.runtimeFunctions, List.append_assoc]
  rw [suffix_at, suffix_at, suffix_at, suffix_at]
  rfl

/-- Release the exact owned result of a physical source completion through
the actual public drop export. Neither readback nor header shape establishes
ownership: the Returned invariant supplies the single root occurrence. -/
theorem Returned.release_public {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (_admission : CodeAdmission F bodies P config pairs functions borrows uniqs)
    (accepted : Public.lower config F bodies P borrows uniqs = .ok lowered)
    {lp : Lir.Program} {origin : Heap} {originAddresses : AddressMap} {external : Nat → Nat}
    {context base limit : Lir.Word} {regionBytes : Nat} {logical : Fir.Val}
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical) :
    ∃ H' memory' slots' lists' clock,
      dropAll returned.heap [returned.value] = some H' ∧
      HeapState P pairs H' returned.addresses memory' external []
        context base returned.bump limit regionBytes slots' lists' ∧
      Gen.ProtectedFrame returned.memory memory' context base returned.bump ∧
      Lir.eval {lowered.runtime.program with main := lowered.drop} clock
        [returned.word] returned.memory context = .ok ([1], memory') := by
  obtain ⟨original, native, equal, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs', functions', _, _, _, _, _, _, length, program, _⟩ := Native.Spec.lower_parts native
  have splitEq : lowered.runtime.program =
      (Public.Spec.inlinedPublicProgram (layoutOf P) functions' main).splitCriticalEdges := by
    rw [equal]
    exact Public.Spec.assemble_split program
  have split : Lir.ProgSim (Public.Spec.inlinedPublicProgram (layoutOf P) functions' main)
      lowered.runtime.program
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions' main)) :=
    splitEq ▸ Public.Spec.program_split _
  have splitDrop : Lir.ProgSim (Public.Spec.inlinedPublicProgram (layoutOf P) functions' lowered.drop)
      {lowered.runtime.program with main := lowered.drop}
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions' main)) :=
    ⟨rfl, split.funcs⟩
  let inl := Public.Spec.inlinedPublicProgram (layoutOf P) functions' lowered.drop
  let arr := (inlinedProgram (layoutOf P) functions' lowered.drop).funcs
  have dropSize : lowered.drop = arr.size := by
    rw [equal]
    change original.program.funcs.size = _
    rw [program]
    simp [arr, Lir.Program.splitCriticalEdges, inlinedProgram, Prune.pruneUnusedReuse,
      Inline.inlineProgram, rawProgram]
  have wrapper : inl.funcs[lowered.drop]? = some (Public.dropWrapper (layoutOf P).decProc) := by
    change (arr.push (Public.dropWrapper (layoutOf P).decProc))[lowered.drop]? = _
    rw [dropSize, Array.getElem?_push_size]
  have runtime : inl.funcs[(layoutOf P).decProc]? = some Gen.dec := by
    have hge : (layoutOf P).sourceCount ≤ (layoutOf P).decProc := by
      simp [layoutOf, Layout.decProc, Layout.incProc]; omega
    have hle : (layoutOf P).decProc ≤ (layoutOf P).isUniqueProc := by
      simp [Layout.isUniqueProc, Layout.init, Layout.decProc]; omega
    have hraw := raw_dec_proc (l := layoutOf P) (funcs := functions') length lowered.drop
    have hinl : (inlinedProgram (layoutOf P) functions' lowered.drop).funcs[(layoutOf P).decProc]? = some Gen.dec := by
      rw [inlinedProgram, Prune.pruneUnusedReuse_get_le hle, Inline.inlineProgram_get_ge _ _ hge]
      exact hraw
    have hlt := (Array.getElem?_eq_some_iff.mp hinl).1
    simpa [inl, Public.Spec.inlinedPublicProgram, Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt] using hinl
  obtain ⟨H', memory', slots', lists', clock, released, ready, frame, execution⟩ :=
    drop_top returned.state returned.represented wrapper runtime rfl
  refine ⟨H', memory', slots', lists', clock, released, ready, frame, ?_⟩
  rw [program_eval_transfer splitDrop clock [returned.word] returned.memory context
    (by rw [execution]; intro impossible; cases impossible)]
  exact execution




end IxCC.Cfg.Rc.Native.Spec
