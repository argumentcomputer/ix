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
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, _, length, program, _⟩ := Native.Spec.lower_parts native
  change original.program.funcs.size = _
  rw [program]
  simp only [Lir.Program.splitCriticalEdges_eq, Array.size_map, inlinedProgram,
    Prune.pruneDeadRuntime, FastDec.install, InlineWrappers.inlineProgram, Prune.pruneUnusedReuse,
    Inline.inlineProgram, Array.size_mapIdx, rawProgram, List.size_toArray,
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
  obtain ⟨main, pairs', functions', _, _, _, _, _, _, _, length, program, _⟩ := Native.Spec.lower_parts native
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
      (Public.Spec.labels (Public.Spec.inlinedPublicProgram (layoutOf P) functions' main)) := by
    rw [inlinedPublicProgram_main_upd (layoutOf P) functions' main lowered.drop]
    exact ⟨rfl, split.funcs⟩
  let inl := Public.Spec.inlinedPublicProgram (layoutOf P) functions' lowered.drop
  let postDec := Public.Spec.postDecPublicProgram (layoutOf P) functions' lowered.drop
  let preDec := InlineWrappers.inlineProgram (layoutOf P)
    (Prune.pruneUnusedReuse (layoutOf P)
      (Inline.inlineProgram (layoutOf P) (Public.Spec.rawPublicProgram (layoutOf P) functions' lowered.drop)))
  have inlEq : inl = Prune.pruneDeadRuntime (layoutOf P) postDec :=
    Public.Spec.inlinedPublicProgram_eq_inline (layoutOf P) functions' lowered.drop length
  let arr := (inlinedProgram (layoutOf P) functions' lowered.drop).funcs
  have dropSize : lowered.drop = arr.size := by
    rw [equal]
    change original.program.funcs.size = _
    rw [program]
    simp [arr, Lir.Program.splitCriticalEdges_eq, inlinedProgram, Prune.pruneDeadRuntime,
      FastDec.install, InlineWrappers.inlineProgram, Prune.pruneUnusedReuse, Inline.inlineProgram,
      rawProgram]
  have hneDrop : lowered.drop ≠ (layoutOf P).decProc := by
    rw [accepted_drop_index accepted]
    apply Nat.ne_of_gt
    simp only [Layout.init, Layout.decProc]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_trans (Nat.le_add_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
  have hnpDrop : Prune.isPrunableDeadRuntime (layoutOf P) lowered.drop = false := by
    apply Prune.isPrunableDeadRuntime_of_gt_isUnique
    rw [accepted_drop_index accepted]
    simp only [Layout.isUniqueProc, reuseProcs, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have wrapperInl : inl.funcs[lowered.drop]? = some (Public.dropWrapper (layoutOf P).decProc) := by
    change (arr.push (Public.dropWrapper (layoutOf P).decProc))[lowered.drop]? = _
    rw [dropSize, Array.getElem?_push_size]
  have wrapperPost : postDec.funcs[lowered.drop]? = some (Public.dropWrapper (layoutOf P).decProc) := by
    rw [inlEq, Prune.pruneDeadRuntime_get_not_prunable hnpDrop] at wrapperInl
    exact wrapperInl
  have wrapper : preDec.funcs[lowered.drop]? = some (Public.dropWrapper (layoutOf P).decProc) := by
    rw [show postDec = FastDec.install (layoutOf P) preDec from rfl,
      FastDec.install_get_ne _ _ hneDrop] at wrapperPost
    exact wrapperPost
  have runtime : preDec.funcs[(layoutOf P).decProc]? = some Gen.dec :=
    Public.Spec.preDecPublicProgram_decProc (l := layoutOf P) length lowered.drop
  obtain ⟨H', memory', slots', lists', clock, released, ready, frame, execution⟩ :=
    drop_top returned.state returned.represented wrapper runtime rfl
  obtain ⟨clock', execFast⟩ :=
    FastDec.install_forward_eq runtime
      (by rw [execution]; intro h; cases h)
      (by rw [execution]; intro h; cases h)
  have hmainPost : postDec.main = lowered.drop := by
    rw [show postDec = Public.Spec.postDecPublicProgram (layoutOf P) functions' lowered.drop from rfl,
      Public.Spec.postDecPublicProgram, FastDec.install_main, InlineWrappers.inlineProgram_main,
      Prune.pruneUnusedReuse_main]
    rfl
  have hliveDrop : Prune.LiveRuntimeFn (layoutOf P) postDec postDec.main := by
    rw [hmainPost]
    exact Prune.liveRuntimeFn_of_not_prunable hnpDrop
  have execPruned : Lir.eval inl clock' [returned.word] returned.memory context =
      .ok ([1], memory') := by
    rw [inlEq, Prune.pruneDeadRuntime_eval_eq
      (Public.Spec.postDecPublicProgram_noDeadRuntimeCalls length lowered.drop)
      (Public.Spec.postDecPublicProgram_noWrapperToWrapperCalls length lowered.drop)
      hliveDrop]
    rw [execution] at execFast
    exact execFast
  refine ⟨H', memory', slots', lists', clock', released, ready, frame, ?_⟩
  rw [program_eval_transfer splitDrop clock' [returned.word] returned.memory context
    (by rw [execPruned]; intro impossible; cases impossible)]
  exact execPruned




end IxCC.Cfg.Rc.Native.Spec
