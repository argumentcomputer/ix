import Compilatrix.Recheck.Rc.Proof.ReleaseCore
import Compilatrix.Cfg.Rc.Proof.Physical.DropStep
import Compilatrix.Cfg.Rc.Proof.Physical.PublicRoot

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc Compilatrix.Rt.Rc.Procs

private theorem suffix_at {α : Type} (before after : List α) (i : Nat) :
    (before ++ after)[before.length + i]? = after[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem accepted_drop_index {config : Rt.Config} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program} {lowered : Public.Lowered}
    (accepted : Public.lower config F bodies P = .ok lowered) :
    lowered.drop = (layoutOf P).init + 3 := by
  obtain ⟨original, native, rfl, _⟩ := Public.Spec.lower_parts accepted
  obtain ⟨main, pairs, functions, _, _, _, _, _, _, length, program, _⟩ := Native.Spec.lower_parts native
  change original.program.funcs.size = _
  rw [program]
  simp only [Lir.Program.splitCriticalEdges, Array.size_map, rawProgram, List.size_toArray,
    List.length_append, List.length_cons, List.length_nil, length, wrappers_length, procedures_length]
  simp [layoutOf, Layout.init, Layout.incProc]
  omega

theorem source_stage_drop (P : Program) (functions : Nat → Lir.Func) (main : Nat) :
    (Public.Spec.sourceStage P functions main).funcs[(layoutOf P).init+3]? =
      some (Public.dropWrapper (layoutOf P).decProc) := by
  have beyond : ¬ (layoutOf P).init + 3 < P.base.size := by
    simp only [layoutOf, Layout.init, Layout.incProc]
    omega
  have index : (layoutOf P).init + 3 - P.base.size =
      (wrappers (layoutOf P)).length + ((procedures (layoutOf P)).length + 3) := by
    rw [wrappers_length, procedures_length]
    simp only [layoutOf, Layout.init, Layout.incProc]
    omega
  rw [Public.Spec.sourceStage_get, if_neg beyond, index]
  simp only [Public.Spec.runtimeFunctions, List.append_assoc]
  rw [suffix_at, suffix_at]
  rfl

/-- Release the exact owned result of a physical source completion through
the actual public drop export. Neither readback nor header shape establishes
ownership: the Returned invariant supplies the single root occurrence. -/
theorem Returned.release_public {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
    {lowered : Public.Lowered} (admission : CodeAdmission F bodies P config pairs functions)
    (accepted : Public.lower config F bodies P = .ok lowered)
    {lp : Lir.Program} {origin : Heap} {originAddresses : AddressMap} {external : Nat → Nat}
    {context base limit : Lir.Word} {regionBytes : Nat} {logical : Fir.Val}
    (returned : Returned P pairs lp origin originAddresses external context base limit regionBytes logical) :
    ∃ H' memory' slots' lists' clock,
      dropAll returned.heap [returned.value] = some H' ∧
      HeapState P pairs H' returned.addresses memory' external []
        context base returned.bump limit regionBytes slots' lists' ∧
      ProtectedFrame returned.memory memory' context base returned.bump ∧
      Lir.eval {lowered.runtime.program with main := lowered.drop} clock
        [returned.word] returned.memory context = .ok ([1], memory') := by
  let raw := Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) lowered.drop
  have index := accepted_drop_index accepted
  have wrapper : raw.funcs[lowered.drop]? = some (Public.dropWrapper (layoutOf P).decProc) := by
    rw [index]
    exact source_stage_drop P _ lowered.drop
  have runtime : raw.funcs[(layoutOf P).decProc]? = some dec :=
    (source_stage_decrement_runtime P _ lowered.drop).2
  obtain ⟨H', memory', slots', lists', clock, released, ready, frame, execution⟩ :=
    drop_top returned.state returned.represented wrapper runtime rfl
  refine ⟨H', memory', slots', lists', clock, released, ready, frame, ?_⟩
  rw [admitted_root_eval_stages admission accepted lowered.drop clock [returned.word]
    returned.memory context (by rw [execution]; intro impossible; cases impossible)]
  exact execution




end Compilatrix.Cfg.Rc.Native.Spec
