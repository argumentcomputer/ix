import Compilatrix.Aiur.CounterAnalysis.Step
import Compilatrix.Aiur.OracleEval.Machine
import Compilatrix.Aiur.Static.Counter

namespace Compilatrix.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values)

/-- The control test in the pinned checker, with the remaining branch depth
explicit. This is used only to state the machine induction invariant. -/
def controlChecked (depth self : Nat) (candidate : UnitCounter.Certificate)
    (state : UnitCounter.State) (control : Ctrl) : Bool :=
  match control with
  | .return _ outputs =>
    match candidate.mode, state.recursiveOutput with
    | .input, _ | .output, none => true
    | .output, some marker =>
      match outputs[candidate.column]? with
      | none => false
      | some index => (state.values[index]?).getD none == some ⟨some marker, candidate.step⟩
  | .match _ cases fallback =>
    cases.all (fun (_, branch) => UnitCounter.check depth self candidate state branch) &&
      fallback.all (UnitCounter.check depth self candidate state)
  | .yield .. | .matchContinue .. => false

def TaskAccepted (self : Nat) (candidate : UnitCounter.Certificate) (state : UnitCounter.State) :
    OracleEval.Task → Prop
  | .ops operations control => ∃ next, operations.foldlM (UnitCounter.stepOp self candidate) state = some next ∧
      ∃ depth, controlChecked depth self candidate next control = true
  | .control control => ∃ depth, controlChecked depth self candidate state control = true

theorem check_accepted {depth self : Nat} {candidate : UnitCounter.Certificate}
    {state : UnitCounter.State} {block : Block}
    (checked : UnitCounter.check depth self candidate state block = true) :
    TaskAccepted self candidate state (OracleEval.start block) := by
  cases depth with
  | zero => cases checked
  | succ depth =>
    rw [UnitCounter.check] at checked
    cases folded : block.ops.foldlM (UnitCounter.stepOp self candidate) state with
    | none => rw [folded] at checked; cases checked
    | some next =>
      rw [folded] at checked
      exact ⟨next, by rw [Array.foldlM_toList, folded], depth, checked⟩

theorem selectBranch_checked {depth self : Nat} {candidate : UnitCounter.Certificate}
    {state : UnitCounter.State} {index : Nat} {cases : Array (G × Block)} {fallback : Option Block}
    {scrutinee : G} {selected : Block}
    (checked : controlChecked depth self candidate state (.match index cases fallback) = true)
    (success : OracleEval.selectBranch scrutinee cases fallback = .ok selected) :
    TaskAccepted self candidate state (OracleEval.start selected) := by
  simp only [controlChecked, Bool.and_eq_true] at checked
  obtain ⟨allCases, allFallback⟩ := checked
  apply check_accepted (depth := depth)
  unfold OracleEval.selectBranch at success
  cases found : cases.toList.find? (fun arm => arm.1 == scrutinee) with
  | none =>
    rw [found] at success
    cases fallback with
    | none => cases success
    | some block =>
      cases success
      exact allFallback
  | some arm =>
    rw [found] at success
    cases success
    have member := List.mem_of_find?_eq_some found
    exact (Array.all_eq_true_iff_forall_mem.mp allCases) arm (by simpa using member)

def CounterRelation (self : Nat) (candidate : UnitCounter.Certificate) (inputs outputs : Values)
    (demands : List Message) : Prop :=
  ∀ childInputs childOutputs, .function self childInputs childOutputs ∈ demands →
    ∃ parent child,
      Static.counterObservation candidate inputs outputs = some parent ∧
      Static.counterObservation candidate childInputs childOutputs = some child ∧
      Static.CounterStep candidate parent child

theorem return_relation {depth self selector : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractState : UnitCounter.State} {state : OracleEval.State} {indices : Array Nat} {outputs : Values}
    (sound : Invariant self candidate inputs abstractState state)
    (checked : controlChecked depth self candidate abstractState (.return selector indices) = true)
    (reads : Reads state.values indices outputs) :
    CounterRelation self candidate inputs.toList outputs state.demandsRev.reverse := by
  intro childInputs childOutputs member
  have member : (⟨self, childInputs, childOutputs⟩ : Call) ∈ calls state.demandsRev :=
    (call_mem _ _ _ _).mpr (List.mem_reverse.mp member)
  cases mode : candidate.mode with
  | input =>
    have old := sound.callsSound
    rw [CallInvariant, mode] at old
    obtain ⟨parent, child, parentRead, childRead, equation⟩ := old _ member rfl
    exact ⟨parent, child, by simpa [Static.counterObservation, mode] using parentRead,
      by simpa [Static.counterObservation, mode] using childRead, by simpa [Static.CounterStep, mode] using equation⟩
  | output =>
    have old := sound.callsSound
    rw [CallInvariant, mode] at old
    cases marker : abstractState.recursiveOutput with
    | none =>
      rw [marker] at old
      exact False.elim (old _ member rfl)
    | some index =>
      rw [marker] at old
      obtain ⟨child, childRead, allCalls⟩ := old
      simp only [controlChecked, mode, marker] at checked
      cases selected : indices[candidate.column]? with
      | none => rw [selected] at checked; cases checked
      | some register =>
        rw [selected] at checked
        obtain ⟨parent, parentRead, registerRead⟩ := reads.get selected
        have known := (optional_affine_beq_eq _ _).mp checked
        obtain ⟨source, sourceRead, equation⟩ := sound.registers.get registerRead _ known
        have equal : source = child := Option.some.inj (sourceRead.symm.trans childRead)
        refine ⟨parent, child, ?_, ?_, ?_⟩
        · simpa [Static.counterObservation, mode] using parentRead
        · simpa [Static.counterObservation, mode] using allCalls _ member rfl
        · simpa [Static.CounterStep, mode, equal] using equation

end Compilatrix.Aiur.CounterAnalysis
