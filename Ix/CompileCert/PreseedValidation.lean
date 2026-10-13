import Ix.CompileCert.HeadWriterFrame
import IxC.Ixon.Verify.WireCheck

/-! The executable universe-wire admission guard. It preserves all state,
accepts exactly wire-valid arrays and rejects before serialized-key sorting. -/

namespace Ix.CompileCert.PreseedValidation

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

theorem array_valid (values : Array Ixon.Univ) :
    values.all Ixon.WireCheck.validUniv = true ↔ ∀ value ∈ values, value.wireWF := by
  rw [Array.all_eq_true]
  constructor
  · intro checked value member
    obtain ⟨index, inside, same⟩ := Array.mem_iff_getElem.mp member
    subst value
    exact (Ixon.Verify.WireCheck.validUniv_iff _).mp (checked index inside)
  · intro valid index inside
    exact (Ixon.Verify.WireCheck.validUniv_iff _).mpr (valid _ (by simp))

theorem run (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (checkPreseedUnivs values) context before =
      (if values.all Ixon.WireCheck.validUniv then .ok ()
       else .error (.resourceLimit "canonical universe successor count exceeds the Ixon UInt64 range"), before) := by
  unfold checkPreseedUnivs
  split <;> rfl

theorem state (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState) :
    (rawRun (checkPreseedUnivs values) context before).2 = before := by
  rw [run]

theorem accepts (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (valid : ∀ value ∈ values, value.wireWF) : rawRun (checkPreseedUnivs values) context before = (.ok (), before) := by
  rw [run, (array_valid values).mpr valid]
  rfl

theorem valid_of_success (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before after : BlockState)
    (ran : rawRun (checkPreseedUnivs values) context before = (.ok (), after)) :
    (∀ value ∈ values, value.wireWF) ∧ after = before := by
  have same := state values context before
  rw [ran] at same
  rw [run] at ran
  split at ran
  · exact ⟨(array_valid values).mp (by assumption), same⟩
  · cases ran

theorem refuses (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (value : Ixon.Univ) (member : value ∈ values) (invalid : ¬value.wireWF) :
    ∃ reason, rawRun (checkPreseedUnivs values) context before = (.error (.resourceLimit reason), before) := by
  have failed : ¬values.all Ixon.WireCheck.validUniv = true := fun checked =>
    invalid ((array_valid values).mp checked value member)
  rw [run]
  simp only [failed]
  exact ⟨_, rfl⟩

theorem wire_count (value : Ixon.Univ) (valid : value.wireWF) : value.succCountNat < UInt64.size := by
  cases value with
  | succ child => exact valid.1
  | _ => change 0 < UInt64.size; decide

theorem refuses_count (values : Array Ixon.Univ) (context : CompileEnv × BlockEnv) (before : BlockState)
    (value : Ixon.Univ) (member : value ∈ values) (large : UInt64.size ≤ value.succCountNat) :
    ∃ reason, rawRun (checkPreseedUnivs values) context before = (.error (.resourceLimit reason), before) :=
  refuses values context before value member (fun valid => Nat.not_le_of_gt (wire_count value valid) large)

/-- Erase the guard's state effect on a successful continuation, retaining
its derived wire-validity fact. -/
theorem after_check (values : Array Ixon.Univ) (next : CompileM α) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : α)
    (ran : rawRun (do checkPreseedUnivs values; next) context before = (.ok output, after)) :
    (∀ value ∈ values, value.wireWF) ∧ rawRun next context before = (.ok output, after) := by
  rw [rawRun_bind, run] at ran
  by_cases checked : values.all Ixon.WireCheck.validUniv = true
  · exact ⟨(array_valid values).mp checked, by simpa only [checked, ↓reduceIte] using ran⟩
  · simp only [checked] at ran
    cases ran

end Ix.CompileCert.PreseedValidation
