import IxCC.Rt.Rc.Procs

/-! Arithmetic obligations for the RC runtime procedures (`Rt.Rc.Procs`),
consumed by the whole-operation memory simulation proofs in `Rt.Rc.Proof`. -/
namespace IxCC.Rt.Rc.Procs

theorem increment_encoding {refs : Nat} (hpos : 0 < refs)
    (hroom : refs < maxCount) :
    refs - 1 + 1 = (refs + 1) - 1 ∧ refs - 1 < maxCount - 1 ∧ refs + 1 ≤ maxCount := by
  unfold maxCount at *
  omega

theorem increment_overflow_boundary {refs : Nat} (hpos : 0 < refs)
    (hbound : refs ≤ maxCount) : refs - 1 = maxCount - 1 ↔ refs = maxCount := by
  unfold maxCount at *
  omega

theorem shared_decrement_encoding {refs : Nat} (hshared : 1 < refs) :
    refs - 1 - 1 = (refs - 1) - 1 ∧ 0 < refs - 1 := by
  omega

/-- Remaining suffix never reads the overwritten predecessor slot. -/
theorem continuation_field_bounds {fields remaining : Nat}
    (hfields : fields < 32) (hremaining : 0 < remaining)
    (hvisited : remaining < fields) :
    1 ≤ fields - remaining ∧ fields - remaining < fields ∧
    8 + 8 * (fields - remaining) + 8 ≤ 8 * (fields + 1) := by
  omega

theorem continuation_next {fields remaining : Nat}
    (hremaining : 0 < remaining) (hvisited : remaining < fields) :
    fields - (remaining - 1) = fields - remaining + 1 := by
  omega

/-- After detaching field0, suffix plus current child is the full pending list. -/
theorem first_child_pending (child : α) (suffix : List α) :
    child :: suffix = (child :: []) ++ suffix := by
  rfl

/-- One resumed child changes only the concrete partition of pending roots. -/
theorem resumed_child_pending (before : List α) (child : α) (suffix : List α) :
    before ++ (child :: suffix) = (before ++ [child]) ++ suffix := by
  simp

end IxCC.Rt.Rc.Procs
