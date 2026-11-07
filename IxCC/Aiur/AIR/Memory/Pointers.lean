import IxCC.Aiur.AIR.Memory.Local
import IxCC.Vendor.Ix.Aiur.Compiler.UnitCounter

/-! Selected memory rows form a prefix. Their pointers advance by one,
including wraparound; a table shorter than the characteristic cannot repeat
an active pointer. Its initial pointer is unrestricted. -/

namespace IxCC.Aiur.AIR.Memory

open _root_.IxCC.Vendor.Aiur (G gSize)

theorem Table.consecutive (table : Table) (satisfied : table.Satisfied)
    (index : Nat) (bound : index + 1 < table.rows.size) :
    (table.row index).Equations (table.row (index + 1)) true := by
  have h := satisfied index (by omega)
  simpa only [Table.window, if_pos bound, decide_eq_true bound, satisfied_iff] using h

theorem Table.selected_prefix (table : Table) (satisfied : table.Satisfied)
    (first last : Nat) (order : first ≤ last) (bound : last < table.rows.size)
    (selected : (table.row last).selector = 1) : (table.row first).selector = 1 := by
  induction last with
  | zero =>
    have same : first = 0 := by omega
    simpa [same] using selected
  | succ last ih =>
    by_cases same : first = last + 1
    · simpa [same] using selected
    · have previous := selected_predecessor (table.consecutive satisfied last bound) selected
      exact ih (by omega) (by omega) previous.1

theorem Table.pointer_ne (table : Table) (satisfied : table.Satisfied)
    (short : table.rows.size < gSize.toNat)
    (first last : Nat) (order : first < last) (bound : last < table.rows.size)
    (selected : (table.row last).selector = 1) :
    (table.row last).pointer ≠ (table.row first).pointer := by
  have steps : ∀ index, index < last - first →
      (table.row (first + (index + 1))).pointer =
        (table.row (first + index)).pointer + 1 := by
    intro index inside
    have next := table.selected_prefix satisfied (first + index + 1) last
      (by omega) bound selected
    have step := selected_predecessor
      (table.consecutive satisfied (first + index) (by omega)) next
    simpa only [Nat.add_assoc] using step.2
  have different := _root_.IxCC.Vendor.Aiur.Bytecode.UnitCounter.Proofs.no_short_field_cycle
    (fun index => (table.row (first + index)).pointer)
    (m := last - first) (by omega) (by omega) steps
  have endIndex : first + (last - first) = last := by omega
  simpa only [endIndex, Nat.add_zero] using different

theorem Table.pointer_injective (table : Table) (satisfied : table.Satisfied)
    (short : table.rows.size < gSize.toNat)
    (left right : Nat) (leftBound : left < table.rows.size) (rightBound : right < table.rows.size)
    (leftSelected : (table.row left).selector = 1) (rightSelected : (table.row right).selector = 1)
    (equal : (table.row left).pointer = (table.row right).pointer) : left = right := by
  by_cases before : left < right
  · exact False.elim (table.pointer_ne satisfied short left right before rightBound rightSelected equal.symm)
  · by_cases after : right < left
    · exact False.elim (table.pointer_ne satisfied short right left after leftBound leftSelected equal)
    · omega

end IxCC.Aiur.AIR.Memory
