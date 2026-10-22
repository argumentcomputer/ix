import Aiur.AST

namespace Aiur

/-- Check duplicates in groups with the same key. The key need not be injective:
full row equality is still checked within each group. This needs only decidable
equality, even when the field has no order or hash function. -/
def nodupByKey [DecidableEq α] [DecidableEq β] (key : α → β) : List α → Bool
  | [] => true
  | row :: rows =>
      let groups := rows.partition (fun value => decide (key value = key row))
      decide (row :: groups.1).Nodup && nodupByKey key groups.2
termination_by rows => rows.length
decreasing_by
  simp only [List.partition_eq_filter_filter]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem nodupByKey_eq [DecidableEq α] [DecidableEq β] (key : α → β) (rows : List α) :
    nodupByKey key rows = decide rows.Nodup := by
  cases rows with
  | nil => simp [nodupByKey]
  | cons row rows =>
      let p := fun value => decide (key value = key row)
      have separate : ∀ a ∈ row :: rows.filter p, ∀ b ∈ rows.filter (fun x => !p x), a ≠ b := by
        intro a ha b hb same
        subst b
        have no : key a ≠ key row := by simpa [p] using (List.mem_filter.mp hb).2
        rcases List.mem_cons.mp ha with rfl | ha
        · exact no rfl
        · exact no (by simpa [p] using (List.mem_filter.mp ha).2)
      have perm := (List.filter_append_perm p rows).cons row
      have equiv : (row :: rows).Nodup ↔
          (row :: rows.filter p).Nodup ∧ (rows.filter (fun x => !p x)).Nodup := by
        rw [← perm.nodup_iff]
        rw [← List.cons_append, List.nodup_append]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, separate⟩⟩
      simp only [nodupByKey, List.partition_eq_filter_filter]
      rw [nodupByKey_eq key]
      simp only [equiv, Bool.decide_and]
      rfl
termination_by rows.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The first argument partitions Cartesian-product input tables into small
groups. It is only an optimization key; every complete row is compared. -/
def tableRowKey : Constant α → Constant α
  | .tuple (first :: _) => first
  | value => value

def tableRowsNodup [DecidableEq α] (rows : List (Constant α)) : Bool :=
  match rows with
  | .tuple [_] :: _ => decide rows.Nodup
  | _ => nodupByKey tableRowKey rows

@[simp] theorem tableRowsNodup_eq [DecidableEq α] (rows : List (Constant α)) :
    tableRowsNodup rows = decide rows.Nodup :=
  by unfold tableRowsNodup; split <;> simp [nodupByKey_eq]

end Aiur
