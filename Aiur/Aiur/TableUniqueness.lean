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

private def nodupTasks [DecidableEq α] : List α → List (Task Bool)
  | [] => []
  | row :: rows => (Task.spawn fun _ => decide (row ∉ rows)) :: nodupTasks rows

private def parallelNodup [DecidableEq α] (rows : List α) : Bool :=
  (nodupTasks rows).all fun result => result.get

private theorem parallelNodup_eq [DecidableEq α] (rows : List α) :
    parallelNodup rows = decide rows.Nodup := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change (decide (row ∉ rows) && parallelNodup rows) = decide (row :: rows).Nodup
      rw [ih]
      simp only [List.nodup_cons, Bool.decide_and]

private def scalarRow (value : α) : Constant α := .tuple [.field value]

/-- The round-trip check permits scalar comparison without sharing nested
row objects between workers. Non-scalar rows retain the general check. -/
private def scalarRowsNodup [DecidableEq α] (rows : List (Constant α))
    (values : List α) : Bool :=
  if rows = values.map scalarRow then parallelNodup values else decide rows.Nodup

private theorem scalarRowsNodup_eq [DecidableEq α] (rows : List (Constant α))
    (values : List α) : scalarRowsNodup rows values = decide rows.Nodup := by
  unfold scalarRowsNodup
  split
  next h =>
    rw [parallelNodup_eq, h]
    simp [List.Nodup, List.pairwise_map, scalarRow]
  · rfl

/-- Large unary tables share immutable scalar suffixes between independent
membership checks. Small tables avoid task-allocation overhead. -/
private def tableRowsNodupParallel [DecidableEq α] (rows : List (Constant α)) : Bool :=
  match rows with
  | .tuple [_] :: _ =>
      if rows.length ≤ 1024 then decide rows.Nodup else
      scalarRowsNodup rows (rows.filterMap fun | .tuple [.field value] => some value | _ => none)
  | _ => nodupByKey tableRowKey rows

private theorem tableRowsNodupParallel_eq [DecidableEq α] (rows : List (Constant α)) :
    tableRowsNodupParallel rows = decide rows.Nodup := by
  unfold tableRowsNodupParallel
  split
  · split
    · rfl
    · exact scalarRowsNodup_eq _ _
  · exact nodupByKey_eq _ _

@[csimp] theorem tableRowsNodup_eq_parallel :
    @tableRowsNodup = @tableRowsNodupParallel := by
  funext α inst rows
  rw [tableRowsNodup_eq, tableRowsNodupParallel_eq]

end Aiur
