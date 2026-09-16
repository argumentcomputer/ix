import Compilatrix.Aiur.AIR.Memory.Pointers

/-! Project distinct-width memory circuits into the existing logical trace.
All active cells agree with one heap; no prior-store or allocation premise. -/

namespace Compilatrix.Aiur.AIR.Memory

open _root_.Aiur (G gSize)

theorem Table.row_mem (table : Table) (index : Nat) (bound : index < table.rows.size) :
    table.row index ∈ table.rows.toList := by
  simpa only [Table.row, Array.getElem?_eq_getElem bound, Option.getD_some] using
    Array.getElem_mem_toList bound

theorem Table.mem_rows (table : Table) (row : Row) :
    row ∈ table.rows.toList ↔ ∃ index, index < table.rows.size ∧ table.row index = row := by
  constructor
  · intro member
    obtain ⟨index, bound, equal⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
    exact ⟨index, bound, by simpa [Table.row, Array.getElem?_eq_getElem bound] using equal⟩
  · rintro ⟨index, bound, rfl⟩
    exact table.row_mem index bound

theorem mem_cells (tables : List Table) (cell : Compilatrix.Aiur.Memory.Cell) :
    cell ∈ Compilatrix.Aiur.Memory.cells (project tables) ↔
      ∃ table ∈ tables, ∃ index, index < table.rows.size ∧
        (table.row index).selector = 1 ∧
        cell = ⟨table.bucket, (table.row index).pointer, (table.row index).values⟩ := by
  simp only [Compilatrix.Aiur.Memory.cells, project, List.mem_filterMap, List.mem_flatMap,
    Table.project, List.mem_map]
  constructor
  · rintro ⟨projected, ⟨table, inTables, row, inRows, rfl⟩, observed⟩
    obtain ⟨index, bound, rfl⟩ := (table.mem_rows row).mp inRows
    have active : (table.row index).selector = 1 := by
      have observed' := observed
      simp [Compilatrix.Aiur.Memory.cell?, Row.project, Row.active] at observed'
      exact Subtype.ext observed'.1
    have equal : cell = ⟨table.bucket, (table.row index).pointer, (table.row index).values⟩ := by
      simpa [Compilatrix.Aiur.Memory.cell?, Row.project, Row.active, active] using observed.symm
    exact ⟨table, inTables, index, bound, active, equal⟩
  · rintro ⟨table, inTables, index, bound, active, rfl⟩
    exact ⟨(table.row index).project table.bucket,
      ⟨table, inTables, table.row index, table.row_mem index bound, rfl⟩,
      by simp [Compilatrix.Aiur.Memory.cell?, Row.project, Row.active, active]⟩

theorem unique_bucket_eq {tables : List Table} (unique : UniqueBuckets tables)
    {left right : Table} (hl : left ∈ tables) (hr : right ∈ tables)
    (equal : left.bucket = right.bucket) : left = right := by
  induction tables with
  | nil => simp at hl
  | cons head tail ih =>
    have nodup : head.bucket ∉ tail.map Table.bucket ∧ (tail.map Table.bucket).Nodup := by
      simpa only [UniqueBuckets, List.map_cons, List.nodup_cons] using unique
    rcases List.mem_cons.mp hl with rfl | laterLeft <;>
      rcases List.mem_cons.mp hr with rfl | laterRight
    · rfl
    · exact False.elim (nodup.1 (List.mem_map.mpr ⟨right, laterRight, equal.symm⟩))
    · exact False.elim (nodup.1 (List.mem_map.mpr ⟨left, laterLeft, equal⟩))
    · exact ih nodup.2 laterLeft laterRight

theorem coherent (tables : List Table) (unique : UniqueBuckets tables)
    (satisfied : ∀ table ∈ tables, table.Satisfied)
    (short : ∀ table ∈ tables, table.rows.size < gSize.toNat) :
    Compilatrix.Aiur.Memory.Coherent (Compilatrix.Aiur.Memory.cells (project tables)) := by
  intro left hl right hr bucket pointer
  obtain ⟨leftTable, inLeft, i, hi, activeLeft, rfl⟩ := (mem_cells tables left).mp hl
  obtain ⟨rightTable, inRight, j, hj, activeRight, rfl⟩ := (mem_cells tables right).mp hr
  have sameTable := unique_bucket_eq unique inLeft inRight bucket
  cases sameTable
  have sameIndex := leftTable.pointer_injective (satisfied leftTable inLeft)
    (short leftTable inLeft) i j hi hj activeLeft activeRight pointer
  cases sameIndex
  rfl

theorem heap_agrees (tables : List Table) (unique : UniqueBuckets tables)
    (satisfied : ∀ table ∈ tables, table.Satisfied)
    (short : ∀ table ∈ tables, table.rows.size < gSize.toNat)
    {table : Table} (member : table ∈ tables) (index : Nat) (bound : index < table.rows.size)
    (selected : (table.row index).selector = 1) :
    Compilatrix.Aiur.Memory.heap (Compilatrix.Aiur.Memory.cells (project tables))
      table.bucket (table.row index).pointer = some (table.row index).values := by
  exact Compilatrix.Aiur.Memory.heap_of_mem _ (coherent tables unique satisfied short)
    ((mem_cells tables _).mpr ⟨table, member, index, bound, selected, rfl⟩)

theorem activity (tables : List Table)
    (satisfied : ∀ table ∈ tables, table.Satisfied)
    (boolean : ∀ table ∈ tables, table.BooleanSelectors) : (project tables).Activity := by
  intro projected member nonzero
  obtain ⟨table, inTables, inRows⟩ := List.mem_flatMap.mp member
  change projected ∈ table.rows.toList.map (Row.project table.bucket) at inRows
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp inRows
  obtain ⟨index, bound, rfl⟩ := (table.mem_rows row).mp rowMember
  have equations := (satisfied_iff _ _ _ _).mp (satisfied table inTables index bound)
  exact row_activity equations (boolean table inTables _ (Array.mem_toList_iff.mp (table.row_mem index bound))) nonzero

end Compilatrix.Aiur.AIR.Memory
