import IxCC.Aiur.AIR.Memory.Projection
import IxCC.Aiur.AIR.Memory.Check
import IxCC.Aiur.BytecodeEvalW

/-! Soundness of the executable memory-table check, including all retained
row facts and the single witness heap. No coherence callback is required. -/

namespace IxCC.Aiur.AIR.Memory

open _root_.Aiur (G gSize)

theorem Table.check_sound (table : Table) (checked : table.check = true) :
    table.Shape ∧ table.rows.size < gSize.toNat ∧ table.BooleanSelectors ∧ table.Satisfied := by
  simp only [Table.check, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨⟨⟨bucket, short⟩, shape⟩, boolean⟩, equations⟩
  refine ⟨⟨bucket, ?_⟩, short, ?_, ?_⟩
  · intro row member
    obtain ⟨index, bound, rfl⟩ := Array.getElem_of_mem member
    exact of_decide_eq_true (Array.all_eq_true.mp shape index bound)
  · intro row member
    obtain ⟨index, bound, rfl⟩ := Array.getElem_of_mem member
    exact of_decide_eq_true (Array.all_eq_true.mp boolean index bound)
  · intro index bound
    exact Circuit.check_sound _ _
      (List.all_eq_true.mp equations index (List.mem_range.mpr bound))

theorem Checked.unique {tables : List Table} (checked : Checked tables) : UniqueBuckets tables := by
  have both : UniqueBuckets tables ∧ tables.all Table.check = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using checked.checked
  exact both.1

theorem Checked.table {tables : List Table} (checked : Checked tables)
    {table : Table} (member : table ∈ tables) :
    table.Shape ∧ table.rows.size < gSize.toNat ∧ table.BooleanSelectors ∧ table.Satisfied := by
  have both : UniqueBuckets tables ∧ tables.all Table.check = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using checked.checked
  exact table.check_sound (List.all_eq_true.mp both.2 table member)

theorem Checked.coherent {tables : List Table} (checked : Checked tables) :
    IxCC.Aiur.Memory.Coherent (IxCC.Aiur.Memory.cells (project tables)) :=
  IxCC.Aiur.AIR.Memory.coherent tables checked.unique (fun _ member => (checked.table member).2.2.2)
    (fun _ member => (checked.table member).2.1)

theorem Checked.activity {tables : List Table} (checked : Checked tables) : (project tables).Activity :=
  IxCC.Aiur.AIR.Memory.activity tables (fun _ member => (checked.table member).2.2.2)
    (fun _ member => (checked.table member).2.2.1)

theorem Checked.heap_agrees {tables : List Table} (checked : Checked tables)
    {table : Table} (member : table ∈ tables) (index : Nat) (bound : index < table.rows.size)
    (selected : (table.row index).selector = 1) :
    IxCC.Aiur.Memory.heap (IxCC.Aiur.Memory.cells (project tables))
      table.bucket (table.row index).pointer = some (table.row index).values :=
  IxCC.Aiur.AIR.Memory.heap_agrees tables checked.unique (fun _ member => (checked.table member).2.2.2)
    (fun _ member => (checked.table member).2.1) member index bound selected

theorem Checked.row_shape {tables : List Table} (checked : Checked tables)
    {table : Table} (member : table ∈ tables) (index : Nat) (bound : index < table.rows.size) :
    (table.row index).values.length = table.bucket :=
  (checked.table member).1.2 _ (Array.mem_toList_iff.mp (table.row_mem index bound))

theorem Checked.message_eval {tables : List Table} (checked : Checked tables)
    (toplevel : _root_.Aiur.Bytecode.Toplevel) (oracle : OracleEval.AdviceOracle)
    {table : Table} (member : table ∈ tables) (index : Nat) (bound : index < table.rows.size)
    (selected : (table.row index).selector = 1) :
    MessageEval toplevel (IxCC.Aiur.Memory.heap
      (IxCC.Aiur.Memory.cells (project tables))) oracle
      (.memory table.bucket (table.row index).pointer (table.row index).values) :=
  .memory (checked.heap_agrees member index bound selected) (checked.row_shape member index bound)

end IxCC.Aiur.AIR.Memory
