import IxCC.Aiur.Trace

/-! A single witness heap for all active memory providers. Pointer values are
observed field values, with no insertion-order or preceding-store premise.
Coherence alone establishes neither type validity nor heap acyclicity. -/

namespace IxCC.Aiur.Memory

open _root_.Aiur (G)

structure Cell where
  bucket : Nat
  pointer : G
  values : List G
  deriving DecidableEq, Repr

def cell? (row : Row) : Option Cell :=
  if row.active then
    match row.provides with
    | .memory bucket pointer values => some ⟨bucket, pointer, values⟩
    | _ => none
  else none

def cells (trace : Trace) : List Cell := trace.rows.filterMap cell?

abbrev Heap := Nat → G → Option (List G)

def heap : List Cell → Heap
  | [] => fun _ _ => none
  | cell :: rest => fun bucket pointer =>
    if cell.bucket = bucket ∧ cell.pointer = pointer then some cell.values
    else heap rest bucket pointer

def Coherent (cells : List Cell) : Prop :=
  ∀ left ∈ cells, ∀ right ∈ cells,
    left.bucket = right.bucket → left.pointer = right.pointer → left.values = right.values

theorem heap_of_mem (cells : List Cell) (coherent : Coherent cells)
    {cell : Cell} (member : cell ∈ cells) :
    heap cells cell.bucket cell.pointer = some cell.values := by
  induction cells with
  | nil => simp at member
  | cons head tail ih =>
    by_cases equal : head.bucket = cell.bucket ∧ head.pointer = cell.pointer
    · have values := coherent head List.mem_cons_self cell member equal.1 equal.2
      simp only [heap, if_pos equal, values]
    · have inTail : cell ∈ tail := by
        rcases List.mem_cons.mp member with same | later
        · cases same
          exact False.elim (equal ⟨rfl, rfl⟩)
        · exact later
      have tailCoherent : Coherent tail := fun left hl right hr =>
        coherent left (List.mem_cons_of_mem _ hl) right (List.mem_cons_of_mem _ hr)
      simpa only [heap, if_neg equal] using ih tailCoherent inTail

theorem row_mem_cells (trace : Trace) (id : trace.RowId)
    (active : (trace.row id).active = true) {bucket : Nat} {pointer : G} {values : List G}
    (provided : (trace.row id).provides = .memory bucket pointer values) :
    (⟨bucket, pointer, values⟩ : Cell) ∈ cells trace := by
  apply List.mem_filterMap.mpr
  exact ⟨trace.row id, trace.row_mem id, by simp [cell?, active, provided]⟩

theorem row_agrees (trace : Trace) (coherent : Coherent (cells trace)) (id : trace.RowId)
    (active : (trace.row id).active = true) {bucket : Nat} {pointer : G} {values : List G}
    (provided : (trace.row id).provides = .memory bucket pointer values) :
    heap (cells trace) bucket pointer = some values :=
  heap_of_mem (cells trace) coherent (row_mem_cells trace id active provided)

def check (trace : Trace) : Bool :=
  (cells trace).all fun left => (cells trace).all fun right =>
    decide (left.bucket = right.bucket → left.pointer = right.pointer → left.values = right.values)

theorem check_sound (trace : Trace) (checked : check trace = true) : Coherent (cells trace) := by
  intro left hl right hr
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked left hl) right hr)

end IxCC.Aiur.Memory
