import IxCC.Aiur.AIR.Memory.Model

/-! Bounded supplied-table ingress. Retains the exact check result; the
proof-only soundness module derives coherence without a quadratic cell check. -/

namespace IxCC.Aiur.AIR.Memory

open _root_.Aiur (gSize)

structure Limits where
  maxTables : Nat := 256
  maxRows : Nat := 65536
  maxWidth : Nat := 256
  maxFields : Nat := 1048576
  deriving DecidableEq, Repr

inductive Error where
  | tableLimit | rowLimit | widthLimit | fieldLimit
  | duplicateBucket
  | height (table : Nat)
  | shape (table row : Nat)
  | selector (table row : Nat)
  | constraint (table row : Nat)
  deriving DecidableEq, Repr

/-- Preflight counts all rows and all supplied fields, including padding. -/
def preflight (limits : Limits) (tables : List Table) : Except Error Unit := do
  if tables.length > limits.maxTables then throw .tableLimit
  let mut rows := 0
  let mut fields := 0
  for table in tables do
    if table.bucket > limits.maxWidth || table.bucket ≥ gSize.toNat then throw .widthLimit
    rows := rows + table.rows.size
    if rows > limits.maxRows then throw .rowLimit
    for row in table.rows do
      fields := fields + 3 + row.values.length
      if fields > limits.maxFields then throw .fieldLimit

def Table.check (table : Table) : Bool :=
  decide (table.bucket < gSize.toNat) &&
  decide (table.rows.size < gSize.toNat) &&
  table.rows.all (fun row => decide (row.values.length = table.bucket)) &&
  table.rows.all (fun row => decide (row.selector = 0 ∨ row.selector = 1)) &&
  (List.range table.rows.size).all (fun index => (build table.bucket).check (table.window index))

def check (tables : List Table) : Bool :=
  decide (UniqueBuckets tables) && tables.all Table.check

structure Checked (tables : List Table) : Type where
  checked : check tables = true

private def diagnose (tables : List Table) : Error := Id.run do
  if !decide (UniqueBuckets tables) then return .duplicateBucket
  for (table, ti) in tables.zipIdx do
    if table.bucket ≥ gSize.toNat then return .widthLimit
    if table.rows.size ≥ gSize.toNat then return .height ti
    for ri in [:table.rows.size] do
      let row := table.row ri
      if row.values.length != table.bucket then return .shape ti ri
      if !(row.selector == 0 || row.selector == 1) then return .selector ti ri
      if !(build table.bucket).check (table.window ri) then return .constraint ti ri
  return .duplicateBucket

def validate (limits : Limits) (tables : List Table) : Except Error (Checked tables) := do
  preflight limits tables
  if accepted : check tables = true then return ⟨accepted⟩
  else throw (diagnose tables)

end IxCC.Aiur.AIR.Memory
