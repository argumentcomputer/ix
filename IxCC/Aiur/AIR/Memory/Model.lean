import IxCC.Aiur.AIR.Expr
import IxCC.Aiur.Memory

/-! Exact memory columns, four polynomial constraints, and the single pull
lookup at the pinned ix revision. Polynomial conformance is checked against
the Rust builder separately; no Rust semantics are assumed in these definitions. -/

namespace IxCC.Aiur.AIR.Memory

open _root_.IxCC.Vendor.Aiur (G gSize)

/-- Match the Rust expression constructors' constant zero/one folding. -/
def scale (expression : Expr) (constant : G) : Expr :=
  if constant = 0 then .constant 0
  else if constant = 1 then expression
  else .mul expression (.constant constant)

def pull (bucket : Nat) : Lookup :=
  let selector := Expr.main 1
  { multiplicity := .neg (.main 0)
    arguments := [selector, scale selector (G.ofNat bucket), .mul selector (.main 2)] ++
      (List.range bucket).map (fun i => .mul selector (.main (3 + i))) }

def build (bucket : Nat) : Circuit :=
  let multiplicity := Expr.main 0
  let selector := Expr.main 1
  let pointer := Expr.main 2
  let one := Expr.constant 1
  let realTransition := Expr.mul (.next 1) .transition
  { width := 3 + bucket
    zeros := [
      .mul selector (.sub selector one),
      .mul multiplicity (.sub one selector),
      .mul realTransition (.sub selector one),
      .mul realTransition (.sub (.add pointer one) (.next 2))]
    lookups := [pull bucket] }

structure Row where
  multiplicity : G
  selector : G
  pointer : G
  values : List G
  deriving DecidableEq, Repr

instance : Inhabited Row := ⟨⟨0, 0, 0, []⟩⟩

def Row.columns (row : Row) : List G :=
  [row.multiplicity, row.selector, row.pointer] ++ row.values

def Row.active (row : Row) : Bool := row.selector == 1

def Row.project (bucket : Nat) (row : Row) : IxCC.Aiur.Row :=
  ⟨row.active, .memory bucket row.pointer row.values, row.multiplicity, []⟩

def Row.window (row next : Row) (transition : Bool) : Window :=
  ⟨row.columns, next.columns, transition, []⟩

/-- The equations evaluated by `build`, in their original order. -/
def Row.Equations (row next : Row) (transition : Bool) : Prop :=
  row.selector * (row.selector - 1) = 0 ∧
  row.multiplicity * (1 - row.selector) = 0 ∧
  (next.selector * (if transition then 1 else 0)) * (row.selector - 1) = 0 ∧
  (next.selector * (if transition then 1 else 0)) * (row.pointer + 1 - next.pointer) = 0

structure Table where
  bucket : Nat
  rows : Array Row
  deriving DecidableEq, Repr

/-- Out-of-bounds values are never used by a table constraint or projection. -/
def Table.row (table : Table) (index : Nat) : Row := table.rows[index]?.getD default

def Table.window (table : Table) (index : Nat) : Window :=
  (table.row index).window
    (table.row (if index + 1 < table.rows.size then index + 1 else 0))
    (decide (index + 1 < table.rows.size))

def Table.Satisfied (table : Table) : Prop :=
  ∀ index, index < table.rows.size → (build table.bucket).Satisfied (table.window index)

def Table.Shape (table : Table) : Prop :=
  table.bucket < gSize.toNat ∧ ∀ row ∈ table.rows, row.values.length = table.bucket

/-- Explicit until Booleanity is derived from the raw selector polynomial. -/
def Table.BooleanSelectors (table : Table) : Prop :=
  ∀ row ∈ table.rows, row.selector = 0 ∨ row.selector = 1

def Table.project (table : Table) : List IxCC.Aiur.Row :=
  table.rows.toList.map (Row.project table.bucket)

def project (tables : List Table) : Trace :=
  ⟨tables.flatMap Table.project, []⟩

def UniqueBuckets (tables : List Table) : Prop := (tables.map Table.bucket).Nodup

instance (tables : List Table) : Decidable (UniqueBuckets tables) :=
  inferInstanceAs (Decidable ((tables.map Table.bucket).Nodup))

end IxCC.Aiur.AIR.Memory
