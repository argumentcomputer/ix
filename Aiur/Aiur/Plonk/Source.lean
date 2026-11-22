import Aiur.Plonk.Scs
import Mathlib.Data.Finsupp.Basic

/-!
# The circuits the PLONK backend compiles

A `Table` is one Aiur circuit at a fixed capacity: a hash-consed node graph
over the current and next main row, fixed columns and the `first`, `last` and
`transition` selectors, polynomial constraints and signed LogUp lookups.
This is the meaning the final circuit must enforce; it is the multi-stark
semantics, with the next row read cyclically.

The lowered Aiur chips (`Tiling.Bridge.lower`) are the tables without fixed,
selector or next-row reads.
-/

namespace Aiur.Plonk

inductive Node (F : Type) where
  | const (value : F)
  | main (column : Nat) (next : Bool)
  | fixed (column : Nat) (next : Bool)
  | first
  | last
  | transition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving Repr, Inhabited, BEq

structure Lookup where
  negative : Bool
  count : Nat
  args : List Nat
  deriving Repr, Inhabited

structure Table (F : Type) where
  name : String
  rows : Nat
  width : Nat
  fixedWidth : Nat
  fixed : Array F
  nodes : Array (Node F)
  constraints : List Nat
  lookups : List Lookup
  deriving Repr, Inhabited

structure Source (F : Type) where
  callable : F
  publics : Nat
  outputs : Nat
  tables : List (Table F)
  deriving Repr

section Semantics

variable {F : Type} [CommRing F]

/-- The value of node `i` on row `r` of a table whose main trace is `main`. -/
def Table.value (t : Table F) (main : Nat → Nat → F) (r : Nat) (i : Nat) : F :=
  let next := (r + 1) % t.rows
  match t.nodes[i]? with
  | some (.const v) => v
  | some (.main c n) => main (if n then next else r) c
  | some (.fixed c n) => t.fixed.getD ((if n then next else r) * t.fixedWidth + c) 0
  | some .first => if r = 0 then 1 else 0
  | some .last => if r + 1 = t.rows then 1 else 0
  | some .transition => if r + 1 = t.rows then 0 else 1
  | some (.add a b) =>
      if _ : a < i then if _ : b < i then t.value main r a + t.value main r b else 0 else 0
  | some (.sub a b) =>
      if _ : a < i then if _ : b < i then t.value main r a - t.value main r b else 0 else 0
  | some (.mul a b) =>
      if _ : a < i then if _ : b < i then t.value main r a * t.value main r b else 0 else 0
  | some (.neg a) => if _ : a < i then -t.value main r a else 0
  | none => 0
termination_by i

def Table.Holds (t : Table F) (main : Nat → Nat → F) (r : Nat) : Prop :=
  ∀ j ∈ t.constraints, t.value main r j = 0

def Table.tuple (t : Table F) (main : Nat → Nat → F) (r : Nat) (l : Lookup) : List F :=
  l.args.map (t.value main r)

def Table.weight (t : Table F) (main : Nat → Nat → F) (r : Nat) (l : Lookup) : F :=
  if l.negative then -t.value main r l.count else t.value main r l.count

abbrev Ledger (F : Type) [Zero F] := List F →₀ F

noncomputable def Table.rowLedger (t : Table F) (main : Nat → Nat → F) (r : Nat) : Ledger F :=
  (t.lookups.map fun l => Finsupp.single (t.tuple main r l) (t.weight main r l)).sum

/-- The ledger of all rows of all tables, plus the root request. `main k`
is table `k`'s trace. -/
noncomputable def Source.ledger (s : Source F) (main : Nat → Nat → Nat → F) (root : List F) :
    Ledger F :=
  Finsupp.single root 1 +
    ((s.tables.zipIdx.map fun (t, k) =>
      ((List.range t.rows).map fun r => t.rowLedger (main k) r).sum).sum)

/-! ## The in-circuit LogUp encoding

`fp γ β u = β + n·γ^n + Σ u_i·γ^(e n i)`, with `e` the rotation that gives
index 2 exponent zero. For each `n`, `e n` permutes `0 .. n-1`; lengths are
separated by the `n·γ^n` term. -/

def expOf (n i : Nat) : Nat := if n < 3 then i else (i + n - 2) % n

def fp (γ β : F) (u : List F) : F :=
  β + (u.length : F) * γ ^ u.length +
    (u.zipIdx.map fun (x, i) => x * γ ^ expOf u.length i).sum

end Semantics

end Aiur.Plonk
