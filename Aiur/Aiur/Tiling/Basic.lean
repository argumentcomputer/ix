import Aiur.Scalar.Circuit.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Lookup circuits

The constraint-system level that the STARK backends consume: one row of main
columns (variables `0 .. width - 1`) and preprocessed columns (variables
`width .. width + fixedWidth - 1`), polynomial constraints that read only the
current row, and LogUp lookups `push(multiplicity, args)`.

Constraints are the existing `Scalar.Circuit.Constraint`. A `Lookup` carries
an arbitrary multiplicity expression. Preprocessed columns are the only
extension over the logical `Circuit.Chip` interface: a circuit that the tiling
pass consumes has `fixedWidth = 0`, and the narrow circuit it produces
reads its gate coefficients, copy labels and copy multiplicities from them.

A lookup ledger is the formal sum of tuples weighted by their field
multiplicities. LogUp balance of a set of traces is the ledger sum being zero.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Constraint Satisfies)

/-- `push(multiplicity, args)`; a pull is a push with negated multiplicity. -/
structure Lookup (F : Type) where
  multiplicity : ArithExpr F
  args : List (ArithExpr F)
  deriving Repr

structure Circuit (F : Type) where
  width : Nat
  fixedWidth : Nat := 0
  constraints : List (Constraint F)
  lookups : List (Lookup F)
  deriving Repr

abbrev Ledger (F : Type) [Zero F] := List F →₀ F

section Semantics

variable {F : Type} [Field F]

def Lookup.tuple (a : Var → F) (lookup : Lookup F) : List F := lookup.args.map (·.denote a)

noncomputable def Lookup.entry (a : Var → F) (lookup : Lookup F) : Ledger F :=
  Finsupp.single (lookup.tuple a) (lookup.multiplicity.denote a)

/-- The lookups of one row, as a ledger. -/
noncomputable def Circuit.rowLedger (circuit : Circuit F) (a : Var → F) : Ledger F :=
  (circuit.lookups.map (·.entry a)).sum

def Circuit.Holds (circuit : Circuit F) (a : Var → F) : Prop := Satisfies circuit.constraints a

end Semantics

/-! ## Hash-consed input graphs

The prover-side form of a wide circuit: operands of node `i` are nodes below
`i`. `Graph.circuit` unfolds it to the `Circuit` that the soundness theorems
are about. The graph is only the lowering's input format; the checker
validates the lowering's output against the unfolded circuit. -/

inductive Node (F : Type) where
  | const (value : F)
  | var (column : Nat)
  | add (x y : Nat)
  | sub (x y : Nat)
  | neg (x : Nat)
  | mul (x y : Nat)
  deriving Repr, BEq, Inhabited

structure Graph (F : Type) where
  width : Nat
  nodes : Array (Node F)
  zeros : List Nat
  /-- Multiplicity node and argument nodes. -/
  lookups : List (Nat × List Nat)
  deriving Repr

def Graph.expr [Zero F] (g : Graph F) (i : Nat) : ArithExpr F :=
  match g.nodes[i]? with
  | some (.const v) => .const v
  | some (.var c) => .var c
  | some (.add x y) => if _hx : x < i then if _hy : y < i then .add (g.expr x) (g.expr y) else .const 0 else .const 0
  | some (.sub x y) => if _hx : x < i then if _hy : y < i then .sub (g.expr x) (g.expr y) else .const 0 else .const 0
  | some (.neg x) => if _hx : x < i then .sub (.const 0) (g.expr x) else .const 0
  | some (.mul x y) => if _hx : x < i then if _hy : y < i then .mul (g.expr x) (g.expr y) else .const 0 else .const 0
  | none => .const 0
termination_by i

def Graph.circuit [Zero F] (g : Graph F) : Circuit F where
  width := g.width
  constraints := g.zeros.map g.expr
  lookups := g.lookups.map fun (m, args) => ⟨g.expr m, args.map g.expr⟩

end Aiur.Tiling
