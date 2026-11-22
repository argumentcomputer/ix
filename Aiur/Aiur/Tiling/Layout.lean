import Aiur.Tiling.Sound
import Aiur.Tiling.Lower
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The narrow circuit and its fixed columns

All templates share one narrow circuit of `W` main cells (`W` a multiple of
4, `L = W/4` lanes). It depends only on `W`; everything specific to the
program lives in its preprocessed columns:

* per lane `qm, q0, q1, q2, q3, qc`; then `join`, `sel`, `tag`, `sub`;
* `W` copy labels and `W` copy multiplicities.

Constraints: `Σ lanes = 0` and `(1 - join)·lane_l = 0` for `l < L - 1`.
Lookups: the message `push(sel·x0, [tag, sub, x1, …, x(W-1)])` and, for
every cell `j`, the copy `push(cmult_j, [COPY, label_j, x_j])`.

Circuit `f` owns `cap f` instances of its template. Physical rows are
enumerated by `places` (circuit, instance, template row); rows past the
last place have all fixed columns zero. Copy labels are `1 +` the index of
(circuit, instance, slot) in `keys`, so they never alias across instances.
A slot with `o` cells gets multiplicity `o - 1` on its first cell (its
anchor) and `-1` on every other cell.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

def COPY : Nat := 3

/-! ## Fixed column indices (relative to the first fixed column) -/

def joinCol (W : Nat) : Nat := 6 * (W / 4)
def selCol (W : Nat) : Nat := joinCol W + 1
def tagCol (W : Nat) : Nat := joinCol W + 2
def subCol (W : Nat) : Nat := joinCol W + 3
def labelCol (W j : Nat) : Nat := joinCol W + 4 + j
def multCol (W j : Nat) : Nat := joinCol W + 4 + W + j
def fixedWidth (W : Nat) : Nat := joinCol W + 4 + 2 * W

/-! ## The narrow circuit -/

section Circuit

variable [Zero F] [One F]

/-- The variable of fixed column `k`. -/
def fixedVar (W k : Nat) : ArithExpr F := .var (W + k)

/-- `qm·x0·x1 + q0·x0 + q1·x1 + q2·x2 + q3·x3 + qc` of lane `l`. -/
def laneExpr (W l : Nat) : ArithExpr F :=
  let x (m : Nat) : ArithExpr F := .var (4 * l + m)
  let q (m : Nat) : ArithExpr F := fixedVar W (6 * l + m)
  .add (.add (.add (.add (.add (.mul (.mul (q 0) (x 0)) (x 1)) (.mul (q 1) (x 0)))
    (.mul (q 2) (x 1))) (.mul (q 3) (x 2))) (.mul (q 4) (x 3))) (q 5)

def lanesSum (W : Nat) : List Nat → ArithExpr F
  | [] => .const 0
  | l :: ls => .add (laneExpr W l) (lanesSum W ls)

def narrowConstraints (W : Nat) : List (ArithExpr F) :=
  lanesSum W (List.range (W / 4)) ::
    (List.range (W / 4 - 1)).map fun l => .mul (.sub (.const 1) (fixedVar W (joinCol W))) (laneExpr W l)

def messageLookup (W : Nat) : Lookup F where
  multiplicity := .mul (fixedVar W (selCol W)) (.var 0)
  args := fixedVar W (tagCol W) :: fixedVar W (subCol W) :: (List.range (W - 1)).map fun j => .var (j + 1)

def copyLookup [NatCast F] (W j : Nat) : Lookup F where
  multiplicity := fixedVar W (multCol W j)
  args := [.const (COPY : F), fixedVar W (labelCol W j), .var j]

def narrowCircuit [NatCast F] (W : Nat) : Circuit F where
  width := W
  fixedWidth := fixedWidth W
  constraints := narrowConstraints W
  lookups := messageLookup W :: (List.range W).map (copyLookup W)

end Circuit

/-! ## Fixed values of one template row -/

section Fixed

variable [Zero F] [One F] [Add F] [Mul F]

/-- Fixed lane column `m` of an instance with invocation id `id`. -/
def Lane.coef (lane : Lane F) (id : F) : Nat → F
  | 0 => lane.qm
  | 1 => lane.q0
  | 2 => lane.q1
  | 3 => lane.q2
  | 4 => lane.q3
  | 5 => lane.qc + lane.qid * id
  | _ => 0

def Row.lane (row : Row F) (l : Nat) : Lane F :=
  match row with
  | .gate lanes _ _ => lanes.getD l Lane.zero
  | .message .. => Lane.zero

def Row.joinValue : Row F → F
  | .gate _ true _ => 1
  | _ => 0

def Row.messageValue : Row F → F × F × F
  | .message sel tag sub _ => (sel, tag, sub)
  | .gate .. => (0, 0, 0)

/-- Fixed column `k` of a template row, given its cells' labels and
multiplicities and the instance's invocation id. -/
def Row.fixed (W : Nat) (row : Row F) (label mult : Nat → F) (id : F) (k : Nat) : F :=
  if k < joinCol W then (row.lane (k / 6)).coef id (k % 6)
  else if k = joinCol W then row.joinValue
  else if k = selCol W then row.messageValue.1
  else if k = tagCol W then row.messageValue.2.1
  else if k = subCol W then row.messageValue.2.2
  else if k < joinCol W + 4 + W then label (k - (joinCol W + 4))
  else if k < fixedWidth W then mult (k - (joinCol W + 4 + W))
  else 0

end Fixed

/-! ## Regions, labels and the fixed matrix -/

/-- Cells of a template in row-major order. -/
def Template.cellIndices (T : Template F) : List (Nat × Nat) :=
  (List.range T.rows.length).flatMap fun r => (List.range T.width).map fun j => (r, j)

/-- The first cell of slot `s`. -/
def Template.anchor (T : Template F) (s : Nat) : Option (Nat × Nat) :=
  T.cellIndices.find? fun (r, j) => T.cell r j == some s

def Template.occurrences (T : Template F) (s : Nat) : Nat :=
  ((Finset.range T.rows.length ×ˢ Finset.range T.width).filter fun e => T.cell e.1 e.2 = some s).card

structure System (F : Type) where
  width : Nat
  circuits : List (Circuit F)
  templates : List (Template F)
  caps : List Nat

namespace System

variable (sys : System F)

def cap (f : Nat) : Nat := sys.caps.getD f 0

def rowCount (f : Nat) : Nat := (sys.templates[f]?.map (·.rows.length)).getD 0

def slotCount (f : Nat) : Nat := (sys.templates[f]?.map (·.slots.length)).getD 0

/-- `(f, i, x)` for every circuit `f`, instance `i < cap f` and `x < count f`. -/
def enumerate (count : Nat → Nat) : List (Nat × Nat × Nat) :=
  (List.range sys.templates.length).flatMap fun f =>
    ((List.range (sys.cap f)).flatMap fun i => (List.range (count f)).map fun x => (i, x)).map
      fun ix => (f, ix)

def places : List (Nat × Nat × Nat) := sys.enumerate sys.rowCount

def keys : List (Nat × Nat × Nat) := sys.enumerate sys.slotCount

/-- The physical row of instance `i` of circuit `f`, template row `r`. -/
def row (f i r : Nat) : Nat := sys.places.idxOf (f, i, r)

def label (f i s : Nat) : Nat := sys.keys.idxOf (f, i, s) + 1

/-- The invocation id of instance `i` of circuit `f`: its index among all
instances, circuit by circuit. -/
def instId (f i : Nat) : Nat := ((List.range f).map sys.cap).sum + i

/-- The copy key (circuit, instance, slot) of cell `j` of physical row `p`. -/
def copyKey (p j : Nat) : Option (Nat × Nat × Nat) :=
  match sys.places[p]? with
  | some (f, i, r) =>
      match sys.templates[f]? with
      | some T => (T.cell r j).map fun s => (f, i, s)
      | none => none
  | none => none

def labelAt [NatCast F] [Zero F] (p j : Nat) : F :=
  match sys.copyKey p j with
  | some (f, i, s) => (sys.label f i s : F)
  | none => 0

def multAt [Zero F] [One F] [Neg F] [Sub F] [NatCast F] (p j : Nat) : F :=
  match sys.places[p]? with
  | some (f, _, r) =>
      match sys.templates[f]? with
      | some T =>
          match T.cell r j with
          | some s => if T.anchor s = some (r, j) then (T.occurrences s : F) - 1 else -1
          | none => 0
      | none => 0
  | none => 0

def fixedAt [Zero F] [One F] [Neg F] [Sub F] [NatCast F] [Add F] [Mul F] (p k : Nat) : F :=
  match sys.places[p]? with
  | some (f, i, r) =>
      match sys.templates[f]? with
      | some T =>
          match T.rows[r]? with
          | some row => row.fixed sys.width (sys.labelAt p) (sys.multAt p) (sys.instId f i : F) k
          | none => 0
      | none => 0
  | none => 0

/-- Main row `p` together with its generated fixed columns. -/
def assign [Zero F] [One F] [Neg F] [Sub F] [NatCast F] [Add F] [Mul F] (main : Nat → Nat → F) (p : Nat) (v : Var) : F :=
  if v < sys.width then main p v else sys.fixedAt p (v - sys.width)

/-- Arity of each message `(tag, sub)`: the payload length after the prefix. -/
def arities : List ((F × F) × Nat) :=
  sys.templates.flatMap fun T => T.messages.map fun (_, tag, sub, cells) =>
    ((tag, sub), ((cells.drop 1).filterMap id).length)

def arityOf [DecidableEq F] (t : List F) : Nat :=
  match t with
  | tag :: sub :: _ => ((sys.arities.lookup (tag, sub))).getD 0
  | _ => 0

/-- Drops the unused cells of a message tuple. -/
def proj [DecidableEq F] (t : List F) : List F := t.take (2 + sys.arityOf t)

def bound : Nat := sys.keys.length + 1 + sys.places.length * sys.width

def check [CommRing F] [DecidableEq F] : Bool :=
  4 ≤ sys.width && sys.width % 4 == 0 &&
  sys.circuits.length == sys.templates.length && sys.caps.length == sys.templates.length &&
    (sys.templates.zip sys.circuits).all (fun (T, C) => T.width == sys.width && T.check C) &&
    (sys.templates.zip sys.circuits).all (fun (T, C) => T.checkUnchunked C) &&
    sys.arities.all (fun (key, n) => sys.arities.lookup key == some n) &&
    sys.arities.all fun (key, _) => key.1 != (COPY : F)

section Ledgers

variable [Field F]

noncomputable def narrowLedger (N : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range N, (narrowCircuit (F := F) sys.width).rowLedger (sys.assign main p)

noncomputable def wideLedger (wide : Nat → Nat → Var → F) : Ledger F :=
  ((List.range sys.circuits.length).map fun f =>
    ((List.range (sys.cap f)).map fun i =>
      ((sys.circuits[f]?.map fun C => C.rowLedger (wide f i)).getD 0)).sum).sum

end Ledgers

end System

/-- Fixed columns of a tiled system, row by row, for `N` physical rows. -/
def System.fixedMatrix [Zero F] [One F] [Neg F] [Sub F] [NatCast F] [Add F] [Mul F] (sys : System F) (N : Nat) :
    List (List F) :=
  (List.range N).map fun p => (List.range (fixedWidth sys.width)).map (sys.fixedAt p)

/-- Lower, check and lay out a set of circuits. -/
def tile [CommRing F] [DecidableEq F] (width : Nat) (graphs : List (Graph F)) (caps : List Nat) :
    Except String (System F) := do
  let templates ← graphs.mapM (lower · width)
  let sys : System F := { width, circuits := graphs.map Graph.circuit, templates, caps }
  unless sys.check do throw "tiled system failed validation"
  return sys

/-- Lay out given circuits, lowering each from its hash-consed graph. The
system's circuits are the given ones, so `System.check` validates the
templates against them. -/
def tileCircuits [CommRing F] [DecidableEq F] (width : Nat) (circuits : List (Circuit F))
    (caps : List Nat) : Except String (System F) := do
  let templates ← circuits.mapM fun C => lower (Graph.ofCircuit C) width
  let sys : System F := { width, circuits, templates, caps }
  unless sys.check do throw "tiled system failed validation"
  return sys

end Aiur.Tiling
