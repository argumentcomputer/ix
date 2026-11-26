import Aiur.Plonk.Lower
import Aiur.Tiling.Sound

/-!
# Row templates as Tiling templates

A uniform table's row gates, read as a `Tiling.Template` of width 4 with one
three-cell lane per row (`c3 = none`): one lane is exactly one gnark gate.
Column slot `k` is cell atom `k` (main column `k / 2` of the current row for
even `k`, of the next row for odd `k`). Every constraint-tagged gate either
defines its output wire (a `sum` slot) or asserts a table constraint
(`root j`). `Template.check` against `Table.wideCircuit` (lookups omitted)
then gives `Template.Checked.constraints_hold`. The message gates are checked
separately.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template SlotDef Lane Row Role Term)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (LGate Ref)

/-- Constraint polynomials of a table over cell atoms `2c + next`; fixed and
selector reads (absent in uniform tables) read as zero. -/
def Table.expr {F : Type} [Zero F] (t : Table F) (i : Nat) : ArithExpr F :=
  match t.nodes[i]? with
  | some (.const v) => .const v
  | some (.main c n) => .var (2 * c + if n then 1 else 0)
  | some (.add a b) => if _ : a < i then if _ : b < i then .add (t.expr a) (t.expr b) else .const 0 else .const 0
  | some (.sub a b) => if _ : a < i then if _ : b < i then .sub (t.expr a) (t.expr b) else .const 0 else .const 0
  | some (.mul a b) => if _ : a < i then if _ : b < i then .mul (t.expr a) (t.expr b) else .const 0 else .const 0
  | some (.neg a) => if _ : a < i then .sub (.const 0) (t.expr a) else .const 0
  | _ => .const 0
termination_by i

def Table.wideCircuit {F : Type} [Zero F] (t : Table F) : Tiling.Circuit F where
  width := 2 * t.width
  constraints := t.constraints.map t.expr
  lookups := []

namespace Lower

/-- The template of a row's constraint gates, or an error naming a gate the
template form cannot hold. Cell reference `r` is wide column `col r`. -/
def toTemplate {F : Type} [Ring F] [BEq F] (gates : Array (LGate F)) (col : Ref → Nat := (· / 4)) :
    Except String (Template F) := do
  let gs := gates.filter (·.tag == .constraint)
  let isCell (r : Ref) := r % 4 == 0
  let cells := (gs.toList.flatMap fun g => [g.a, g.b, g.c].filter isCell).eraseDups.mergeSort (· ≤ ·)
  let mut slotOf : Std.HashMap Ref Nat := {}
  let mut slots : Array (SlotDef F) := #[]
  for r in cells do
    slotOf := slotOf.insert r slots.size
    slots := slots.push (.column (col r))
  let mut rows : Array (Row F) := #[]
  for g in gs do
    let get (r : Ref) : Except String Nat :=
      match slotOf[r]? with
      | some s => pure s
      | none => throw s!"gate reads an undefined wire {r}"
    let sa ← get g.a
    let sb ← get g.b
    match g.root with
    | some j =>
        let sc ← get g.c
        rows := rows.push (.gate [⟨g.M, g.L, g.R, g.O, 0, g.C, some sa, some sb, some sc, none, 0⟩] false [.root j])
    | none =>
        unless g.c % 4 == 1 && g.O == -1 && !slotOf.contains g.c do
          throw "a non-root gate must define a fresh internal wire"
        let s := slots.size
        slotOf := slotOf.insert g.c s
        let terms : List (Term F) :=
          (if g.L == 0 then [] else [.linear g.L sa]) ++ (if g.R == 0 then [] else [.linear g.R sb]) ++
            (if g.M == 0 then [] else [.product g.M sa sb])
        slots := slots.push (.sum terms g.C)
        rows := rows.push (.gate [⟨g.M, g.L, g.R, -1, 0, g.C, some sa, some sb, some s, none, 0⟩] false [.defines s])
  return { width := 4, slots := slots.toList, rows := rows.toList }

/-- The constraint gates `root` depends on: the root and the defining gates of
the internal wires it reaches, in emission order. -/
def cone {F : Type} [Zero F] (gs : Array (LGate F)) (root : Nat) : Array (LGate F) := Id.run do
  let mut defOf : Std.HashMap Ref Nat := {}
  for h : i in [0:gs.size] do
    if gs[i].root.isNone then defOf := defOf.insert gs[i].c i
  let mut need : Std.HashMap Nat Unit := {}
  let mut stack := [root]
  while !stack.isEmpty do
    let i := stack.head!
    stack := stack.tail!
    if need.contains i then continue
    need := need.insert i ()
    let g := gs.getD i LGate.empty
    for r in [g.a, g.b, g.c] do
      if let some d := defOf[r]? then
        if d != i then stack := d :: stack
  return (Array.range gs.size).filterMap fun i => if need.contains i then gs[i]? else none

/-- Check a uniform table's constraints one at a time: constraint `j` against
the template of its gate cone. A constraint without a gate must normalize to
the zero polynomial. -/
def checkUniform {p : Nat} [Fact (Nat.Prime p)] (t : Table (ZMod p)) : Except String Unit := do
  let ((), s) := (lowerRow t (sharedNodes t) 0).run {}
  let gs := s.gates.filter (·.tag == .constraint)
  let C := t.wideCircuit
  for h : j in [0:C.constraints.length] do
    let Cj : Tiling.Circuit (ZMod p) := { C with constraints := [C.constraints[j]] }
    let roots := (Array.range gs.size).filter fun i => gs[i]!.root == some j
    match roots.toList with
    | [] =>
        let T : Template (ZMod p) := { width := 4, slots := [], rows := [] }
        unless T.check Cj do throw s!"{t.name}: constraint {j} has no gate and is not identically zero"
    | [i] =>
        let cg := (cone gs i).map fun g => if g.root.isSome then { g with root := some 0 } else g
        let T ← toTemplate cg
        unless T.check Cj do throw s!"{t.name}: constraint {j} is not implied by its gates"
    | _ => throw s!"{t.name}: constraint {j} has several root gates"

end Lower

end Aiur.Plonk
