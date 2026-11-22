import Aiur.Plonk.Norm
import Aiur.Tiling.WideStage

/-!
# The circuits of a wide stage as PLONK input

The tables the PLONK backend compiles are the `WideStage.Air`s of
`WideIxa.stageOf`: unit tables (`IChip.lower`, no fixed columns), map tables
and ROM tables (fixed columns, no constraints). This is the trusted input;
`Plonk.Table` is only the lowering's working form here.

* `AirIn.fixRow a r` reads the fixed columns of row `r` as constants
  (`fixRow_denote`: same value under `a.assign main r`).
* `AirIn.rowConstraint a r j` is constraint `j` at row `r`, fixed values
  substituted and normalised (`Poly.ofExpr`, `Poly.norm`), as a
  one-constraint circuit. `holds_of_rowConstraints`: if every
  `rowConstraint a r j` holds at `a.assign main r`, so does `a.circuit`.
* `AirIn.table a r` (untrusted) is row `r` as a `Plonk.Table`: the circuit
  with row `r`'s fixed values folded in, hash-consed bottom-up, main column
  `v` as cell atom `2v`.
* `AirIn.checkConstraints` lowers the rows and checks each constraint against
  `rowConstraint` with `Tiling.Template.check` on its gate cone. A circuit
  whose constraints read no fixed column is lowered and checked once.

The constraint expressions of `IChip.lower` are trees of at most a few
hundred nodes on the L3 terminal, so normalising them directly is linear in
their size; only `Plonk.Table`'s node graph needs the node-by-node
normaliser of `Norm.lean`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Poly)
open Aiur.Tiling.WideStage (Air)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (Fr LGate Ref)

namespace AirIn

def fixRow (a : Air Fr) (r : Nat) : ArithExpr Fr → ArithExpr Fr
  | .const v => .const v
  | .var v => if v < a.circuit.width then .var v else .const (a.fixed r (v - a.circuit.width))
  | .add x y => .add (fixRow a r x) (fixRow a r y)
  | .sub x y => .sub (fixRow a r x) (fixRow a r y)
  | .mul x y => .mul (fixRow a r x) (fixRow a r y)

theorem fixRow_denote (a : Air Fr) (main : Nat → Nat → Fr) (r : Nat) (e : ArithExpr Fr) :
    (fixRow a r e).denote (a.assign main r) = e.denote (a.assign main r) := by
  induction e with
  | const v => rfl
  | var v =>
      by_cases h : v < a.circuit.width <;>
        simp [fixRow, h, ArithExpr.denote, Air.assign]
  | add x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]
  | sub x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]
  | mul x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]

theorem fixRow_of_inBounds (a : Air Fr) (r : Nat) (e : ArithExpr Fr)
    (h : e.inBounds a.circuit.width = true) : fixRow a r e = e := by
  induction e with
  | const v => rfl
  | var v => simp [ArithExpr.inBounds] at h; simp [fixRow, h]
  | add x y hx hy =>
      simp [ArithExpr.inBounds] at h; simp [fixRow, hx h.1, hy h.2]
  | sub x y hx hy =>
      simp [ArithExpr.inBounds] at h; simp [fixRow, hx h.1, hy h.2]
  | mul x y hx hy =>
      simp [ArithExpr.inBounds] at h; simp [fixRow, hx h.1, hy h.2]

/-- An expression as the expression of its normal form. -/
def normExpr (e : ArithExpr Fr) : ArithExpr Fr := Poly.toExpr (Poly.norm (Poly.ofExpr e))

theorem normExpr_denote (x : Nat → Fr) (e : ArithExpr Fr) : (normExpr e).denote x = e.denote x := by
  simp [normExpr, Poly.toExpr_denote, Poly.denote_norm, Poly.denote_ofExpr]

def rowConstraint (a : Air Fr) (r j : Nat) : Tiling.Circuit Fr where
  width := a.circuit.width
  constraints := [normExpr (fixRow a r (a.circuit.constraints.getD j (.const 0)))]
  lookups := []

theorem rowConstraint_holds_iff (a : Air Fr) (main : Nat → Nat → Fr) (r j : Nat)
    (hj : j < a.circuit.constraints.length) :
    (rowConstraint a r j).Holds (a.assign main r) ↔ a.circuit.constraints[j].denote (a.assign main r) = 0 := by
  simp [rowConstraint, Tiling.Circuit.Holds, Scalar.Circuit.Satisfies, normExpr_denote, fixRow_denote,
    List.getD_eq_getElem?_getD, hj]

theorem holds_of_rowConstraints (a : Air Fr) (main : Nat → Nat → Fr) (r : Nat)
    (h : ∀ j (hj : j < a.circuit.constraints.length), (rowConstraint a r j).Holds (a.assign main r)) :
    a.circuit.Holds (a.assign main r) := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  exact (rowConstraint_holds_iff a main r j hj).mp (h j hj)

/-- Every constraint reads only main columns. -/
def readsMainOnly (a : Air Fr) : Bool := a.circuit.constraints.all (·.inBounds a.circuit.width)

theorem rowConstraint_uniform (a : Air Fr) (h : readsMainOnly a = true) (r j : Nat) :
    rowConstraint a r j = rowConstraint a 0 j := by
  unfold rowConstraint
  congr 2
  cases hj : a.circuit.constraints[j]? with
  | none => simp [List.getD_eq_getElem?_getD, hj, fixRow]
  | some c =>
      have hin : c.inBounds a.circuit.width = true :=
        List.all_eq_true.mp h c (List.mem_of_getElem? hj)
      simp [List.getD_eq_getElem?_getD, hj, fixRow_of_inBounds a _ c hin]

/-! ## The lowering's view (untrusted) -/

/-- Hash-consing key of a node over already numbered operands. -/
abbrev NodeKey := Nat × Nat × Nat × Nat

structure HC where
  nodes : Array (Node Fr) := #[]
  ids : Std.HashMap NodeKey Nat := {}

/-- The node of `e` (bottom-up, structurally equal subterms shared); a main
column `v` is `.main v false`. -/
def hcVisit : ArithExpr Fr → StateM HC Nat
  | .const v => intern (0, v.val, 0, 0) (.const v)
  | .var c => intern (1, c, 0, 0) (.main c false)
  | .add x y => do let a ← hcVisit x; let b ← hcVisit y; intern (2, a, b, 0) (.add a b)
  | .sub x y => do let a ← hcVisit x; let b ← hcVisit y; intern (3, a, b, 0) (.sub a b)
  | .mul x y => do let a ← hcVisit x; let b ← hcVisit y; intern (4, a, b, 0) (.mul a b)
where
  intern (key : NodeKey) (n : Node Fr) : StateM HC Nat := modifyGet fun s =>
    match s.ids[key]? with
    | some i => (i, s)
    | none => (s.nodes.size, { nodes := s.nodes.push n, ids := s.ids.insert key s.nodes.size })

/-- Row `r` as a `Plonk.Table`; a multiplicity `0 - m` is a negative lookup of `m`. -/
def table (a : Air Fr) (r : Nat) : Table Fr :=
  let C : Tiling.Circuit Fr :=
    { width := a.circuit.width
      constraints := a.circuit.constraints.map (fixRow a r)
      lookups := a.circuit.lookups.map fun l => ⟨fixRow a r l.multiplicity, l.args.map (fixRow a r)⟩ }
  let build : StateM HC (List Nat × List (Nat × List Nat)) := do
    let zeros ← C.constraints.mapM hcVisit
    let lookups ← C.lookups.mapM fun l => do
      let m ← hcVisit l.multiplicity
      let args ← l.args.mapM hcVisit
      return (m, args)
    return (zeros, lookups)
  let ((zeros, lookups), hc) := build.run {}
  let nodes := hc.nodes
  let lookup (m : Nat) (args : List Nat) : Lookup :=
    match nodes[m]? with
    | some (.sub z x) =>
        match nodes[z]? with
        | some (.const v) =>
            if v == 0 then { negative := true, count := x, args } else { negative := false, count := m, args }
        | _ => { negative := false, count := m, args }
    | _ => { negative := false, count := m, args }
  { name := "", rows := a.rows, width := a.circuit.width, fixedWidth := a.circuit.fixedWidth, fixed := #[], nodes,
    constraints := zeros, lookups := lookups.map fun (m, args) => lookup m args }

end AirIn

/-- Every variable of every constraint's normal form is a column below `W`
that has a slot in `T`. -/
def coversVars (T : Tiling.Template Fr) (W : Nat) (C : Tiling.Circuit Fr) : Bool :=
  C.constraints.all fun e =>
    (Poly.norm (Poly.ofExpr e)).all fun t => t.1.all fun v => decide (v < W) && (T.colSlot v).isSome

namespace Lower

/-- The template of constraint `j`'s gate cone, cell reference `r` read as
wide column `col r`; the empty template when no gate asserts `j`. -/
def coneTemplate (gs : Array LGate) (col : Ref → Nat) (j : Nat) : Except String (Tiling.Template Fr) :=
  let roots := (Array.range gs.size).filter fun i => gs[i]!.root == some j
  match roots.toList with
  | [] => .ok { width := 4, slots := [], rows := [] }
  | [i] => toTemplate ((cone gs i).map fun g => if g.root.isSome then { g with root := some 0 } else g) col
  | _ => .error "several root gates"

/-- Constraint `j` is checked: its cone template passes `Template.check`
against `C j`, and every variable of `C j` is a slotted column below `W`. -/
def coneOk (gs : Array LGate) (col : Ref → Nat) (W : Nat) (C : Nat → Tiling.Circuit Fr) (j : Nat) : Bool :=
  match coneTemplate gs col j with
  | .ok T => T.check (C j) && coversVars T W (C j)
  | .error _ => false

theorem coneOk_spec {gs : Array LGate} {col : Ref → Nat} {W : Nat} {C : Nat → Tiling.Circuit Fr} {j : Nat}
    (h : coneOk gs col W C j = true) :
    ∃ T, coneTemplate gs col j = .ok T ∧ T.check (C j) = true ∧ coversVars T W (C j) = true := by
  unfold coneOk at h
  split at h
  · rename_i T hT; simp only [Bool.and_eq_true] at h; exact ⟨T, hT, h.1, h.2⟩
  · exact absurd h (by simp)

end Lower

namespace AirIn

/-- The constraint gates of row `r`. -/
def rowGates (a : Air Fr) (r : Nat) : Array LGate :=
  let t := table a r
  let ((), s) := (Lower.lowerRow t (Lower.sharedNodes t) 0).run {}
  s.gates.filter (·.tag == .constraint)

/-- Cell atom `2v` (reference `8v`) is main column `v`. -/
def airCol (r : Ref) : Nat := r / 8

/-- Every constraint of row `r` is checked on its cone. -/
def rowOk (a : Air Fr) (r : Nat) : Bool :=
  let gs := rowGates a r
  (List.range a.circuit.constraints.length).all (Lower.coneOk gs airCol a.circuit.width (rowConstraint a r))

theorem rowOk_spec {a : Air Fr} {r : Nat} (h : rowOk a r = true) {j : Nat} (hj : j < a.circuit.constraints.length) :
    ∃ T, Lower.coneTemplate (rowGates a r) airCol j = .ok T ∧ T.check (rowConstraint a r j) = true ∧
      coversVars T a.circuit.width (rowConstraint a r j) = true :=
  Lower.coneOk_spec (List.all_eq_true.mp h j (List.mem_range.mpr hj))

def checkRow (name : String) (a : Air Fr) (r : Nat) : Except String Unit := do
  if rowOk a r then return
  let gs := rowGates a r
  for j in [0:a.circuit.constraints.length] do
    unless Lower.coneOk gs airCol a.circuit.width (rowConstraint a r) j do
      throw s!"{name}: constraint {j} is not implied by its gates"

/-- Check every row's constraints; once when they read no fixed column
(`rowConstraint_uniform`). -/
def checkConstraints (name : String) (a : Air Fr) : Except String Unit := do
  if a.circuit.constraints.isEmpty then return
  if readsMainOnly a then checkRow name a 0
  else
    for r in [0:a.rows] do checkRow s!"{name} row {r}" a r

end AirIn

end Aiur.Plonk
