import Aiur.Plonk.Template

/-!
# Constraint normal forms over the shared node graph

`Table.expr` unfolds the hash-consed node graph into a tree, which is
exponential when nodes are shared. `Table.polys` normalises node by node,
reading operands from the already computed prefix, so every node is
normalised once. `Table.normCircuit` is `Table.wideCircuit` with each
constraint replaced by the expression of its normal form; both have the same
`Holds` (`normCircuit_holds_iff`).
-/

namespace Aiur.Plonk

open Aiur.Tiling (Poly Mono)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (Fr)

def Table.stepPoly (t : Table Fr) (acc : Array (Poly Fr)) (i : Nat) : Poly Fr :=
  match t.nodes[i]? with
  | some (.const v) => Poly.const v
  | some (.main c n) => Poly.var (2 * c + if n then 1 else 0)
  | some (.add a b) => if a < i ∧ b < i then Poly.norm (acc.getD a [] ++ acc.getD b []) else Poly.const 0
  | some (.sub a b) => if a < i ∧ b < i then Poly.norm (Poly.sub (acc.getD a []) (acc.getD b [])) else Poly.const 0
  | some (.mul a b) => if a < i ∧ b < i then Poly.norm (Poly.mul (acc.getD a []) (acc.getD b [])) else Poly.const 0
  | some (.neg a) => if a < i then Poly.neg (acc.getD a []) else Poly.const 0
  | _ => Poly.const 0

def Table.polysUpTo (t : Table Fr) (n : Nat) : Array (Poly Fr) :=
  (List.range n).foldl (fun acc i => acc.push (t.stepPoly acc i)) #[]

def Table.polys (t : Table Fr) : Array (Poly Fr) := t.polysUpTo t.nodes.size

theorem Table.polysUpTo_spec (t : Table Fr) (x : Nat → Fr) :
    ∀ n, (t.polysUpTo n).size = n ∧
      ∀ j < n, Poly.denote x ((t.polysUpTo n).getD j []) = (t.expr j).denote x := by
  intro n
  induction n with
  | zero => simp [Table.polysUpTo]
  | succ n ih =>
    obtain ⟨hsize, hval⟩ := ih
    have unfold : t.polysUpTo (n + 1) = (t.polysUpTo n).push (t.stepPoly (t.polysUpTo n) n) := by
      simp [Table.polysUpTo, List.range_succ, List.foldl_append]
    rw [unfold]
    refine ⟨by simp [hsize], fun j hj => ?_⟩
    by_cases hlt : j < n
    · have : ((t.polysUpTo n).push (t.stepPoly (t.polysUpTo n) n)).getD j [] = (t.polysUpTo n).getD j [] := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize, Nat.ne_of_lt hlt]
      rw [this, hval j hlt]
    · have hj' : j = n := by omega
      subst hj'
      have : ((t.polysUpTo j).push (t.stepPoly (t.polysUpTo j) j)).getD j [] = t.stepPoly (t.polysUpTo j) j := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize] <;>
          simp [Array.getElem_push, hsize]
      have hval' : ∀ k < j, Poly.denote x ((t.polysUpTo j)[k]?.getD []) = (t.expr k).denote x := by
        intro k hk; have := hval k hk; simpa [Array.getD_eq_getD_getElem?] using this
      rw [this, Table.stepPoly, Table.expr]
      cases h : t.nodes[j]? with
      | none => simp [ArithExpr.denote]
      | some node =>
        cases node with
        | const v => simp [ArithExpr.denote]
        | main c n => simp [ArithExpr.denote]
        | fixed => simp [ArithExpr.denote]
        | first => simp [ArithExpr.denote]
        | last => simp [ArithExpr.denote]
        | transition => simp [ArithExpr.denote]
        | add a b =>
            by_cases ha : a < j <;> by_cases hb : b < j <;>
              simp [ha, hb, ArithExpr.denote, Poly.denote_norm, hval' a, hval' b]
        | sub a b =>
            by_cases ha : a < j <;> by_cases hb : b < j <;>
              simp [ha, hb, ArithExpr.denote, Poly.denote_norm, hval' a, hval' b]
        | mul a b =>
            by_cases ha : a < j <;> by_cases hb : b < j <;>
              simp [ha, hb, ArithExpr.denote, Poly.denote_norm, hval' a, hval' b]
        | neg a =>
            by_cases ha : a < j <;> simp [ha, ArithExpr.denote, hval' a]

theorem Table.polys_denote (t : Table Fr) (x : Nat → Fr) (j : Nat) (hj : j < t.nodes.size) :
    Poly.denote x (t.polys.getD j []) = (t.expr j).denote x :=
  (t.polysUpTo_spec x t.nodes.size).2 j hj

def monoExpr (m : Mono) : ArithExpr Fr := m.foldr (fun v e => .mul (.var v) e) (.const 1)

def Poly.toExpr (p : Poly Fr) : ArithExpr Fr :=
  p.foldr (fun t e => .add (.mul (.const t.2) (monoExpr t.1)) e) (.const 0)

theorem monoExpr_denote (x : Nat → Fr) (m : Mono) : (monoExpr m).denote x = Mono.eval x m := by
  induction m with
  | nil => simp [monoExpr, ArithExpr.denote, Mono.eval]
  | cons v m ih =>
      simp only [monoExpr, List.foldr_cons] at ih ⊢
      simp [ArithExpr.denote, ih, Mono.eval]

theorem Poly.toExpr_denote (x : Nat → Fr) (p : Poly Fr) : (Poly.toExpr p).denote x = Poly.denote x p := by
  induction p with
  | nil => simp [Poly.toExpr, ArithExpr.denote]
  | cons t p ih =>
      simp only [Poly.toExpr, List.foldr_cons] at ih ⊢
      simp [ArithExpr.denote, ih, monoExpr_denote]

/-- Constraint `j` as the expression of its normal form; constraints naming
no node read as zero, as in `Table.expr`. -/
def Table.normExpr (t : Table Fr) (j : Nat) : ArithExpr Fr :=
  if j < t.nodes.size then Poly.toExpr (t.polys.getD j []) else .const 0

theorem Table.normExpr_denote (t : Table Fr) (x : Nat → Fr) (j : Nat) :
    (t.normExpr j).denote x = (t.expr j).denote x := by
  unfold Table.normExpr
  split
  · rename_i hj; rw [Poly.toExpr_denote, t.polys_denote x j hj]
  · rename_i hj
    rw [Table.expr]
    have : t.nodes[j]? = none := by simp; omega
    simp [this, ArithExpr.denote]

def Table.normCircuit (t : Table Fr) : Tiling.Circuit Fr where
  width := 2 * t.width
  constraints := t.constraints.map t.normExpr
  lookups := []

theorem Table.normCircuit_holds_iff (t : Table Fr) (x : Nat → Fr) :
    t.normCircuit.Holds x ↔ t.wideCircuit.Holds x := by
  simp [Tiling.Circuit.Holds, Scalar.Circuit.Satisfies, Table.normCircuit, Table.wideCircuit,
    Table.normExpr_denote]

namespace Lower

/-- `checkUniform` against the normal-form circuit. -/
def checkUniformNorm (t : Table Fr) : Except String Unit := do
  let ((), s) := (lowerRow t (sharedNodes t) 0).run {}
  let gs := s.gates.filter (·.tag == .constraint)
  let C := t.normCircuit
  for h : j in [0:C.constraints.length] do
    let Cj : Tiling.Circuit Fr := { C with constraints := [C.constraints[j]] }
    let roots := (Array.range gs.size).filter fun i => gs[i]!.root == some j
    match roots.toList with
    | [] =>
        let T : Tiling.Template Fr := { width := 4, slots := [], rows := [] }
        unless T.check Cj do throw s!"{t.name}: constraint {j} has no gate and is not identically zero"
    | [i] =>
        let cg := (cone gs i).map fun g => if g.root.isSome then { g with root := some 0 } else g
        let T ← toTemplate cg
        unless T.check Cj do throw s!"{t.name}: constraint {j} is not implied by its gates"
    | _ => throw s!"{t.name}: constraint {j} has several root gates"

end Lower

end Aiur.Plonk
