import Ix.CompileCert.SharingRoots
import IxC.Kernel.Ixon.ShapeSpec

/-! # Symbolic result shapes commute with canonical sharing -/

namespace Ix.CompileCert.ShapeSharing

open Ix.Kernel.Reader
open Ix.Sharing.Verify.SharingExact (substShares SharesIn)

def TableMeaning (expand : Nat → Ixon.Expr) (table : Array (Option Shape.Term)) : Prop :=
  ∀ (i : Nat), i < table.size → table[i]? = some (Shape.convert #[] (expand i))

theorem convert_subst (expand : Nat → Ixon.Expr) (table : Array (Option Shape.Term))
    (meaning : TableMeaning expand table) (raw : Ixon.Expr)
    (bounded : SharesIn (fun i => i < table.size) raw) :
    Shape.convert table raw = Shape.convert #[] (substShares expand raw) := by
  induction raw with
  | share i => simp only [Shape.convert, substShares, meaning i.toNat bounded, Option.join_some]
  | prj _ _ _ ih => simp only [Shape.convert, substShares, ih bounded]
  | app _ _ ihf iha | lam _ _ ihf iha | all _ _ ihf iha =>
    simp only [Shape.convert, substShares, ihf bounded.1, iha bounded.2]
  | letE _ _ _ _ _ _ ihv ihb =>
    simp only [Shape.convert, substShares, ihv bounded.2.1, ihb bounded.2.2]
  | _ => rfl

theorem table_push (expand : Nat → Ixon.Expr) (table : Array (Option Shape.Term))
    (meaning : TableMeaning expand table) (raw : Ixon.Expr)
    (bounded : SharesIn (fun i => i < table.size) raw)
    (equation : expand table.size = substShares expand raw) :
    TableMeaning expand (table.push (Shape.convert table raw)) := by
  have read : Shape.convert table raw = Shape.convert #[] (expand table.size) := by
    rw [convert_subst expand table meaning raw bounded, equation]
  intro i bound
  by_cases old : i < table.size
  · rw [Array.getElem?_push_lt old]
    have prior := meaning i old
    rw [Array.getElem?_eq_getElem old] at prior
    exact prior
  · have last : i = table.size := by simp only [Array.size_push] at bound; omega
    subst i
    rw [Array.getElem?_push_size, read]

def buildTable (raw : List Ixon.Expr) (initial : Array (Option Shape.Term)) :
    Array (Option Shape.Term) :=
  raw.foldl (fun table entry => table.push (Shape.convert table entry)) initial

theorem buildTable_meaning (expand : Nat → Ixon.Expr) (raw : List Ixon.Expr)
    (initial : Array (Option Shape.Term)) (meaning : TableMeaning expand initial)
    (entries : ∀ i, i < raw.length →
      expand (initial.size + i) = substShares expand raw[i]! ∧
        SharesIn (fun slot => slot < initial.size + i) raw[i]!) :
    (buildTable raw initial).size = initial.size + raw.length ∧
      TableMeaning expand (buildTable raw initial) := by
  induction raw generalizing initial with
  | nil => exact ⟨by simp [buildTable], meaning⟩
  | cons first rest ih =>
    have front := entries 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at front
    have next := table_push expand initial meaning first front.2 front.1
    have tail := ih (initial.push (Shape.convert initial first)) next (by
      intro i bound
      have row := entries (i + 1) (by simp only [List.length_cons]; omega)
      simpa only [Array.size_push, List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using row)
    refine ⟨?_, tail.2⟩
    change (buildTable rest (initial.push (Shape.convert initial first))).size = _
    rw [tail.1]
    simp only [Array.size_push, List.length_cons]
    omega

theorem sharing_meaning (constant : Ixon.Constant) (expand : Nat → Ixon.Expr)
    (entries : ∀ i, i < constant.sharing.size →
      expand i = substShares expand constant.sharing[i]! ∧
        SharesIn (fun slot => slot < i) constant.sharing[i]!) :
    (Shape.sharing constant.sharing).size = constant.sharing.size ∧
      TableMeaning expand (Shape.sharing constant.sharing) := by
  have built := buildTable_meaning expand constant.sharing.toList #[] (by
    intro i bound
    simp at bound) (by
      intro i bound
      simpa only [Array.size_empty, Nat.zero_add, Array.length_toList, Array.getElem!_toList] using
        entries i (by simpa using bound))
  simpa only [buildTable, Shape.sharing, Array.foldl_toList, Array.size_empty, Nat.zero_add,
    Array.length_toList] using built

theorem read_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr)
    (entries : ∀ i, i < constant.sharing.size →
      expand i = substShares expand constant.sharing[i]! ∧
        SharesIn (fun slot => slot < i) constant.sharing[i]!)
    (raw : Ixon.Expr) (bounded : SharesIn (fun i => i < constant.sharing.size) raw) :
    Shape.read constant raw = Shape.read flat (substShares expand raw) := by
  have meaning := sharing_meaning constant expand entries
  have bounded' : SharesIn (fun i => i < (Shape.sharing constant.sharing).size) raw := by
    simpa only [meaning.1] using bounded
  simpa only [Shape.read, empty, Shape.sharing, Array.foldl_empty] using
    convert_subst expand _ meaning.2 raw bounded'

theorem resultVar_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr)
    (entries : ∀ i, i < constant.sharing.size →
      expand i = substShares expand constant.sharing[i]! ∧
        SharesIn (fun slot => slot < i) constant.sharing[i]!)
    (raw : Ixon.Expr) (bounded : SharesIn (fun i => i < constant.sharing.size) raw)
    (fuel : Nat) :
    Shape.resultVar fuel constant raw = Shape.resultVar fuel flat (substShares expand raw) := by
  simp only [Shape.resultVar, read_expand constant flat empty expand entries raw bounded]

theorem analyse_expand (constant flat : Ixon.Constant) (empty : flat.sharing = #[])
    (expand : Nat → Ixon.Expr)
    (entries : ∀ i, i < constant.sharing.size →
      expand i = substShares expand constant.sharing[i]! ∧
        SharesIn (fun slot => slot < i) constant.sharing[i]!)
    (recursor : Ixon.Recursor)
    (bounded : SharesIn (fun i => i < constant.sharing.size) recursor.typ) (fuel : Nat) :
    Shape.analyse fuel constant recursor =
      Shape.analyse fuel flat { recursor with typ := substShares expand recursor.typ } := by
  have converted := read_expand constant flat empty expand entries recursor.typ bounded
  unfold Shape.read at converted
  simp only [Shape.analyse, Shape.analysePrepared, Shape.telescopePrepared, converted]

end Ix.CompileCert.ShapeSharing
