import Ix.CompileCert.CliqueRowShape
import Ix.CompileCert.Canon.QSort
import Ix.Cert.ReaderUnits

/-! # Coverage of the actual clique-row producer outputs

The real qsort arrays and successful mapM workers are related position by
position. Counts and both directions of coverage preserve duplicate member
occurrences; no raw-name/hash or address injectivity is assumed. Copies use
the constants returned by const?, so their names come from those headers,
not from an unproved equality between a queried name and its stored header.

The non-WF empty branch stays explicit. Coverage is for actual rowMembers
and encoding-set array representatives, not every actual planner member,
driver/memo/publication coverage or semantic source-copy faithfulness.
-/

namespace Ix.CompileCert.CliqueRowsCoverage

open Ix (Name Expr ConstantInfo)
open Ix.Compile.Pass.Clique
open Ix.CompileCert.CliqueRowShape
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (array_mapM_ok forall₂_imp forall₂_mem_right)

def copyOrder (enc : Std.HashSet Name) : Array Name :=
  enc.toArray.qsort fun a b => (srcName a).pretty < (srcName b).pretty

def rowOrder (plan : CliquePlan) : Array Name :=
  (rowMembers plan).qsort fun a b => (rowName a).pretty < (rowName b).pretty

/-- An actual looked-up definition/theorem is copied by the producer. -/
def CopyOf (const? : Name → Option ConstantInfo) (enc : Std.HashSet Name)
    (n : Name) (copy : ConstantInfo) : Prop :=
  ∃ ci, const? n = some ci ∧
    (match ci with | .defnInfo _ | .thmInfo _ => True | _ => False) ∧ copy = srcCopy enc ci

/-- Positional coverage retains multiplicity, including aliased names or
identical output records. Every row carries its actual worker success. -/
def Produced (const? : Name → Option ConstantInfo) (plan : CliquePlan) (enc : Std.HashSet Name)
    (copies rows : Array ConstantInfo) : Prop :=
  List.Forall₂ (CopyOf const? enc) (copyOrder enc).toList copies.toList ∧
  List.Forall₂ (fun f row => rowOfWith const? plan enc f = .ok row ∧ RowShape const? plan enc f row)
    (rowOrder plan).toList rows.toList

theorem forall₂_swap {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : List.Forall₂ (fun y x => R x y) ys xs := by
  induction h with
  | nil => exact .nil
  | cons head _ tail => exact .cons head tail

theorem forall₂_lengths {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ tail => exact congrArg Nat.succ tail

/-- The actual spawned workers, read by the actual mapM, are the same pure
calls in the same order. This adds no schedule/refinement hypothesis. -/
theorem row_workers (const? : Name → Option ConstantInfo) (plan : CliquePlan)
    (enc : Std.HashSet Name) (members : Array Name) :
    (members.map fun f => Task.spawn fun _ => rowOfWith const? plan enc f).mapM (·.get) =
      members.mapM (rowOfWith const? plan enc) := by
  rw [Array.mapM_map]
  rfl

/-- Successful rowsOf retains either the exact non-WF empty result or the
actual encoding set and every positional copy/row worker result. -/
theorem rowsOf_produced {const? : Name → Option ConstantInfo} {plan : CliquePlan}
    {copies rows : Array ConstantInfo} (h : rowsOf const? plan = .ok (copies, rows)) :
    (plan.encoding ≠ .wellFounded ∧ copies = #[] ∧ rows = #[]) ∨
      ∃ enc, plan.encoding = .wellFounded ∧ encodingSet const? plan = .ok enc ∧
        Produced const? plan enc copies rows := by
  unfold rowsOf at h
  cases encoding : plan.encoding <;> simp only [encoding] at h
  case wellFounded =>
    obtain ⟨enc, henc, h⟩ := except_bind_ok.mp h
    obtain ⟨copies', hcopies, h⟩ := except_bind_ok.mp h
    obtain ⟨rows', hrows, h⟩ := except_bind_ok.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    refine .inr ⟨enc, rfl, henc, ?_, ?_⟩
    · apply forall₂_imp (fun n copy step => ?_) (array_mapM_ok hcopies)
      cases source : const? n with
      | none => simp only [source] at step; cases step
      | some ci =>
        cases ci with
        | defnInfo v =>
          simp only [source] at step
          exact ⟨_, source, trivial, (Except.ok.inj step).symm⟩
        | thmInfo v =>
          simp only [source] at step
          exact ⟨_, source, trivial, (Except.ok.inj step).symm⟩
        | _ => simp only [source] at step; cases step
    · rw [row_workers] at hrows
      exact forall₂_imp (fun _ _ worker => ⟨worker, rowOfWith_shape worker⟩) (array_mapM_ok hrows)
  all_goals
    have eq : (#[], #[]) = (copies, rows) := Except.ok.inj h
    exact .inl ⟨by simp, (congrArg Prod.fst eq).symm, (congrArg Prod.snd eq).symm⟩

/-- Explicit specialization to the branch that actually produces rows. -/
theorem rowsOf_wf {const? : Name → Option ConstantInfo} {plan : CliquePlan}
    {copies rows : Array ConstantInfo} (h : rowsOf const? plan = .ok (copies, rows))
    (wf : plan.encoding = .wellFounded) :
    ∃ enc, encodingSet const? plan = .ok enc ∧ Produced const? plan enc copies rows := by
  rcases rowsOf_produced h with ⟨notWF, _⟩ | ⟨enc, _, henc, produced⟩
  · exact (notWF wf).elim
  · exact ⟨enc, henc, produced⟩

namespace Produced

variable {const? : Name → Option ConstantInfo} {plan : CliquePlan} {enc : Std.HashSet Name}
  {copies rows : Array ConstantInfo} (h : Produced const? plan enc copies rows)
include h

/-- Counts are for occurrences, not unique names or distinct addresses. -/
theorem sizes : copies.size = enc.toArray.size ∧ rows.size = (rowMembers plan).size := by
  have hc : (copyOrder enc).size = copies.size := by simpa using forall₂_lengths h.1
  have hr : (rowOrder plan).size = rows.size := by simpa using forall₂_lengths h.2
  exact ⟨hc.symm.trans (Canon.qsort_perm _ _).size_eq, hr.symm.trans (Canon.qsort_perm _ _).size_eq⟩

theorem copy_of_input {n : Name} (member : n ∈ enc.toArray) :
    ∃ copy ∈ copies, CopyOf const? enc n copy := by
  have sorted : n ∈ copyOrder enc := Canon.mem_qsort.mpr member
  obtain ⟨copy, hc, related⟩ := forall₂_mem_right (forall₂_swap h.1) n (Array.mem_toList_iff.mpr sorted)
  exact ⟨copy, Array.mem_toList_iff.mp hc, related⟩

theorem row_of_member {f : Name} (member : f ∈ rowMembers plan) :
    ∃ row ∈ rows, rowOfWith const? plan enc f = .ok row ∧ RowShape const? plan enc f row := by
  have sorted : f ∈ rowOrder plan := Canon.mem_qsort.mpr member
  obtain ⟨row, hr, related⟩ := forall₂_mem_right (forall₂_swap h.2) f (Array.mem_toList_iff.mpr sorted)
  exact ⟨row, Array.mem_toList_iff.mp hr, related⟩

theorem input_of_copy {copy : ConstantInfo} (member : copy ∈ copies) :
    ∃ n ∈ enc.toArray, CopyOf const? enc n copy := by
  obtain ⟨n, hn, related⟩ := forall₂_mem_right h.1 copy (Array.mem_toList_iff.mpr member)
  exact ⟨n, Canon.mem_qsort.mp (Array.mem_toList_iff.mp hn), related⟩

theorem member_of_row {row : ConstantInfo} (member : row ∈ rows) :
    ∃ f ∈ rowMembers plan, rowOfWith const? plan enc f = .ok row ∧ RowShape const? plan enc f row := by
  obtain ⟨f, hf, related⟩ := forall₂_mem_right h.2 row (Array.mem_toList_iff.mpr member)
  exact ⟨f, Canon.mem_qsort.mp (Array.mem_toList_iff.mp hf), related⟩

/-- Every actual encoding-array input has a copied definition/theorem with
the actual returned header and value operations. Its header name may differ
from the queried n; no equality between them is invented here. -/
theorem copy_contents {n : Name} (member : n ∈ enc.toArray) :
    ∃ (copy : ConstantInfo) (ci : ConstantInfo) (value : Expr),
      copy ∈ copies ∧ const? n = some ci ∧ valueOf? ci = some value ∧
      copy.getCnst = ⟨srcName ci.getCnst.name, ci.getCnst.levelParams,
        renameConsts (srcRename enc) ci.getCnst.type⟩ ∧
      valueOf? copy = some (rowLhs enc value) := by
  obtain ⟨copy, copied, ci, source, kind, rfl⟩ := h.copy_of_input member
  cases ci with
  | defnInfo v => exact ⟨_, _, v.value, copied, source, rfl, srcCopy_header _ _, srcCopy_value rfl⟩
  | thmInfo v => exact ⟨_, _, v.value, copied, source, rfl, srcCopy_header _ _, srcCopy_value rfl⟩
  | _ => cases kind

end Produced

end Ix.CompileCert.CliqueRowsCoverage
