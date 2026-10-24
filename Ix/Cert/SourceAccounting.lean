import Ix.Compile.SourceGraph.Accounting
import Ix.Cert.SourceOrder

namespace Ix.Cert.SourceAccounting
open Ix (Name)
open Ix.Compile.SourceGraph
open Ix.Compile.SourceGraph.Accounting

def Accounted (input published failed : Name → Bool) : Prop :=
  (∀ n, input n = true → published n = !failed n) ∧
  (∀ n, failed n = true → input n = true)

theorem selectKeys_eq (m : Ix.Map Name α) (bad : Name → Bool) :
    (selectKeys m bad).toList = m.keys.filter bad := by
  unfold selectKeys
  rw [Std.HashMap.fold_eq_foldl_toList]
  rw [← List.foldl_map (f := Prod.fst) (g := fun (acc : Array Name) n => if bad n then acc.push n else acc),
    ← List.foldl_filter, Array.foldl_toList_eq_map]
  simp [Std.HashMap.map_fst_toList_eq_keys]

private theorem selected_empty (m : Ix.Map Name α) (bad : Name → Bool)
    (respects : ∀ a b, (a == b) = true → bad a = bad b) :
    (selectKeys m bad).toList = [] ↔ ∀ n, m.contains n = true → bad n = false := by
  rw [selectKeys_eq, List.filter_eq_nil_iff]
  constructor
  · intro h n present
    rw [← Std.HashMap.contains_keys] at present
    obtain ⟨k, stored, same⟩ := List.contains_iff_exists_mem_beq.mp present
    rw [respects n k same]
    simpa using h k stored
  · intro h k stored
    have present : m.contains k = true := by
      rw [← Std.HashMap.contains_keys]
      exact List.elem_eq_true_of_mem stored
    simp [h k present]

private theorem verdict_ok (failed : Ix.Map Name String) (r : Report) :
    verdict failed r = .ok () ↔ r.uncovered.toList = [] ∧ r.outside.toList = [] := by
  obtain ⟨⟨bad⟩, ⟨outside⟩⟩ := r
  cases bad <;> cases outside <;> simp [verdict]

/-- Exact XOR on original key classes, and all flat failures inside input. -/
theorem check_success_iff (nodes : Ix.Map Name Node) (named : Ix.Map Name Ixon.Named) (failed : Ix.Map Name String) :
    check nodes named failed = .ok () ↔ Accounted nodes.contains named.contains failed.contains := by
  have xor (p f : Bool) : (p == f) = false ↔ p = !f := by cases p <;> cases f <;> decide
  rw [check, verdict_ok]
  simp only [scan]
  rw [selected_empty _ _ (by intro a b h; simp only [Std.HashMap.contains_congr h]),
    selected_empty _ _ (by intro a b h; simp only [Std.HashMap.contains_congr h])]
  simp [Accounted, xor]

private theorem merge_contains (m : Ix.Map Name String) (p : Name × String) (n : Name) :
    (if m.contains p.1 then m else m.insert p.1 p.2).contains n = (m.contains n || (p.1 == n)) := by
  by_cases present : m.contains p.1 = true
  · simp only [present, ite_true]
    by_cases same : (p.1 == n) = true
    · have hn : m.contains n = true := (Std.HashMap.contains_congr same).symm.trans present
      simp [hn]
    · simp [same]
  · simp [present, Std.HashMap.contains_insert, Bool.or_comm]

/-- Membership, not diagnostic precedence: the actual merge retains the
union even when ground/block messages for a key differ. -/
theorem failures_toMap_contains (f : Failures) (n : Name) : f.toMap.contains n = f.failed n := by
  have fold : ∀ (xs : List (Name × String)) (m : Ix.Map Name String),
      (xs.foldl (fun m p => if m.contains p.1 then m else m.insert p.1 p.2) m).contains n =
        (m.contains n || xs.any (fun p => n == p.1)) := by
    intro xs
    induction xs with
    | nil => intro m; simp
    | cons p xs ih =>
      intro m
      rw [List.foldl_cons, ih, merge_contains]
      simp [BEq.comm, Bool.or_assoc]
  unfold Failures.toMap Failures.failed
  rw [Std.HashMap.fold_eq_foldl_toList, fold]
  have same : f.blocks.toList.any (fun p => n == p.1) = f.blocks.contains n := by
    rw [← Std.HashMap.contains_keys, ← Std.HashMap.map_fst_toList_eq_keys]
    simp only [List.contains_map]
  rw [same]

private theorem domain (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (n : Name) :
    (Prepass.produce reserved raw workers).2.facts.nodes.contains n =
      (SourceGraph.full (SourceStream.canonical raw)).consts.contains n := by
  rw [← Std.HashMap.contains_keys, ← Std.HashMap.contains_keys,
    ← Std.HashMap.map_fst_toList_eq_keys, ← Std.HashMap.map_fst_toList_eq_keys, SourceOrder.produced_keys]

theorem produced_check_iff (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (named : Ix.Map Name Ixon.Named) (failed : Ix.Map Name String) :
    check (Prepass.produce reserved raw workers).2.facts.nodes named failed = .ok () ↔
      Accounted (SourceGraph.full (SourceStream.canonical raw)).consts.contains named.contains failed.contains := by
  rw [check_success_iff]
  simp only [Accounted, domain]

/-- Exact ordered reference coverage list, at the same supplied report.
No live ground/cenv failure argument equality is assumed or concluded. -/
theorem produced_uncovered (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (ixe : Ixon.Env) (f : Failures) :
    (scan (Prepass.produce reserved raw workers).2.facts.nodes ixe.named f.toMap).uncovered.toList =
      Ix.Cert.uncovered (SourceGraph.full (SourceStream.canonical raw)) ixe f := by
  simp only [scan, selectKeys_eq, failures_toMap_contains]
  rw [← Std.HashMap.map_fst_toList_eq_keys, SourceOrder.produced_keys, Std.HashMap.map_fst_toList_eq_keys]
  rfl

/-- The outside scan agrees with strayFailure on the SAME supplied flat
map, not on an assumed pure block-failure or grounding argument. -/
theorem produced_outside_empty_iff (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (named : Ix.Map Name Ixon.Named) (failed : Ix.Map Name String) :
    (scan (Prepass.produce reserved raw workers).2.facts.nodes named failed).outside.toList = [] ↔
      strayFailure (SourceGraph.full (SourceStream.canonical raw)) failed = none := by
  have head : (scan (Prepass.produce reserved raw workers).2.facts.nodes named failed).outside.toList.head? =
      strayFailure (SourceGraph.full (SourceStream.canonical raw)) failed := by
    simp only [scan, selectKeys_eq, domain]
    rw [← Std.HashMap.map_fst_toList_eq_keys, ← List.filterMap_eq_filter,
      List.filterMap_map, List.head?_filterMap]
    unfold strayFailure
    congr 1
    funext p
    simp only [Function.comp_def, Option.guard, Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.get?_eq_getElem?]
    have flip (b : Bool) : (if !b then some p.1 else none) = (if b then none else some p.1) := by
      cases b <;> rfl
    exact flip _
  rw [← List.head?_eq_none_iff, head]

/-- No failed original key plus successful accounting gives named
publication. This supplies no authenticated record or admission/value run. -/
theorem produced_published (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (ixe : Ixon.Env) (failed : Ix.Map Name String)
    (checked : check (Prepass.produce reserved raw workers).2.facts.nodes ixe.named failed = .ok ())
    (noFailure : ∀ n ci, (SourceGraph.full (SourceStream.canonical raw)).consts.get? n = some ci →
      failed.contains n = false) : Published ixe (SourceGraph.full (SourceStream.canonical raw)) := by
  intro n ci found
  have present : (SourceGraph.full (SourceStream.canonical raw)).consts.contains n = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change ((SourceGraph.full (SourceStream.canonical raw)).consts.get? n).isSome = true
    rw [found]; rfl
  have pub := ((produced_check_iff reserved raw workers ixe.named failed).mp checked).1 n present
  rw [noFailure n ci found, Std.HashMap.contains_eq_isSome_getElem?] at pub
  exact Option.isSome_iff_exists.mp pub

end Ix.Cert.SourceAccounting
