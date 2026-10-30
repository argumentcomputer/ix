module

public import Ix.Sharing.Family
public import Ix.Sharing.ParallelTable
public import Ix.Sharing.ParallelChoices
public import Ix.Sharing.Exact.KnapsackFast
import all Ix.Sharing.Exact.KnapsackFast
import all Ix.Sharing.Family
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Ix.Sharing.Family.Parallel

open Ix.Sharing.Exact

theorem sorted_le (xs : List Nat) : (sorted xs).toList.Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  simpa [sorted] using h

theorem reverse_toArray_eq_sorted {chosen : List Nat} (h : chosen.reverse.Pairwise (· ≤ ·)) :
    chosen.reverse.toArray = sorted chosen := by
  apply Array.toList_inj.mp
  simpa [sorted] using List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    h (sorted_le chosen) ((List.reverse_perm chosen).trans (List.mergeSort_perm _ _).symm)

/-- When the input member list is already non-decreasing, `chosen` is built in
reverse ascending order, so `chosen.reverse.toArray` produces the exact sorted
array at each leaf without running `mergeSort`. -/
def foldChoicesRev (visit : α → Array Nat → α) : List Nat → List Nat → α → α
  | [], chosen, acc => visit acc chosen.reverse.toArray
  | m :: rest, chosen, acc =>
    foldChoicesRev visit rest (m :: chosen) (foldChoicesRev visit rest chosen acc)

theorem foldChoicesRev_eq (visit : α → Array Nat → α) (remaining chosen : List Nat) (acc : α)
    (h : (chosen.reverse ++ remaining).Pairwise (· ≤ ·)) :
    foldChoicesRev visit remaining chosen acc = foldChoices visit remaining chosen acc := by
  induction remaining generalizing chosen acc with
  | nil =>
    simp only [List.append_nil] at h
    simp only [foldChoicesRev, foldChoices, reverse_toArray_eq_sorted h]
  | cons m rest ih =>
    simp only [foldChoicesRev, foldChoices]
    have h₁ : (chosen.reverse ++ rest).Pairwise (· ≤ ·) :=
      h.sublist (List.Sublist.append_left (List.sublist_cons_self m rest) chosen.reverse)
    have h₂ : ((m :: chosen).reverse ++ rest).Pairwise (· ≤ ·) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h
    rw [ih chosen acc h₁, ih (m :: chosen) _ h₂]

def foldChoicesFast (visit : α → Array Nat → α) (members : List Nat) (acc : α) : α :=
  if decide (members.Pairwise (· ≤ ·)) then
    foldChoicesRev visit members [] acc
  else
    foldChoices visit members [] acc

theorem foldChoicesFast_eq (visit : α → Array Nat → α) (members : List Nat) (acc : α) :
    foldChoicesFast visit members acc = foldChoices visit members [] acc := by
  unfold foldChoicesFast
  split
  · rename_i h
    exact foldChoicesRev_eq visit members [] acc (by simpa using of_decide_eq_true h)
  · rfl

def merge (left right : CTable) : CTable :=
  ParallelTable.merge entryLt left right

theorem better_eq (entry : Entry) (previous : Option Entry) :
    ParallelTable.better entryLt entry previous = betterEntry entry previous := by
  cases previous with
  | none => rfl
  | some previous => cases previous; rfl

theorem add_eq (rows : CTable) (entry : Entry) :
    rows.add entry = ParallelTable.add entryLt (fun e : Entry => e.2.size) rows entry := by
  unfold ParallelTable.add
  simp only [better_eq]
  rfl

theorem merge_add (left right : CTable) (entry : Entry) :
    merge left (right.add entry) = (merge left right).add entry := by
  unfold merge
  rw [add_eq, add_eq]
  exact ParallelTable.merge_add entryLt (fun e : Entry => e.2.size)
    (fun _ _ _ => entryLt_trans) (fun _ _ => entryLt_total) left right entry

@[simp] theorem merge_empty (rows : CTable) : merge rows #[] = rows :=
  ParallelTable.merge_empty_right entryLt rows

def visit (cost : Cost) (rows : CTable) (set : Array Nat) : CTable :=
  rows.add (cost set, set)

theorem merge_fold (cost : Cost) (left right : CTable) (remaining chosen : List Nat) :
    merge left (foldChoices (visit cost) remaining chosen right) =
      foldChoices (visit cost) remaining chosen (merge left right) := by
  induction remaining generalizing chosen right with
  | nil => exact merge_add left right _
  | cons member rest ih =>
    simp only [foldChoices]
    rw [ih, ih]

theorem merge_foldRev (cost : Cost) (left right : CTable) (remaining chosen : List Nat) :
    merge left (foldChoicesRev (visit cost) remaining chosen right) =
      foldChoicesRev (visit cost) remaining chosen (merge left right) := by
  induction remaining generalizing chosen right with
  | nil => exact merge_add left right _
  | cons member rest ih =>
    simp only [foldChoicesRev]
    rw [ih, ih]

/-- Each branch uses the bounded subset fold and retains only one
winning row per count. The prefix depth is capped at three before task creation. -/
def exactTable (depth : Nat) (cost : Cost) (members : List Nat) : CTable :=
  if decide (members.Pairwise (· ≤ ·)) then
    ParallelChoices.run depth members [] #[] merge (foldChoicesRev (visit cost))
  else
    ParallelChoices.run depth members [] #[] merge (foldChoices (visit cost))

theorem exactTable_eq (depth : Nat) (cost : Cost) (members : List Nat) :
    exactTable depth cost members = foldChoices (visit cost) members [] #[] := by
  unfold exactTable
  split
  · rename_i h
    have hrun : ParallelChoices.run depth members [] #[] merge (foldChoicesRev (visit cost)) =
        foldChoicesRev (visit cost) members [] #[] := by
      apply ParallelChoices.run_eq
      · intro member rest chosen acc
        rfl
      · intro remaining chosen acc
        rw [merge_foldRev, merge_empty]
    rw [hrun]
    exact foldChoicesRev_eq (visit cost) members [] #[] (by simpa using of_decide_eq_true h)
  · apply ParallelChoices.run_eq
    · intro member rest chosen acc
      rfl
    · intro remaining chosen acc
      rw [merge_fold, merge_empty]

/-- Large exact families within the production K16 range use the
parallel evaluator; smaller exact families use the sort-free leaf fold when
members are ascending; greedy and larger offline families keep their
existing implementation and declared limits. -/
def tableWithDepth (depth : Nat) (cfg : Config) (cost : Cost) (members : List Nat) : CTable :=
  if 12 ≤ members.length ∧ members.length ≤ 16 ∧ members.length ≤ cfg.exactLimit then
    exactTable depth cost members
  else if members.length ≤ cfg.exactLimit then
    foldChoicesFast (visit cost) members #[]
  else Family.table cfg cost members

/-- Complete table equality, including lengths, empty cells and ties. Member
lists may contain duplicates; no sortedness or cost-oracle premise is added. -/
theorem tableWithDepth_eq (depth : Nat) (cfg : Config) (cost : Cost) (members : List Nat) :
    tableWithDepth depth cfg cost members = Family.table cfg cost members := by
  unfold tableWithDepth
  split
  · rename_i selected
    rw [exactTable_eq]
    simp only [Family.table, foldFamily, selected.2.2, ite_true]
    rfl
  · split
    · rename_i exact
      rw [foldChoicesFast_eq]
      simp only [Family.table, foldFamily, exact, ite_true]
      rfl
    · rfl

def table (cfg : Config) (cost : Cost) (members : List Nat) : CTable :=
  tableWithDepth 3 cfg cost members

theorem table_eq (cfg : Config) (cost : Cost) (members : List Nat) :
    table cfg cost members = Family.table cfg cost members :=
  tableWithDepth_eq 3 cfg cost members

@[csimp] theorem table_eq_function : @Family.table = @table := by
  funext cfg cost members
  exact (table_eq cfg cost members).symm

end Ix.Sharing.Family.Parallel
