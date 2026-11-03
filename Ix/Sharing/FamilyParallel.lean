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
    foldChoicesFast (visit cost) members [] #[]
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

/-- A genuinely sequential family fold. Calling `tableWithDepth 0` would
still spawn a task and mark every array captured by `cost` as multithreaded. -/
def tableSequential (cfg : Config) (cost : Cost) (members : List Nat) : CTable :=
  foldFamily cfg cost members (visit cost) #[]

theorem tableSequential_eq (cfg : Config) (cost : Cost) (members : List Nat) :
    tableSequential cfg cost members = Family.table cfg cost members := rfl

/-- A subset task captures the full position table. Lean marks that table as
multithreaded, so clearing it afterwards copies all `positions` cells. Admit
this copy only when it fits within one of the eight branches' local node
evaluations. The bounded member check precedes exponentiation, including for
offline configurations with a larger exact limit. -/
def areaParallel (cfg : Config) (positions area members : Nat) : Bool :=
  if 12 ≤ members ∧ members ≤ 16 ∧ members ≤ cfg.exactLimit then
    decide (8 * positions ≤ area * 2 ^ members)
  else false

/-- Across admitted components, position-table copying is bounded by their
local subset evaluations, rather than by DAG size times component count. -/
theorem areaParallel_copy_bound (cfg : Config) (positions area members : Nat)
    (h : areaParallel cfg positions area members = true) :
    8 * positions ≤ area * 2 ^ members := by
  unfold areaParallel at h
  split at h
  · exact of_decide_eq_true h
  · cases h

/-- Preserve position-buffer reuse when the area is small relative to the
whole DAG; the family and every winning row are independent of this choice. -/
def tableForArea (cfg : Config) (positions area : Nat) (cost : Cost)
    (members : List Nat) : CTable :=
  if areaParallel cfg positions area members.length then
    table cfg cost members
  else tableSequential cfg cost members

theorem tableForArea_eq (cfg : Config) (positions area : Nat) (cost : Cost)
    (members : List Nat) :
    tableForArea cfg positions area cost members = Family.table cfg cost members := by
  unfold tableForArea
  split
  · exact table_eq cfg cost members
  · exact tableSequential_eq cfg cost members

@[csimp] theorem table_eq_function : @Family.table = @table := by
  funext cfg cost members
  exact (table_eq cfg cost members).symm

end Ix.Sharing.Family.Parallel
