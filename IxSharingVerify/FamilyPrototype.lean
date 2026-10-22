import Ix.Sharing.FamilyPrototype
import IxSharingVerify.UniformTables
import IxC.Kernel.Audit.Axioms

/-! Additive family contracts. These facts describe the actual experimental
chain and untrimmed rows; they do not establish slack preservation, global
knapsack optimality, representation independence or a total normalizer. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel

theorem sorted_size (xs : List Nat) : (sorted xs).size = xs.length := by
  simp [sorted]

theorem sorted_mem (xs : List Nat) (x : Nat) : x ∈ (sorted xs).toList ↔ x ∈ xs := by
  simp [sorted]

theorem pickTail_mem (cost : Cost) (chosen : List Nat) (best : Nat × Entry) (rest : List Nat) :
    (pickTail cost chosen best rest).1 ∈ best.1 :: rest := by
  induction rest generalizing best with
  | nil => simp [pickTail]
  | cons m rest ih =>
    simp only [pickTail]
    split
    · have h := ih (m, score cost chosen m)
      simpa only [List.mem_cons] using (show (pickTail cost chosen (m, score cost chosen m) rest).1 = best.1 ∨
        (pickTail cost chosen (m, score cost chosen m) rest).1 = m ∨
        (pickTail cost chosen (m, score cost chosen m) rest).1 ∈ rest from Or.inr (List.mem_cons.mp h))
    · have h := List.mem_cons.mp (ih best)
      exact List.mem_cons.mpr (h.imp_right (List.mem_cons_of_mem m))

theorem pick_mem (cost : Cost) (chosen : List Nat) (m : Nat) (rest : List Nat) :
    pick cost chosen m rest ∈ m :: rest := pickTail_mem cost chosen (m, score cost chosen m) rest

theorem pickTail_scored (cost : Cost) (chosen : List Nat) (best : Nat × Entry) (rest : List Nat)
    (h : best.2 = score cost chosen best.1) :
    (pickTail cost chosen best rest).2 = score cost chosen (pickTail cost chosen best rest).1 := by
  induction rest generalizing best with
  | nil => exact h
  | cons m rest ih =>
    simp only [pickTail]
    split
    · exact ih _ rfl
    · exact ih _ h

theorem pickTail_bound (cost : Cost) (chosen : List Nat) (best : Nat × Entry) (rest : List Nat) :
    (pickTail cost chosen best rest).2.1 ≤ best.2.1 ∧
      ∀ m ∈ rest, (pickTail cost chosen best rest).2.1 ≤ (score cost chosen m).1 := by
  induction rest generalizing best with
  | nil => simp [pickTail]
  | cons m rest ih =>
    simp only [pickTail]
    split
    · rename_i better
      have lower : (score cost chosen m).1 ≤ best.2.1 := by
        rcases best with ⟨b, d, s⟩
        change (score cost chosen m).1 ≤ d
        simp only [betterEntry, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at better
        omega
      have next := ih (m, score cost chosen m)
      refine ⟨Int.le_trans next.1 lower, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact next.1
      · exact next.2 x hx
    · rename_i better
      have lower : best.2.1 ≤ (score cost chosen m).1 := by
        rcases best with ⟨b, d, s⟩
        change d ≤ (score cost chosen m).1
        simp only [betterEntry, Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not,
          Bool.and_eq_false_imp, beq_iff_eq] at better
        omega
      have next := ih best
      refine ⟨next.1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans next.1 lower
      · exact next.2 x hx

/-- The actual next extension minimizes the component-cost function. -/
theorem pick_minimum (cost : Cost) (chosen : List Nat) (m : Nat) (rest : List Nat)
    (x : Nat) (hx : x ∈ m :: rest) :
    cost (sorted (pick cost chosen m rest :: chosen)) ≤ cost (sorted (x :: chosen)) := by
  have scored := pickTail_scored cost chosen (m, score cost chosen m) rest rfl
  have bound := pickTail_bound cost chosen (m, score cost chosen m) rest
  change (score cost chosen (pick cost chosen m rest)).1 ≤ (score cost chosen x).1
  unfold pick
  rw [← scored]
  rcases List.mem_cons.mp hx with rfl | hx
  · exact bound.1
  · exact bound.2 x hx

/-- The greedy order removes exactly one present member at every step. -/
theorem greedyOrderAux_perm (cost : Cost) (fuel : Nat) (chosen members : List Nat)
    (enough : members.length ≤ fuel) :
    (greedyOrderAux cost fuel chosen members).Perm members := by
  induction fuel generalizing chosen members with
  | zero =>
    have h : members = [] := by cases members <;> simp_all
    subst members
    simp [greedyOrderAux]
  | succ fuel ih =>
    cases members with
    | nil => simp [greedyOrderAux]
    | cons m rest =>
      let next := pick cost chosen m rest
      have present : next ∈ m :: rest := pick_mem cost chosen m rest
      have length := List.length_erase_of_mem present
      have step := ih (next :: chosen) ((m :: rest).erase next) (by simp at enough length ⊢; omega)
      exact (step.cons next).trans (List.perm_cons_erase present).symm

theorem greedyOrder_perm (cost : Cost) (members : List Nat) :
    (greedyOrder cost members).Perm members :=
  greedyOrderAux_perm cost members.length [] members (Nat.le_refl _)

theorem greedyOrder_nodup (cost : Cost) {members : List Nat} (h : members.Nodup) :
    (greedyOrder cost members).Nodup := (greedyOrder_perm cost members).nodup_iff.mpr h

theorem chainSet_size (cost : Cost) (members : List Nat) (k : Nat) (hk : k ≤ members.length) :
    (chainSet cost members k).size = k := by
  have length := (greedyOrder_perm cost members).length_eq
  simp [chainSet, sorted_size, length, Nat.min_eq_left hk]

theorem chain_length (cost : Cost) (members : List Nat) :
    (chain cost members).length = members.length + 1 := by simp [chain]

theorem chainSet_zero (cost : Cost) (members : List Nat) : chainSet cost members 0 = #[] := by
  simp [chainSet, sorted]

theorem chainSet_end (cost : Cost) (members : List Nat) (x : Nat) :
    x ∈ (chainSet cost members members.length).toList ↔ x ∈ members := by
  have hp := greedyOrder_perm cost members
  unfold chainSet
  rw [sorted_mem, ← hp.length_eq, List.take_length]
  exact hp.mem_iff

theorem chainSet_subset (cost : Cost) (members : List Nat) (k x : Nat)
    (h : x ∈ (chainSet cost members k).toList) : x ∈ members := by
  apply (greedyOrder_perm cost members).mem_iff.mp
  exact List.mem_of_mem_take ((sorted_mem _ _).mp h)

theorem chainSet_nodup (cost : Cost) {members : List Nat} (h : members.Nodup) (k : Nat) :
    (chainSet cost members k).toList.Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (greedyOrder_nodup cost h).take

theorem chainSet_mono (cost : Cost) (members : List Nat) {i j x : Nat} (hij : i ≤ j)
    (hx : x ∈ (chainSet cost members i).toList) : x ∈ (chainSet cost members j).toList := by
  exact (sorted_mem _ _).mpr (List.take_subset_take_left _ hij ((sorted_mem _ _).mp hx))

theorem chainSet_distinct (cost : Cost) (members : List Nat) {i j : Nat}
    (hi : i ≤ members.length) (hj : j ≤ members.length) (hne : i ≠ j) :
    chainSet cost members i ≠ chainSet cost members j := by
  intro h
  have := congrArg Array.size h
  rw [chainSet_size cost members i hi, chainSet_size cost members j hj] at this
  exact hne this

/-- A chain contains precisely its count-indexed prefixes. -/
theorem chain_mem (cost : Cost) (members : List Nat) (set : Array Nat) :
    set ∈ chain cost members ↔ ∃ k, k ≤ members.length ∧ set = chainSet cost members k := by
  simp only [chain, List.mem_map, List.mem_range, chainSet]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h.symm⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, by omega, h.symm⟩

theorem foldChoices_eq (visit : α → Array Nat → α) (members chosen : List Nat) (acc : α) :
    foldChoices visit members chosen acc = (choices members chosen).foldl visit acc := by
  induction members generalizing chosen acc with
  | nil => simp [foldChoices, choices]
  | cons m rest ih => simp [foldChoices, choices, List.foldl_append, ih]

theorem choices_length (members chosen : List Nat) :
    (choices members chosen).length = 2 ^ members.length := by
  induction members generalizing chosen with
  | nil => simp [choices]
  | cons m rest ih => simp [choices, ih, Nat.pow_succ, Nat.mul_two]

theorem choices_members (members chosen : List Nat) (set : Array Nat)
    (h : set ∈ choices members chosen) : ∀ x ∈ set.toList, x ∈ members ∨ x ∈ chosen := by
  induction members generalizing chosen with
  | nil =>
    simp only [choices, List.mem_singleton] at h
    subst set
    intro x hx
    exact Or.inr ((sorted_mem chosen x).mp hx)
  | cons m rest ih =>
    simp only [choices, List.mem_append] at h
    rcases h with h | h
    · intro x hx
      exact (ih chosen h x hx).imp_left (List.mem_cons_of_mem m)
    · intro x hx
      rcases ih (m :: chosen) h x hx with hr | hc
      · exact Or.inl (List.mem_cons_of_mem m hr)
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl List.mem_cons_self
        · exact Or.inr hc

theorem foldFamily_eq (cfg : Config) (cost : Cost) (members : List Nat)
    (visit : α → Array Nat → α) (acc : α) :
    foldFamily cfg cost members visit acc = (family cfg cost members).foldl visit acc := by
  simp only [foldFamily, family]
  split <;> simp [foldChoices_eq]

/-- Soundness and per-count domination are separate from slack trimming.
The selected row is a member of the actual family with its actual cost. -/
structure TableMeaning (cost : Cost) (sets : List (Array Nat)) (rows : CTable) : Prop where
  sound : Entries rows (fun e => e.2 ∈ sets ∧ e.1 = cost e.2)
  covers : ∀ set ∈ sets, HasAt rows set.size (cost set)

/-- Stronger interface for the later tie-preserving slack/knapsack bridge.
It is deliberately an explicit separate obligation at this checkpoint. -/
def TieCoverage (cost : Cost) (sets : List (Array Nat)) (rows : CTable) : Prop :=
  ∀ set ∈ sets, HasAtT rows set.size (cost set) set.toList

theorem table_meaning (cfg : Config) (cost : Cost) (members : List Nat) :
    TableMeaning cost (family cfg cost members) (table cfg cost members) := by
  unfold table
  rw [foldFamily_eq]
  constructor
  · apply foldl_entries (Q := fun set => set ∈ family cfg cost members)
    · intro acc set member valid
      exact add_entries valid ⟨member, rfl⟩
    · exact fun _ h => h
    · intro k e h
      simp at h
  · intro set member
    exact foldl_hasAt _ (fun acc x => add_improves acc (cost x, x)) member
      (fun acc => add_hasAt acc (cost set, set)) #[]

/-- The generic per-count result is genuinely minimal over its family. -/
theorem table_minimum (cfg : Config) (cost : Cost) (members : List Nat) (set : Array Nat)
    (member : set ∈ family cfg cost members) :
    ∃ selected, (table cfg cost members)[set.size]! = some (cost selected, selected) ∧
      selected ∈ family cfg cost members ∧ selected.size = set.size ∧ cost selected ≤ cost set := by
  have meaning := table_meaning cfg cost members
  obtain ⟨e, row, best⟩ := meaning.covers set member
  obtain ⟨size, inside, scored⟩ := meaning.sound set.size e row
  exact ⟨e.2, by simpa [← scored] using row, inside, size, by simpa [scored] using best⟩

/-- The emitted experimental table uses the actual component evaluator,
with its empty-subset baseline, rather than a standalone-gain heuristic. -/
theorem component_meaning (cfg : Config) (ex : Expanded) (stage : UStage)
    (width index : Nat) (members : Array Nat) :
    let cx := componentContext ex stage members
    let cost := componentDelta cx (cx.phiE (fun _ => false) #[]).1
    TableMeaning cost (family cfg cost members.toList)
      (component cfg ex stage width index members).rows := by
  exact table_meaning cfg _ members.toList

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.pick_minimum [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.greedyOrder_perm [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.chainSet_distinct [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.chainSet_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.chainSet_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.table_minimum [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.component_meaning [propext, Classical.choice, Quot.sound]
