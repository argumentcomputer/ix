import IxSharingVerify.FamilyPrototype

/-! Ascending experimental families and tie-preserving per-count tables.
These are additive contracts for the actual prototype. Slack trimming,
whole-component replacement and knapsack origin are separate obligations. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel

theorem sorted_le (xs : List Nat) : (sorted xs).toList.Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  simpa [sorted] using h

theorem sorted_strict {xs : List Nat} (h : xs.Nodup) :
    (sorted xs).toList.Pairwise (· < ·) := by
  have hn : (sorted xs).toList.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr h
  exact ((sorted_le xs).and hn).imp (by intro a b h; omega)

theorem sorted_eq_of_perm {xs ys : List Nat} (h : xs.Perm ys) : sorted xs = sorted ys := by
  apply Array.toList_inj.mp
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    (sorted_le xs) (sorted_le ys)
  exact (List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm)

theorem sorted_eq_self {set : Array Nat} (h : set.toList.Pairwise (· < ·)) :
    sorted set.toList = set := by
  apply Array.toList_inj.mp
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    (sorted_le _) (h.imp (fun h => Nat.le_of_lt h)) (List.mergeSort_perm _ _)

/-- Every recursive choice remains a set when the undecided and chosen
members together have no duplicates. -/
theorem choices_sorted (members chosen : List Nat) (set : Array Nat)
    (hd : (members ++ chosen).Nodup) (hs : set ∈ choices members chosen) :
    set.toList.Pairwise (· < ·) := by
  induction members generalizing chosen with
  | nil =>
    simp only [choices, List.mem_singleton] at hs
    subst set
    exact sorted_strict (by simpa using hd)
  | cons m rest ih =>
    simp only [choices, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih chosen hd.of_cons hs
    · apply ih (m :: chosen) _ hs
      exact List.perm_middle.nodup_iff.mpr hd

theorem family_sorted (cfg : Config) (cost : Cost) (members : List Nat)
    (hd : members.Nodup) (set : Array Nat) (hs : set ∈ family cfg cost members) :
    set.toList.Pairwise (· < ·) := by
  unfold family at hs
  split at hs
  · exact choices_sorted members [] set (by simpa using hd) hs
  · obtain ⟨k, _, rfl⟩ := (chain_mem cost members set).mp hs
    exact sorted_strict (greedyOrder_nodup cost hd).take

/-- Selecting a predicate gives an explicit branch of the exact family.
The reverse reflects the executable's accumulator; sorting removes it. -/
theorem choices_filter (p : Nat → Bool) (members chosen : List Nat) :
    sorted ((members.filter p).reverse ++ chosen) ∈ choices members chosen := by
  induction members generalizing chosen with
  | nil => simp [choices]
  | cons m rest ih =>
    cases hm : p m
    · simpa [choices, List.filter_cons, hm] using
        (List.mem_append_left (choices rest (m :: chosen)) (ih chosen))
    · simpa [choices, List.filter_cons, hm, List.reverse_cons, List.append_assoc] using
        (List.mem_append_right (choices rest chosen) (ih (m :: chosen)))

/-- Every ascending subset of the component occurs in the exact family. -/
theorem choices_covers {members : List Nat} (hd : members.Nodup) (set : Array Nat)
    (hset : set.toList.Pairwise (· < ·)) (hsub : ∀ x ∈ set.toList, x ∈ members) :
    set ∈ choices members [] := by
  let chosen := members.filter set.contains
  have hn : chosen.Nodup := hd.filter _
  have hsetn : set.toList.Nodup := hset.imp (fun h => Nat.ne_of_lt h)
  have hp : chosen.Perm set.toList := (List.perm_ext_iff_of_nodup hn hsetn).mpr (by
    intro x
    simp only [chosen, List.mem_filter, Array.contains_iff_mem, Array.mem_toList_iff]
    exact ⟨fun h => h.2, fun h => ⟨hsub x (by simpa using h), h⟩⟩)
  have same : sorted chosen.reverse = set :=
    (sorted_eq_of_perm ((List.reverse_perm chosen).trans hp)).trans (sorted_eq_self hset)
  have member := choices_filter set.contains members []
  simp only [List.append_nil] at member
  change sorted chosen.reverse ∈ choices members [] at member
  simpa only [same] using member

theorem family_members (cfg : Config) (cost : Cost) (members : List Nat) (set : Array Nat)
    (hs : set ∈ family cfg cost members) : ∀ x ∈ set.toList, x ∈ members := by
  unfold family at hs
  split at hs
  · intro x hx
    simpa using choices_members members [] set hs x hx
  · obtain ⟨k, _, rfl⟩ := (chain_mem cost members set).mp hs
    exact chainSet_subset cost members k

/-- Under the initial size gate, the declared family is exactly all
ascending subsets, not merely a sound list of some choices. -/
theorem exact_family_iff (cfg : Config) (cost : Cost) {members : List Nat}
    (hd : members.Nodup) (gate : members.length ≤ cfg.experimentK) (set : Array Nat) :
    set ∈ family cfg cost members ↔
      set.toList.Pairwise (· < ·) ∧ ∀ x ∈ set.toList, x ∈ members := by
  constructor
  · intro h
    exact ⟨family_sorted cfg cost members hd set h, family_members cfg cost members set h⟩
  · rintro ⟨hs, hsub⟩
    simpa [family, gate] using choices_covers hd set hs hsub

/-- All legal counts remain inhabited before slack trimming. -/
theorem family_count (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup)
    (k : Nat) (hk : k ≤ members.length) :
    ∃ set, set ∈ family cfg cost members ∧ set.size = k := by
  by_cases gate : members.length ≤ cfg.experimentK
  · refine ⟨sorted (members.take k), (exact_family_iff cfg cost hd gate _).mpr ?_, ?_⟩
    · exact ⟨sorted_strict hd.take, fun x hx => List.mem_of_mem_take ((sorted_mem _ _).mp hx)⟩
    · simp [sorted_size, Nat.min_eq_left hk]
  · refine ⟨chainSet cost members k, ?_, chainSet_size cost members k hk⟩
    simpa [family, gate] using (chain_mem cost members _).mpr ⟨k, hk, rfl⟩

theorem family_empty (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup) :
    #[] ∈ family cfg cost members := by
  by_cases gate : members.length ≤ cfg.experimentK
  · exact (exact_family_iff cfg cost hd gate _).mpr ⟨by simp, by simp⟩
  · have member := (chain_mem cost members (chainSet cost members 0)).mpr ⟨0, by omega, rfl⟩
    simpa [family, gate, chainSet_zero] using member

/-- The full component is present in both branches. This is a component
family endpoint, not a whole-output size witness. -/
theorem family_full (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup) :
    sorted members ∈ family cfg cost members := by
  by_cases gate : members.length ≤ cfg.experimentK
  · exact (exact_family_iff cfg cost hd gate _).mpr
      ⟨sorted_strict hd, fun x hx => (sorted_mem members x).mp hx⟩
  · have hp := greedyOrder_perm cost members
    have same : chainSet cost members members.length = sorted members := by
      unfold chainSet
      rw [← hp.length_eq, List.take_length]
      exact sorted_eq_of_perm hp
    have member := (chain_mem cost members (chainSet cost members members.length)).mpr
      ⟨members.length, Nat.le_refl _, rfl⟩
    simpa [family, gate, same] using member

/-- Fold the existing tie-preserving table operation over ascending sets.
This packages its sortedness, improvement and coverage conclusions. -/
theorem fold_table_ties (cost : Cost) (sets : List (Array Nat))
    (hs : ∀ set ∈ sets, set.toList.Pairwise (· < ·)) (initial : CTable) (hi : SortedT initial) :
    let out := sets.foldl (fun rows set => rows.add (cost set, set)) initial
    SortedT out ∧ ImprovesT initial out ∧
      ∀ set ∈ sets, HasAtT out set.size (cost set) set.toList := by
  induction sets generalizing initial with
  | nil => exact ⟨hi, improvesT_refl _, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons set rest ih =>
    have first := hs set List.mem_cons_self
    have step := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      (initial.add (cost set, set)) (add_sortedT hi first)
    refine ⟨step.1, improvesT_trans (add_improvesT hi first) step.2.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (add_hasAtT hi first).mono step.2.1
    · exact step.2.2 x hx

/-- Actual untrimmed family tables have ascending rows and full tie-aware
per-count coverage. No global-minimum or slack premise is introduced. -/
theorem table_ties (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup) :
    SortedT (table cfg cost members) ∧
      TieCoverage cost (family cfg cost members) (table cfg cost members) := by
  unfold table
  rw [foldFamily_eq]
  have result := fold_table_ties cost (family cfg cost members)
    (family_sorted cfg cost members hd) #[] (by intro k e h; simp at h)
  exact ⟨result.1, result.2.2⟩

theorem table_tie_coverage (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup) :
    TieCoverage cost (family cfg cost members) (table cfg cost members) := (table_ties cfg cost hd).2

/-- A returned row beats every family choice at that count, including ties. -/
theorem table_row_least (cfg : Config) (cost : Cost) {members : List Nat} (hd : members.Nodup)
    {k : Nat} {entry : Entry} (row : (table cfg cost members)[k]! = some entry)
    (set : Array Nat) (member : set ∈ family cfg cost members) (count : set.size = k) :
    TLe entry (cost set, set) := by
  obtain ⟨other, atCount, least⟩ := table_tie_coverage cfg cost hd set member
  rw [count, row] at atCount
  cases Option.some.inj atCount
  exact least

/-- The admitted exact branch ranges over every ascending subset, with
the same least-row order; no global optimizer theorem is weakened. -/
theorem exact_table_row_least (cfg : Config) (cost : Cost) {members : List Nat}
    (hd : members.Nodup) (gate : members.length ≤ cfg.experimentK)
    {k : Nat} {entry : Entry} (row : (table cfg cost members)[k]! = some entry)
    (set : Array Nat) (ascending : set.toList.Pairwise (· < ·))
    (subset : ∀ x ∈ set.toList, x ∈ members) (count : set.size = k) :
    TLe entry (cost set, set) :=
  table_row_least cfg cost hd row set ((exact_family_iff cfg cost hd gate set).mpr ⟨ascending, subset⟩) count

/-- Specialization to the prototype's actual initial component context. -/
theorem component_ties (cfg : Config) (ex : Expanded) (stage : UStage)
    (width index : Nat) (members : Array Nat) (hd : members.toList.Nodup) :
    let cx := componentContext ex stage members
    let cost := componentDelta cx (cx.phiE (fun _ => false) #[]).1
    SortedT (component cfg ex stage width index members).rows ∧
      TieCoverage cost (family cfg cost members.toList)
        (component cfg ex stage width index members).rows := by
  exact table_ties cfg _ hd

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.exact_family_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.family_sorted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.family_count [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.family_full [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.table_tie_coverage [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.exact_table_row_least [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.component_ties [propext, Classical.choice, Quot.sound]
