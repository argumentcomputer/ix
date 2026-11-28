import IxCK.Kernel.Ixon.Reader
import Std.Data.HashMap.Lemmas

/-! # The actual partition of recursor twins

The grouping accumulator retains the reverse of every family's input subsequence. Its
family list has no repetitions and contains exactly the nonempty buckets. Reversing the
buckets at the end therefore retains every payload and its order within its family.
-/

namespace Ix.Kernel.Reader

private abbrev Twin := ConstRef Address × RecEntry
private abbrev GroupState := Std.HashMap Address (List Twin) × List Address

private def twinRows (seen : List Twin) (block : Address) : List Twin :=
  seen.filter fun entry => entry.2.block == block

private def GroupInv (seen : List Twin) (state : GroupState) : Prop :=
  (∀ block, state.1[block]? = match twinRows seen block with
    | [] => none
    | head :: tail => some (head :: tail)) ∧
  state.2.Nodup ∧ ∀ block, block ∈ state.2 ↔ twinRows seen block ≠ []

private theorem GroupInv.getD {seen : List Twin} {state : GroupState}
    (valid : GroupInv seen state) (block : Address) : state.1.getD block [] = twinRows seen block := by
  rw [Std.HashMap.getD_eq_getD_getElem?, valid.1 block]
  cases twinRows seen block <;> rfl

private theorem groupInv_empty : GroupInv [] ({}, []) := by
  simp [GroupInv, twinRows]

private theorem twinGroupStep_inv {seen : List Twin} {state : GroupState}
    (valid : GroupInv seen state) (entry : Twin) :
    GroupInv (entry :: seen) (twinGroupStep state entry) := by
  unfold twinGroupStep
  cases found : state.1[entry.2.block]? with
  | none =>
    have rowsEmpty : twinRows seen entry.2.block = [] := by
      have lookup := valid.getD entry.2.block
      rw [Std.HashMap.getD_eq_getD_getElem?, found] at lookup
      exact lookup.symm
    have fresh : entry.2.block ∉ state.2 := by
      intro present
      exact (valid.2.2 _).mp present rowsEmpty
    refine ⟨?_, List.nodup_cons.mpr ⟨fresh, valid.2.1⟩, ?_⟩
    · intro block
      rw [Std.HashMap.getElem?_insert]
      by_cases same : entry.2.block = block
      · subst block
        have empty : seen.filter (fun other => other.2.block == entry.2.block) = [] := rowsEmpty
        simp [twinRows, empty]
      · have distinct := beq_eq_false_iff_ne.mpr same
        simp only [distinct]
        simpa only [twinRows, List.filter_cons, distinct, Bool.false_eq_true, ↓reduceIte]
          using valid.1 block
    · intro block
      by_cases same : entry.2.block = block
      · subst block
        simp [twinRows]
      · have distinct := beq_eq_false_iff_ne.mpr same
        simpa only [List.mem_cons, Ne.symm same, false_or, twinRows, List.filter_cons,
          distinct, Bool.false_eq_true, ↓reduceIte] using valid.2.2 block
  | some previous =>
    have previousRows : previous = twinRows seen entry.2.block := by
      have lookup := valid.getD entry.2.block
      simpa only [Std.HashMap.getD_eq_getD_getElem?, found, Option.getD_some] using lookup
    have nonempty : twinRows seen entry.2.block ≠ [] := by
      intro empty
      have lookup := valid.1 entry.2.block
      rw [found, empty] at lookup
      cases lookup
    have present := (valid.2.2 _).mpr nonempty
    refine ⟨?_, valid.2.1, ?_⟩
    · intro block
      rw [Std.HashMap.getElem?_insert]
      by_cases same : entry.2.block = block
      · subst block
        simp [twinRows, previousRows]
      · have distinct := beq_eq_false_iff_ne.mpr same
        simp only [distinct]
        simpa only [twinRows, List.filter_cons, distinct, Bool.false_eq_true, ↓reduceIte]
          using valid.1 block
    · intro block
      by_cases same : entry.2.block = block
      · subst block
        simp [present, twinRows]
      · have distinct := beq_eq_false_iff_ne.mpr same
        simpa only [twinRows, List.filter_cons, distinct, Bool.false_eq_true, ↓reduceIte]
          using valid.2.2 block

private theorem twinGroupFold_inv (input : List Twin) {seen : List Twin} {state : GroupState}
    (valid : GroupInv seen state) :
    GroupInv (input.reverse ++ seen) (input.foldl twinGroupStep state) := by
  induction input generalizing seen state with
  | nil => simpa using valid
  | cons entry rest ih =>
    have later := ih (twinGroupStep_inv valid entry)
    simpa only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using later

/-- The output groups are precisely the nonempty family subsequences, each in input order,
listed once per family. -/
theorem groupTwins_families (twins : Array (ConstRef Address × RecEntry)) :
    ∃ blocks : List Address, blocks.Nodup ∧
      (∀ block, block ∈ blocks ↔ (twins.toList.filter fun entry => entry.2.block == block) ≠ []) ∧
      (groupTwins twins).toList = blocks.map fun block =>
        (twins.toList.filter fun entry => entry.2.block == block).toArray := by
  let state := twins.toList.foldl twinGroupStep ({}, [])
  have valid : GroupInv twins.toList.reverse state := by
    simpa only [List.append_nil] using twinGroupFold_inv twins.toList groupInv_empty
  refine ⟨state.2.reverse, (List.reverse_perm state.2).nodup_iff.mpr valid.2.1, ?_, ?_⟩
  · intro block
    rw [List.mem_reverse, valid.2.2 block]
    simp only [twinRows, List.filter_reverse, ne_eq, List.reverse_eq_nil_iff]
  · unfold groupTwins
    rw [← Array.foldl_toList]
    change (state.2.reverse.toArray.map _).toList = _
    rw [Array.toList_map, List.toList_toArray]
    apply List.map_congr_left
    intro block _
    rw [valid.getD block]
    simp only [twinRows, List.filter_reverse, List.reverse_reverse]

/-- Every grouped payload comes from the original twin array. -/
theorem groupTwins_member {twins : Array (ConstRef Address × RecEntry)}
    {family : Array (ConstRef Address × RecEntry)} (group : family ∈ groupTwins twins)
    {entry : ConstRef Address × RecEntry} (member : entry ∈ family) : entry ∈ twins := by
  obtain ⟨blocks, _, _, groups⟩ := groupTwins_families twins
  have present := Array.mem_toList_iff.mpr group
  rw [groups] at present
  obtain ⟨block, _, same⟩ := List.mem_map.mp present
  subst family
  have filtered : entry ∈ twins.toList.filter (fun entry => entry.2.block == block) := by
    simpa only [List.mem_toArray] using member
  exact Array.mem_toList_iff.mp (List.mem_filter.mp filtered).1

/-- Every input payload is retained by a group. -/
theorem groupTwins_coverage {twins : Array (ConstRef Address × RecEntry)}
    {entry : ConstRef Address × RecEntry} (member : entry ∈ twins) :
    ∃ family ∈ groupTwins twins, entry ∈ family := by
  obtain ⟨blocks, _, present, groups⟩ := groupTwins_families twins
  have filtered : entry ∈ twins.toList.filter (fun other => other.2.block == entry.2.block) :=
    List.mem_filter.mpr ⟨Array.mem_toList_iff.mpr member, by simp⟩
  have nonempty : (twins.toList.filter fun other => other.2.block == entry.2.block) ≠ [] := by
    intro empty
    rw [empty] at filtered
    cases filtered
  refine ⟨(twins.toList.filter fun other => other.2.block == entry.2.block).toArray,
    ?_, by simpa only [List.mem_toArray] using filtered⟩
  apply Array.mem_toList_iff.mp
  rw [groups]
  exact List.mem_map.mpr ⟨entry.2.block, (present _).mpr nonempty, rfl⟩

/-- A group contains payloads for one inductive family. -/
theorem groupTwins_homogeneous {twins : Array (ConstRef Address × RecEntry)}
    {family : Array (ConstRef Address × RecEntry)} (group : family ∈ groupTwins twins) :
    ∃ block, ∀ entry ∈ family, entry.2.block = block := by
  obtain ⟨blocks, _, _, groups⟩ := groupTwins_families twins
  have present := Array.mem_toList_iff.mpr group
  rw [groups] at present
  obtain ⟨block, _, same⟩ := List.mem_map.mp present
  subst family
  refine ⟨block, fun entry member => ?_⟩
  have filtered : entry ∈ twins.toList.filter (fun entry => entry.2.block == block) := by
    simpa only [List.mem_toArray] using member
  exact beq_iff_eq.mp (List.mem_filter.mp filtered).2

/-- Every successful old one-family reading is preserved exactly. -/
theorem lowerTwins_of_lowerTwin {md : Mode} {cx : Ctx md}
    {twins : Array (ConstRef Address × RecEntry)} {r : Read md}
    (read : lowerTwin cx twins = .ok r) : lowerTwins cx twins = .ok r := by
  cases first : twins[0]? with
  | none =>
    simpa only [lowerTwin, lowerTwins, first] using read
  | some pair =>
    obtain ⟨ref, entry⟩ := pair
    by_cases sameFamily : twins.all (·.2.block == entry.block) = true
    · simpa only [lowerTwins, first, sameFamily, ↓reduceIte] using read
    · simp [lowerTwin, first, sameFamily, malformed, throw, throwThe, MonadExceptOf.throw,
        bind, Except.bind] at read

end Ix.Kernel.Reader
