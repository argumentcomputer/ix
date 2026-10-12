import Ix.CompileCert.CanonUnivMeaning

/-! Value preservation for the production subsumption pass. The upper bound
follows from removing contributions. The lower bound orders variables before
constants on each path and strictly decreases path length across variable
domination, accounting for chains of removals against the original snapshot.

`normalize_eval` composes this with the actual cached normalization pass and
its proved self-gating invariant, for every input universe and valuation.
Complete linearization remains the final universe-canonicalization obligation. -/

namespace Ix.CompileCert.CanonUnivSubsumption

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning

theorem varsEval_le (ρ : UInt64 → Nat) (vars : List (UInt64 × Nat)) (bound : Nat) :
    varsEval ρ vars ≤ bound ↔ ∀ parameter offset, (parameter, offset) ∈ vars → ρ parameter + offset ≤ bound := by
  induction vars with
  | nil => simp [varsEval]
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    simp only [varsEval, Nat.max_le, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ⟨head, tail⟩ query value (⟨rfl, rfl⟩ | member)
      · exact head
      · exact tail query value member
    · intro holds
      exact ⟨holds parameter offset (Or.inl ⟨rfl, rfl⟩),
        fun query value member => holds query value (Or.inr member)⟩

theorem subsumeVars_le (ρ : UInt64 → Nat) (xs ys : Array (UInt64 × Nat)) :
    varsEval ρ (subsumeVars xs ys).toList ≤ varsEval ρ xs.toList := by
  apply (varsEval_le ρ _ _).mpr
  intro parameter offset member
  exact subsumeVars_go_preserves xs ys 0 0 #[] (fun entry => ρ entry.1 + entry.2 ≤ varsEval ρ xs.toList)
    (fun entry inside => var_le ρ (by simpa using inside)) (by simp)
    (parameter, offset) (Array.mem_toList_iff.mp member)

theorem node_zero_le (ρ : UInt64 → Nat) (node : CNode) :
    nodeEval ρ { node with constant := 0 } ≤ nodeEval ρ node := by
  simp only [nodeEval, Nat.zero_max]
  exact Nat.le_max_right _ _

theorem node_subsume_le (ρ : UInt64 → Nat) (node : CNode) (other : Array (UInt64 × Nat)) :
    nodeEval ρ { node with vars := subsumeVars node.vars other } ≤ nodeEval ρ node := by
  have bound := subsumeVars_le ρ node.vars other
  simp only [nodeEval]
  omega

theorem norm_insert_le (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) (node : CNode)
    (bound : Nat) (prior : normEval ρ norm ≤ bound) (added : pathValue ρ path (nodeEval ρ node) ≤ bound) :
    normEval ρ (norm.insert path node) ≤ bound := by
  apply (entriesEval_le ρ _ _).mpr
  intro query value member
  rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
  · exact Nat.le_trans (normEntry_le ρ norm old) prior
  · cases same; exact added

theorem subsumption_le (ρ : UInt64 → Nat) (norm : CNorm) :
    normEval ρ (subsumption norm) ≤ normEval ρ norm := by
  unfold subsumption
  apply listLoop_preserves (fun current => normEval ρ current ≤ normEval ρ norm)
  · exact Nat.le_refl _
  · intro entry member current valid
    rcases entry with ⟨path, node⟩
    change normEval ρ (current.insert path _) ≤ normEval ρ norm
    apply norm_insert_le ρ current path _ _ valid
    apply Nat.le_trans (pathValue_mono ρ path ?_) (normEntry_le ρ norm member)
    apply listLoop_preserves (fun currentNode => nodeEval ρ currentNode ≤ nodeEval ρ node)
    · exact Nat.le_refl _
    · intro entry _ currentNode bound
      rcases entry with ⟨otherPath, otherNode⟩
      with_reducible repeat' first
        | apply StepHolds.choose
        | dsimp only
      all_goals
        dsimp only [pure, StepHolds]
        first
          | exact bound
          | exact Nat.le_trans (node_zero_le ρ currentNode) bound
          | exact Nat.le_trans (node_subsume_le ρ currentNode otherNode.vars) bound
          | exact Nat.le_trans (node_subsume_le ρ { currentNode with constant := 0 } otherNode.vars)
              (Nat.le_trans (node_zero_le ρ currentNode) bound)

theorem isSubset_sublist (left right : CPath) (checked : isSubset left right = true) :
    List.Sublist left right := by
  induction right generalizing left with
  | nil => cases left <;> simp_all [isSubset]
  | cons head rest ih =>
    cases left with
    | nil => exact List.nil_sublist _
    | cons first tail =>
      simp only [isSubset] at checked
      split at checked
      · exact List.Sublist.cons head (ih _ checked)
      · split at checked
        · rename_i same
          have same : head = first := beq_iff_eq.mp same
          subst head
          exact List.Sublist.cons_cons first (ih _ checked)
        · cases checked

theorem isSubset_active (ρ : UInt64 → Nat) {left right : CPath}
    (checked : isSubset left right = true) (enabled : active ρ right = true) : active ρ left = true := by
  simp only [active, List.all_eq_true, decide_eq_true_eq] at enabled ⊢
  intro parameter member
  exact enabled parameter ((isSubset_sublist left right checked).subset member)

theorem insert_findD_property (Q : CNode → Prop) (norm : CNorm) (path : CPath) (node : CNode)
    (query : CPath) (prior : Q (norm.findD query {})) (updated : path = query → Q node) :
    Q ((norm.insert path node).findD query {}) := by
  unfold RBTree.RBMap.findD
  rw [RBTree.RBMap.find?_insert]
  split
  · rename_i same
    have same : query = path := Std.LawfulEqCmp.eq_of_compare same
    exact updated same.symm
  · exact prior

theorem step_if {P : α → Prop} {condition : Prop} [Decidable condition]
    {left right : ForInStep α} (yes : condition → StepHolds P left) (no : ¬condition → StepHolds P right) :
    StepHolds P (if condition then left else right) := by
  split
  · exact yes (by assumption)
  · exact no (by assumption)

theorem subsumeVars_go_keepsResult (xs ys : Array (UInt64 × Nat)) (xi yi : Nat)
    (result : Array (UInt64 × Nat)) :
    ∀ value ∈ result, value ∈ subsumeVars.go xs ys xi yi result := by
  rw [subsumeVars.go]
  split
  · split
    · intro value member; exact Array.mem_append_left _ member
    · dsimp only
      split
      · intro value member
        exact subsumeVars_go_keepsResult xs ys (xi + 1) yi _ value (Array.mem_push_of_mem _ member)
      · split
        · split
          · intro value member
            exact subsumeVars_go_keepsResult xs ys (xi + 1) (yi + 1) _ value (Array.mem_push_of_mem _ member)
          · exact subsumeVars_go_keepsResult xs ys (xi + 1) (yi + 1) result
        · exact subsumeVars_go_keepsResult xs ys xi (yi + 1) result
  · intros; assumption
termination_by (xs.size - xi) + (ys.size - yi)
decreasing_by all_goals omega

/-- Any source atom above the entire dominator table's value survives the
actual merge walk. This does not assume that either array is sorted. -/
theorem subsumeVars_go_keepsBig (ρ : UInt64 → Nat) (xs ys : Array (UInt64 × Nat))
    (xi yi : Nat) (result : Array (UInt64 × Nat)) (bound : Nat)
    (dominators : varsEval ρ ys.toList ≤ bound) (index : Nat) (inSource : index < xs.size)
    (pending : xi ≤ index) (large : bound < ρ xs[index].1 + xs[index].2) :
    xs[index] ∈ subsumeVars.go xs ys xi yi result := by
  rw [subsumeVars.go]
  split
  · rename_i atSource
    split
    · apply Array.mem_append_right
      apply Array.mem_extract_iff_getElem.mpr
      refine ⟨index - xi, by omega, ?_⟩
      congr 1
      omega
    · rename_i atOther
      have atOther : yi < ys.size := by omega
      dsimp only
      split
      · by_cases same : index = xi
        · subst index
          have member := subsumeVars_go_keepsResult xs ys (xi + 1) yi (result.push xs[xi]!)
            xs[xi]! Array.mem_push_self
          simpa only [getElem!_pos xs xi atSource] using member
        · exact subsumeVars_go_keepsBig ρ xs ys (xi + 1) yi _ bound dominators index inSource (by omega) large
      · split
        · rename_i sameParameter
          split
          · by_cases same : index = xi
            · subst index
              have member := subsumeVars_go_keepsResult xs ys (xi + 1) (yi + 1) (result.push xs[xi]!)
                xs[xi]! Array.mem_push_self
              simpa only [getElem!_pos xs xi atSource] using member
            · exact subsumeVars_go_keepsBig ρ xs ys (xi + 1) (yi + 1) _ bound dominators index inSource (by omega) large
          · rename_i dominated
            by_cases same : index = xi
            · subst index
              have otherBound := Nat.le_trans (var_le ρ (vars := ys.toList)
                (parameter := ys[yi].1) (offset := ys[yi].2)
                (Array.mem_toList_iff.mpr (Array.getElem_mem atOther))) dominators
              have names : xs[xi].1 = ys[yi].1 := by
                simpa only [getElem!_pos xs xi atSource, getElem!_pos ys yi atOther, beq_iff_eq] using sameParameter
              simp only [getElem!_pos xs xi atSource, getElem!_pos ys yi atOther, names] at dominated large
              omega
            · exact subsumeVars_go_keepsBig ρ xs ys (xi + 1) (yi + 1) result bound dominators index inSource (by omega) large
        · exact subsumeVars_go_keepsBig ρ xs ys xi (yi + 1) result bound dominators index inSource pending large
  · omega
termination_by (xs.size - xi) + (ys.size - yi)
decreasing_by all_goals omega

theorem subsumeVars_keepsBig (ρ : UInt64 → Nat) (xs ys : Array (UInt64 × Nat))
    (bound : Nat) (dominators : varsEval ρ ys.toList ≤ bound)
    (parameter : UInt64) (offset : Nat) (member : (parameter, offset) ∈ xs.toList)
    (large : bound < ρ parameter + offset) : (parameter, offset) ∈ (subsumeVars xs ys).toList := by
  obtain ⟨index, inside, same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  have retained := subsumeVars_go_keepsBig ρ xs ys 0 0 #[] bound dominators index inside
    (Nat.zero_le _) (by simpa only [same] using large)
  exact Array.mem_toList_iff.mpr (by simpa only [Ixon.CanonUniv.subsumeVars, same] using retained)

theorem subsumption_keeps_var (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) (node : CNode)
    (member : (path, node) ∈ norm.toList) (enabled : active ρ path = true)
    (parameter : UInt64) (offset : Nat) (occurs : (parameter, offset) ∈ node.vars.toList)
    (bound : Nat) (large : bound < ρ parameter + offset)
    (smaller : ∀ otherPath otherNode, (otherPath, otherNode) ∈ norm.toList →
      otherPath.length < path.length → active ρ otherPath = true →
      varsEval ρ otherNode.vars.toList ≤ bound) :
    (parameter, offset) ∈ ((subsumption norm).findD path {}).vars.toList := by
  unfold subsumption
  apply listLoop_preserves (fun current : CNorm => (parameter, offset) ∈ (current.findD path {}).vars.toList)
  · simpa only [findD_of_member norm member] using occurs
  · intro entry entryMember current valid
    rcases entry with ⟨query, source⟩
    change (parameter, offset) ∈ ((current.insert query _).findD path {}).vars.toList
    apply insert_findD_property (fun value => (parameter, offset) ∈ value.vars.toList) current query _ path valid
    intro same
    subst query
    have sameNode : source = node :=
      (findD_of_member norm entryMember).symm.trans (findD_of_member norm member)
    subst source
    apply listLoop_preserves (fun value : CNode => (parameter, offset) ∈ value.vars.toList)
    · exact occurs
    · intro entry otherMember currentNode kept
      rcases entry with ⟨otherPath, otherNode⟩
      dsimp only
      apply step_if
      · intro subset
        have filterKeeps (candidate : CNode) (present : (parameter, offset) ∈ candidate.vars.toList) :
            StepHolds (fun value : CNode => (parameter, offset) ∈ value.vars.toList)
              (if (!(path.length == otherPath.length) && !otherNode.vars.isEmpty) then
                (pure (.yield { candidate with vars := subsumeVars candidate.vars otherNode.vars }) : Id (ForInStep CNode))
              else (pure (.yield candidate) : Id (ForInStep CNode))) := by
          apply step_if
          · intro removed
            have different : path.length ≠ otherPath.length := by
              have component := (Bool.and_eq_true_iff.mp removed).1
              simpa using component
            have shorter : otherPath.length < path.length := by
              have lengthBound := (isSubset_sublist otherPath path subset).length_le
              omega
            dsimp only [pure, StepHolds]
            exact subsumeVars_keepsBig ρ candidate.vars otherNode.vars bound
              (smaller otherPath otherNode otherMember shorter (isSubset_active ρ subset enabled))
              parameter offset present large
          · intro _
            exact present
        with_reducible repeat' first
          | exact filterKeeps currentNode kept
          | exact filterKeeps { currentNode with constant := 0 } kept
          | apply StepHolds.choose
      · intro _
        exact kept

theorem offsetFold_le (vars : List (UInt64 × Nat)) (bound initial : Nat)
    (start : initial + 1 ≤ bound) (entries : ∀ value ∈ vars, value.2 + 1 ≤ bound) :
    vars.foldl (fun current value => max current value.2) initial + 1 ≤ bound := by
  induction vars generalizing initial with
  | nil => exact start
  | cons value rest ih =>
    rw [List.foldl_cons]
    have first := entries value (by simp)
    exact ih _ (by omega) (fun value member => entries value (by simp [member]))

theorem nodeOffset_le (ρ : UInt64 → Nat) (path : CPath) (node : CNode) (bound : Nat)
    (fits : NodeFits path node) (enabled : active ρ path = true)
    (variables : varsEval ρ node.vars.toList ≤ bound) (positive : 1 ≤ bound) :
    node.vars.foldl (fun current value => max current value.2) 0 + 1 ≤ bound := by
  rw [← Array.foldl_toList]
  apply offsetFold_le _ bound 0 positive
  intro value member
  have nonzero := active_member_pos ρ enabled (fits value.1 value.2 member)
  have valueBound := (varsEval_le ρ node.vars.toList bound).mp variables value.1 value.2 member
  omega

/-- The exact constant-retention Boolean cannot remove a constant above the
bound when all lower-ranked contributors already satisfy that bound. -/
theorem keepConst_true (ρ : UInt64 → Nat) (path otherPath : CPath) (node otherNode : CNode)
    (bound : Nat) (large : bound < node.constant) (fits : NodeFits path node)
    (otherFits : NodeFits otherPath otherNode) (enabled : active ρ path = true)
    (subset : isSubset otherPath path = true) (variables : varsEval ρ node.vars.toList ≤ bound)
    (otherVariables : varsEval ρ otherNode.vars.toList ≤ bound)
    (smallerConstant : otherPath.length < path.length → otherNode.constant ≤ bound) :
    ((path.length == otherPath.length || decide (node.constant > otherNode.constant)) &&
      (otherNode.vars.isEmpty || decide (node.constant > node.vars.foldl (fun current value => max current value.2) 0 + 1))) = true := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · by_cases same : path.length = otherPath.length
    · exact Or.inl (by simpa using same)
    · right
      have lengthBound := (isSubset_sublist otherPath path subset).length_le
      have below := smallerConstant (by omega)
      omega
  · by_cases empty : otherNode.vars.isEmpty = true
    · exact Or.inl empty
    · right
      have nonempty : otherNode.vars.isEmpty = false := Bool.eq_false_iff.mpr empty
      obtain ⟨value, member⟩ := Array.isEmpty_eq_false_iff_exists_mem.mp nonempty
      have positiveValue := active_member_pos ρ (isSubset_active ρ subset enabled)
        (otherFits value.1 value.2 (Array.mem_toList_iff.mpr member))
      have valueBound := (varsEval_le ρ otherNode.vars.toList bound).mp otherVariables
        value.1 value.2 (Array.mem_toList_iff.mpr member)
      have positive : 1 ≤ bound := by omega
      have offsetBound := nodeOffset_le ρ path node bound fits enabled variables positive
      omega

theorem subsumption_keeps_const (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm)
    (path : CPath) (node : CNode) (member : (path, node) ∈ norm.toList)
    (enabled : active ρ path = true) (bound : Nat) (large : bound < node.constant)
    (smallerVars : ∀ otherPath otherNode, (otherPath, otherNode) ∈ norm.toList →
      otherPath.length ≤ path.length → active ρ otherPath = true → varsEval ρ otherNode.vars.toList ≤ bound)
    (smallerConstants : ∀ otherPath otherNode, (otherPath, otherNode) ∈ norm.toList →
      otherPath.length < path.length → active ρ otherPath = true → otherNode.constant ≤ bound) :
    ((subsumption norm).findD path {}).constant = node.constant ∧
      NodeFits path ((subsumption norm).findD path {}) ∧
      varsEval ρ ((subsumption norm).findD path {}).vars.toList ≤ bound := by
  let P : CNode → Prop := fun value => value.constant = node.constant ∧ NodeFits path value ∧
    varsEval ρ value.vars.toList ≤ bound
  have initial : P node := ⟨rfl, wellFormed path node member,
    smallerVars path node member (Nat.le_refl _) enabled⟩
  change P ((subsumption norm).findD path {})
  unfold subsumption
  apply listLoop_preserves (fun current : CNorm => P (current.findD path {}))
  · simpa only [findD_of_member norm member] using initial
  · intro entry entryMember current valid
    rcases entry with ⟨query, source⟩
    change P ((current.insert query _).findD path {})
    apply insert_findD_property P current query _ path valid
    intro same
    subst query
    have sameNode : source = node :=
      (findD_of_member norm entryMember).symm.trans (findD_of_member norm member)
    subst source
    apply listLoop_preserves P
    · exact initial
    · intro entry otherMember currentNode currentGood
      rcases entry with ⟨otherPath, otherNode⟩
      dsimp only
      apply step_if
      · intro subset
        have otherActive := isSubset_active ρ subset enabled
        have lengthBound := (isSubset_sublist otherPath path subset).length_le
        have kept := keepConst_true ρ path otherPath currentNode otherNode bound
          (by simpa only [currentGood.1] using large) currentGood.2.1
          (wellFormed otherPath otherNode otherMember) enabled subset currentGood.2.2
          (smallerVars otherPath otherNode otherMember lengthBound otherActive)
          (fun shorter => smallerConstants otherPath otherNode otherMember shorter otherActive)
        rw [kept]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        with_reducible repeat' first
          | apply StepHolds.choose
          | dsimp only
        all_goals
          dsimp only [pure, StepHolds]
          first
            | exact currentGood
            | exact ⟨currentGood.1, currentGood.2.1.subsumeVars otherNode.vars,
                Nat.le_trans (subsumeVars_le ρ currentNode.vars otherNode.vars) currentGood.2.2⟩
      · intro _
        exact currentGood

/-- Variables rank before constants at the same path; a strict sub-path has
smaller rank for either kind of contribution. -/
def AtRank (ρ : UInt64 → Nat) (norm : CNorm) (bound rank : Nat) : Prop :=
  (∀ path node, (path, node) ∈ norm.toList → 2 * path.length = rank →
    ∀ parameter offset, (parameter, offset) ∈ node.vars.toList →
      pathValue ρ path (ρ parameter + offset) ≤ bound) ∧
  (∀ path node, (path, node) ∈ norm.toList → 2 * path.length + 1 = rank →
    pathValue ρ path node.constant ≤ bound)

theorem subsumption_ge (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm) :
    normEval ρ norm ≤ normEval ρ (subsumption norm) := by
  let bound := normEval ρ (subsumption norm)
  have everyRank : ∀ rank, AtRank ρ norm bound rank := by
    intro rank
    induction rank using (measure (fun rank : Nat => rank)).wf.induction with
    | h rank ih =>
      constructor
      · intro path node member rankEq parameter offset occurs
        by_cases enabled : active ρ path = true
        · simp only [pathValue, enabled, ↓reduceIte]
          by_cases small : ρ parameter + offset ≤ bound
          · exact small
          · have large : bound < ρ parameter + offset := by omega
            have retained := subsumption_keeps_var ρ norm path node member enabled parameter offset occurs bound large
              (fun otherPath otherNode otherMember shorter otherActive => by
                apply (varsEval_le ρ otherNode.vars.toList bound).mpr
                intro otherParameter increment inside
                have checked := (ih (2 * otherPath.length) (by change 2 * otherPath.length < rank; omega)).1
                  otherPath otherNode otherMember rfl otherParameter increment inside
                simpa only [pathValue, otherActive, ↓reduceIte] using checked)
            have atomBound := Nat.le_trans (var_le ρ retained)
              (Nat.le_max_right ((subsumption norm).findD path {}).constant _)
            change ρ parameter + offset ≤ nodeEval ρ ((subsumption norm).findD path {}) at atomBound
            have nodeBound := findD_value_le ρ (subsumption norm) path
            simp only [pathValue, enabled, ↓reduceIte] at nodeBound
            change nodeEval ρ ((subsumption norm).findD path {}) ≤ bound at nodeBound
            omega
        · simp [pathValue, enabled]
      · intro path node member rankEq
        by_cases enabled : active ρ path = true
        · simp only [pathValue, enabled, ↓reduceIte]
          by_cases small : node.constant ≤ bound
          · exact small
          · have large : bound < node.constant := by omega
            have retained := subsumption_keeps_const ρ norm wellFormed path node member enabled bound large
              (fun otherPath otherNode otherMember shorter otherActive => by
                apply (varsEval_le ρ otherNode.vars.toList bound).mpr
                intro otherParameter increment inside
                have checked := (ih (2 * otherPath.length) (by change 2 * otherPath.length < rank; omega)).1
                  otherPath otherNode otherMember rfl otherParameter increment inside
                simpa only [pathValue, otherActive, ↓reduceIte] using checked)
              (fun otherPath otherNode otherMember shorter otherActive => by
                have checked := (ih (2 * otherPath.length + 1) (by change 2 * otherPath.length + 1 < rank; omega)).2
                  otherPath otherNode otherMember rfl
                simpa only [pathValue, otherActive, ↓reduceIte] using checked)
            have constantBound : node.constant ≤ nodeEval ρ ((subsumption norm).findD path {}) := by
              rw [← retained.1]
              exact Nat.le_max_left _ _
            have nodeBound := findD_value_le ρ (subsumption norm) path
            simp only [pathValue, enabled, ↓reduceIte] at nodeBound
            change nodeEval ρ ((subsumption norm).findD path {}) ≤ bound at nodeBound
            omega
        · simp [pathValue, enabled]
  apply (entriesEval_le ρ norm.toList bound).mpr
  intro path node member
  by_cases enabled : active ρ path = true
  · have constantBound := (everyRank (2 * path.length + 1)).2 path node member rfl
    have variablesBound : varsEval ρ node.vars.toList ≤ bound := by
      apply (varsEval_le ρ node.vars.toList bound).mpr
      intro parameter offset occurs
      have checked := (everyRank (2 * path.length)).1 path node member rfl parameter offset occurs
      simpa only [pathValue, enabled, ↓reduceIte] using checked
    simp only [pathValue, enabled, ↓reduceIte] at constantBound ⊢
    exact Nat.max_le.mpr ⟨constantBound, variablesBound⟩
  · simp [pathValue, enabled]

/-- Actual subsumption preserves all valuations. Its only representation
premise is supplied by the actual normalization pass. -/
theorem subsumption_eval (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm) :
    normEval ρ (subsumption norm) = normEval ρ norm :=
  Nat.le_antisymm (subsumption_le ρ norm) (subsumption_ge ρ norm wellFormed)

/-- The complete production `normalize`, with memoization and subsumption,
has the input's value for every universe and every valuation. -/
theorem normalize_eval (ρ : UInt64 → Nat) (level : Univ) :
    normEval ρ (normalize level) = univEval ρ level := by
  unfold normalize
  rw [subsumption_eval ρ _ (normalizeAux_initial_selfGated level)]
  exact normalizeAux_initial_eval ρ level

end Ix.CompileCert.CanonUnivSubsumption

