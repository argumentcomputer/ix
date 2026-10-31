import Ix.CompileCert.CanonUnivGateOrder

/-! Value preservation for the complete production universe canonicalizer.
The phase definitions are proved equal to the producer. Grouping preserves
the input value, every consumed marker has a larger target group with the
required gate prefix, and induction over those contexts establishes complete
emission coverage. Root-constant absorption and the upper bound are included.

`canonUniv_eval` has no external invariant or successful-check premise. These
proofs install no runtime substitutions. -/

namespace Ix.CompileCert.CanonUnivEmit

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning
open Ix.CompileCert.CanonUnivPaths Ix.CompileCert.CanonUnivGateOrder

abbrev Groups := RBTree.RBMap CPath CGroup compare
abbrev Markers := List (CPath × UInt64)

namespace MapValue

def listMax (weight : α → Nat) : List α → Nat
  | [] => 0
  | value :: rest => max (weight value) (listMax weight rest)

theorem listMax_le (weight : α → Nat) (items : List α) (bound : Nat) :
    listMax weight items ≤ bound ↔ ∀ item ∈ items, weight item ≤ bound := by
  induction items with
  | nil => simp [listMax]
  | cons head rest ih => simp [listMax, Nat.max_le, ih]

theorem member_le (weight : α → Nat) {items : List α} {item : α} (member : item ∈ items) :
    weight item ≤ listMax weight items := (listMax_le weight items _).mp (Nat.le_refl _) item member

variable {κ : Type u} {α : Type v} {cmp : κ → κ → Ordering}

def eval (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) : Nat :=
  listMax (fun entry => weight entry.1 entry.2) table.toList

def lookup (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) (key : κ) : Nat :=
  ((table.find? key).map (weight key)).getD 0

theorem entry_le (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) {key value}
    (member : (key, value) ∈ table.toList) : weight key value ≤ eval weight table :=
  member_le (fun entry : κ × α => weight entry.1 entry.2) member

theorem eval_le (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) (bound : Nat)
    (holds : ∀ key value, (key, value) ∈ table.toList → weight key value ≤ bound) : eval weight table ≤ bound :=
  (listMax_le _ table.toList bound).mpr (fun entry member => holds entry.1 entry.2 member)

variable [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

theorem lookup_of_member (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) {key value}
    (member : (key, value) ∈ table.toList) : lookup weight table key = weight key value := by
  have found : table.find? key = some value := RBTree.RBMap.find?_some.mpr ⟨key, member, Std.ReflCmp.compare_self⟩
  simp [lookup, found]

theorem lookup_le (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp) (key : κ) :
    lookup weight table key ≤ eval weight table := by
  cases found : table.find? key with
  | none => simp [lookup, found]
  | some value =>
    obtain ⟨other, member, same⟩ := RBTree.RBMap.find?_some.mp found
    have same : key = other := Std.LawfulEqCmp.eq_of_compare same
    subst other
    simpa [lookup, found] using entry_le weight table member

/-- A max-merge at one key contributes exactly its new value to the map's
maximum; missing keys contribute zero through the actual optional lookup. -/
theorem insert_merge (weight : κ → α → Nat) (table : RBTree.RBMap κ α cmp)
    (key : κ) (value : α) (contribution : Nat)
    (merged : weight key value = max (lookup weight table key) contribution) :
    eval weight (table.insert key value) = max (eval weight table) contribution := by
  have added := entry_le weight (table.insert key value) (RBTree.RBMap.mem_toList_insert_self value table)
  rw [merged] at added
  apply Nat.le_antisymm
  · apply eval_le
    intro query item member
    rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
    · exact Nat.le_trans (entry_le weight table old) (Nat.le_max_left _ _)
    · cases same
      rw [merged]
      have before := lookup_le weight table key
      omega
  · apply Nat.max_le.mpr
    refine ⟨?_, Nat.le_trans (Nat.le_max_right _ _) added⟩
    apply eval_le
    intro query item member
    rcases RBTree.RBMap.mem_toList_insert_of_mem value member with retained | same
    · exact entry_le weight (table.insert key value) retained
    · have same : key = query := Std.LawfulEqCmp.eq_of_compare same
      subst query
      rw [← lookup_of_member weight table member]
      exact Nat.le_trans (Nat.le_max_left _ _) added

end MapValue

def atomsEval (ρ : UInt64 → Nat) (atoms : RBTree.RBMap UInt64 Nat compare) : Nat :=
  MapValue.eval (fun parameter offset => ρ parameter + offset) atoms

def groupValue (ρ : UInt64 → Nat) (group : CGroup) : Nat := max group.constant (atomsEval ρ group.atoms)

def groupEval (ρ : UInt64 → Nat) (path : CPath) (group : CGroup) : Nat := pathValue ρ path (groupValue ρ group)

def groupsEval (ρ : UInt64 → Nat) (groups : Groups) : Nat := MapValue.eval (groupEval ρ) groups

theorem atoms_insert_eval (ρ : UInt64 → Nat) (atoms : RBTree.RBMap UInt64 Nat compare)
    (parameter : UInt64) (offset : Nat) :
    atomsEval ρ (atoms.insert parameter (max (atoms.findD parameter 0) offset)) =
      max (atomsEval ρ atoms) (ρ parameter + offset) := by
  apply MapValue.insert_merge
  cases found : atoms.find? parameter with
  | none => simp [RBTree.RBMap.findD, MapValue.lookup, found]
  | some prior =>
    simp only [RBTree.RBMap.findD, MapValue.lookup, found, Option.map_some, Option.getD_some]
    omega

theorem group_lookup (ρ : UInt64 → Nat) (groups : Groups) (path : CPath) :
    MapValue.lookup (groupEval ρ) groups path = groupEval ρ path (groups.findD path {}) := by
  cases found : groups.find? path with
  | none => simp [MapValue.lookup, RBTree.RBMap.findD, found, groupEval, groupValue,
      atomsEval, MapValue.eval, MapValue.listMax, pathValue]
  | some group => simp [MapValue.lookup, RBTree.RBMap.findD, found]

theorem groups_insert_const_eval (ρ : UInt64 → Nat) (groups : Groups) (path : CPath) (value : Nat) :
    groupsEval ρ (groups.insert path { groups.findD path {} with
      constant := max (groups.findD path {}).constant value }) =
      max (groupsEval ρ groups) (pathValue ρ path value) := by
  apply MapValue.insert_merge
  rw [group_lookup]
  unfold groupEval groupValue pathValue
  dsimp only
  split <;> omega

theorem groups_insert_atom_eval (ρ : UInt64 → Nat) (groups : Groups) (path : CPath)
    (parameter : UInt64) (offset : Nat) :
    groupsEval ρ (groups.insert path { groups.findD path {} with
      atoms := (groups.findD path {}).atoms.insert parameter (max ((groups.findD path {}).atoms.findD parameter 0) offset) }) =
      max (groupsEval ρ groups) (pathValue ρ path (ρ parameter + offset)) := by
  apply MapValue.insert_merge
  rw [group_lookup]
  unfold groupEval groupValue
  rw [atoms_insert_eval]
  unfold pathValue
  dsimp only
  split <;> omega

def atomHome (norm : CNorm) (path : CPath) (parameter : UInt64) (offset : Nat) : CPath :=
  let context := path.filter (· != parameter)
  if covered norm offset context && gatesLeakFree norm context then context else path

def groupAtoms (norm : CNorm) (path : CPath) (vars : Array (UInt64 × Nat)) (initial : Groups) : Groups := Id.run do
  let mut groups := initial
  for (parameter, offset) in vars do
    let targetPath := atomHome norm path parameter offset
    let group := groups.findD targetPath {}
    let slot := max (group.atoms.findD parameter 0) offset
    groups := groups.insert targetPath { group with atoms := group.atoms.insert parameter slot }
  return groups

theorem arrayLoop_preserves (P : β → Prop) (items : Array α) (initial : β)
    (body : α → β → Id (ForInStep β)) (start : P initial)
    (step : ∀ item ∈ items, ∀ state, P state → StepHolds P (body item state)) :
    P (forIn items initial body : Id β) := by
  rw [← Array.forIn_toList]
  exact listLoop_preserves P items.toList initial body start
    (fun item member state valid => step item (Array.mem_toList_iff.mp member) state valid)

theorem listLoop_covers (value : β → Nat) (weight : α → Nat) (items : List α) (initial : β)
    (body : α → β → Id (ForInStep β))
    (step : ∀ item ∈ items, ∀ before, ∃ after, body item before = .yield after ∧
      value before ≤ value after ∧ weight item ≤ value after) :
    max (value initial) (MapValue.listMax weight items) ≤ value (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => simp [MapValue.listMax, pure]
  | cons item rest ih =>
    obtain ⟨after, ran, growth, covered⟩ := step item (by simp) initial
    have later := ih after (fun item member before => step item (List.mem_cons_of_mem _ member) before)
    have initialBound := Nat.le_trans growth (Nat.le_trans (Nat.le_max_left _ _) later)
    have itemBound := Nat.le_trans covered (Nat.le_trans (Nat.le_max_left _ _) later)
    have restBound := Nat.le_trans (Nat.le_max_right _ _) later
    have bound : max (value initial) (max (weight item) (MapValue.listMax weight rest)) ≤
        value (forIn rest after body : Id β) := by omega
    simpa [List.forIn_cons, ran, pure, bind, MapValue.listMax] using bound

theorem arrayLoop_covers (value : β → Nat) (weight : α → Nat) (items : Array α) (initial : β)
    (body : α → β → Id (ForInStep β))
    (step : ∀ item ∈ items, ∀ before, ∃ after, body item before = .yield after ∧
      value before ≤ value after ∧ weight item ≤ value after) :
    max (value initial) (MapValue.listMax weight items.toList) ≤ value (forIn items initial body : Id β) := by
  rw [← Array.forIn_toList]
  exact listLoop_covers value weight items.toList initial body
    (fun item member before => step item (Array.mem_toList_iff.mp member) before)

theorem pathValue_filter_le (ρ : UInt64 → Nat) (path : CPath) (keep : UInt64 → Bool) (value : Nat) :
    pathValue ρ path value ≤ pathValue ρ (path.filter keep) value := by
  by_cases enabled : active ρ path = true
  · have afterEnabled : active ρ (path.filter keep) = true := by
      apply List.all_eq_true.mpr
      intro parameter member
      exact decide_eq_true (active_member_pos ρ enabled (List.mem_filter.mp member).1)
    simp [pathValue, enabled, afterEnabled]
  · simp [pathValue, enabled]

theorem atomHome_ge (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) (parameter : UInt64)
    (offset : Nat) (value : Nat) : pathValue ρ path value ≤ pathValue ρ (atomHome norm path parameter offset) value := by
  unfold atomHome
  dsimp only
  split
  · exact pathValue_filter_le ρ path _ value
  · exact Nat.le_refl _

theorem weighted_vars (ρ : UInt64 → Nat) (path : CPath) (vars : List (UInt64 × Nat)) :
    MapValue.listMax (fun entry => pathValue ρ path (ρ entry.1 + entry.2)) vars =
      pathValue ρ path (varsEval ρ vars) := by
  induction vars with
  | nil => simp [MapValue.listMax, varsEval, pathValue]
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    simp only [MapValue.listMax, varsEval, ih, pathValue_max]

theorem groupAtoms_covers (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath)
    (vars : Array (UInt64 × Nat)) (initial : Groups) :
    max (groupsEval ρ initial) (pathValue ρ path (varsEval ρ vars.toList)) ≤
      groupsEval ρ (groupAtoms norm path vars initial) := by
  rw [← weighted_vars]
  unfold groupAtoms
  apply arrayLoop_covers
  intro entry _ before
  rcases entry with ⟨parameter, offset⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [groups_insert_atom_eval]
    exact Nat.le_max_left _ _
  · rw [groups_insert_atom_eval]
    exact Nat.le_trans (atomHome_ge ρ norm path parameter offset _) (Nat.le_max_right _ _)

theorem original_atom_le (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) (node : CNode)
    (member : (path, node) ∈ norm.toList) (parameter : UInt64) (offset : Nat)
    (occurs : (parameter, offset) ∈ node.vars.toList) :
    pathValue ρ path (ρ parameter + offset) ≤ normEval ρ norm := by
  have atom : ρ parameter + offset ≤ nodeEval ρ node :=
    Nat.le_trans (var_le ρ occurs) (Nat.le_max_right node.constant _)
  exact Nat.le_trans (pathValue_mono ρ path atom) (normEntry_le ρ norm member)

theorem home_atom_le (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm)
    (path : CPath) (node : CNode) (member : (path, node) ∈ norm.toList)
    (parameter : UInt64) (offset : Nat) (occurs : (parameter, offset) ∈ node.vars.toList) :
    pathValue ρ (atomHome norm path parameter offset) (ρ parameter + offset) ≤ normEval ρ norm := by
  unfold atomHome
  dsimp only
  split
  · rename_i accepted
    exact stripped_atom_le ρ norm wellFormed path node member parameter offset occurs
      (Bool.and_eq_true_iff.mp accepted).1
  · exact original_atom_le ρ norm path node member parameter offset occurs

theorem groupAtoms_le (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath)
    (vars : Array (UInt64 × Nat)) (initial : Groups) (bound : Nat)
    (start : groupsEval ρ initial ≤ bound)
    (atoms : ∀ parameter offset, (parameter, offset) ∈ vars.toList →
      pathValue ρ (atomHome norm path parameter offset) (ρ parameter + offset) ≤ bound) :
    groupsEval ρ (groupAtoms norm path vars initial) ≤ bound := by
  unfold groupAtoms
  apply arrayLoop_preserves (fun groups => groupsEval ρ groups ≤ bound)
  · exact start
  · intro entry member groups valid
    rcases entry with ⟨parameter, offset⟩
    change groupsEval ρ (groups.insert (atomHome norm path parameter offset) _) ≤ bound
    rw [groups_insert_atom_eval]
    exact Nat.max_le.mpr ⟨valid, atoms parameter offset (Array.mem_toList_iff.mpr member)⟩

def buildGroups (norm : CNorm) : Groups := Id.run do
  let mut groups : Groups := .empty
  for (path, node) in norm.toList do
    if !path.isEmpty && node.constant > 0 then
      let g := groups.findD path {}
      groups := groups.insert path { g with constant := max g.constant node.constant }
    for (i, k) in node.vars do
      let ctx := path.filter (· != i)
      let targetPath := if covered norm k ctx && gatesLeakFree norm ctx then ctx else path
      let g := groups.findD targetPath {}
      let slot := max (g.atoms.findD i 0) k
      groups := groups.insert targetPath { g with atoms := g.atoms.insert i slot }
  return groups

theorem buildGroups_le (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm) :
    groupsEval ρ (buildGroups norm) ≤ normEval ρ norm := by
  unfold buildGroups
  apply listLoop_preserves (fun groups => groupsEval ρ groups ≤ normEval ρ norm)
  · simp [groupsEval, MapValue.eval, MapValue.listMax]
  · intro entry member groups valid
    rcases entry with ⟨path, node⟩
    have atoms (initial : Groups) (start : groupsEval ρ initial ≤ normEval ρ norm) :
        groupsEval ρ (groupAtoms norm path node.vars initial) ≤ normEval ρ norm :=
      groupAtoms_le ρ norm path node.vars initial _ start
        (fun parameter offset occurs => home_atom_le ρ norm wellFormed path node member parameter offset occurs)
    dsimp only
    apply CanonUnivSubsumption.step_if
    · intro _
      change groupsEval ρ (groupAtoms norm path node.vars _) ≤ normEval ρ norm
      apply atoms
      rw [groups_insert_const_eval]
      exact Nat.max_le.mpr ⟨valid,
        Nat.le_trans (pathValue_mono ρ path (Nat.le_max_left node.constant _)) (normEntry_le ρ norm member)⟩
    · intro _
      exact atoms groups valid

theorem weighted_nodes (ρ : UInt64 → Nat) (entries : List (CPath × CNode)) :
    MapValue.listMax (fun entry => pathValue ρ entry.1 (nodeEval ρ entry.2)) entries = entriesEval ρ entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨path, node⟩
    change max (pathValue ρ path (nodeEval ρ node))
        (MapValue.listMax (fun entry : CPath × CNode => pathValue ρ entry.1 (nodeEval ρ entry.2)) rest) =
      max (pathValue ρ path (nodeEval ρ node)) (entriesEval ρ rest)
    rw [ih]

theorem buildGroups_covers (ρ : UInt64 → Nat) (norm : CNorm) :
    max (max (norm.findD [] {}).constant (groupsEval ρ (∅ : Groups))) (normEval ρ norm) ≤
      max (norm.findD [] {}).constant (groupsEval ρ (buildGroups norm)) := by
  unfold normEval
  rw [← weighted_nodes]
  unfold buildGroups
  apply listLoop_covers (fun groups => max (norm.findD [] {}).constant (groupsEval ρ groups))
    (fun entry : CPath × CNode => pathValue ρ entry.1 (nodeEval ρ entry.2))
  intro entry member before
  rcases entry with ⟨path, node⟩
  dsimp only
  split
  · let prepared := before.insert path { before.findD path {} with
      constant := max (before.findD path {}).constant node.constant }
    let after := groupAtoms norm path node.vars prepared
    have atoms := groupAtoms_covers ρ norm path node.vars prepared
    have growth : groupsEval ρ before ≤ groupsEval ρ after := by
      have start : groupsEval ρ before ≤ groupsEval ρ prepared := by
        dsimp only [prepared]
        rw [groups_insert_const_eval]
        exact Nat.le_max_left _ _
      exact Nat.le_trans start (Nat.le_trans (Nat.le_max_left _ _) atoms)
    have constantBound : pathValue ρ path node.constant ≤ groupsEval ρ after := by
      have start : pathValue ρ path node.constant ≤ groupsEval ρ prepared := by
        dsimp only [prepared]
        rw [groups_insert_const_eval]
        exact Nat.le_max_right _ _
      exact Nat.le_trans start (Nat.le_trans (Nat.le_max_left _ _) atoms)
    have variablesBound := Nat.le_trans (Nat.le_max_right _ _) atoms
    refine ⟨after, rfl, ?_, ?_⟩
    · omega
    · change pathValue ρ path (max node.constant (varsEval ρ node.vars.toList)) ≤ _
      rw [pathValue_max]
      exact Nat.le_trans (Nat.max_le.mpr ⟨constantBound, variablesBound⟩) (Nat.le_max_right _ _)
  · rename_i skipped
    let after := groupAtoms norm path node.vars before
    have atoms := groupAtoms_covers ρ norm path node.vars before
    have growth := Nat.le_trans (Nat.le_max_left _ _) atoms
    change groupsEval ρ before ≤ groupsEval ρ after at growth
    have variablesBound := Nat.le_trans (Nat.le_max_right _ _) atoms
    have constantBound : pathValue ρ path node.constant ≤
        max (norm.findD [] {}).constant (groupsEval ρ after) := by
      by_cases empty : path = []
      · subst path
        rw [findD_of_member norm member]
        simpa only [pathValue, active, List.all_nil, ↓reduceIte] using Nat.le_max_left node.constant (groupsEval ρ after)
      · have zero : node.constant = 0 := by
          simp [empty] at skipped
          omega
        simp [pathValue, zero]
    refine ⟨after, rfl, ?_, ?_⟩
    · omega
    · change pathValue ρ path (max node.constant (varsEval ρ node.vars.toList)) ≤ _
      rw [pathValue_max]
      exact Nat.max_le.mpr ⟨constantBound, Nat.le_trans variablesBound (Nat.le_max_right _ _)⟩

theorem buildGroups_ge (ρ : UInt64 → Nat) (norm : CNorm) :
    normEval ρ norm ≤ max (norm.findD [] {}).constant (groupsEval ρ (buildGroups norm)) :=
  Nat.le_trans (Nat.le_max_right _ _) (buildGroups_covers ρ norm)

/-- The actual grouping pass, together with the separately retained root
constant, has exactly the input normal form's value. -/
theorem buildGroups_eval (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm) :
    max (norm.findD [] {}).constant (groupsEval ρ (buildGroups norm)) = normEval ρ norm := by
  apply Nat.le_antisymm
  · apply Nat.max_le.mpr
    refine ⟨?_, buildGroups_le ρ norm wellFormed⟩
    have root := findD_value_le ρ norm []
    simp only [pathValue, active, List.all_nil, ↓reduceIte] at root
    exact Nat.le_trans (Nat.le_max_left _ _) root
  · exact buildGroups_ge ρ norm

def GoodPath (norm : CNorm) (path : CPath) : Prop := StrictPath path ∧ gatesLeakFree norm path = true

theorem atomHome_good (level : Univ) (path : CPath) (node : CNode)
    (member : (path, node) ∈ (normalize level).toList) (parameter : UInt64) (offset : Nat) :
    GoodPath (normalize level) (atomHome (normalize level) path parameter offset) := by
  unfold atomHome
  dsimp only
  split
  · rename_i accepted
    exact ⟨List.Pairwise.filter _ (normalize_strictPaths level path node member),
      (Bool.and_eq_true_iff.mp accepted).2⟩
  · exact ⟨normalize_strictPaths level path node member, normalize_gatesLeakFree level path node member⟩

theorem groupAtoms_paths (norm : CNorm) (path : CPath) (vars : Array (UInt64 × Nat))
    (P : CPath → Prop) (initial : Groups) (prior : PathsHave P initial)
    (atoms : ∀ parameter offset, (parameter, offset) ∈ vars.toList → P (atomHome norm path parameter offset)) :
    PathsHave P (groupAtoms norm path vars initial) := by
  unfold groupAtoms
  apply arrayLoop_preserves (PathsHave P)
  · exact prior
  · intro entry member current valid
    rcases entry with ⟨parameter, offset⟩
    change PathsHave P (current.insert (atomHome norm path parameter offset) _)
    exact valid.insert _ _ (atoms parameter offset (Array.mem_toList_iff.mpr member))

theorem buildGroups_goodPaths (level : Univ) :
    PathsHave (GoodPath (normalize level)) (buildGroups (normalize level)) := by
  unfold buildGroups
  apply listLoop_preserves (PathsHave (GoodPath (normalize level)))
  · intro path group impossible; cases impossible
  · intro entry member current valid
    rcases entry with ⟨path, node⟩
    have atoms (initial : Groups) (prior : PathsHave (GoodPath (normalize level)) initial) :
        PathsHave (GoodPath (normalize level)) (groupAtoms (normalize level) path node.vars initial) :=
      groupAtoms_paths _ _ _ _ _ prior (fun parameter offset _ => atomHome_good level path node member parameter offset)
    dsimp only
    apply CanonUnivSubsumption.step_if
    · intro _
      change PathsHave (GoodPath (normalize level)) (groupAtoms (normalize level) path node.vars _)
      exact atoms _ (valid.insert path _ ⟨normalize_strictPaths level path node member,
        normalize_gatesLeakFree level path node member⟩)
    · intro _
      exact atoms current valid

theorem groups_findD_insert (groups : Groups) (path query : CPath) (group : CGroup) :
    (groups.insert path group).findD query {} = if query = path then group else groups.findD query {} := by
  by_cases same : query = path
  · subst query
    simp [RBTree.RBMap.findD, RBTree.RBMap.find?_insert, Std.ReflCmp.compare_self]
  · have different : compare query path ≠ .eq := fun equal => same (Std.LawfulEqCmp.eq_of_compare equal)
    simp [RBTree.RBMap.findD, RBTree.RBMap.find?_insert, different, same]

def RootZero (groups : Groups) : Prop := (groups.findD [] {}).constant = 0

theorem RootZero.atom {groups : Groups} (zero : RootZero groups) (path : CPath)
    (parameter : UInt64) (offset : Nat) :
    RootZero (groups.insert path { groups.findD path {} with
      atoms := (groups.findD path {}).atoms.insert parameter (max ((groups.findD path {}).atoms.findD parameter 0) offset) }) := by
  unfold RootZero
  rw [groups_findD_insert]
  split
  · rename_i empty
    simpa [RootZero, ← empty] using zero
  · exact zero

theorem groupAtoms_rootZero (norm : CNorm) (path : CPath) (vars : Array (UInt64 × Nat))
    (initial : Groups) (zero : RootZero initial) : RootZero (groupAtoms norm path vars initial) := by
  unfold groupAtoms
  apply arrayLoop_preserves RootZero
  · exact zero
  · intro entry _ current valid
    rcases entry with ⟨parameter, offset⟩
    change RootZero (current.insert (atomHome norm path parameter offset) _)
    exact valid.atom _ parameter offset

theorem buildGroups_rootZero (norm : CNorm) : RootZero (buildGroups norm) := by
  unfold buildGroups
  apply listLoop_preserves RootZero
  · rfl
  · intro entry _ current valid
    rcases entry with ⟨path, node⟩
    dsimp only
    apply CanonUnivSubsumption.step_if
    · intro added
      have nonempty : path ≠ [] := by
        have condition := (Bool.and_eq_true_iff.mp added).1
        simpa using condition
      change RootZero (groupAtoms norm path node.vars _)
      apply groupAtoms_rootZero
      unfold RootZero
      rw [groups_findD_insert, ite_eq_right (Ne.symm nonempty)]
      exact valid
    · intro _
      exact groupAtoms_rootZero norm path node.vars current valid

def consumeMarkers (norm : CNorm) (groups : Groups) : Markers := Id.run do
  let mut consumed : Markers := []
  for (ctx, g) in groups.toList do
    if ctx.isEmpty || (g.constant == 0 && g.atoms.isEmpty) then continue
    let order := gateOrder norm ctx
    for j in [0:order.length] do
      let p := order[j]!
      let markerPath := (order.take j).mergeSort (· ≤ ·)
      if (groups.find? markerPath).any (fun sg => sg.atoms.find? p == some 0) then
        consumed := (markerPath, p) :: consumed
  return consumed

theorem rangeLoop_preserves (P : β → Prop) (stop : Nat) (initial : β)
    (body : Nat → β → Id (ForInStep β)) (start : P initial)
    (step : ∀ index, index < stop → ∀ state, P state → StepHolds P (body index state)) :
    P (forIn [0:stop] initial body : Id β) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply listLoop_preserves P
  · exact start
  · intro index member state valid
    have within : index ∈ ([0:stop] : Std.Legacy.Range) := Std.Legacy.Range.mem_of_mem_range' member
    exact step index within.2.1 state valid

/-- The consumer recorded this marker from a nonempty, non-root group at
the indicated position of that group's actual gate order. -/
def ConsumedBy (norm : CNorm) (groups : Groups) (marker : CPath × UInt64) : Prop :=
  ∃ context group, (context, group) ∈ groups.toList ∧
    ¬(context.isEmpty || (group.constant == 0 && group.atoms.isEmpty)) = true ∧
    ∃ (index : Nat) (inside : index < (gateOrder norm context).length),
      marker = (((gateOrder norm context).take index).mergeSort (· ≤ ·), (gateOrder norm context)[index])

theorem consumeMarkers_valid (norm : CNorm) (groups : Groups) :
    ∀ marker ∈ consumeMarkers norm groups, ConsumedBy norm groups marker := by
  unfold consumeMarkers
  apply listLoop_preserves (fun markers : Markers => ∀ marker ∈ markers, ConsumedBy norm groups marker)
  · simp
  · intro entry member markers valid
    rcases entry with ⟨context, group⟩
    dsimp only
    apply CanonUnivSubsumption.step_if
    · intro _
      exact valid
    · intro live
      apply rangeLoop_preserves (fun markers : Markers => ∀ marker ∈ markers, ConsumedBy norm groups marker)
      · exact valid
      · intro index inside prior accepted
        apply StepHolds.choose
        · dsimp only [pure, StepHolds]
          intro marker occurs
          rcases List.mem_cons.mp occurs with same | old
          · subst marker
            refine ⟨context, group, member, live, index, inside, ?_⟩
            rw [getElem!_pos (gateOrder norm context) index inside]
          · exact accepted marker old
        · exact accepted

theorem ConsumedBy.longer {norm : CNorm} {groups : Groups} {marker : CPath × UInt64}
    (consumed : ConsumedBy norm groups marker) :
    ∃ context group, (context, group) ∈ groups.toList ∧ marker.1.length < context.length := by
  obtain ⟨context, group, member, _, index, inside, same⟩ := consumed
  subst marker
  exact ⟨context, group, member, consumption_context_shorter norm context index inside⟩

/-- A consumed marker's target order starts with the source group's order,
then the marker itself. This is the semantic replacement used in the chain
induction, including when an intermediate group emits no own atom. -/
theorem ConsumedBy.prefix {norm : CNorm} {groups : Groups} {marker : CPath × UInt64}
    (paths : PathsHave (GoodPath norm) groups) (consumed : ConsumedBy norm groups marker) :
    ∃ context group suffix, (context, group) ∈ groups.toList ∧
      ¬(context.isEmpty || (group.constant == 0 && group.atoms.isEmpty)) = true ∧
      marker.1.length < context.length ∧
      gateOrder norm context = gateOrder norm marker.1 ++ marker.2 :: suffix := by
  obtain ⟨context, group, member, live, index, inside, same⟩ := consumed
  subst marker
  have shape := (paths context group member).1
  have agrees := gateOrder_sorted_prefix norm context shape.sorted shape.nodup index
  refine ⟨context, group, (gateOrder norm context).drop (index + 1), member, live,
    consumption_context_shorter norm context index inside, ?_⟩
  rw [agrees]
  rw [List.getElem_cons_drop inside, List.take_append_drop]

def collectStep (term : α → Option β) (item : α) (initial : List β) : Id (ForInStep (List β)) :=
  match term item with
  | none => pure (.yield initial)
  | some value => pure (.yield (initial ++ [value]))

theorem collectLoop_eq (term : α → Option β) (items : List α) (initial : List β) :
    (forIn items initial (collectStep term) : Id (List β)) = initial ++ items.filterMap term := by
  induction items generalizing initial with
  | nil => simp [pure]
  | cons item rest ih =>
    cases found : term item <;>
      simp [List.forIn_cons, collectStep, found, pure, bind, ih, List.append_assoc]

def atomTerm (consumed : Markers) (context : CPath) (entry : UInt64 × Nat) : Option Univ :=
  if entry.2 == 0 && consumed.contains (context, entry.1) then none
  else some (Univ.addSuccs (.var entry.1) entry.2)

def collectVars (consumed : Markers) (context : CPath) (atoms : RBTree.RBMap UInt64 Nat compare)
    (initial : List Univ) : List Univ := Id.run do
  let mut result := initial
  for (parameter, offset) in atoms.toList do
    if offset == 0 && consumed.contains (context, parameter) then continue
    result := result ++ [Univ.addSuccs (.var parameter) offset]
  return result

theorem collectVars_eq (consumed : Markers) (context : CPath) (atoms : RBTree.RBMap UInt64 Nat compare)
    (initial : List Univ) : collectVars consumed context atoms initial =
      initial ++ atoms.toList.filterMap (atomTerm consumed context) := by
  rw [← collectLoop_eq]
  unfold collectVars
  change (forIn atoms.toList initial _ : Id (List Univ)) =
    (forIn atoms.toList initial (collectStep (atomTerm consumed context)) : Id (List Univ))
  apply congrArg (fun body => (forIn atoms.toList initial body : Id (List Univ)))
  funext entry current
  rcases entry with ⟨parameter, offset⟩
  dsimp only
  by_cases skipped : offset = 0 ∧ (context, parameter) ∈ consumed <;>
    simp [collectStep, atomTerm, skipped]

def retainedTerms (consumed : Markers) (context : CPath) (group : CGroup) : List Univ :=
  group.atoms.toList.filterMap (atomTerm consumed context) ++
    if group.constant > 0 then [Univ.addSuccs .zero group.constant] else []

def groupOutput (norm : CNorm) (consumed : Markers) (context : CPath) (group : CGroup) : Option Univ :=
  if context.isEmpty then none
  else if (retainedTerms consumed context group).isEmpty then none
  else some (emitGated (gateOrder norm context) (maxChain (retainedTerms consumed context group)))

def emitRow (norm : CNorm) (consumed : Markers) (entry : CPath × CGroup)
    (initial : List Univ) : Id (ForInStep (List Univ)) := do
  let (context, group) := entry
  if context.isEmpty then return .yield initial
  let mut atoms := collectVars consumed context group.atoms []
  if group.constant > 0 then atoms := atoms ++ [Univ.addSuccs .zero group.constant]
  if atoms.isEmpty then return .yield initial
  return .yield (initial ++ [emitGated (gateOrder norm context) (maxChain atoms)])

theorem emitRow_eq (norm : CNorm) (consumed : Markers) (entry : CPath × CGroup) (initial : List Univ) :
    emitRow norm consumed entry initial =
      collectStep (fun item : CPath × CGroup => groupOutput norm consumed item.1 item.2) entry initial := by
  rcases entry with ⟨context, group⟩
  cases root : context.isEmpty <;>
    by_cases positive : group.constant > 0 <;>
      cases empty : (group.atoms.toList.filterMap (atomTerm consumed context)).isEmpty <;>
        simp [emitRow, collectVars_eq, collectStep, groupOutput, retainedTerms, root, positive, empty]

def rootStep (root : Nat) (consumed : Markers) (entry : UInt64 × Nat)
    (state : List Univ × Bool) : Id (ForInStep (List Univ × Bool)) := do
  let (parameter, offset) := entry
  let mut terms := state.1
  let mut absorbed := state.2
  if offset == 0 && consumed.contains ([], parameter) then return .yield (terms, absorbed)
  terms := terms ++ [Univ.addSuccs (.var parameter) offset]
  if offset ≥ root then absorbed := true
  return .yield (terms, absorbed)

def rootHit (root : Nat) (consumed : Markers) (entry : UInt64 × Nat) : Bool :=
  !(entry.2 == 0 && consumed.contains ([], entry.1)) && decide (entry.2 ≥ root)

theorem rootLoop_eq (root : Nat) (consumed : Markers) (entries : List (UInt64 × Nat))
    (initial : List Univ × Bool) :
    (forIn entries initial (rootStep root consumed) : Id (List Univ × Bool)) =
      (initial.1 ++ entries.filterMap (atomTerm consumed []), initial.2 || entries.any (rootHit root consumed)) := by
  induction entries generalizing initial with
  | nil => simp [pure]
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    rcases initial with ⟨terms, absorbed⟩
    cases zero : (offset == 0) <;> cases skipped : consumed.contains ([], parameter) <;>
      by_cases covers : offset ≥ root <;>
        simp only [List.forIn_cons, rootStep, atomTerm, rootHit, zero, skipped, covers, pure, bind,
          List.filterMap_cons, List.any_cons, ih, List.append_assoc, List.singleton_append,
          Bool.not_false, Bool.not_true, Bool.or_true, Bool.true_or, Bool.false_or,
          Bool.and_false, Bool.and_true, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

def rootPass (norm : CNorm) (groups : Groups) (consumed : Markers) : List Univ × Bool :=
  match groups.find? [] with
  | none => ([], false)
  | some group => (forIn group.atoms.toList ([], false) (rootStep (norm.findD [] {}).constant consumed) : Id (List Univ × Bool))

def finishEmission (root : Nat) (absorbed : Bool) (initial : List Univ) : Univ := Id.run do
  let mut terms := initial
  if root > 0 && !absorbed then terms := terms ++ [Univ.addSuccs .zero root]
  return maxChain terms

def emitGroups (norm : CNorm) (groups : Groups) (consumed : Markers) : Univ := Id.run do
  let cRoot := (norm.findD [] {}).constant
  let mut terms : List Univ := []
  let mut rootCAbsorbed := false
  if let some top := groups.find? [] then
    for (i, k) in top.atoms.toList do
      if k == 0 && consumed.contains ([], i) then continue
      terms := terms ++ [Univ.addSuccs (.var i) k]
      if k ≥ cRoot then rootCAbsorbed := true
  for (ctx, g) in groups.toList do
    if ctx.isEmpty then continue
    let mut atoms : List Univ := []
    for (i, k) in g.atoms.toList do
      if k == 0 && consumed.contains (ctx, i) then continue
      atoms := atoms ++ [Univ.addSuccs (.var i) k]
    if g.constant > 0 then atoms := atoms ++ [Univ.addSuccs .zero g.constant]
    if atoms.isEmpty then continue
    let body := maxChain atoms
    let order := gateOrder norm ctx
    let term := order.reverse.foldl (fun acc p => Univ.imax acc (.var p)) body
    terms := terms ++ [term]
  if cRoot > 0 && !rootCAbsorbed then terms := terms ++ [Univ.addSuccs .zero cRoot]
  return maxChain terms

theorem emitGroups_split (norm : CNorm) (groups : Groups) (consumed : Markers) :
    emitGroups norm groups consumed =
      let start := rootPass norm groups consumed
      finishEmission (norm.findD [] {}).constant start.2
        (forIn groups.toList start.1 (emitRow norm consumed) : Id (List Univ)) := by
  unfold emitGroups rootPass
  cases groups.find? [] <;> rfl

theorem emitGroups_terms (norm : CNorm) (groups : Groups) (consumed : Markers) :
    emitGroups norm groups consumed =
      let start := rootPass norm groups consumed
      finishEmission (norm.findD [] {}).constant start.2
        (start.1 ++ groups.toList.filterMap (fun entry => groupOutput norm consumed entry.1 entry.2)) := by
  rw [emitGroups_split]
  dsimp only
  have rows : emitRow norm consumed =
      collectStep (fun entry : CPath × CGroup => groupOutput norm consumed entry.1 entry.2) := by
    funext entry initial
    exact emitRow_eq norm consumed entry initial
  rw [rows, collectLoop_eq]

theorem evalTerms_le (ρ : UInt64 → Nat) (terms : List Univ) (bound : Nat) :
    evalTerms ρ terms ≤ bound ↔ ∀ term ∈ terms, univEval ρ term ≤ bound := by
  induction terms <;> simp [evalTerms, Nat.max_le, *]

theorem evalTerms_member_le (ρ : UInt64 → Nat) {terms : List Univ} {term : Univ} (member : term ∈ terms) :
    univEval ρ term ≤ evalTerms ρ terms := (evalTerms_le ρ terms _).mp (Nat.le_refl _) term member

theorem atomTerm_kept (consumed : Markers) (context : CPath) (parameter : UInt64) (offset : Nat)
    (kept : ¬(offset = 0 ∧ (context, parameter) ∈ consumed)) :
    atomTerm consumed context (parameter, offset) = some (Univ.addSuccs (.var parameter) offset) := by
  simp [atomTerm, kept]

theorem atomTerm_value (ρ : UInt64 → Nat) (consumed : Markers) (context : CPath)
    (parameter : UInt64) (offset : Nat) {term : Univ}
    (present : atomTerm consumed context (parameter, offset) = some term) :
    univEval ρ term = ρ parameter + offset := by
  unfold atomTerm at present
  split at present
  · cases present
  · cases Option.some.inj present
    simp [addSuccs_eval, univEval]

theorem rootPass_terms (norm : CNorm) (groups : Groups) (consumed : Markers) {group : CGroup}
    (found : groups.find? [] = some group) :
    (rootPass norm groups consumed).1 = group.atoms.toList.filterMap (atomTerm consumed []) := by
  simp only [rootPass, found, rootLoop_eq, List.nil_append, Bool.false_or]

theorem rootPass_flag (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (absorbed : (rootPass norm groups consumed).2 = true) :
    (norm.findD [] {}).constant ≤ evalTerms ρ (rootPass norm groups consumed).1 := by
  cases found : groups.find? [] with
  | none => simp [rootPass, found] at absorbed
  | some group =>
    have hit : group.atoms.toList.any (rootHit (norm.findD [] {}).constant consumed) = true := by
      simpa only [rootPass, found, rootLoop_eq, Bool.false_or] using absorbed
    obtain ⟨⟨parameter, offset⟩, member, accepted⟩ := List.any_eq_true.mp hit
    have conditions : ¬(offset = 0 ∧ ([], parameter) ∈ consumed) ∧ (norm.findD [] {}).constant ≤ offset := by
      have facts : (offset ≠ 0 ∨ ([], parameter) ∉ consumed) ∧ (norm.findD [] {}).constant ≤ offset := by
        simpa [rootHit] using accepted
      refine ⟨?_, facts.2⟩
      rintro ⟨zero, present⟩
      rcases facts.1 with nonzero | absent
      · exact nonzero zero
      · exact absent present
    have emitted : Univ.addSuccs (.var parameter) offset ∈ (rootPass norm groups consumed).1 := by
      rw [rootPass_terms norm groups consumed found]
      exact List.mem_filterMap.mpr ⟨(parameter, offset), member, atomTerm_kept consumed [] parameter offset conditions.1⟩
    have bound := evalTerms_member_le ρ emitted
    rw [addSuccs_eval, univEval] at bound
    omega

theorem finishEmission_ge (ρ : UInt64 → Nat) (root : Nat) (absorbed : Bool) (terms : List Univ) :
    evalTerms ρ terms ≤ univEval ρ (finishEmission root absorbed terms) := by
  unfold finishEmission
  split
  · simp only [pure, Id.run, maxChain_eval, evalTerms_append, evalTerms, addSuccs_eval, univEval]
    omega
  · simp only [pure, Id.run, maxChain_eval]
    exact Nat.le_refl _

theorem finishEmission_root (ρ : UInt64 → Nat) (root : Nat) (absorbed : Bool) (terms : List Univ)
    (covered : absorbed = true → root ≤ evalTerms ρ terms) : root ≤ univEval ρ (finishEmission root absorbed terms) := by
  unfold finishEmission
  split
  · simp only [pure, Id.run, maxChain_eval, evalTerms_append, evalTerms, addSuccs_eval, univEval]
    omega
  · rename_i noAppend
    simp only [pure, Id.run, maxChain_eval]
    cases absorbed with
    | true => exact covered rfl
    | false => simp at noAppend; omega

theorem emitGroups_term_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (term : Univ) (member : term ∈ (rootPass norm groups consumed).1 ++
      groups.toList.filterMap (fun entry => groupOutput norm consumed entry.1 entry.2)) :
    univEval ρ term ≤ univEval ρ (emitGroups norm groups consumed) := by
  rw [emitGroups_terms]
  exact Nat.le_trans (evalTerms_member_le ρ member) (finishEmission_ge ρ _ _ _)

theorem emitGroups_root_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers) :
    (norm.findD [] {}).constant ≤ univEval ρ (emitGroups norm groups consumed) := by
  rw [emitGroups_terms]
  apply finishEmission_root
  intro absorbed
  rw [evalTerms_append]
  exact Nat.le_trans (rootPass_flag ρ norm groups consumed absorbed) (Nat.le_max_left _ _)

theorem retained_atom_mem (consumed : Markers) (context : CPath) (group : CGroup)
    (parameter : UInt64) (offset : Nat) (member : (parameter, offset) ∈ group.atoms.toList)
    (kept : ¬(offset = 0 ∧ (context, parameter) ∈ consumed)) :
    Univ.addSuccs (.var parameter) offset ∈ retainedTerms consumed context group := by
  apply List.mem_append_left
  exact List.mem_filterMap.mpr ⟨(parameter, offset), member, atomTerm_kept consumed context parameter offset kept⟩

theorem retained_const_mem (consumed : Markers) (context : CPath) (group : CGroup)
    (positive : group.constant > 0) : Univ.addSuccs .zero group.constant ∈ retainedTerms consumed context group := by
  simp [retainedTerms, positive]

theorem retainedTerms_eval_le (ρ : UInt64 → Nat) (consumed : Markers) (context : CPath) (group : CGroup) :
    evalTerms ρ (retainedTerms consumed context group) ≤ groupValue ρ group := by
  apply (evalTerms_le ρ _ _).mpr
  intro term member
  unfold retainedTerms at member
  rcases List.mem_append.mp member with atom | constant
  · obtain ⟨⟨parameter, offset⟩, inside, present⟩ := List.mem_filterMap.mp atom
    rw [atomTerm_value ρ consumed context parameter offset present]
    exact Nat.le_trans (MapValue.entry_le (fun p k => ρ p + k) group.atoms inside) (Nat.le_max_right _ _)
  · split at constant
    · have same : term = Univ.addSuccs .zero group.constant := by simpa using constant
      subst term
      simp only [addSuccs_eval, univEval, Nat.zero_add]
      exact Nat.le_max_left _ _
    · cases constant

def fullTerms (group : CGroup) : List Univ :=
  group.atoms.toList.map (fun entry => Univ.addSuccs (.var entry.1) entry.2) ++
    if group.constant > 0 then [Univ.addSuccs .zero group.constant] else []

theorem mappedAtoms_eval (ρ : UInt64 → Nat) (entries : List (UInt64 × Nat)) :
    evalTerms ρ (entries.map (fun entry => Univ.addSuccs (.var entry.1) entry.2)) =
      MapValue.listMax (fun entry => ρ entry.1 + entry.2) entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    simp only [List.map_cons, evalTerms, addSuccs_eval, univEval, ih, MapValue.listMax]

theorem fullTerms_eval (ρ : UInt64 → Nat) (group : CGroup) : evalTerms ρ (fullTerms group) = groupValue ρ group := by
  unfold fullTerms
  rw [evalTerms_append, mappedAtoms_eval]
  unfold groupValue atomsEval MapValue.eval
  by_cases positive : group.constant > 0
  · simp [positive, evalTerms, addSuccs_eval, univEval, Nat.max_comm]
  · have zero : group.constant = 0 := by omega
    simp [zero, evalTerms]

theorem fullTerms_nonempty (group : CGroup)
    (live : ¬(group.constant == 0 && group.atoms.isEmpty) = true) : fullTerms group ≠ [] := by
  intro empty
  have facts : group.atoms.toList = [] ∧ group.constant = 0 := by
    simpa [fullTerms] using empty
  have noAtoms : group.atoms.isEmpty = true := RBTree.RBSet.isEmpty_iff_toList_eq_nil.mpr facts.1
  exact live (by simp [facts.2, noAtoms])

def potentialTerm (norm : CNorm) (context : CPath) (group : CGroup) : Univ :=
  emitGated (gateOrder norm context) (maxChain (fullTerms group))

theorem potentialTerm_eval (ρ : UInt64 → Nat) (norm : CNorm) (context : CPath) (group : CGroup) :
    univEval ρ (potentialTerm norm context group) =
      max (groupEval ρ context group) (univEval ρ (emitGated (gateOrder norm context) .zero)) := by
  unfold potentialTerm
  rw [emitGated_eval, maxChain_eval, fullTerms_eval, active_gateOrder]
  rfl

theorem emitGated_mono (ρ : UInt64 → Nat) (order : List UInt64) (first second : Univ)
    (bound : univEval ρ first ≤ univEval ρ second) :
    univEval ρ (emitGated order first) ≤ univEval ρ (emitGated order second) := by
  rw [emitGated_eval ρ order first, emitGated_eval ρ order second]
  have grows := pathValue_mono ρ order bound
  change max (pathValue ρ order (univEval ρ first)) _ ≤ max (pathValue ρ order (univEval ρ second)) _
  omega

theorem gated_marker_le (ρ : UInt64 → Nat) (before after : List UInt64) (gate : UInt64) (body : Univ) :
    univEval ρ (emitGated before (.var gate)) ≤ univEval ρ (emitGated (before ++ gate :: after) body) := by
  rw [emitGated_append]
  apply emitGated_mono
  rw [emitGated_cons]
  simp only [univEval]
  by_cases zero : ρ gate = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    exact Nat.le_max_right _ _

theorem gated_chain_le (ρ : UInt64 → Nat) (order : List UInt64) (terms : List Univ) (bound : Nat)
    (nonempty : terms ≠ []) (each : ∀ term ∈ terms, univEval ρ (emitGated order term) ≤ bound) :
    univEval ρ (emitGated order (maxChain terms)) ≤ bound := by
  obtain ⟨term, member⟩ := List.exists_mem_of_ne_nil terms nonempty
  have first := each term member
  rw [emitGated_eval] at first
  have leakage : univEval ρ (emitGated order .zero) ≤ bound := by omega
  rw [emitGated_eval, maxChain_eval]
  by_cases enabled : active ρ order = true
  · have body : evalTerms ρ terms ≤ bound := by
      apply (evalTerms_le ρ terms bound).mpr
      intro term member
      have checked := each term member
      rw [emitGated_eval] at checked
      simp only [enabled, ↓reduceIte] at checked
      omega
    simp only [enabled, ↓reduceIte]
    exact Nat.max_le.mpr ⟨body, leakage⟩
  · simpa [enabled] using leakage

theorem retained_output_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (context : CPath) (group : CGroup) (member : (context, group) ∈ groups.toList) (nonroot : context ≠ [])
    (term : Univ) (retained : term ∈ retainedTerms consumed context group) :
    univEval ρ (emitGated (gateOrder norm context) term) ≤ univEval ρ (emitGroups norm groups consumed) := by
  have nonempty := List.ne_nil_of_mem retained
  have emitted : groupOutput norm consumed context group =
      some (emitGated (gateOrder norm context) (maxChain (retainedTerms consumed context group))) := by
    simp [groupOutput, nonroot, nonempty]
  have inOutput : emitGated (gateOrder norm context) (maxChain (retainedTerms consumed context group)) ∈
      (rootPass norm groups consumed).1 ++ groups.toList.filterMap (fun entry => groupOutput norm consumed entry.1 entry.2) :=
    List.mem_append_right _ (List.mem_filterMap.mpr ⟨(context, group), member, emitted⟩)
  exact Nat.le_trans (emitGated_mono ρ _ _ _ (by rw [maxChain_eval]; exact evalTerms_member_le ρ retained))
    (emitGroups_term_le ρ norm groups consumed _ inOutput)

theorem root_atom_output_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (group : CGroup) (member : ([], group) ∈ groups.toList) (parameter : UInt64) (offset : Nat)
    (occurs : (parameter, offset) ∈ group.atoms.toList) (kept : ¬(offset = 0 ∧ ([], parameter) ∈ consumed)) :
    univEval ρ (Univ.addSuccs (.var parameter) offset) ≤ univEval ρ (emitGroups norm groups consumed) := by
  have found : groups.find? [] = some group := RBTree.RBMap.find?_some.mpr ⟨[], member, Std.ReflCmp.compare_self⟩
  apply emitGroups_term_le
  apply List.mem_append_left
  rw [rootPass_terms norm groups consumed found]
  exact List.mem_filterMap.mpr ⟨(parameter, offset), occurs, atomTerm_kept consumed [] parameter offset kept⟩

theorem potential_bound_step (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (paths : PathsHave (GoodPath norm) groups) (rootZero : RootZero groups)
    (valid : ∀ marker ∈ consumed, ConsumedBy norm groups marker)
    (context : CPath) (group : CGroup) (member : (context, group) ∈ groups.toList)
    (live : ¬(group.constant == 0 && group.atoms.isEmpty) = true)
    (larger : ∀ target value, (target, value) ∈ groups.toList → context.length < target.length →
      ¬(value.constant == 0 && value.atoms.isEmpty) = true →
      univEval ρ (potentialTerm norm target value) ≤ univEval ρ (emitGroups norm groups consumed)) :
    univEval ρ (potentialTerm norm context group) ≤ univEval ρ (emitGroups norm groups consumed) := by
  apply gated_chain_le ρ _ _ _ (fullTerms_nonempty group live)
  intro term inside
  unfold fullTerms at inside
  rcases List.mem_append.mp inside with atom | constant
  · obtain ⟨⟨parameter, offset⟩, occurs, same⟩ := List.mem_map.mp atom
    subst term
    by_cases removed : offset = 0 ∧ (context, parameter) ∈ consumed
    · obtain ⟨rfl, removed⟩ := removed
      obtain ⟨target, value, suffix, targetMember, activeGroup, longer, prefixEq⟩ :=
        (valid (context, parameter) removed).prefix paths
      have targetLive : ¬(value.constant == 0 && value.atoms.isEmpty) = true := by
        intro empty
        exact activeGroup (by simp [empty])
      have targetBound := larger target value targetMember longer targetLive
      have transferred := gated_marker_le ρ (gateOrder norm context) suffix parameter (maxChain (fullTerms value))
      rw [← prefixEq] at transferred
      exact Nat.le_trans transferred targetBound
    · have retained := retained_atom_mem consumed context group parameter offset occurs removed
      by_cases root : context = []
      · subst context
        simpa only [gateOrder_eq, orderAux_nil, emitGated_nil] using
          root_atom_output_le ρ norm groups consumed group member parameter offset occurs removed
      · exact retained_output_le ρ norm groups consumed context group member root _ retained
  · split at constant
    · rename_i positive
      have same : term = Univ.addSuccs .zero group.constant := by simpa using constant
      subst term
      by_cases root : context = []
      · subst context
        have found : groups.find? [] = some group := RBTree.RBMap.find?_some.mpr ⟨[], member, Std.ReflCmp.compare_self⟩
        have zero : group.constant = 0 := by simpa only [RootZero, RBTree.RBMap.findD, found, Option.getD_some] using rootZero
        omega
      · exact retained_output_le ρ norm groups consumed context group member root _ (retained_const_mem consumed context group positive)
    · cases constant

theorem potential_output_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (paths : PathsHave (GoodPath norm) groups) (rootZero : RootZero groups)
    (valid : ∀ marker ∈ consumed, ConsumedBy norm groups marker)
    (context : CPath) (group : CGroup) (member : (context, group) ∈ groups.toList)
    (live : ¬(group.constant == 0 && group.atoms.isEmpty) = true) :
    univEval ρ (potentialTerm norm context group) ≤ univEval ρ (emitGroups norm groups consumed) := by
  let maximum := MapValue.listMax (fun entry : CPath × CGroup => entry.1.length) groups.toList
  have lengthBound : ∀ path value, (path, value) ∈ groups.toList → path.length ≤ maximum :=
    fun path value inside => MapValue.member_le (fun entry : CPath × CGroup => entry.1.length) inside
  have all : ∀ remaining, ∀ path value, (path, value) ∈ groups.toList → maximum - path.length = remaining →
      ¬(value.constant == 0 && value.atoms.isEmpty) = true →
      univEval ρ (potentialTerm norm path value) ≤ univEval ρ (emitGroups norm groups consumed) := by
    intro remaining
    induction remaining using (measure (fun n : Nat => n)).wf.induction with
    | h remaining ih =>
      intro path value inside rankEq activeGroup
      apply potential_bound_step ρ norm groups consumed paths rootZero valid path value inside activeGroup
      intro target targetValue targetMember longer targetLive
      have bounded := lengthBound target targetValue targetMember
      exact ih (maximum - target.length) (by change maximum - target.length < remaining; omega)
        target targetValue targetMember rfl targetLive
  exact all _ context group member rfl live

theorem emitGroups_ge (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (paths : PathsHave (GoodPath norm) groups) (rootZero : RootZero groups)
    (valid : ∀ marker ∈ consumed, ConsumedBy norm groups marker) :
    max (norm.findD [] {}).constant (groupsEval ρ groups) ≤ univEval ρ (emitGroups norm groups consumed) := by
  apply Nat.max_le.mpr
  refine ⟨emitGroups_root_le ρ norm groups consumed, ?_⟩
  apply MapValue.eval_le
  intro context group member
  by_cases live : ¬(group.constant == 0 && group.atoms.isEmpty) = true
  · have bound := potential_output_le ρ norm groups consumed paths rootZero valid context group member live
    rw [potentialTerm_eval] at bound
    exact Nat.le_trans (Nat.le_max_left _ _) bound
  · have empty : (group.constant == 0 && group.atoms.isEmpty) = true := Classical.not_not.mp live
    obtain ⟨zero, noAtoms⟩ := Bool.and_eq_true_iff.mp empty
    have zero : group.constant = 0 := beq_iff_eq.mp zero
    have noAtoms : group.atoms.toList = [] := RBTree.RBSet.isEmpty_iff_toList_eq_nil.mp noAtoms
    simp [groupEval, groupValue, atomsEval, MapValue.eval, MapValue.listMax, pathValue, zero, noAtoms]

theorem finishEmission_le (ρ : UInt64 → Nat) (root : Nat) (absorbed : Bool) (terms : List Univ)
    (bound : Nat) (rootBound : root ≤ bound) (termsBound : evalTerms ρ terms ≤ bound) :
    univEval ρ (finishEmission root absorbed terms) ≤ bound := by
  unfold finishEmission
  split
  · simp only [pure, Id.run, maxChain_eval, evalTerms_append, evalTerms, addSuccs_eval, univEval]
    omega
  · simpa only [pure, Id.run, maxChain_eval] using termsBound

theorem rootPass_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (bounded : groupsEval ρ groups ≤ normEval ρ norm) :
    evalTerms ρ (rootPass norm groups consumed).1 ≤ normEval ρ norm := by
  cases found : groups.find? [] with
  | none => simp [rootPass, found, evalTerms]
  | some group =>
    rw [rootPass_terms norm groups consumed found]
    have groupBound : groupValue ρ group ≤ groupsEval ρ groups := by
      have bound := MapValue.lookup_le (groupEval ρ) groups []
      simpa [MapValue.lookup, found, groupEval, groupsEval, pathValue, active] using bound
    apply (evalTerms_le ρ _ _).mpr
    intro term member
    obtain ⟨⟨parameter, offset⟩, occurs, present⟩ := List.mem_filterMap.mp member
    rw [atomTerm_value ρ consumed [] parameter offset present]
    have atomBound : ρ parameter + offset ≤ groupValue ρ group :=
      Nat.le_trans (MapValue.entry_le (fun p k => ρ p + k) group.atoms occurs) (Nat.le_max_right _ _)
    exact Nat.le_trans atomBound (Nat.le_trans groupBound bounded)

theorem groupOutput_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (paths : PathsHave (GoodPath norm) groups) (bounded : groupsEval ρ groups ≤ normEval ρ norm)
    (context : CPath) (group : CGroup) (member : (context, group) ∈ groups.toList) {term : Univ}
    (emitted : groupOutput norm consumed context group = some term) : univEval ρ term ≤ normEval ρ norm := by
  unfold groupOutput at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · cases Option.some.inj emitted
      rw [emitGated_eval, maxChain_eval, active_gateOrder]
      have body := pathValue_mono ρ context (retainedTerms_eval_le ρ consumed context group)
      have groupBound := Nat.le_trans (MapValue.entry_le (groupEval ρ) groups member) bounded
      have leakage := gatesLeakFree_sound norm context (paths context group member).2 ρ
      change max (pathValue ρ context (evalTerms ρ (retainedTerms consumed context group))) _ ≤ _
      exact Nat.max_le.mpr ⟨Nat.le_trans body groupBound, leakage⟩

theorem emitGroups_le (ρ : UInt64 → Nat) (norm : CNorm) (groups : Groups) (consumed : Markers)
    (paths : PathsHave (GoodPath norm) groups) (bounded : groupsEval ρ groups ≤ normEval ρ norm) :
    univEval ρ (emitGroups norm groups consumed) ≤ normEval ρ norm := by
  rw [emitGroups_terms]
  apply finishEmission_le
  · have root := findD_value_le ρ norm []
    simp only [pathValue, active, List.all_nil, ↓reduceIte] at root
    exact Nat.le_trans (Nat.le_max_left _ _) root
  · rw [evalTerms_append]
    apply Nat.max_le.mpr
    refine ⟨rootPass_le ρ norm groups consumed bounded, ?_⟩
    apply (evalTerms_le ρ _ _).mpr
    intro term member
    obtain ⟨⟨context, group⟩, inside, emitted⟩ := List.mem_filterMap.mp member
    exact groupOutput_le ρ norm groups consumed paths bounded context group inside emitted

theorem linearize_phases (norm : CNorm) : linearize norm =
    emitGroups norm (buildGroups norm) (consumeMarkers norm (buildGroups norm)) := by
  rfl

theorem linearize_normalize_eval (ρ : UInt64 → Nat) (level : Univ) :
    univEval ρ (linearize (normalize level)) = normEval ρ (normalize level) := by
  rw [linearize_phases]
  have wellFormed := normalize_selfGated level
  have paths := buildGroups_goodPaths level
  apply Nat.le_antisymm
  · exact emitGroups_le ρ (normalize level) _ _ paths (buildGroups_le ρ (normalize level) wellFormed)
  · have bound := emitGroups_ge ρ (normalize level) (buildGroups (normalize level)) _ paths
      (buildGroups_rootZero (normalize level)) (consumeMarkers_valid (normalize level) _)
    rw [buildGroups_eval ρ (normalize level) wellFormed] at bound
    exact bound

/-- The complete production universe canonicalizer preserves every universe
valuation, with all normalization, grouping and marker-consumption invariants
derived from its actual input construction. -/
theorem canonUniv_eval (ρ : UInt64 → Nat) (level : Univ) :
    univEval ρ (canonUniv level) = univEval ρ level := by
  unfold canonUniv
  rw [linearize_normalize_eval]
  exact CanonUnivSubsumption.normalize_eval ρ level

end Ix.CompileCert.CanonUnivEmit

