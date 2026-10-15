import Ix.CompileCert.CanonUnivSubsumption

/-! Gate availability and path shape for production universe normalization.
Separating valuations transport absorber witnesses through semantic growth,
including subsumption. Every produced path receives an accepted gate order
and is strictly ordered without duplicates. Complete emission is separate. -/

namespace Ix.CompileCert.CanonUnivPaths

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning

theorem entriesEval_gt (ρ : UInt64 → Nat) (entries : List (CPath × CNode)) (bound : Nat)
    (large : bound < entriesEval ρ entries) :
    ∃ path node, (path, node) ∈ entries ∧ active ρ path = true ∧ bound < nodeEval ρ node := by
  induction entries with
  | nil => simp [entriesEval] at large
  | cons entry rest ih =>
    rcases entry with ⟨path, node⟩
    by_cases head : bound < pathValue ρ path (nodeEval ρ node)
    · by_cases enabled : active ρ path = true
      · exact ⟨path, node, by simp, enabled, by simpa only [pathValue, enabled, ↓reduceIte] using head⟩
      · simp [pathValue, enabled] at head
    · have tail : bound < entriesEval ρ rest := by
        change bound < max (pathValue ρ path (nodeEval ρ node)) (entriesEval ρ rest) at large
        omega
      obtain ⟨key, value, member, enabled, valueLarge⟩ := ih tail
      exact ⟨key, value, List.mem_cons_of_mem _ member, enabled, valueLarge⟩

theorem varsEval_gt (ρ : UInt64 → Nat) (vars : List (UInt64 × Nat)) (bound : Nat)
    (large : bound < varsEval ρ vars) :
    ∃ parameter offset, (parameter, offset) ∈ vars ∧ bound < ρ parameter + offset := by
  induction vars with
  | nil => simp [varsEval] at large
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    by_cases head : bound < ρ parameter + offset
    · exact ⟨parameter, offset, by simp, head⟩
    · have tail : bound < varsEval ρ rest := by
        simp only [varsEval] at large
        omega
      obtain ⟨key, value, member, valueLarge⟩ := ih tail
      exact ⟨key, value, List.mem_cons_of_mem _ member, valueLarge⟩

def oneBound (norm : CNorm) : Nat := normEval (fun _ => 1) norm

theorem constant_le_oneBound (norm : CNorm) {path node} (member : (path, node) ∈ norm.toList) :
    node.constant ≤ oneBound norm := by
  have row := entry_le (fun _ => 1) member (by simp [active])
  exact Nat.le_trans (Nat.le_max_left _ _) row

theorem variable_le_oneBound (norm : CNorm) {path node} (member : (path, node) ∈ norm.toList)
    {parameter offset} (occurs : (parameter, offset) ∈ node.vars.toList) : offset + 1 ≤ oneBound norm := by
  have row := entry_le (fun _ => 1) member (by simp [active])
  have atom := Nat.le_trans (var_le (fun _ => 1) occurs) (Nat.le_max_right node.constant _)
  simpa only [oneBound, normEval, Nat.add_comm] using Nat.le_trans atom row

/-- A finite separating valuation: the selected gate is larger than all
constant/offset contributions; chosen gates are 1 and every other gate is 0. -/
def spike (bound : Nat) (chosen : List UInt64) (gate query : UInt64) : Nat :=
  if query = gate then bound + 1 else if query ∈ chosen then 1 else 0

theorem spike_pos (bound : Nat) (chosen : List UInt64) (gate query : UInt64) :
    0 < spike bound chosen gate query ↔ query = gate ∨ query ∈ chosen := by
  by_cases same : query = gate <;> by_cases member : query ∈ chosen <;> simp [spike, same, member]

theorem spike_other_le (bound : Nat) (chosen : List UInt64) (gate query : UInt64)
    (different : query ≠ gate) : spike bound chosen gate query ≤ 1 := by
  by_cases member : query ∈ chosen <;> simp [spike, different, member]

/-- A large value at the separating valuation witnesses an actual variable
marker at a path contained in the chosen gates plus the selected gate. -/
theorem absorbable_of_spike (norm : CNorm) (wellFormed : SelfGated norm)
    (chosen : List UInt64) (gate : UInt64)
    (large : oneBound norm < normEval (spike (oneBound norm) chosen gate) norm) :
    absorbable norm chosen gate = true := by
  obtain ⟨path, node, member, enabled, rowLarge⟩ :=
    entriesEval_gt (spike (oneBound norm) chosen gate) norm.toList (oneBound norm) large
  have constantBound := constant_le_oneBound norm member
  have varsLarge : oneBound norm < varsEval (spike (oneBound norm) chosen gate) node.vars.toList := by
    simp only [nodeEval] at rowLarge
    omega
  obtain ⟨parameter, offset, occurs, atomLarge⟩ :=
    varsEval_gt (spike (oneBound norm) chosen gate) node.vars.toList (oneBound norm) varsLarge
  have offsetBound := variable_le_oneBound norm member occurs
  have same : parameter = gate := by
    by_cases equal : parameter = gate
    · exact equal
    · have small := spike_other_le (oneBound norm) chosen gate parameter equal
      omega
  subst parameter
  have gateInPath := wellFormed path node member gate offset occurs
  have nonempty : path ≠ [] := by intro empty; simp [empty] at gateInPath
  unfold absorbable
  apply List.any_eq_true.mpr
  refine ⟨(path, node), member, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · simpa using nonempty
    · apply List.all_eq_true.mpr
      intro query inside
      have positive := active_member_pos (spike (oneBound norm) chosen gate) enabled inside
      simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using
        (spike_pos (oneBound norm) chosen gate query).mp positive
  · apply Array.any_eq_true'.mpr
    exact ⟨(gate, offset), Array.mem_toList_iff.mp occurs, by simp⟩

/-- Semantic growth preserves all gate-marker witnesses. This lets the
emission proof reuse the established normalization and subsumption value
theorems instead of assuming markers survive a particular mutation. -/
theorem absorbable_mono (before after : CNorm) (wellFormed : SelfGated after)
    (growth : ∀ ρ, normEval ρ before ≤ normEval ρ after) (chosen : List UInt64) (gate : UInt64)
    (accepted : absorbable before chosen gate = true) : absorbable after chosen gate = true := by
  obtain ⟨⟨path, node⟩, member, conditions⟩ := List.any_eq_true.mp accepted
  obtain ⟨pathConditions, variableHit⟩ := Bool.and_eq_true_iff.mp conditions
  obtain ⟨_, subset⟩ := Bool.and_eq_true_iff.mp pathConditions
  obtain ⟨⟨parameter, offset⟩, occurs, same⟩ := Array.any_eq_true'.mp variableHit
  have same : parameter = gate := by simpa using same
  subst parameter
  let ρ := spike (oneBound after) chosen gate
  have enabled : active ρ path = true := by
    apply List.all_eq_true.mpr
    intro query inside
    have allowed := List.all_eq_true.mp subset query inside
    have allowed : query = gate ∨ query ∈ chosen := by
      simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using allowed
    exact decide_eq_true ((spike_pos (oneBound after) chosen gate query).mpr allowed)
  have row := entry_le ρ member enabled
  have atom := Nat.le_trans (var_le ρ (Array.mem_toList_iff.mpr occurs)) (Nat.le_max_right node.constant _)
  have bound := Nat.le_trans (Nat.le_trans atom row) (growth ρ)
  apply absorbable_of_spike after wellFormed chosen gate
  change spike (oneBound after) chosen gate gate + offset ≤ normEval ρ after at bound
  simp only [spike, ↓reduceIte] at bound
  change oneBound after < normEval ρ after
  omega

/-- Any incomplete selection can add another gate with an actual absorber.
The selection may contain extra gates; this form is stable under extension. -/
def Ready (norm : CNorm) (path : CPath) : Prop :=
  ∀ chosen : List UInt64, (∃ gate ∈ path, gate ∉ chosen) →
    ∃ gate ∈ path, gate ∉ chosen ∧ absorbable norm chosen gate = true

theorem Ready.nil (norm : CNorm) : Ready norm [] := by
  intro chosen missing
  obtain ⟨gate, impossible, _⟩ := missing
  cases impossible

theorem Ready.mono {before after : CNorm} {path : CPath} (ready : Ready before path)
    (wellFormed : SelfGated after) (growth : ∀ ρ, normEval ρ before ≤ normEval ρ after) : Ready after path := by
  intro chosen missing
  obtain ⟨gate, inside, absent, available⟩ := ready chosen missing
  exact ⟨gate, inside, absent, absorbable_mono before after wellFormed growth chosen gate available⟩

/-- The actual variable insertion supplies the new gate's absorber; all old
gate choices remain available by the proved numeric growth law. -/
theorem Ready.insert {norm : CNorm} {path result : CPath} (ready : Ready norm path)
    (wellFormed : SelfGated norm) (parameter : UInt64) (offset : Nat)
    (inserted : orderedInsert parameter path = some result) :
    Ready (norm.addVar parameter offset result) result := by
  have parameterInside := (orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl)
  have afterWellFormed := wellFormed.addVar parameter offset result parameterInside
  have oldReady := ready.mono afterWellFormed (fun ρ => norm_addVar_mono ρ norm parameter offset result)
  intro chosen missing
  by_cases oldMissing : ∃ gate ∈ path, gate ∉ chosen
  · obtain ⟨gate, inside, absent, available⟩ := oldReady chosen oldMissing
    exact ⟨gate, (orderedInsert_members parameter path inserted gate).mpr (Or.inr inside), absent, available⟩
  · have oldChosen : ∀ gate ∈ path, gate ∈ chosen := by
      intro gate inside
      by_contra absent
      exact oldMissing ⟨gate, inside, absent⟩
    have newMissing : parameter ∉ chosen := by
      intro present
      obtain ⟨gate, inside, absent⟩ := missing
      rcases (orderedInsert_members parameter path inserted gate).mp inside with same | old
      · exact absent (same ▸ present)
      · exact absent (oldChosen gate old)
    refine ⟨parameter, parameterInside, newMissing, ?_⟩
    let after := norm.addVar parameter offset result
    let ρ := spike (oneBound after) chosen parameter
    have enabled : active ρ result = true := by
      apply List.all_eq_true.mpr
      intro gate inside
      have allowed : gate = parameter ∨ gate ∈ chosen := by
        rcases (orderedInsert_members parameter path inserted gate).mp inside with same | old
        · exact Or.inl same
        · exact Or.inr (oldChosen gate old)
      exact decide_eq_true ((spike_pos (oneBound after) chosen parameter gate).mpr allowed)
    have value : ρ parameter + offset ≤ normEval ρ after := by
      change ρ parameter + offset ≤ normEval ρ (norm.addVar parameter offset result)
      rw [norm_addVar_eval]
      simp only [pathValue, enabled, ↓reduceIte]
      exact Nat.le_max_right _ _
    have selected : ρ parameter = oneBound after + 1 := by simp [ρ, spike]
    rw [selected] at value
    apply absorbable_of_spike after afterWellFormed chosen parameter
    change oneBound after < normEval ρ after
    omega

theorem Ready.subsumption {norm : CNorm} {path : CPath} (ready : Ready norm path)
    (wellFormed : SelfGated norm) : Ready (subsumption norm) path :=
  ready.mono (subsumption_selfGated norm wellFormed)
    (fun ρ => Nat.le_of_eq (Ix.CompileCert.CanonUnivSubsumption.subsumption_eval ρ norm wellFormed).symm)

def AllReady (norm : CNorm) : Prop :=
  ∀ path node, (path, node) ∈ norm.toList → Ready norm path

theorem AllReady.insert {norm : CNorm} (prior : AllReady norm) (path : CPath) (node : CNode)
    (wellFormed : SelfGated (norm.insert path node))
    (growth : ∀ ρ, normEval ρ norm ≤ normEval ρ (norm.insert path node))
    (here : Ready (norm.insert path node) path) : AllReady (norm.insert path node) := by
  intro query value member
  rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
  · exact (prior query value old).mono wellFormed growth
  · cases same; exact here

theorem AllReady.addConst {norm : CNorm} (prior : AllReady norm) (wellFormed : SelfGated norm)
    (path : CPath) (offset : Nat) (here : Ready norm path) : AllReady (norm.addConst offset path) := by
  unfold CNorm.addConst
  split
  · exact prior
  · let node := { norm.findD path {} with constant := max (norm.findD path {}).constant offset }
    have afterWellFormed := wellFormed.insert path node (wellFormed.findD path)
    have growth (ρ : UInt64 → Nat) : normEval ρ norm ≤ normEval ρ (norm.insert path node) := by
      rw [norm_merge_eval ρ norm path node offset (by simp only [node, nodeEval]; omega)]
      exact Nat.le_max_left _ _
    exact prior.insert path node afterWellFormed growth (here.mono afterWellFormed growth)

theorem AllReady.addVar {norm : CNorm} (prior : AllReady norm) (wellFormed : SelfGated norm)
    (path : CPath) (parameter : UInt64) (offset : Nat) (inside : parameter ∈ path)
    (here : Ready (norm.addVar parameter offset path) path) : AllReady (norm.addVar parameter offset path) :=
  prior.insert path _ (wellFormed.addVar parameter offset path inside)
    (fun ρ => norm_addVar_mono ρ norm parameter offset path) here

theorem subsumption_paths (norm : CNorm) :
    ∀ path node, (path, node) ∈ (subsumption norm).toList → ∃ source, (path, source) ∈ norm.toList := by
  unfold subsumption
  apply listLoop_preserves (fun current : CNorm =>
    ∀ path node, (path, node) ∈ current.toList → ∃ source, (path, source) ∈ norm.toList)
  · intro path node member; exact ⟨node, member⟩
  · intro entry entryMember current valid
    rcases entry with ⟨path, node⟩
    change ∀ query value, (query, value) ∈ (current.insert path _).toList →
      ∃ source, (query, source) ∈ norm.toList
    intro query value member
    rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
    · exact valid query value old
    · cases same; exact ⟨node, entryMember⟩

theorem AllReady.subsumption {norm : CNorm} (ready : AllReady norm) (wellFormed : SelfGated norm) :
    AllReady (Ixon.CanonUniv.subsumption norm) := by
  intro path node member
  obtain ⟨source, original⟩ := subsumption_paths norm path node member
  exact (ready path source original).subsumption wellFormed

/-- The loop's remaining list consists precisely of unchosen input gates. -/
def Remaining (context : CPath) (state : GateState) : Prop :=
  ∀ gate, gate ∈ state.2.2 ↔ gate ∈ context ∧ gate ∉ state.1

theorem Remaining.pick {context : CPath} {order remaining : List UInt64} {flag : Bool}
    (prior : Remaining context (order, flag, remaining)) (picked : UInt64) :
    Remaining context (order ++ [picked], flag, remaining.filter (· != picked)) := by
  intro gate
  simp only [List.mem_filter, bne_iff_ne, prior gate, List.mem_append, List.mem_singleton, not_or]
  constructor
  · rintro ⟨⟨inside, absent⟩, different⟩
    exact ⟨inside, absent, different⟩
  · rintro ⟨inside, absent, different⟩
    exact ⟨⟨inside, absent⟩, different⟩

theorem gateLoop_accepts (norm : CNorm) (context : CPath) (ready : Ready norm context)
    (state : GateState) (remaining : Remaining context state) (accepted : state.2.1 = true) :
    (gateLoop norm state).2.1 = true := by
  induction state using (measure (fun state : GateState => state.2.2.length)).wf.induction with
  | h state ih =>
    rcases state with ⟨order, flag, rest⟩
    rw [gateLoop_eq]
    by_cases empty : rest = []
    · subst rest
      simpa [gateStep, pure] using accepted
    · obtain ⟨gate, member⟩ := List.exists_mem_of_ne_nil rest empty
      obtain ⟨inside, absent⟩ := (remaining gate).mp member
      obtain ⟨available, inContext, unchosen, canPick⟩ := ready order ⟨gate, inside, absent⟩
      have inRest := (remaining available).mpr ⟨inContext, unchosen⟩
      cases found : rest.find? (absorbable norm order) with
      | none => exact ((List.find?_eq_none.mp found) available inRest canPick).elim
      | some picked =>
        have pickedMember := List.mem_of_find?_eq_some found
        have smaller : (rest.filter (· != picked)).length < rest.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨picked, pickedMember, by simp⟩
        have next := ih (order ++ [picked], flag, rest.filter (· != picked)) smaller
          (remaining.pick picked) accepted
        simpa [gateStep, empty, found, pure] using next

theorem Ready.gatesLeakFree {norm : CNorm} {path : CPath} (ready : Ready norm path) :
    Ixon.CanonUniv.gatesLeakFree norm path = true := by
  unfold Ixon.CanonUniv.gatesLeakFree
  rw [gateOrderChecked_eq]
  exact gateLoop_accepts norm path ready ([], true, path) (by intro gate; simp) rfl

mutual

theorem normalizeAux_ready (level : Univ) (path : CPath) (offset : Nat) (state : NState)
    (wellFormed : SelfGated state.acc) (paths : AllReady state.acc) (here : Ready state.acc path) :
    AllReady (normalizeAux level path offset state).acc := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  rw [normalizeAux]
  split
  · exact paths
  · cases level with
    | zero => exact paths.addConst wellFormed path offset here
    | succ inner => exact normalizeAux_ready inner path (offset + 1) marked wellFormed paths here
    | max left right =>
      have firstWellFormed := normalizeAux_selfGated left path offset marked wellFormed
      have firstPaths := normalizeAux_ready left path offset marked wellFormed paths here
      exact normalizeAux_ready right path offset (normalizeAux left path offset marked)
        firstWellFormed firstPaths
        (here.mono firstWellFormed (fun ρ => normalizeAux_mono ρ left path offset marked))
    | imax left right => exact normalizeImaxDispatch_ready left right path offset marked wellFormed paths here
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · have inside := orderedInsert_none_mem parameter path inserted
          have afterWellFormed := wellFormed.addVar parameter offset path inside
          exact paths.addVar wellFormed path parameter offset inside
            (here.mono afterWellFormed (fun ρ => norm_addVar_mono ρ state.acc parameter offset path))
        · exact paths
      | some result =>
        simp only [inserted]
        have firstWellFormed := wellFormed.addConst offset path
        have firstPaths := paths.addConst wellFormed path offset here
        have firstReady := here.mono firstWellFormed (fun ρ => norm_addConst_mono ρ state.acc offset path)
        exact firstPaths.addVar firstWellFormed result parameter offset
          ((orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl))
          (firstReady.insert firstWellFormed parameter offset inserted)
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_ready (first left right : Univ) (path : CPath) (offset : Nat) (state : NState)
    (wellFormed : SelfGated state.acc) (paths : AllReady state.acc) (here : Ready state.acc path) :
    AllReady (normalizeImaxMax first left right path offset state).acc := by
  rw [normalizeImaxMax]
  have firstWellFormed := normalizeImaxDispatch_selfGated first left path offset state wellFormed
  have firstPaths := normalizeImaxDispatch_ready first left path offset state wellFormed paths here
  exact normalizeImaxDispatch_ready first right path offset (normalizeImaxDispatch first left path offset state)
    firstWellFormed firstPaths
    (here.mono firstWellFormed (fun ρ => normalizeImaxDispatch_mono ρ first left path offset state))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hl := Univ.size_pos left
  all_goals have hr := Univ.size_pos right
  all_goals omega

theorem normalizeImaxImax_ready (first left right : Univ) (path : CPath) (offset : Nat) (state : NState)
    (wellFormed : SelfGated state.acc) (paths : AllReady state.acc) (here : Ready state.acc path) :
    AllReady (normalizeImaxImax first left right path offset state).acc := by
  rw [normalizeImaxImax]
  have firstWellFormed := normalizeImaxDispatch_selfGated first right path offset state wellFormed
  have firstPaths := normalizeImaxDispatch_ready first right path offset state wellFormed paths here
  exact normalizeImaxDispatch_ready left right path offset (normalizeImaxDispatch first right path offset state)
    firstWellFormed firstPaths
    (here.mono firstWellFormed (fun ρ => normalizeImaxDispatch_mono ρ first right path offset state))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hf := Univ.size_pos first
  all_goals have hl := Univ.size_pos left
  all_goals omega

theorem normalizeImaxDispatch_ready (first second : Univ) (path : CPath) (offset : Nat) (state : NState)
    (wellFormed : SelfGated state.acc) (paths : AllReady state.acc) (here : Ready state.acc path) :
    AllReady (normalizeImaxDispatch first second path offset state).acc := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  rw [normalizeImaxDispatch]
  split
  · exact paths
  · cases second with
    | zero => exact paths.addConst wellFormed path offset here
    | succ inner =>
      have firstWellFormed := normalizeAux_selfGated first path offset marked wellFormed
      have firstPaths := normalizeAux_ready first path offset marked wellFormed paths here
      exact normalizeAux_ready inner path (offset + 1) (normalizeAux first path offset marked)
        firstWellFormed firstPaths
        (here.mono firstWellFormed (fun ρ => normalizeAux_mono ρ first path offset marked))
    | max left right => exact normalizeImaxMax_ready first left right path offset marked wellFormed paths here
    | imax left right => exact normalizeImaxImax_ready first left right path offset marked wellFormed paths here
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · have inside := orderedInsert_none_mem parameter path inserted
          have afterWellFormed := wellFormed.addVar parameter offset path inside
          have afterReady := here.mono afterWellFormed (fun ρ => norm_addVar_mono ρ state.acc parameter offset path)
          exact normalizeAux_ready first path offset (marked.addVar parameter offset path)
            afterWellFormed (paths.addVar wellFormed path parameter offset inside afterReady) afterReady
        · exact normalizeAux_ready first path offset marked wellFormed paths here
      | some result =>
        simp only [inserted]
        have firstWellFormed := wellFormed.addConst offset path
        have firstPaths := paths.addConst wellFormed path offset here
        have firstReady := here.mono firstWellFormed (fun ρ => norm_addConst_mono ρ state.acc offset path)
        have inside := (orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl)
        have afterWellFormed := firstWellFormed.addVar parameter offset result inside
        have afterReady := firstReady.insert firstWellFormed parameter offset inserted
        have afterPaths := firstPaths.addVar firstWellFormed result parameter offset inside afterReady
        exact normalizeAux_ready first result offset
          ((marked.addConst offset path).addVar parameter offset result) afterWellFormed afterPaths afterReady
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

theorem initial_allReady : AllReady ((∅ : CNorm).insert [] {}) := by
  intro path node member
  change (path, node) ∈ [([], ({} : CNode))] at member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  exact Ready.nil _

theorem normalizeAux_initial_ready (level : Univ) :
    AllReady (normalizeAux level [] 0 { acc := (∅ : CNorm).insert [] {} }).acc := by
  have empty : SelfGated (∅ : CNorm) := by
    intro path node impossible
    cases impossible
  exact normalizeAux_ready level [] 0 _ (empty.insert [] {} (nodeFits_empty [])) initial_allReady (Ready.nil _)

theorem normalize_ready (level : Univ) : AllReady (normalize level) :=
  (normalizeAux_initial_ready level).subsumption (normalizeAux_initial_selfGated level)

/-- Every path produced by complete normalization receives an accepted gate
order. This covers the unstripped fallback path used by `linearize`. -/
theorem normalize_gatesLeakFree (level : Univ) (path : CPath) (node : CNode)
    (member : (path, node) ∈ (normalize level).toList) :
    gatesLeakFree (normalize level) path = true :=
  (normalize_ready level path node member).gatesLeakFree

def PathsHave (P : CPath → Prop) (table : RBTree.RBMap CPath α compare) : Prop :=
  ∀ path value, (path, value) ∈ table.toList → P path

theorem PathsHave.insert {table : RBTree.RBMap CPath α compare} {P : CPath → Prop}
    (prior : PathsHave P table) (path : CPath) (value : α) (here : P path) :
    PathsHave P (table.insert path value) := by
  intro query item member
  rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
  · exact prior query item old
  · cases same; exact here

theorem PathsHave.addConst {norm : CNorm} {P : CPath → Prop} (prior : PathsHave P norm)
    (path : CPath) (offset : Nat) (here : P path) : PathsHave P (norm.addConst offset path) := by
  unfold CNorm.addConst
  split
  · exact prior
  · exact prior.insert path _ here

theorem PathsHave.addVar {norm : CNorm} {P : CPath → Prop} (prior : PathsHave P norm)
    (path : CPath) (parameter : UInt64) (offset : Nat) (here : P path) :
    PathsHave P (norm.addVar parameter offset path) := prior.insert path _ here

theorem PathsHave.subsumption {norm : CNorm} {P : CPath → Prop} (prior : PathsHave P norm) :
    PathsHave P (Ixon.CanonUniv.subsumption norm) := by
  intro path node member
  obtain ⟨source, original⟩ := subsumption_paths norm path node member
  exact prior path source original

mutual

theorem normalizeAux_paths (P : CPath → Prop)
    (insert : ∀ parameter path result, P path → orderedInsert parameter path = some result → P result)
    (level : Univ) (path : CPath) (offset : Nat) (state : NState)
    (paths : PathsHave P state.acc) (here : P path) : PathsHave P (normalizeAux level path offset state).acc := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  rw [normalizeAux]
  split
  · exact paths
  · cases level with
    | zero => exact paths.addConst path offset here
    | succ inner => exact normalizeAux_paths P insert inner path (offset + 1) marked paths here
    | max left right =>
      exact normalizeAux_paths P insert right path offset (normalizeAux left path offset marked)
        (normalizeAux_paths P insert left path offset marked paths here) here
    | imax left right => exact normalizeImaxDispatch_paths P insert left right path offset marked paths here
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact paths.addVar path parameter offset here
        · exact paths
      | some result =>
        simp only [inserted]
        exact (paths.addConst path offset here).addVar result parameter offset (insert parameter path result here inserted)
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_paths (P : CPath → Prop)
    (insert : ∀ parameter path result, P path → orderedInsert parameter path = some result → P result)
    (first left right : Univ) (path : CPath) (offset : Nat) (state : NState)
    (paths : PathsHave P state.acc) (here : P path) : PathsHave P (normalizeImaxMax first left right path offset state).acc := by
  rw [normalizeImaxMax]
  exact normalizeImaxDispatch_paths P insert first right path offset (normalizeImaxDispatch first left path offset state)
    (normalizeImaxDispatch_paths P insert first left path offset state paths here) here
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hl := Univ.size_pos left
  all_goals have hr := Univ.size_pos right
  all_goals omega

theorem normalizeImaxImax_paths (P : CPath → Prop)
    (insert : ∀ parameter path result, P path → orderedInsert parameter path = some result → P result)
    (first left right : Univ) (path : CPath) (offset : Nat) (state : NState)
    (paths : PathsHave P state.acc) (here : P path) : PathsHave P (normalizeImaxImax first left right path offset state).acc := by
  rw [normalizeImaxImax]
  exact normalizeImaxDispatch_paths P insert left right path offset (normalizeImaxDispatch first right path offset state)
    (normalizeImaxDispatch_paths P insert first right path offset state paths here) here
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hf := Univ.size_pos first
  all_goals have hl := Univ.size_pos left
  all_goals omega

theorem normalizeImaxDispatch_paths (P : CPath → Prop)
    (insert : ∀ parameter path result, P path → orderedInsert parameter path = some result → P result)
    (first second : Univ) (path : CPath) (offset : Nat) (state : NState)
    (paths : PathsHave P state.acc) (here : P path) : PathsHave P (normalizeImaxDispatch first second path offset state).acc := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  rw [normalizeImaxDispatch]
  split
  · exact paths
  · cases second with
    | zero => exact paths.addConst path offset here
    | succ inner =>
      exact normalizeAux_paths P insert inner path (offset + 1) (normalizeAux first path offset marked)
        (normalizeAux_paths P insert first path offset marked paths here) here
    | max left right => exact normalizeImaxMax_paths P insert first left right path offset marked paths here
    | imax left right => exact normalizeImaxImax_paths P insert first left right path offset marked paths here
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact normalizeAux_paths P insert first path offset (marked.addVar parameter offset path)
            (paths.addVar path parameter offset here) here
        · exact normalizeAux_paths P insert first path offset marked paths here
      | some result =>
        simp only [inserted]
        have newPath := insert parameter path result here inserted
        exact normalizeAux_paths P insert first result offset
          ((marked.addConst offset path).addVar parameter offset result)
          ((paths.addConst path offset here).addVar result parameter offset newPath) newPath
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

theorem normalize_paths (P : CPath → Prop) (empty : P [])
    (insert : ∀ parameter path result, P path → orderedInsert parameter path = some result → P result)
    (level : Univ) : PathsHave P (normalize level) := by
  have initial : PathsHave P ((∅ : CNorm).insert [] {}) := by
    intro path node member
    change (path, node) ∈ [([], ({} : CNode))] at member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact empty
  exact (normalizeAux_paths P insert level [] 0 _ initial empty).subsumption

def StrictPath (path : CPath) : Prop := path.Pairwise (fun left right => left.toNat < right.toNat)

theorem orderedInsert_strict (parameter : UInt64) (path result : CPath)
    (ordered : StrictPath path) (inserted : orderedInsert parameter path = some result) : StrictPath result := by
  induction path generalizing result with
  | nil =>
    simp only [orderedInsert, Option.some.injEq] at inserted
    subst result
    simp [StrictPath]
  | cons head rest ih =>
    obtain ⟨headLess, tailOrdered⟩ := List.pairwise_cons.mp ordered
    simp only [orderedInsert] at inserted
    split at inserted
    · rename_i before
      cases Option.some.inj inserted
      apply List.pairwise_cons.mpr
      refine ⟨?_, ordered⟩
      intro query member
      rcases List.mem_cons.mp member with same | tail
      · subst query; exact UInt64.lt_iff_toNat_lt.mp before
      · exact Nat.lt_trans (UInt64.lt_iff_toNat_lt.mp before) (headLess query tail)
    · rename_i after
      split at inserted
      · cases inserted
      · rename_i different
        cases next : orderedInsert parameter rest with
        | none => simp [next] at inserted
        | some tail =>
          have same : head :: tail = result := by simpa [next] using inserted
          subst result
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih tail tailOrdered next⟩
          intro query member
          rcases (orderedInsert_members parameter rest next query).mp member with same | old
          · subst query
            have greater : head < parameter := by
              apply UInt64.not_le.mp
              intro reversed
              have equal := UInt64.le_antisymm reversed (UInt64.not_lt.mp after)
              exact different (beq_iff_eq.mpr equal)
            exact UInt64.lt_iff_toNat_lt.mp greater
          · exact headLess query old

theorem normalize_strictPaths (level : Univ) : PathsHave StrictPath (normalize level) :=
  normalize_paths StrictPath (by simp [StrictPath]) orderedInsert_strict level

theorem StrictPath.sorted {path : CPath} (strict : StrictPath path) : path.Pairwise (· ≤ ·) :=
  List.Pairwise.imp (fun {_left _right} smaller => UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt smaller)) strict

theorem StrictPath.nodup {path : CPath} (strict : StrictPath path) : path.Nodup :=
  List.Pairwise.imp (fun {left right} smaller same => by cases same; omega) strict

end Ix.CompileCert.CanonUnivPaths

