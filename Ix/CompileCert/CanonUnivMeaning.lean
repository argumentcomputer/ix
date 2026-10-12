import Ix.CompileCert.Translate
import Init.Internal.Order.While
import Batteries.Recycling.RBTree.Lemmas
import Ix.CompileCert.Interning
import Std.Data.HashSet.Lemmas

/-! Correctness of cached universe normalization and the production emission
guards. `normalizeAux_initial_eval` proves exact evaluation from the actual
initial state, discharging cache validity and path support. Self-gating is
established for the complete normalizer, including subsumption. The emission
lemmas account explicitly for imax gate leakage and guarded atom stripping.

Value preservation through subsumption and complete linearization remains to
be proved before these results establish the semantics of `canonUniv`. -/

namespace Ix.CompileCert.CanonUnivMeaning

open Ixon Ixon.CanonUniv

theorem pathCompare_eq : (compare : CPath → CPath → Ordering) =
    List.compareLex (compare : UInt64 → UInt64 → Ordering) := by
  funext left right
  change compareList left right = _
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head rest ih =>
    cases right with
    | nil => rfl
    | cons next tail =>
      simp only [compareList, List.compareLex]
      cases compare head next <;> simp_all

instance pathCompare_trans : Std.TransCmp (compare : CPath → CPath → Ordering) := by
  rw [pathCompare_eq]
  infer_instance

instance pathCompare_lawful : Std.LawfulEqCmp (compare : CPath → CPath → Ordering) := by
  rw [pathCompare_eq]
  infer_instance

def evalTerms (ρ : UInt64 → Nat) : List Univ → Nat
  | [] => 0
  | value :: rest => max (univEval ρ value) (evalTerms ρ rest)

theorem evalTerms_append (ρ : UInt64 → Nat) (left right : List Univ) :
    evalTerms ρ (left ++ right) = max (evalTerms ρ left) (evalTerms ρ right) := by
  induction left <;> simp_all [evalTerms, Nat.max_assoc]

theorem evalTerms_reverse (ρ : UInt64 → Nat) (terms : List Univ) :
    evalTerms ρ terms.reverse = evalTerms ρ terms := by
  induction terms <;> simp_all [evalTerms, evalTerms_append, Nat.max_comm]

theorem maxFold_eval (ρ : UInt64 → Nat) (terms : List Univ) (seed : Univ) :
    univEval ρ (terms.foldl (fun acc term => Univ.max term acc) seed) =
      max (evalTerms ρ terms) (univEval ρ seed) := by
  induction terms generalizing seed <;> simp_all [evalTerms, univEval]
  omega

theorem maxChain_eval (ρ : UInt64 → Nat) (terms : List Univ) :
    univEval ρ (maxChain terms) = evalTerms ρ terms := by
  unfold maxChain
  have reversed := evalTerms_reverse ρ terms
  cases same : terms.reverse with
  | nil => simpa [same, evalTerms, univEval] using reversed
  | cons last rest =>
    simpa [same, evalTerms, maxFold_eval, Nat.max_comm] using reversed

theorem addSuccs_eval (ρ : UInt64 → Nat) (value : Univ) (count : Nat) :
    univEval ρ (Univ.addSuccs value count) = univEval ρ value + count := by
  induction count <;> simp_all [Univ.addSuccs, univEval, Nat.add_assoc]

/-- This is the exact gate fold in `linearize`, with the outermost gate first. -/
def emitGated (order : List UInt64) (body : Univ) : Univ :=
  order.reverse.foldl (fun acc parameter => Univ.imax acc (.var parameter)) body

theorem emitGated_nil (body : Univ) : emitGated [] body = body := rfl

theorem emitGated_cons (parameter : UInt64) (rest : List UInt64) (body : Univ) :
    emitGated (parameter :: rest) body = Univ.imax (emitGated rest body) (.var parameter) := by
  simp [emitGated, List.foldl_append]

theorem emitGated_append (front back : List UInt64) (body : Univ) :
    emitGated (front ++ back) body = emitGated front (emitGated back body) := by
  simp [emitGated, List.foldl_append]

def active (ρ : UInt64 → Nat) (path : List UInt64) : Bool :=
  path.all (fun parameter => decide (0 < ρ parameter))

/-- An imax chain emits its gated body plus a precise leak independent of the
body. The production gate-order/marker rules must account for this leak. -/
theorem emitGated_eval (ρ : UInt64 → Nat) (order : List UInt64) (body : Univ) :
    univEval ρ (emitGated order body) =
      max (if active ρ order then univEval ρ body else 0)
        (univEval ρ (emitGated order .zero)) := by
  induction order with
  | nil => simp [emitGated_nil, active, univEval]
  | cons parameter rest ih =>
    rw [emitGated_cons, emitGated_cons]
    simp only [univEval, active, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    by_cases positive : 0 < ρ parameter
    · have nonzero : ρ parameter ≠ 0 := Nat.ne_of_gt positive
      simp only [nonzero, ↓reduceIte, positive, true_and]
      rw [ih]
      change max (max (if active ρ rest then univEval ρ body else 0)
        (univEval ρ (emitGated rest .zero))) (ρ parameter) =
          max (if active ρ rest then univEval ρ body else 0)
            (max (univEval ρ (emitGated rest .zero)) (ρ parameter))
      exact Nat.max_assoc _ _ _
    · have zero : ρ parameter = 0 := Nat.eq_zero_of_not_pos positive
      simp [zero]

theorem emitGated_absorbed (ρ : UInt64 → Nat) (order : List UInt64) (body : Univ)
    (ambient : Nat) (leak : univEval ρ (emitGated order .zero) ≤ ambient) :
    max ambient (univEval ρ (emitGated order body)) =
      max ambient (if active ρ order then univEval ρ body else 0) := by
  rw [emitGated_eval]
  omega

def varsEval (ρ : UInt64 → Nat) : List (UInt64 × Nat) → Nat
  | [] => 0
  | (parameter, offset) :: rest => max (ρ parameter + offset) (varsEval ρ rest)

def nodeEval (ρ : UInt64 → Nat) (node : CNode) : Nat :=
  max node.constant (varsEval ρ node.vars.toList)

theorem varsEval_append (ρ : UInt64 → Nat) (left right : List (UInt64 × Nat)) :
    varsEval ρ (left ++ right) = max (varsEval ρ left) (varsEval ρ right) := by
  induction left with
  | nil => simp [varsEval]
  | cons entry rest ih =>
    rcases entry with ⟨parameter, offset⟩
    simp [varsEval, ih, Nat.max_assoc]

theorem varsEval_insert (ρ : UInt64 → Nat) (index : Nat) (vars : List (UInt64 × Nat))
    (parameter : UInt64) (offset : Nat) (bound : index ≤ vars.length) :
    varsEval ρ (vars.insertIdx index (parameter, offset)) =
      max (varsEval ρ vars) (ρ parameter + offset) := by
  induction index generalizing vars with
  | zero => simp [varsEval, Nat.max_comm]
  | succ index ih =>
    cases vars with
    | nil => simp at bound
    | cons entry rest =>
      rcases entry with ⟨name, increment⟩
      simp only [List.insertIdx_succ_cons, varsEval, ih rest (by simpa using bound)]
      omega

theorem varsEval_setMax (ρ : UInt64 → Nat) (index : Nat) (vars : List (UInt64 × Nat))
    (parameter : UInt64) (old offset : Nat) (found : vars[index]? = some (parameter, old)) :
    varsEval ρ (vars.set index (parameter, max old offset)) =
      max (varsEval ρ vars) (ρ parameter + offset) := by
  induction index generalizing vars with
  | zero =>
    cases vars with
    | nil => simp at found
    | cons entry rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst entry
      simp only [List.set_cons_zero, varsEval]
      omega
  | succ index ih =>
    cases vars with
    | nil => simp at found
    | cons entry rest =>
      rcases entry with ⟨name, increment⟩
      simp only [List.getElem?_cons_succ] at found
      simp only [List.set_cons_succ, varsEval, ih rest found]
      omega

/-- The actual array insertion/max-merge has the intended numeric effect;
no ordering or duplicate-freedom premise is needed for this value law. -/
theorem addVar_eval (ρ : UInt64 → Nat) (node : CNode) (parameter : UInt64) (offset : Nat) :
    nodeEval ρ (node.addVar parameter offset) =
      max (nodeEval ρ node) (ρ parameter + offset) := by
  unfold CNode.addVar
  cases found : node.vars.findIdx? (fun v => parameter ≤ v.1) with
  | none =>
    simp only [nodeEval, Array.toList_push, varsEval_append, varsEval]
    omega
  | some index =>
    have bound := (Array.findIdx?_eq_some_iff_getElem.mp found).choose
    simp only [getElem!_pos node.vars index bound]
    split
    · rename_i same
      have same : node.vars[index].1 = parameter := beq_iff_eq.mp same
      have entry : node.vars.toList[index]? = some (parameter, node.vars[index].2) := by
        simpa [← same] using
          (List.getElem?_eq_some_iff.mpr ⟨by simpa using bound, rfl⟩ :
            node.vars.toList[index]? = some node.vars[index])
      simp only [nodeEval, Array.toList_set!, same, varsEval_setMax ρ index _ _ _ _ entry]
      omega
    · have fits : index ≤ node.vars.size := Nat.le_of_lt bound
      simp only [nodeEval, Array.insertIdx!, fits, ↓reduceDIte, Array.toList_insertIdx,
        varsEval_insert ρ index node.vars.toList parameter offset fits]
      omega

def entriesEval (ρ : UInt64 → Nat) : List (CPath × CNode) → Nat
  | [] => 0
  | (path, node) :: rest =>
    max (if active ρ path then nodeEval ρ node else 0) (entriesEval ρ rest)

def normEval (ρ : UInt64 → Nat) (norm : CNorm) : Nat := entriesEval ρ norm.toList

def SelfGated (norm : CNorm) : Prop :=
  ∀ path node, (path, node) ∈ norm.toList → ∀ parameter offset,
    (parameter, offset) ∈ node.vars.toList → parameter ∈ path

def NodeFits (path : CPath) (node : CNode) : Prop :=
  ∀ parameter offset, (parameter, offset) ∈ node.vars.toList → parameter ∈ path

theorem nodeFits_empty (path : CPath) : NodeFits path {} := by
  intro parameter offset impossible
  cases impossible

theorem NodeFits.addVar {path : CPath} {node : CNode} (fits : NodeFits path node)
    (parameter : UInt64) (offset : Nat) (inside : parameter ∈ path) :
    NodeFits path (node.addVar parameter offset) := by
  intro query increment member
  unfold CNode.addVar at member
  cases found : node.vars.findIdx? (fun v => parameter ≤ v.1) with
  | none =>
    simp only [found, Array.toList_push, List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
    rcases member with old | ⟨rfl, rfl⟩
    · exact fits query increment old
    · exact inside
  | some index =>
    simp only [found] at member
    split at member
    · rename_i same
      have same : node.vars[index]!.1 = parameter := beq_iff_eq.mp same
      simp only [Array.toList_set!] at member
      rcases List.mem_or_eq_of_mem_set member with old | equal
      · exact fits query increment old
      · have : query = parameter := (congrArg Prod.fst equal).trans same
        simpa [this] using inside
    · have bound := (Array.findIdx?_eq_some_iff_getElem.mp found).choose
      have within : index ≤ node.vars.size := Nat.le_of_lt bound
      simp only [Array.insertIdx!, within, ↓reduceDIte, Array.toList_insertIdx,
        List.mem_insertIdx within] at member
      rcases member with equal | old
      · cases equal; exact inside
      · exact fits query increment old

theorem SelfGated.findD {norm : CNorm} (sound : SelfGated norm) (path : CPath) :
    NodeFits path (norm.findD path {}) := by
  cases found : norm.find? path with
  | none => simpa [RBTree.RBMap.findD, found] using nodeFits_empty path
  | some node =>
    obtain ⟨key, member, same⟩ := RBTree.RBMap.find?_some.mp found
    have equal : path = key := Std.LawfulEqCmp.eq_of_compare same
    subst key
    simpa [NodeFits, RBTree.RBMap.findD, found] using sound path node member

theorem SelfGated.insert {norm : CNorm} (sound : SelfGated norm) (path : CPath)
    (node : CNode) (fits : NodeFits path node) : SelfGated (norm.insert path node) := by
  intro query value member
  rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
  · exact sound query value old
  · cases same; exact fits

theorem SelfGated.addVar {norm : CNorm} (sound : SelfGated norm) (parameter : UInt64)
    (offset : Nat) (path : CPath) (inside : parameter ∈ path) :
    SelfGated (norm.addVar parameter offset path) :=
  sound.insert path _ ((sound.findD path).addVar parameter offset inside)

theorem SelfGated.addConst {norm : CNorm} (sound : SelfGated norm) (offset : Nat) (path : CPath) :
    SelfGated (norm.addConst offset path) := by
  unfold CNorm.addConst
  split
  · exact sound
  · exact sound.insert path _ (sound.findD path)

theorem var_le (ρ : UInt64 → Nat) {vars : List (UInt64 × Nat)} {parameter offset}
    (member : (parameter, offset) ∈ vars) : ρ parameter + offset ≤ varsEval ρ vars := by
  induction vars with
  | nil => cases member
  | cons value rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst value
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem entry_le (ρ : UInt64 → Nat) {entries : List (CPath × CNode)} {path node}
    (member : (path, node) ∈ entries) (enabled : active ρ path = true) :
    nodeEval ρ node ≤ entriesEval ρ entries := by
  induction entries with
  | nil => cases member
  | cons value rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst value
      simp only [entriesEval, enabled, ↓reduceIte]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def pathValue (ρ : UInt64 → Nat) (path : CPath) (value : Nat) : Nat :=
  if active ρ path then value else 0

theorem pathValue_max (ρ : UInt64 → Nat) (path : CPath) (left right : Nat) :
    pathValue ρ path (max left right) = max (pathValue ρ path left) (pathValue ρ path right) := by
  unfold pathValue
  split <;> simp

theorem pathValue_mono (ρ : UInt64 → Nat) (path : CPath) {left right : Nat} (bound : left ≤ right) :
    pathValue ρ path left ≤ pathValue ρ path right := by
  unfold pathValue
  split <;> simp_all

theorem entriesEval_le (ρ : UInt64 → Nat) (entries : List (CPath × CNode)) (bound : Nat) :
    entriesEval ρ entries ≤ bound ↔
      ∀ path node, (path, node) ∈ entries → pathValue ρ path (nodeEval ρ node) ≤ bound := by
  induction entries with
  | nil => simp [entriesEval]
  | cons entry rest ih =>
    rcases entry with ⟨path, node⟩
    simp only [entriesEval, Nat.max_le, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ⟨head, tail⟩ query value (⟨rfl, rfl⟩ | inside)
      · exact head
      · exact tail query value inside
    · intro holds
      exact ⟨holds path node (Or.inl ⟨rfl, rfl⟩), fun query value inside =>
        holds query value (Or.inr inside)⟩

theorem normEntry_le (ρ : UInt64 → Nat) (norm : CNorm) {path node}
    (member : (path, node) ∈ norm.toList) : pathValue ρ path (nodeEval ρ node) ≤ normEval ρ norm :=
  (entriesEval_le ρ norm.toList _).mp (Nat.le_refl _) path node member

theorem findD_of_member (norm : CNorm) {path node} (member : (path, node) ∈ norm.toList) :
    norm.findD path {} = node := by
  have found : norm.find? path = some node :=
    RBTree.RBMap.find?_some.mpr ⟨path, member, Std.ReflCmp.compare_self⟩
  simp [RBTree.RBMap.findD, found]

theorem findD_value_le (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) :
    pathValue ρ path (nodeEval ρ (norm.findD path {})) ≤ normEval ρ norm := by
  cases found : norm.find? path with
  | none => simp [RBTree.RBMap.findD, found, nodeEval, varsEval, pathValue]
  | some node =>
    obtain ⟨key, member, same⟩ := RBTree.RBMap.find?_some.mp found
    have equal : path = key := Std.LawfulEqCmp.eq_of_compare same
    subst key
    simpa [RBTree.RBMap.findD, found] using normEntry_le ρ norm member

/-- A max-merge at one actual RBMap entry contributes precisely its gated
value. This uses the production comparator and the map library's proved
lookup/insertion laws. -/
theorem norm_merge_eval (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath)
    (updated : CNode) (contribution : Nat)
    (merged : nodeEval ρ updated = max (nodeEval ρ (norm.findD path {})) contribution) :
    normEval ρ (norm.insert path updated) =
      max (normEval ρ norm) (pathValue ρ path contribution) := by
  have newEntry := normEntry_le ρ (norm.insert path updated)
    (RBTree.RBMap.mem_toList_insert_self updated norm)
  have newValue : pathValue ρ path (nodeEval ρ updated) =
      max (pathValue ρ path (nodeEval ρ (norm.findD path {}))) (pathValue ρ path contribution) := by
    rw [merged, pathValue_max]
  rw [newValue] at newEntry
  apply Nat.le_antisymm
  · apply (entriesEval_le ρ (norm.insert path updated).toList _).mpr
    intro query value member
    rcases RBTree.RBMap.mem_toList_insert.mp member with ⟨old, _⟩ | same
    · exact Nat.le_trans (normEntry_le ρ norm old) (Nat.le_max_left _ _)
    · cases same
      rw [newValue]
      have bound := findD_value_le ρ norm path
      omega
  · apply Nat.max_le.mpr
    refine ⟨?_, Nat.le_trans (Nat.le_max_right _ _) newEntry⟩
    apply (entriesEval_le ρ norm.toList _).mpr
    intro query value member
    rcases RBTree.RBMap.mem_toList_insert_of_mem updated member with retained | same
    · exact normEntry_le ρ (norm.insert path updated) retained
    · have equal : path = query := Std.LawfulEqCmp.eq_of_compare same
      subst query
      rw [← findD_of_member norm member]
      exact Nat.le_trans (Nat.le_max_left _ _) newEntry

theorem norm_addVar_eval (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath)
    (parameter : UInt64) (offset : Nat) :
    normEval ρ (norm.addVar parameter offset path) =
      max (normEval ρ norm) (pathValue ρ path (ρ parameter + offset)) :=
  norm_merge_eval ρ norm path _ _ (addVar_eval ρ (norm.findD path {}) parameter offset)

/-- The constant-1 elision requires an existing positive contribution on
nonempty paths; its exact condition remains visible for normalization to prove. -/
theorem norm_addConst_eval (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath) (offset : Nat)
    (oneCovered : offset = 1 → path ≠ [] → pathValue ρ path 1 ≤ normEval ρ norm) :
    normEval ρ (norm.addConst offset path) =
      max (normEval ρ norm) (pathValue ρ path offset) := by
  unfold CNorm.addConst
  split
  · rename_i skipped
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at skipped
    rcases skipped with zero | ⟨one, nonempty⟩
    · subst offset; simp [pathValue]
    · rw [one]
      exact (Nat.max_eq_left (oneCovered one (by simpa using nonempty))).symm
  · apply norm_merge_eval
    simp only [nodeEval]
    omega

/-- Each gate already contributes its own value wherever the whole path is
active. Normalization uses this when eliding a repeated parameter or 1. -/
def Supports (norm : CNorm) (path : CPath) : Prop :=
  ∀ ρ parameter, parameter ∈ path → pathValue ρ path (ρ parameter) ≤ normEval ρ norm

theorem supports_nil (norm : CNorm) : Supports norm [] := by
  intro ρ parameter impossible
  cases impossible

theorem Supports.one {norm : CNorm} {path : CPath} (support : Supports norm path)
    (ρ : UInt64 → Nat) (nonempty : path ≠ []) : pathValue ρ path 1 ≤ normEval ρ norm := by
  by_cases enabled : active ρ path = true
  · obtain ⟨parameter, member⟩ := List.exists_mem_of_ne_nil path nonempty
    have positive : 0 < ρ parameter := by
      simpa [active] using (List.all_eq_true.mp enabled parameter member)
    have bound := support ρ parameter member
    simp only [pathValue, enabled, ↓reduceIte] at bound ⊢
    omega
  · simp [pathValue, enabled]

theorem norm_addConst_supported_eval (ρ : UInt64 → Nat) (norm : CNorm) (path : CPath)
    (offset : Nat) (support : Supports norm path) :
    normEval ρ (norm.addConst offset path) =
      max (normEval ρ norm) (pathValue ρ path offset) :=
  norm_addConst_eval ρ norm path offset (fun _ nonempty => support.one ρ nonempty)

theorem norm_addVar_mono (ρ : UInt64 → Nat) (norm : CNorm) (parameter : UInt64)
    (offset : Nat) (path : CPath) : normEval ρ norm ≤ normEval ρ (norm.addVar parameter offset path) := by
  rw [norm_addVar_eval]
  exact Nat.le_max_left _ _

theorem norm_addConst_mono (ρ : UInt64 → Nat) (norm : CNorm) (offset : Nat) (path : CPath) :
    normEval ρ norm ≤ normEval ρ (norm.addConst offset path) := by
  unfold CNorm.addConst
  split
  · exact Nat.le_refl _
  · rw [norm_merge_eval ρ norm path _ offset (by simp only [nodeEval]; omega)]
    exact Nat.le_max_left _ _

theorem norm_addConst_le (ρ : UInt64 → Nat) (norm : CNorm) (offset : Nat) (path : CPath) :
    normEval ρ (norm.addConst offset path) ≤
      max (normEval ρ norm) (pathValue ρ path offset) := by
  unfold CNorm.addConst
  split
  · exact Nat.le_max_left _ _
  · rw [norm_merge_eval ρ norm path _ offset (by simp only [nodeEval]; omega)]
    exact Nat.le_refl _

theorem Supports.mono {before after : CNorm} {path : CPath} (support : Supports before path)
    (grows : ∀ ρ, normEval ρ before ≤ normEval ρ after) : Supports after path := by
  intro ρ parameter member
  exact Nat.le_trans (support ρ parameter member) (grows ρ)

theorem orderedInsert_members (parameter : UInt64) (path : CPath) {result : CPath}
    (inserted : orderedInsert parameter path = some result) (query : UInt64) :
    query ∈ result ↔ query = parameter ∨ query ∈ path := by
  induction path generalizing result with
  | nil => simp only [orderedInsert, Option.some.injEq] at inserted; subst result; simp
  | cons head rest ih =>
    simp only [orderedInsert] at inserted
    split at inserted
    · cases Option.some.inj inserted
      simp
    · split at inserted
      · cases inserted
      · cases next : orderedInsert parameter rest with
        | none => simp [next] at inserted
        | some tail =>
          have same : head :: tail = result := by simpa [next] using inserted
          subst result
          simp only [List.mem_cons, ih next, or_left_comm]

theorem orderedInsert_none_mem (parameter : UInt64) (path : CPath)
    (present : orderedInsert parameter path = none) : parameter ∈ path := by
  induction path with
  | nil => simp [orderedInsert] at present
  | cons head rest ih =>
    simp only [orderedInsert] at present
    split at present
    · cases present
    · split at present
      · rename_i same
        have : parameter = head := beq_iff_eq.mp same
        simp [this]
      · have missing : orderedInsert parameter rest = none := by simpa using present
        exact List.mem_cons_of_mem head (ih missing)

theorem active_orderedInsert (ρ : UInt64 → Nat) (parameter : UInt64) (path : CPath)
    {result : CPath} (inserted : orderedInsert parameter path = some result) :
    active ρ result = (decide (0 < ρ parameter) && active ρ path) := by
  apply Bool.eq_iff_iff.mpr
  simp only [active, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro holds
    exact ⟨holds parameter ((orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl)),
      fun query member => holds query ((orderedInsert_members parameter path inserted query).mpr (Or.inr member))⟩
  · rintro ⟨positive, holds⟩ query member
    rcases (orderedInsert_members parameter path inserted query).mp member with same | old
    · simpa [same] using positive
    · exact holds query old

theorem active_member_pos (ρ : UInt64 → Nat) {path : CPath} (enabled : active ρ path = true)
    {parameter : UInt64} (member : parameter ∈ path) : 0 < ρ parameter := by
  simpa [active] using List.all_eq_true.mp enabled parameter member

/-- The new variable contribution establishes support for the enlarged path;
all earlier gates retain their support because insertion only increases the
normal form's value. -/
theorem Supports.insert {norm : CNorm} {path result : CPath} (support : Supports norm path)
    (parameter : UInt64) (offset : Nat) (inserted : orderedInsert parameter path = some result) :
    Supports (norm.addVar parameter offset result) result := by
  intro ρ query member
  by_cases enabled : active ρ result = true
  · have oldEnabled : active ρ path = true := by
      simp only [active, List.all_eq_true, decide_eq_true_eq] at enabled ⊢
      intro name inside
      exact enabled name ((orderedInsert_members parameter path inserted name).mpr (Or.inr inside))
    rcases (orderedInsert_members parameter path inserted query).mp member with same | old
    · subst query
      rw [norm_addVar_eval]
      simp only [pathValue, enabled, ↓reduceIte]
      omega
    · have bound := support ρ query old
      have grows := norm_addVar_mono ρ norm parameter offset result
      simp only [pathValue, oldEnabled, enabled, ↓reduceIte] at bound ⊢
      omega
  · simp [pathValue, enabled]

mutual

/-- Every actual normalizer call retains all numeric contributions already
present, including calls that return immediately from the seen cache. -/
theorem normalizeAux_mono (ρ : UInt64 → Nat) (level : Univ) (path : CPath) (offset : Nat)
    (state : NState) :
    normEval ρ state.acc ≤ normEval ρ (normalizeAux level path offset state).acc := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  rw [normalizeAux]
  split
  · exact Nat.le_refl _
  · cases level with
    | zero => exact norm_addConst_mono ρ state.acc offset path
    | succ inner => exact normalizeAux_mono ρ inner path (offset + 1) marked
    | max left right =>
      exact Nat.le_trans (normalizeAux_mono ρ left path offset marked)
        (normalizeAux_mono ρ right path offset (normalizeAux left path offset marked))
    | imax left right => exact normalizeImaxDispatch_mono ρ left right path offset marked
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact norm_addVar_mono ρ state.acc parameter offset path
        · exact Nat.le_refl _
      | some result =>
        simp only [inserted]
        exact Nat.le_trans (norm_addConst_mono ρ state.acc offset path)
          (norm_addVar_mono ρ (state.acc.addConst offset path) parameter offset result)
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_mono (ρ : UInt64 → Nat) (first left right : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ state.acc ≤ normEval ρ (normalizeImaxMax first left right path offset state).acc := by
  rw [normalizeImaxMax]
  exact Nat.le_trans (normalizeImaxDispatch_mono ρ first left path offset state)
    (normalizeImaxDispatch_mono ρ first right path offset
      (normalizeImaxDispatch first left path offset state))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hl := Univ.size_pos left
  all_goals have hr := Univ.size_pos right
  all_goals omega

theorem normalizeImaxImax_mono (ρ : UInt64 → Nat) (first left right : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ state.acc ≤ normEval ρ (normalizeImaxImax first left right path offset state).acc := by
  rw [normalizeImaxImax]
  exact Nat.le_trans (normalizeImaxDispatch_mono ρ first right path offset state)
    (normalizeImaxDispatch_mono ρ left right path offset
      (normalizeImaxDispatch first right path offset state))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hf := Univ.size_pos first
  all_goals have hl := Univ.size_pos left
  all_goals omega

theorem normalizeImaxDispatch_mono (ρ : UInt64 → Nat) (first second : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ state.acc ≤ normEval ρ (normalizeImaxDispatch first second path offset state).acc := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  rw [normalizeImaxDispatch]
  split
  · exact Nat.le_refl _
  · cases second with
    | zero => exact norm_addConst_mono ρ state.acc offset path
    | succ inner =>
      exact Nat.le_trans (normalizeAux_mono ρ first path offset marked)
        (normalizeAux_mono ρ inner path (offset + 1) (normalizeAux first path offset marked))
    | max left right => exact normalizeImaxMax_mono ρ first left right path offset marked
    | imax left right => exact normalizeImaxImax_mono ρ first left right path offset marked
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact Nat.le_trans (norm_addVar_mono ρ state.acc parameter offset path)
            (normalizeAux_mono ρ first path offset (marked.addVar parameter offset path))
        · exact normalizeAux_mono ρ first path offset marked
      | some result =>
        simp only [inserted]
        exact Nat.le_trans (norm_addConst_mono ρ state.acc offset path)
          (Nat.le_trans (norm_addVar_mono ρ (state.acc.addConst offset path) parameter offset result)
            (normalizeAux_mono ρ first result offset ((marked.addConst offset path).addVar parameter offset result)))
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

mutual

/-- Upper value bound for the actual memoized normalizer. Arbitrary seen
entries may omit contributions, but cannot invent a larger one. -/
theorem normalizeAux_le (ρ : UInt64 → Nat) (level : Univ) (path : CPath) (offset : Nat)
    (state : NState) : normEval ρ (normalizeAux level path offset state).acc ≤
      max (normEval ρ state.acc) (pathValue ρ path (univEval ρ level + offset)) := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  rw [normalizeAux]
  split
  · exact Nat.le_max_left _ _
  · cases level with
    | zero => simpa only [NState.addConst, univEval, Nat.zero_add] using norm_addConst_le ρ state.acc offset path
    | succ inner =>
      simpa only [marked, univEval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        normalizeAux_le ρ inner path (offset + 1) marked
    | max left right =>
      have first := normalizeAux_le ρ left path offset marked
      have second := normalizeAux_le ρ right path offset (normalizeAux left path offset marked)
      dsimp only [marked] at first second
      simp only [univEval, pathValue] at first second ⊢
      by_cases enabled : active ρ path = true <;> simp [enabled] at * <;> omega
    | imax left right => exact normalizeImaxDispatch_le ρ left right path offset marked
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact Nat.le_of_eq (norm_addVar_eval ρ state.acc path parameter offset)
        · exact Nat.le_max_left _ _
      | some result =>
        simp only [inserted]
        change normEval ρ ((state.acc.addConst offset path).addVar parameter offset result) ≤ _
        rw [norm_addVar_eval]
        have first := norm_addConst_le ρ state.acc offset path
        simp only [univEval, pathValue, active_orderedInsert ρ parameter path inserted] at first ⊢
        by_cases enabled : active ρ path = true <;>
          by_cases positive : 0 < ρ parameter <;> simp [enabled, positive] at * <;> omega
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_le (ρ : UInt64 → Nat) (first left right : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ (normalizeImaxMax first left right path offset state).acc ≤
      max (normEval ρ state.acc) (pathValue ρ path (univEval ρ (.imax first (.max left right)) + offset)) := by
  rw [normalizeImaxMax]
  have one := normalizeImaxDispatch_le ρ first left path offset state
  have two := normalizeImaxDispatch_le ρ first right path offset
    (normalizeImaxDispatch first left path offset state)
  simp only [univEval, pathValue] at one two ⊢
  by_cases enabled : active ρ path = true <;>
    by_cases zeroLeft : univEval ρ left = 0 <;> by_cases zeroRight : univEval ρ right = 0 <;>
      simp [enabled, zeroLeft, zeroRight] at * <;> omega
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hl := Univ.size_pos left
  all_goals have hr := Univ.size_pos right
  all_goals omega

theorem normalizeImaxImax_le (ρ : UInt64 → Nat) (first left right : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ (normalizeImaxImax first left right path offset state).acc ≤
      max (normEval ρ state.acc) (pathValue ρ path (univEval ρ (.imax first (.imax left right)) + offset)) := by
  rw [normalizeImaxImax]
  have one := normalizeImaxDispatch_le ρ first right path offset state
  have two := normalizeImaxDispatch_le ρ left right path offset
    (normalizeImaxDispatch first right path offset state)
  simp only [univEval, pathValue] at one two ⊢
  by_cases enabled : active ρ path = true <;> by_cases zeroRight : univEval ρ right = 0 <;>
    simp [enabled, zeroRight] at * <;> omega
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hf := Univ.size_pos first
  all_goals have hl := Univ.size_pos left
  all_goals omega

theorem normalizeImaxDispatch_le (ρ : UInt64 → Nat) (first second : Univ)
    (path : CPath) (offset : Nat) (state : NState) :
    normEval ρ (normalizeImaxDispatch first second path offset state).acc ≤
      max (normEval ρ state.acc) (pathValue ρ path (univEval ρ (.imax first second) + offset)) := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  rw [normalizeImaxDispatch]
  split
  · exact Nat.le_max_left _ _
  · cases second with
    | zero => simpa only [NState.addConst, univEval, ↓reduceIte, Nat.zero_add] using norm_addConst_le ρ state.acc offset path
    | succ inner =>
      have one := normalizeAux_le ρ first path offset marked
      have two := normalizeAux_le ρ inner path (offset + 1) (normalizeAux first path offset marked)
      dsimp only [marked] at one two
      simp only [univEval, pathValue] at one two ⊢
      by_cases enabled : active ρ path = true <;> simp [enabled] at * <;> omega
    | max left right => exact normalizeImaxMax_le ρ first left right path offset marked
    | imax left right => exact normalizeImaxImax_le ρ first left right path offset marked
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        have member := orderedInsert_none_mem parameter path inserted
        split
        · have child := normalizeAux_le ρ first path offset (marked.addVar parameter offset path)
          dsimp only [NState.addVar, marked] at child ⊢
          rw [norm_addVar_eval] at child
          simp only [univEval, pathValue] at child ⊢
          by_cases enabled : active ρ path = true
          · have positive := active_member_pos ρ enabled member
            simp [enabled, Nat.ne_of_gt positive] at *
            omega
          · simp [enabled] at *; omega
        · have child := normalizeAux_le ρ first path offset marked
          dsimp only [marked] at child
          simp only [univEval, pathValue] at child ⊢
          by_cases enabled : active ρ path = true
          · have positive := active_member_pos ρ enabled member
            simp [enabled, Nat.ne_of_gt positive] at *
            omega
          · simp [enabled] at *; omega
      | some result =>
        simp only [inserted]
        have added := norm_addConst_le ρ state.acc offset path
        have child := normalizeAux_le ρ first result offset
          ((marked.addConst offset path).addVar parameter offset result)
        dsimp only [NState.addConst, NState.addVar, marked] at child ⊢
        rw [norm_addVar_eval] at child
        simp only [univEval, pathValue, active_orderedInsert ρ parameter path inserted] at child added ⊢
        by_cases enabled : active ρ path = true <;>
          by_cases zero : ρ parameter = 0 <;> simp [enabled, zero, Nat.pos_iff_ne_zero] at * <;> omega
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

theorem initial_norm_eval (ρ : UInt64 → Nat) : normEval ρ ((∅ : CNorm).insert [] {}) = 0 := rfl

theorem normalizeAux_initial_le (ρ : UInt64 → Nat) (source : Univ) :
    normEval ρ (normalizeAux source [] 0 { acc := (∅ : CNorm).insert [] {} }).acc ≤ univEval ρ source := by
  simpa [pathValue, active, initial_norm_eval] using
    normalizeAux_le ρ source [] 0 { acc := (∅ : CNorm).insert [] {} }

abbrev AuxKey := Univ × CPath × Nat
abbrev DispatchKey := Univ × Univ × CPath × Nat

def auxRank (key : AuxKey) : Nat := 3 * key.1.size
def dispatchRank (key : DispatchKey) : Nat := 3 * (key.1.size + key.2.1.size) + 2

/-- Newly marked calls are bounded by the current well-founded rank. This
distinguishes an in-progress parent's marker from completed smaller calls. -/
def NewWithin (before after : NState) (limit : Nat) : Prop :=
  (∀ key, after.seenAux.contains key = true → before.seenAux.contains key = true ∨ auxRank key ≤ limit) ∧
  (∀ key, after.seenDispatch.contains key = true → before.seenDispatch.contains key = true ∨ dispatchRank key ≤ limit)

theorem NewWithin.refl (state : NState) (limit : Nat) : NewWithin state state limit :=
  ⟨fun _ member => Or.inl member, fun _ member => Or.inl member⟩

theorem NewWithin.trans {first middle last : NState} {limit : Nat}
    (early : NewWithin first middle limit) (later : NewWithin middle last limit) :
    NewWithin first last limit := by
  constructor
  · intro key member
    rcases later.1 key member with old | bound
    · exact early.1 key old
    · exact Or.inr bound
  · intro key member
    rcases later.2 key member with old | bound
    · exact early.2 key old
    · exact Or.inr bound

theorem NewWithin.mono {before after : NState} {small large : Nat}
    (growth : NewWithin before after small) (bound : small ≤ large) : NewWithin before after large := by
  constructor
  · intro key member
    exact (growth.1 key member).imp_right (fun small => Nat.le_trans small bound)
  · intro key member
    exact (growth.2 key member).imp_right (fun small => Nat.le_trans small bound)

theorem NewWithin.markAux (state : NState) (key : AuxKey) (limit : Nat) (bound : auxRank key ≤ limit) :
    NewWithin state { state with seenAux := state.seenAux.insert key } limit := by
  constructor
  · intro query member
    have cases : key = query ∨ state.seenAux.contains query = true := by
      simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using member
    rcases cases with same | old
    · subst query; exact Or.inr bound
    · exact Or.inl old
  · intro query member; exact Or.inl member

theorem NewWithin.markDispatch (state : NState) (key : DispatchKey) (limit : Nat)
    (bound : dispatchRank key ≤ limit) :
    NewWithin state { state with seenDispatch := state.seenDispatch.insert key } limit := by
  constructor
  · intro query member; exact Or.inl member
  · intro query member
    have cases : key = query ∨ state.seenDispatch.contains query = true := by
      simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using member
    rcases cases with same | old
    · subst query; exact Or.inr bound
    · exact Or.inl old

mutual

theorem normalizeAux_newWithin (level : Univ) (path : CPath) (offset : Nat) (state : NState) :
    NewWithin state (normalizeAux level path offset state) (3 * level.size) := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  have mark := NewWithin.markAux state (level, path, offset) (3 * level.size) (Nat.le_refl _)
  rw [normalizeAux]
  split
  · exact NewWithin.refl _ _
  · cases level with
    | zero => exact mark
    | succ inner =>
      exact mark.trans ((normalizeAux_newWithin inner path (offset + 1) marked).mono (by simp [Univ.size]; omega))
    | max left right =>
      exact (mark.trans ((normalizeAux_newWithin left path offset marked).mono (by simp [Univ.size]; omega))).trans
        ((normalizeAux_newWithin right path offset (normalizeAux left path offset marked)).mono (by simp [Univ.size]; omega))
    | imax left right =>
      exact mark.trans ((normalizeImaxDispatch_newWithin left right path offset marked).mono (by simp [Univ.size]; omega))
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none => simp only [inserted]; split <;> exact mark
      | some _ => simp only [inserted]; exact mark
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_newWithin (first left right : Univ) (path : CPath) (offset : Nat) (state : NState) :
    NewWithin state (normalizeImaxMax first left right path offset state)
      (3 * (first.size + left.size + right.size) + 1) := by
  rw [normalizeImaxMax]
  have hl := Univ.size_pos left
  have hr := Univ.size_pos right
  exact ((normalizeImaxDispatch_newWithin first left path offset state).mono (by omega)).trans
    ((normalizeImaxDispatch_newWithin first right path offset
      (normalizeImaxDispatch first left path offset state)).mono (by omega))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by all_goals omega

theorem normalizeImaxImax_newWithin (first left right : Univ) (path : CPath) (offset : Nat) (state : NState) :
    NewWithin state (normalizeImaxImax first left right path offset state)
      (3 * (first.size + left.size + right.size) + 1) := by
  rw [normalizeImaxImax]
  have hf := Univ.size_pos first
  have hl := Univ.size_pos left
  exact ((normalizeImaxDispatch_newWithin first right path offset state).mono (by omega)).trans
    ((normalizeImaxDispatch_newWithin left right path offset
      (normalizeImaxDispatch first right path offset state)).mono (by omega))
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by all_goals omega

theorem normalizeImaxDispatch_newWithin (first second : Univ) (path : CPath) (offset : Nat) (state : NState) :
    NewWithin state (normalizeImaxDispatch first second path offset state) (3 * (first.size + second.size) + 2) := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  have mark := NewWithin.markDispatch state (first, second, path, offset)
    (3 * (first.size + second.size) + 2) (Nat.le_refl _)
  rw [normalizeImaxDispatch]
  split
  · exact NewWithin.refl _ _
  · cases second with
    | zero => exact mark
    | succ inner =>
      exact (mark.trans ((normalizeAux_newWithin first path offset marked).mono (by simp [Univ.size]; omega))).trans
        ((normalizeAux_newWithin inner path (offset + 1) (normalizeAux first path offset marked)).mono
          (by simp [Univ.size]; omega))
    | max left right =>
      exact mark.trans ((normalizeImaxMax_newWithin first left right path offset marked).mono (by simp [Univ.size]; omega))
    | imax left right =>
      exact mark.trans ((normalizeImaxImax_newWithin first left right path offset marked).mono (by simp [Univ.size]; omega))
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact mark.trans ((normalizeAux_newWithin first path offset (marked.addVar parameter offset path)).mono
            (by simp [Univ.size]; omega))
        · exact mark.trans ((normalizeAux_newWithin first path offset marked).mono (by simp [Univ.size]; omega))
      | some result =>
        simp only [inserted]
        exact mark.trans ((normalizeAux_newWithin first result offset
          ((marked.addConst offset path).addVar parameter offset result)).mono (by simp [Univ.size]; omega))
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

def auxValue (ρ : UInt64 → Nat) (key : AuxKey) : Nat :=
  pathValue ρ key.2.1 (univEval ρ key.1 + key.2.2)

def dispatchValue (ρ : UInt64 → Nat) (key : DispatchKey) : Nat :=
  pathValue ρ key.2.2.1 (univEval ρ (.imax key.1 key.2.1) + key.2.2.2)

/-- Completed seen entries below a rank threshold already contribute their
requested value. Larger entries may be in-progress ancestors. -/
def SeenSound (ρ : UInt64 → Nat) (limit : Nat) (state : NState) : Prop :=
  (∀ key, auxRank key < limit → state.seenAux.contains key = true →
    auxValue ρ key ≤ normEval ρ state.acc) ∧
  (∀ key, dispatchRank key < limit → state.seenDispatch.contains key = true →
    dispatchValue ρ key ≤ normEval ρ state.acc)

theorem SeenSound.empty (ρ : UInt64 → Nat) (limit : Nat) (acc : CNorm) :
    SeenSound ρ limit { acc } := by
  constructor <;> intro key _ member <;> simp at member

theorem SeenSound.lower {ρ : UInt64 → Nat} {small large : Nat} {state : NState}
    (valid : SeenSound ρ large state) (bound : small ≤ large) : SeenSound ρ small state :=
  ⟨fun key rank member => valid.1 key (Nat.lt_of_lt_of_le rank bound) member,
    fun key rank member => valid.2 key (Nat.lt_of_lt_of_le rank bound) member⟩

theorem SeenSound.acc {ρ : UInt64 → Nat} {limit : Nat} {state : NState}
    (valid : SeenSound ρ limit state) (acc : CNorm) (growth : normEval ρ state.acc ≤ normEval ρ acc) :
    SeenSound ρ limit { state with acc } :=
  ⟨fun key rank member => Nat.le_trans (valid.1 key rank member) growth,
    fun key rank member => Nat.le_trans (valid.2 key rank member) growth⟩

theorem SeenSound.lift {ρ : UInt64 → Nat} {limit fresh : Nat} {before after : NState}
    (prior : SeenSound ρ limit before) (new : SeenSound ρ (fresh + 1) after)
    (marked : NewWithin before after fresh) (growth : normEval ρ before.acc ≤ normEval ρ after.acc) :
    SeenSound ρ limit after := by
  constructor
  · intro key rank member
    rcases marked.1 key member with old | small
    · exact Nat.le_trans (prior.1 key rank old) growth
    · exact new.1 key (by omega) member
  · intro key rank member
    rcases marked.2 key member with old | small
    · exact Nat.le_trans (prior.2 key rank old) growth
    · exact new.2 key (by omega) member

theorem SeenSound.markAux_below {ρ : UInt64 → Nat} {limit : Nat} {state : NState}
    (valid : SeenSound ρ limit state) (key : AuxKey) (larger : limit ≤ auxRank key) :
    SeenSound ρ limit { state with seenAux := state.seenAux.insert key } := by
  constructor
  · intro query rank member
    have alternatives : key = query ∨ state.seenAux.contains query = true := by
      simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using member
    rcases alternatives with same | old
    · subst query; omega
    · exact valid.1 query rank old
  · exact valid.2

theorem SeenSound.markDispatch_below {ρ : UInt64 → Nat} {limit : Nat} {state : NState}
    (valid : SeenSound ρ limit state) (key : DispatchKey) (larger : limit ≤ dispatchRank key) :
    SeenSound ρ limit { state with seenDispatch := state.seenDispatch.insert key } := by
  constructor
  · exact valid.1
  · intro query rank member
    have alternatives : key = query ∨ state.seenDispatch.contains query = true := by
      simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using member
    rcases alternatives with same | old
    · subst query; omega
    · exact valid.2 query rank old

theorem auxRank_pos (key : AuxKey) : 0 < auxRank key := by
  have positive := Univ.size_pos key.1
  unfold auxRank
  omega

theorem dispatchRank_pos (key : DispatchKey) : 0 < dispatchRank key := by
  unfold dispatchRank
  omega

theorem SeenSound.completeAux {ρ : UInt64 → Nat} {before after : NState} (key : AuxKey)
    (prior : SeenSound ρ (auxRank key + 1) before)
    (small : SeenSound ρ (auxRank key) after)
    (fresh : NewWithin { before with seenAux := before.seenAux.insert key } after (auxRank key - 1))
    (growth : normEval ρ before.acc ≤ normEval ρ after.acc)
    (value : auxValue ρ key ≤ normEval ρ after.acc) :
    SeenSound ρ (auxRank key + 1) after := by
  have positive := auxRank_pos key
  constructor
  · intro query rank member
    rcases fresh.1 query member with marked | smaller
    · have alternatives : key = query ∨ before.seenAux.contains query = true := by
        simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using marked
      rcases alternatives with same | old
      · subst query; exact value
      · exact Nat.le_trans (prior.1 query rank old) growth
    · exact small.1 query (by omega) member
  · intro query rank member
    rcases fresh.2 query member with old | smaller
    · exact Nat.le_trans (prior.2 query rank old) growth
    · exact small.2 query (by omega) member

theorem SeenSound.completeDispatch {ρ : UInt64 → Nat} {before after : NState} (key : DispatchKey)
    (prior : SeenSound ρ (dispatchRank key + 1) before)
    (small : SeenSound ρ (dispatchRank key) after)
    (fresh : NewWithin { before with seenDispatch := before.seenDispatch.insert key } after (dispatchRank key - 1))
    (growth : normEval ρ before.acc ≤ normEval ρ after.acc)
    (value : dispatchValue ρ key ≤ normEval ρ after.acc) :
    SeenSound ρ (dispatchRank key + 1) after := by
  have positive := dispatchRank_pos key
  constructor
  · intro query rank member
    rcases fresh.1 query member with old | smaller
    · exact Nat.le_trans (prior.1 query rank old) growth
    · exact small.1 query (by omega) member
  · intro query rank member
    rcases fresh.2 query member with marked | smaller
    · have alternatives : key = query ∨ before.seenDispatch.contains query = true := by
        simpa only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using marked
      rcases alternatives with same | old
      · subst query; exact value
      · exact Nat.le_trans (prior.2 query rank old) growth
    · exact small.2 query (by omega) member

inductive NormalizeCall where
  | aux (level : Univ)
  | dispatch (first second : Univ)

def callRank : NormalizeCall → Nat
  | .aux level => 3 * level.size
  | .dispatch first second => 3 * (first.size + second.size) + 2

def callRun (call : NormalizeCall) (path : CPath) (offset : Nat) (state : NState) : NState :=
  match call with
  | .aux level => normalizeAux level path offset state
  | .dispatch first second => normalizeImaxDispatch first second path offset state

def callValue (ρ : UInt64 → Nat) : NormalizeCall → Nat
  | .aux level => univEval ρ level
  | .dispatch first second => univEval ρ (.imax first second)

theorem call_lower (call : NormalizeCall) :
    ∀ (ρ : UInt64 → Nat) (path : CPath) (offset : Nat) (state : NState),
      Supports state.acc path → SeenSound ρ (callRank call + 1) state →
      pathValue ρ path (callValue ρ call + offset) ≤ normEval ρ (callRun call path offset state).acc ∧
        SeenSound ρ (callRank call + 1) (callRun call path offset state) := by
  induction call using (measure callRank).wf.induction with
  | h call ih =>
    have normalizeAux_lower (ρ : UInt64 → Nat) (level : Univ) (path : CPath) (offset : Nat)
        (state : NState) (support : Supports state.acc path)
        (cache : SeenSound ρ (3 * level.size + 1) state)
        (smaller : 3 * level.size < callRank call := by simp_all only [callRank, Univ.size]; omega) :
        pathValue ρ path (univEval ρ level + offset) ≤ normEval ρ (normalizeAux level path offset state).acc ∧
          SeenSound ρ (3 * level.size + 1) (normalizeAux level path offset state) :=
      ih (.aux level) smaller ρ path offset state support cache
    have normalizeImaxDispatch_lower (ρ : UInt64 → Nat) (first second : Univ)
        (path : CPath) (offset : Nat) (state : NState) (support : Supports state.acc path)
        (cache : SeenSound ρ (3 * (first.size + second.size) + 3) state)
        (smaller : 3 * (first.size + second.size) + 2 < callRank call :=
          by simp_all only [callRank, Univ.size]; omega) :
        pathValue ρ path (univEval ρ (.imax first second) + offset) ≤
            normEval ρ (normalizeImaxDispatch first second path offset state).acc ∧
          SeenSound ρ (3 * (first.size + second.size) + 3)
            (normalizeImaxDispatch first second path offset state) :=
      ih (.dispatch first second) smaller ρ path offset state support cache
    cases call with
    | aux level =>
      intro ρ path offset state support cache
      change SeenSound ρ (3 * level.size + 1) state at cache
      change pathValue ρ path (univEval ρ level + offset) ≤ normEval ρ (normalizeAux level path offset state).acc ∧
        SeenSound ρ (3 * level.size + 1) (normalizeAux level path offset state)
      by_cases hit : state.seenAux.contains (level, path, offset) = true
      · rw [normalizeAux, ite_eq_left hit]
        exact ⟨cache.1 (level, path, offset) (by simp [auxRank]) hit, cache⟩
      · let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
        have below : SeenSound ρ (3 * level.size) marked :=
          (cache.lower (by omega)).markAux_below (level, path, offset) (Nat.le_refl _)
        have settled :
            pathValue ρ path (univEval ρ level + offset) ≤ normEval ρ (normalizeAux level path offset state).acc ∧
            SeenSound ρ (3 * level.size) (normalizeAux level path offset state) ∧
            NewWithin marked (normalizeAux level path offset state) (3 * level.size - 1) := by
          generalize ran : normalizeAux level path offset state = after
          rw [normalizeAux, ite_eq_right hit] at ran
          cases level with
          | zero =>
            dsimp only at ran
            subst after
            have value := norm_addConst_supported_eval ρ state.acc path offset support
            refine ⟨?_, below.acc _ (norm_addConst_mono ρ state.acc offset path), NewWithin.refl marked _⟩
            change pathValue ρ path (0 + offset) ≤ normEval ρ (state.acc.addConst offset path)
            rw [value]
            simpa using Nat.le_max_right (normEval ρ state.acc) (pathValue ρ path offset)
          | succ inner =>
            dsimp only at ran
            subst after
            have child := normalizeAux_lower ρ inner path (offset + 1) marked support
              (below.lower (by simp [Univ.size]; omega))
            have fresh := normalizeAux_newWithin inner path (offset + 1) marked
            refine ⟨?_, below.lift child.2 fresh (normalizeAux_mono ρ inner path (offset + 1) marked),
              fresh.mono (by simp [Univ.size]; omega)⟩
            simpa only [univEval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using child.1
          | max left right =>
            dsimp only at ran
            subst after
            have one := normalizeAux_lower ρ left path offset marked support
              (below.lower (by simp [Univ.size]; omega))
            have freshOne := normalizeAux_newWithin left path offset marked
            have firstCache := below.lift one.2 freshOne (normalizeAux_mono ρ left path offset marked)
            have two := normalizeAux_lower ρ right path offset (normalizeAux left path offset marked)
              (support.mono (fun ρ => normalizeAux_mono ρ left path offset marked))
              (firstCache.lower (by simp [Univ.size]; omega))
            have freshTwo := normalizeAux_newWithin right path offset (normalizeAux left path offset marked)
            have grows := normalizeAux_mono ρ right path offset (normalizeAux left path offset marked)
            refine ⟨?_, firstCache.lift two.2 freshTwo grows,
              (freshOne.mono (by simp [Univ.size]; omega)).trans
                (freshTwo.mono (by simp [Univ.size]; omega))⟩
            have firstBound := Nat.le_trans one.1 grows
            have secondBound := two.1
            dsimp only [marked] at firstBound secondBound ⊢
            simp only [univEval, pathValue] at firstBound secondBound ⊢
            by_cases enabled : active ρ path = true
            · simp [enabled] at firstBound secondBound ⊢
              omega
            · simp [enabled]
          | imax left right =>
            dsimp only at ran
            subst after
            have child := normalizeImaxDispatch_lower ρ left right path offset marked support
              (below.lower (by simp [Univ.size]; omega))
            have fresh := normalizeImaxDispatch_newWithin left right path offset marked
            exact ⟨child.1, below.lift child.2 fresh (normalizeImaxDispatch_mono ρ left right path offset marked),
              fresh.mono (by simp [Univ.size]; omega)⟩
          | var parameter =>
            cases inserted : orderedInsert parameter path with
            | none =>
              simp only [inserted] at ran
              split at ran
              · subst after
                refine ⟨?_, below.acc _ (norm_addVar_mono ρ state.acc parameter offset path), NewWithin.refl marked _⟩
                change pathValue ρ path (ρ parameter + offset) ≤ normEval ρ (state.acc.addVar parameter offset path)
                rw [norm_addVar_eval]
                exact Nat.le_max_right _ _
              · rename_i zero
                have zero : offset = 0 := by simpa using zero
                subst after
                refine ⟨?_, below, NewWithin.refl marked _⟩
                simpa [univEval, zero] using support ρ parameter (orderedInsert_none_mem parameter path inserted)
            | some result =>
              simp only [inserted] at ran
              subst after
              have grows := Nat.le_trans (norm_addConst_mono ρ state.acc offset path)
                (norm_addVar_mono ρ (state.acc.addConst offset path) parameter offset result)
              refine ⟨?_, below.acc _ grows, NewWithin.refl marked _⟩
              change pathValue ρ path (ρ parameter + offset) ≤
                normEval ρ ((state.acc.addConst offset path).addVar parameter offset result)
              rw [norm_addVar_eval, norm_addConst_supported_eval ρ state.acc path offset support]
              simp only [pathValue, active_orderedInsert ρ parameter path inserted]
              by_cases enabled : active ρ path = true <;> by_cases positive : 0 < ρ parameter <;>
                simp [enabled, positive] <;> omega
        exact ⟨settled.1, SeenSound.completeAux (level, path, offset) cache settled.2.1 settled.2.2
          (normalizeAux_mono ρ level path offset state) settled.1⟩
    
    | dispatch first second =>
      intro ρ path offset state support cache
      change SeenSound ρ (3 * (first.size + second.size) + 3) state at cache
      change pathValue ρ path (univEval ρ (.imax first second) + offset) ≤
          normEval ρ (normalizeImaxDispatch first second path offset state).acc ∧
        SeenSound ρ (3 * (first.size + second.size) + 3)
          (normalizeImaxDispatch first second path offset state)
      by_cases hit : state.seenDispatch.contains (first, second, path, offset) = true
      · rw [normalizeImaxDispatch, ite_eq_left hit]
        exact ⟨cache.2 (first, second, path, offset) (by simp [dispatchRank]) hit, cache⟩
      · let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
        have below : SeenSound ρ (3 * (first.size + second.size) + 2) marked :=
          (cache.lower (by omega)).markDispatch_below (first, second, path, offset) (Nat.le_refl _)
        have settled :
            pathValue ρ path (univEval ρ (.imax first second) + offset) ≤
              normEval ρ (normalizeImaxDispatch first second path offset state).acc ∧
            SeenSound ρ (3 * (first.size + second.size) + 2)
              (normalizeImaxDispatch first second path offset state) ∧
            NewWithin marked (normalizeImaxDispatch first second path offset state)
              (3 * (first.size + second.size) + 2 - 1) := by
          generalize ran : normalizeImaxDispatch first second path offset state = after
          rw [normalizeImaxDispatch, ite_eq_right hit] at ran
          cases second with
          | zero =>
            dsimp only at ran
            subst after
            have value := norm_addConst_supported_eval ρ state.acc path offset support
            refine ⟨?_, below.acc _ (norm_addConst_mono ρ state.acc offset path), NewWithin.refl marked _⟩
            simp only [univEval, ↓reduceIte, Nat.zero_add]
            change pathValue ρ path offset ≤ normEval ρ (state.acc.addConst offset path)
            rw [value]
            exact Nat.le_max_right _ _
          | succ inner =>
            dsimp only at ran
            subst after
            have one := normalizeAux_lower ρ first path offset marked support
              (below.lower (by simp [Univ.size]; omega))
            have freshOne := normalizeAux_newWithin first path offset marked
            have firstCache := below.lift one.2 freshOne (normalizeAux_mono ρ first path offset marked)
            have two := normalizeAux_lower ρ inner path (offset + 1) (normalizeAux first path offset marked)
              (support.mono (fun ρ => normalizeAux_mono ρ first path offset marked))
              (firstCache.lower (by simp [Univ.size]; omega))
            have freshTwo := normalizeAux_newWithin inner path (offset + 1) (normalizeAux first path offset marked)
            have grows := normalizeAux_mono ρ inner path (offset + 1) (normalizeAux first path offset marked)
            refine ⟨?_, firstCache.lift two.2 freshTwo grows,
              (freshOne.mono (by simp [Univ.size]; omega)).trans
                (freshTwo.mono (by simp [Univ.size]; omega))⟩
            have firstBound := Nat.le_trans one.1 grows
            have secondBound := two.1
            dsimp only [marked] at firstBound secondBound ⊢
            simp only [univEval, pathValue] at firstBound secondBound ⊢
            by_cases enabled : active ρ path = true
            · simp [enabled] at firstBound secondBound ⊢
              omega
            · simp [enabled]
          | max left right =>
            dsimp only at ran
            rw [normalizeImaxMax] at ran
            subst after
            have one := normalizeImaxDispatch_lower ρ first left path offset marked support
              (below.lower (by simp [Univ.size]; omega))
            have freshOne := normalizeImaxDispatch_newWithin first left path offset marked
            have firstCache := below.lift one.2 freshOne (normalizeImaxDispatch_mono ρ first left path offset marked)
            have two := normalizeImaxDispatch_lower ρ first right path offset
              (normalizeImaxDispatch first left path offset marked)
              (support.mono (fun ρ => normalizeImaxDispatch_mono ρ first left path offset marked))
              (firstCache.lower (by simp [Univ.size]; omega))
            have freshTwo := normalizeImaxDispatch_newWithin first right path offset
              (normalizeImaxDispatch first left path offset marked)
            have grows := normalizeImaxDispatch_mono ρ first right path offset
              (normalizeImaxDispatch first left path offset marked)
            refine ⟨?_, firstCache.lift two.2 freshTwo grows,
              (freshOne.mono (by simp [Univ.size]; omega)).trans
                (freshTwo.mono (by simp [Univ.size]; omega))⟩
            have firstBound := Nat.le_trans one.1 grows
            have secondBound := two.1
            dsimp only [marked] at firstBound secondBound ⊢
            simp only [univEval, pathValue] at firstBound secondBound ⊢
            by_cases enabled : active ρ path = true <;> by_cases zeroLeft : univEval ρ left = 0 <;>
              by_cases zeroRight : univEval ρ right = 0 <;> simp [enabled, zeroLeft, zeroRight] at * <;> omega
          | imax left right =>
            dsimp only at ran
            rw [normalizeImaxImax] at ran
            subst after
            have one := normalizeImaxDispatch_lower ρ first right path offset marked support
              (below.lower (by simp [Univ.size]; omega))
            have freshOne := normalizeImaxDispatch_newWithin first right path offset marked
            have firstCache := below.lift one.2 freshOne (normalizeImaxDispatch_mono ρ first right path offset marked)
            have two := normalizeImaxDispatch_lower ρ left right path offset
              (normalizeImaxDispatch first right path offset marked)
              (support.mono (fun ρ => normalizeImaxDispatch_mono ρ first right path offset marked))
              (firstCache.lower (by simp [Univ.size]; omega))
            have freshTwo := normalizeImaxDispatch_newWithin left right path offset
              (normalizeImaxDispatch first right path offset marked)
            have grows := normalizeImaxDispatch_mono ρ left right path offset
              (normalizeImaxDispatch first right path offset marked)
            refine ⟨?_, firstCache.lift two.2 freshTwo grows,
              (freshOne.mono (by simp [Univ.size]; omega)).trans
                (freshTwo.mono (by simp [Univ.size]; omega))⟩
            have firstBound := Nat.le_trans one.1 grows
            have secondBound := two.1
            dsimp only [marked] at firstBound secondBound ⊢
            simp only [univEval, pathValue] at firstBound secondBound ⊢
            by_cases enabled : active ρ path = true <;> by_cases zeroRight : univEval ρ right = 0 <;>
              simp [enabled, zeroRight] at * <;> omega
          | var parameter =>
            cases inserted : orderedInsert parameter path with
            | none =>
              simp only [inserted] at ran
              have member := orderedInsert_none_mem parameter path inserted
              split at ran
              · subst after
                have prefixGrowth := norm_addVar_mono ρ state.acc parameter offset path
                have child := normalizeAux_lower ρ first path offset (marked.addVar parameter offset path)
                  (support.mono (fun ρ => norm_addVar_mono ρ state.acc parameter offset path))
                  ((below.acc _ prefixGrowth).lower (by simp [Univ.size]; omega))
                have fresh := normalizeAux_newWithin first path offset (marked.addVar parameter offset path)
                have grows := normalizeAux_mono ρ first path offset (marked.addVar parameter offset path)
                refine ⟨?_, (below.acc _ prefixGrowth).lift child.2 fresh grows,
                  fresh.mono (by simp [Univ.size]; omega)⟩
                have parameterBound : pathValue ρ path (ρ parameter + offset) ≤
                    normEval ρ (state.acc.addVar parameter offset path) := by
                  rw [norm_addVar_eval]; exact Nat.le_max_right _ _
                have parameterFinal := Nat.le_trans parameterBound grows
                have childBound := child.1
                dsimp only [marked, NState.addVar] at parameterFinal childBound ⊢
                simp only [univEval, pathValue] at parameterFinal childBound ⊢
                by_cases enabled : active ρ path = true
                · have positive := active_member_pos ρ enabled member
                  simp [enabled, Nat.ne_of_gt positive] at *; omega
                · simp [enabled] at *
              · rename_i zero
                have zero : offset = 0 := by simpa using zero
                subst after
                have child := normalizeAux_lower ρ first path offset marked support
                  (below.lower (by simp [Univ.size]; omega))
                have fresh := normalizeAux_newWithin first path offset marked
                have grows := normalizeAux_mono ρ first path offset marked
                refine ⟨?_, below.lift child.2 fresh grows, fresh.mono (by simp [Univ.size]; omega)⟩
                have parameterFinal := Nat.le_trans (support ρ parameter member) grows
                have childBound := child.1
                dsimp only [marked] at parameterFinal childBound ⊢
                simp only [univEval, pathValue, zero, Nat.add_zero] at parameterFinal childBound ⊢
                by_cases enabled : active ρ path = true
                · have positive := active_member_pos ρ enabled member
                  simp [enabled, Nat.ne_of_gt positive] at *; omega
                · simp [enabled] at *
            | some result =>
              simp only [inserted] at ran
              subst after
              let prepared := (marked.addConst offset path).addVar parameter offset result
              have prefixGrowth := Nat.le_trans (norm_addConst_mono ρ state.acc offset path)
                (norm_addVar_mono ρ (state.acc.addConst offset path) parameter offset result)
              have prefixSupport : Supports prepared.acc result :=
                (support.mono (fun ρ => norm_addConst_mono ρ state.acc offset path)).insert parameter offset inserted
              have child := normalizeAux_lower ρ first result offset prepared prefixSupport
                ((below.acc _ prefixGrowth).lower (by simp [Univ.size]; omega))
              have fresh := normalizeAux_newWithin first result offset prepared
              have grows := normalizeAux_mono ρ first result offset prepared
              refine ⟨?_, (below.acc _ prefixGrowth).lift child.2 fresh grows,
                fresh.mono (by simp [Univ.size]; omega)⟩
              have prefixValue : normEval ρ prepared.acc =
                  max (max (normEval ρ state.acc) (pathValue ρ path offset))
                    (pathValue ρ result (ρ parameter + offset)) := by
                change normEval ρ ((state.acc.addConst offset path).addVar parameter offset result) = _
                rw [norm_addVar_eval, norm_addConst_supported_eval ρ state.acc path offset support]
              have childBound := child.1
              rw [prefixValue] at grows
              dsimp only [prepared, marked, NState.addConst, NState.addVar] at grows childBound ⊢
              simp only [univEval, pathValue, active_orderedInsert ρ parameter path inserted] at grows childBound ⊢
              by_cases enabled : active ρ path = true <;> by_cases zero : ρ parameter = 0 <;>
                simp [enabled, zero, Nat.pos_iff_ne_zero] at * <;> omega
        exact ⟨settled.1, SeenSound.completeDispatch (first, second, path, offset) cache settled.2.1 settled.2.2
          (normalizeImaxDispatch_mono ρ first second path offset state) settled.1⟩
    
theorem normalizeAux_lower (ρ : UInt64 → Nat) (level : Univ) (path : CPath) (offset : Nat)
    (state : NState) (support : Supports state.acc path)
    (cache : SeenSound ρ (3 * level.size + 1) state) :
    pathValue ρ path (univEval ρ level + offset) ≤ normEval ρ (normalizeAux level path offset state).acc ∧
      SeenSound ρ (3 * level.size + 1) (normalizeAux level path offset state) :=
  call_lower (.aux level) ρ path offset state support cache

theorem normalizeImaxDispatch_lower (ρ : UInt64 → Nat) (first second : Univ)
    (path : CPath) (offset : Nat) (state : NState) (support : Supports state.acc path)
    (cache : SeenSound ρ (3 * (first.size + second.size) + 3) state) :
    pathValue ρ path (univEval ρ (.imax first second) + offset) ≤
        normEval ρ (normalizeImaxDispatch first second path offset state).acc ∧
      SeenSound ρ (3 * (first.size + second.size) + 3)
        (normalizeImaxDispatch first second path offset state) :=
  call_lower (.dispatch first second) ρ path offset state support cache

theorem normalizeAux_eval (ρ : UInt64 → Nat) (level : Univ) (path : CPath) (offset : Nat)
    (state : NState) (support : Supports state.acc path)
    (cache : SeenSound ρ (3 * level.size + 1) state) :
    normEval ρ (normalizeAux level path offset state).acc =
      max (normEval ρ state.acc) (pathValue ρ path (univEval ρ level + offset)) :=
  Nat.le_antisymm (normalizeAux_le ρ level path offset state)
    (Nat.max_le.mpr ⟨normalizeAux_mono ρ level path offset state,
      (normalizeAux_lower ρ level path offset state support cache).1⟩)

/-- Exact evaluation of the production normalization pass from its actual
initial state, without a cache-correctness or gate-support premise. Subsumption
and linearization are the remaining two stages of `canonUniv`. -/
theorem normalizeAux_initial_eval (ρ : UInt64 → Nat) (level : Univ) :
    normEval ρ (normalizeAux level [] 0 { acc := (∅ : CNorm).insert [] {} }).acc = univEval ρ level := by
  simpa [pathValue, active, initial_norm_eval] using
    normalizeAux_eval ρ level [] 0 { acc := (∅ : CNorm).insert [] {} }
      (supports_nil _) (SeenSound.empty ρ _ _)

mutual

theorem normalizeAux_selfGated (level : Univ) (path : CPath) (offset : Nat)
    (state : NState) (sound : SelfGated state.acc) :
    SelfGated (normalizeAux level path offset state).acc := by
  let marked : NState := { state with seenAux := state.seenAux.insert (level, path, offset) }
  rw [normalizeAux]
  split
  · exact sound
  · cases level with
    | zero => exact sound.addConst offset path
    | succ inner => exact normalizeAux_selfGated inner path (offset + 1) marked sound
    | max left right =>
      exact normalizeAux_selfGated right path offset (normalizeAux left path offset marked)
        (normalizeAux_selfGated left path offset marked sound)
    | imax left right => exact normalizeImaxDispatch_selfGated left right path offset marked sound
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact sound.addVar parameter offset path (orderedInsert_none_mem parameter path inserted)
        · exact sound
      | some result =>
        simp only [inserted]
        exact (sound.addConst offset path).addVar parameter offset result
          ((orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl))
termination_by 3 * level.size
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

theorem normalizeImaxMax_selfGated (first left right : Univ) (path : CPath) (offset : Nat)
    (state : NState) (sound : SelfGated state.acc) :
    SelfGated (normalizeImaxMax first left right path offset state).acc := by
  rw [normalizeImaxMax]
  exact normalizeImaxDispatch_selfGated first right path offset
    (normalizeImaxDispatch first left path offset state)
    (normalizeImaxDispatch_selfGated first left path offset state sound)
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hl := Univ.size_pos left
  all_goals have hr := Univ.size_pos right
  all_goals omega

theorem normalizeImaxImax_selfGated (first left right : Univ) (path : CPath) (offset : Nat)
    (state : NState) (sound : SelfGated state.acc) :
    SelfGated (normalizeImaxImax first left right path offset state).acc := by
  rw [normalizeImaxImax]
  exact normalizeImaxDispatch_selfGated left right path offset
    (normalizeImaxDispatch first right path offset state)
    (normalizeImaxDispatch_selfGated first right path offset state sound)
termination_by 3 * (first.size + left.size + right.size) + 1
decreasing_by
  all_goals have hf := Univ.size_pos first
  all_goals have hl := Univ.size_pos left
  all_goals omega

theorem normalizeImaxDispatch_selfGated (first second : Univ) (path : CPath) (offset : Nat)
    (state : NState) (sound : SelfGated state.acc) :
    SelfGated (normalizeImaxDispatch first second path offset state).acc := by
  let marked : NState := { state with seenDispatch := state.seenDispatch.insert (first, second, path, offset) }
  rw [normalizeImaxDispatch]
  split
  · exact sound
  · cases second with
    | zero => exact sound.addConst offset path
    | succ inner =>
      exact normalizeAux_selfGated inner path (offset + 1) (normalizeAux first path offset marked)
        (normalizeAux_selfGated first path offset marked sound)
    | max left right => exact normalizeImaxMax_selfGated first left right path offset marked sound
    | imax left right => exact normalizeImaxImax_selfGated first left right path offset marked sound
    | var parameter =>
      cases inserted : orderedInsert parameter path with
      | none =>
        simp only [inserted]
        split
        · exact normalizeAux_selfGated first path offset (marked.addVar parameter offset path)
            (sound.addVar parameter offset path (orderedInsert_none_mem parameter path inserted))
        · exact normalizeAux_selfGated first path offset marked sound
      | some result =>
        simp only [inserted]
        exact normalizeAux_selfGated first result offset
          ((marked.addConst offset path).addVar parameter offset result)
          ((sound.addConst offset path).addVar parameter offset result
            ((orderedInsert_members parameter path inserted parameter).mpr (Or.inl rfl)))
termination_by 3 * (first.size + second.size) + 2
decreasing_by
  all_goals simp [Univ.size]
  all_goals omega

end

theorem normalizeAux_initial_selfGated (level : Univ) :
    SelfGated (normalizeAux level [] 0 { acc := (∅ : CNorm).insert [] {} }).acc := by
  have empty : SelfGated (∅ : CNorm) := by
    intro path node impossible
    cases impossible
  exact normalizeAux_selfGated level [] 0 _ (empty.insert [] {} (nodeFits_empty []))

theorem subsumeVars_go_preserves (xs ys : Array (UInt64 × Nat)) (xi yi : Nat)
    (result : Array (UInt64 × Nat)) (P : UInt64 × Nat → Prop)
    (source : ∀ value ∈ xs, P value) (prior : ∀ value ∈ result, P value) :
    ∀ value ∈ subsumeVars.go xs ys xi yi result, P value := by
  rw [subsumeVars.go]
  split
  · rename_i inSource
    have pushed : ∀ value ∈ result.push xs[xi]!, P value := by
      intro value member
      rcases Array.mem_push.mp member with old | same
      · exact prior value old
      · subst value
        rw [getElem!_pos xs xi inSource]
        exact source _ (Array.getElem_mem inSource)
    split
    · intro value member
      rcases Array.mem_append.mp member with old | tail
      · exact prior value old
      · obtain ⟨index, bound, equal⟩ := Array.mem_extract_iff_getElem.mp tail
        exact source value (equal ▸ Array.getElem_mem (by omega))
    · dsimp only
      split
      · exact subsumeVars_go_preserves xs ys (xi + 1) yi _ P source pushed
      · split
        · split
          · exact subsumeVars_go_preserves xs ys (xi + 1) (yi + 1) _ P source pushed
          · exact subsumeVars_go_preserves xs ys (xi + 1) (yi + 1) _ P source prior
        · exact subsumeVars_go_preserves xs ys xi (yi + 1) result P source prior
  · exact prior
termination_by (xs.size - xi) + (ys.size - yi)
decreasing_by all_goals omega

theorem NodeFits.subsumeVars {path : CPath} {node : CNode} (fits : NodeFits path node)
    (other : Array (UInt64 × Nat)) :
    NodeFits path { node with vars := subsumeVars node.vars other } := by
  intro parameter offset member
  apply subsumeVars_go_preserves node.vars other 0 0 #[] (fun value => value.1 ∈ path)
    (fun value inside => fits value.1 value.2 (by simpa using inside))
    (by simp)
    (parameter, offset)
  exact Array.mem_toList_iff.mp member

def StepHolds (P : α → Prop) : ForInStep α → Prop
  | .done value | .yield value => P value

theorem StepHolds.choose {P : α → Prop} {condition : Prop} [Decidable condition]
    {left right : ForInStep α} (yes : StepHolds P left) (no : StepHolds P right) :
    StepHolds P (if condition then left else right) := by
  split <;> assumption

theorem listLoop_preserves (P : β → Prop) (items : List α) (initial : β)
    (body : α → β → Id (ForInStep β)) (start : P initial)
    (step : ∀ item ∈ items, ∀ state, P state → StepHolds P (body item state)) :
    P (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => exact start
  | cons item rest ih =>
    have good := step item (by simp) initial start
    cases ran : body item initial with
    | done value =>
      simpa [List.forIn_cons, ran, pure, bind, StepHolds] using good
    | yield value =>
      have next : P value := by simpa [ran, StepHolds] using good
      simpa [List.forIn_cons, ran, pure, bind] using
        ih value next (fun item member state valid => step item (by simp [member]) state valid)

theorem subsumption_selfGated (norm : CNorm) (sound : SelfGated norm) :
    SelfGated (subsumption norm) := by
  unfold subsumption
  apply listLoop_preserves
  · exact sound
  · intro entry member current valid
    rcases entry with ⟨path, node⟩
    change SelfGated (current.insert path _)
    apply valid.insert
    apply listLoop_preserves
    · exact sound path node member
    · intro entry _ currentNode fits
      rcases entry with ⟨otherPath, otherNode⟩
      with_reducible repeat' first
        | exact fits
        | exact NodeFits.subsumeVars fits _
        | apply StepHolds.choose
        | dsimp only
      all_goals
        dsimp only [pure, StepHolds]
        first | exact fits | exact NodeFits.subsumeVars fits _

theorem normalize_selfGated (level : Univ) : SelfGated (normalize level) :=
  subsumption_selfGated _ (normalizeAux_initial_selfGated level)

/-- The production coverage check bounds a stripped atom's offset wherever
the proposed shorter context is active. Self-gating is the normalizer invariant
needed by the variable-offset branch of that check. -/
theorem covered_sound (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm)
    (offset : Nat) (context : CPath) (checked : covered norm offset context = true)
    (enabled : active ρ context = true) : offset ≤ normEval ρ norm := by
  unfold covered at checked
  simp only [Bool.or_eq_true] at checked
  rcases checked with zero | checked
  · have : offset = 0 := by simpa using zero
    simp [this]
  · obtain ⟨⟨path, node⟩, member, coveredBy⟩ := List.any_eq_true.mp checked
    obtain ⟨subset, contribution⟩ := Bool.and_eq_true_iff.mp coveredBy
    have pathActive : active ρ path = true := by
      simp only [active, List.all_eq_true, decide_eq_true_eq] at enabled ⊢
      intro parameter inside
      have := List.all_eq_true.mp subset parameter inside
      exact enabled parameter (by simpa using this)
    have nodeBound := entry_le ρ member pathActive
    simp only [Bool.or_eq_true] at contribution
    rcases contribution with constant | variableHit
    · have bound : offset ≤ node.constant := by simpa using constant
      exact Nat.le_trans bound (Nat.le_trans (Nat.le_max_left _ _) nodeBound)
    · obtain ⟨⟨parameter, increment⟩, occurs, enough⟩ := Array.any_eq_true'.mp variableHit
      have inVars : (parameter, increment) ∈ node.vars.toList := by simpa using occurs
      have inPath := wellFormed path node member parameter increment inVars
      have positive : 0 < ρ parameter := by
        simpa [active] using (List.all_eq_true.mp pathActive parameter inPath)
      have bound : offset ≤ increment + 1 := by simpa using enough
      have contributionBound := Nat.le_trans (var_le ρ inVars)
        (Nat.le_trans (Nat.le_max_right node.constant _) nodeBound)
      change offset ≤ entriesEval ρ norm.toList
      omega

def absorbable (norm : CNorm) (order : List UInt64) (parameter : UInt64) : Bool :=
  norm.toList.any fun (path, node) =>
    !path.isEmpty && path.all (fun x => x == parameter || order.contains x)
      && node.vars.any (fun v => v.1 == parameter)

def GateSound (norm : CNorm) (order : List UInt64) : Prop :=
  ∀ ρ, univEval ρ (emitGated order .zero) ≤ normEval ρ norm

theorem gateSound_nil (norm : CNorm) : GateSound norm [] := by
  intro ρ; simp [emitGated_nil, univEval]

theorem gateSound_append {norm : CNorm} {order : List UInt64} (sound : GateSound norm order)
    (parameter : UInt64) (found : absorbable norm order parameter = true) :
    GateSound norm (order ++ [parameter]) := by
  intro ρ
  rw [emitGated_append, emitGated_eval]
  apply Nat.max_le.mpr
  refine ⟨?_, sound ρ⟩
  by_cases enabled : active ρ order = true
  · simp only [enabled, ↓reduceIte, emitGated_cons, emitGated_nil, univEval, Nat.zero_max]
    by_cases zero : ρ parameter = 0
    · simp [zero]
    · simp only [zero, ↓reduceIte]
      obtain ⟨⟨path, node⟩, member, conditions⟩ := List.any_eq_true.mp found
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        List.all_eq_true, List.contains_iff_mem, Array.any_eq_true'] at conditions
      obtain ⟨⟨_, subset⟩, ⟨⟨name, offset⟩, occurs, same⟩⟩ := conditions
      dsimp only at same
      subst name
      have pathActive : active ρ path = true := by
        simp only [active, List.all_eq_true, decide_eq_true_eq] at enabled ⊢
        intro name inside
        rcases subset name inside with same | earlier
        · subst name; omega
        · exact enabled name earlier
      have nodeBound := entry_le ρ member pathActive
      have varBound := var_le ρ (vars := node.vars.toList) (by simpa using occurs)
      have bound := Nat.le_trans varBound (Nat.le_trans (Nat.le_max_right node.constant _) nodeBound)
      change ρ parameter ≤ entriesEval ρ norm.toList
      omega
  · simp [enabled]

abbrev GateState := List UInt64 × Bool × CPath

/-- The actual while body, exposed for a length-decreasing induction. -/
def gateStep (norm : CNorm) (_ : Unit) (state : GateState) : Id (ForInStep GateState) := do
  let mut order := state.1
  let mut leakFree := state.2.1
  let mut remaining := state.2.2
  if h : !remaining.isEmpty then
    let found := remaining.find? (absorbable norm order)
    if found.isNone then leakFree := false
    let pick := found.getD (remaining.head (by simpa using h))
    order := order ++ [pick]
    remaining := remaining.filter (· != pick)
    return .yield (order, leakFree, remaining)
  else return .done (order, leakFree, remaining)

def gateLoop (norm : CNorm) (state : GateState) : GateState :=
  Lean.Loop.forIn (m := Id) {} state (gateStep norm)

theorem gateOrderChecked_eq (norm : CNorm) (context : CPath) :
    gateOrderChecked norm context =
      ((gateLoop norm ([], true, context)).1, (gateLoop norm ([], true, context)).2.1) := rfl

theorem gateLoop_eq (norm : CNorm) (state : GateState) :
    gateLoop norm state = match gateStep norm () state with
      | .done result => result
      | .yield next => gateLoop norm next := by
  unfold gateLoop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases gateStep norm () state <;> rfl

def StateSound (norm : CNorm) (state : GateState) : Prop :=
  state.2.1 = true → GateSound norm state.1

theorem gateLoop_sound (norm : CNorm) (state : GateState) :
    StateSound norm state → StateSound norm (gateLoop norm state) := by
  induction state using (measure (fun state : GateState => state.2.2.length)).wf.induction with
  | h state ih =>
    rcases state with ⟨order, flag, remaining⟩
    intro prior
    rw [gateLoop_eq]
    by_cases empty : remaining = []
    · subst remaining
      simpa [gateStep, pure] using prior
    · have notNil : remaining ≠ [] := empty
      cases found : remaining.find? (absorbable norm order) with
      | none =>
        have member := List.head_mem notNil
        have smaller : (remaining.filter (· != remaining.head notNil)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (order ++ [remaining.head notNil], false,
          remaining.filter (· != remaining.head notNil)) smaller (by intro impossible; cases impossible)
        simpa [gateStep, empty, found, pure] using next
      | some parameter =>
        have member := List.mem_of_find?_eq_some found
        have smaller : (remaining.filter (· != parameter)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (order ++ [parameter], flag, remaining.filter (· != parameter)) smaller
          (fun accepted => gateSound_append (prior accepted) parameter (List.find?_some found))
        simpa [gateStep, empty, found, pure] using next

/-- The actual checked gate-order loop justifies absorption of all imax gate
leaks, for every valuation. The length induction also accounts for termination
even when the input context repeats parameters. -/
theorem gatesLeakFree_sound (norm : CNorm) (context : CPath)
    (checked : gatesLeakFree norm context = true) : GateSound norm (gateOrder norm context) := by
  have sound := gateLoop_sound norm ([], true, context) (fun _ => gateSound_nil norm)
  unfold gatesLeakFree gateOrder at *
  rw [gateOrderChecked_eq] at checked ⊢
  exact sound checked

theorem pick_members (order remaining : List UInt64) (pick : UInt64) (member : pick ∈ remaining)
    (parameter : UInt64) :
    (parameter ∈ order ++ [pick] ∨ parameter ∈ remaining.filter (· != pick)) ↔
      (parameter ∈ order ∨ parameter ∈ remaining) := by
  by_cases same : parameter = pick <;> simp_all

/-- The actual loop returns precisely the input context's members, regardless
of duplicates or whether the leak check accepts. -/
theorem gateLoop_members (norm : CNorm) (state : GateState) (parameter : UInt64) :
    parameter ∈ (gateLoop norm state).1 ↔ parameter ∈ state.1 ∨ parameter ∈ state.2.2 := by
  induction state using (measure (fun state : GateState => state.2.2.length)).wf.induction with
  | h state ih =>
    rcases state with ⟨order, flag, remaining⟩
    rw [gateLoop_eq]
    by_cases empty : remaining = []
    · subst remaining
      simp [gateStep, pure]
    · have notNil : remaining ≠ [] := empty
      cases found : remaining.find? (absorbable norm order) with
      | none =>
        have member := List.head_mem notNil
        have smaller : (remaining.filter (· != remaining.head notNil)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (order ++ [remaining.head notNil], false,
          remaining.filter (· != remaining.head notNil)) smaller
        simpa [gateStep, empty, found, pure] using
          next.trans (pick_members order remaining _ member parameter)
      | some pick =>
        have member := List.mem_of_find?_eq_some found
        have smaller : (remaining.filter (· != pick)).length < remaining.length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨_, member, by simp⟩
        have next := ih (order ++ [pick], flag, remaining.filter (· != pick)) smaller
        simpa [gateStep, empty, found, pure] using
          next.trans (pick_members order remaining pick member parameter)

theorem gateOrder_members (norm : CNorm) (context : CPath) (parameter : UInt64) :
    parameter ∈ gateOrder norm context ↔ parameter ∈ context := by
  unfold gateOrder
  rw [gateOrderChecked_eq]
  simpa using gateLoop_members norm ([], true, context) parameter

theorem active_gateOrder (ρ : UInt64 → Nat) (norm : CNorm) (context : CPath) :
    active ρ (gateOrder norm context) = active ρ context := by
  apply Bool.eq_iff_iff.mpr
  simp [active, gateOrder_members]

/-- An original atom stays bounded by its normal form when its own gate is
stripped under the actual coverage check. -/
theorem stripped_atom_le (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm)
    (path : CPath) (node : CNode) (member : (path, node) ∈ norm.toList)
    (parameter : UInt64) (offset : Nat) (occurs : (parameter, offset) ∈ node.vars.toList)
    (checked : covered norm offset (path.filter (· != parameter)) = true) :
    (if active ρ (path.filter (· != parameter)) then ρ parameter + offset else 0) ≤
      normEval ρ norm := by
  by_cases enabled : active ρ (path.filter (· != parameter)) = true
  · simp only [enabled, ↓reduceIte]
    by_cases zero : ρ parameter = 0
    · simpa [zero] using covered_sound ρ norm wellFormed offset _ checked enabled
    · have pathActive : active ρ path = true := by
        simp only [active, List.all_eq_true, decide_eq_true_eq] at enabled ⊢
        intro name inside
        by_cases same : name = parameter
        · subst name; omega
        · exact enabled name (by simp [inside, same])
      exact Nat.le_trans (var_le ρ occurs)
        (Nat.le_trans (Nat.le_max_right node.constant _) (entry_le ρ member pathActive))
  · simp [enabled]

/-- The exact successful guard in `linearize` makes its stripped atom safe to
emit, including the gate values introduced by the recovered imax chain. -/
theorem stripped_emission_le (ρ : UInt64 → Nat) (norm : CNorm) (wellFormed : SelfGated norm)
    (path : CPath) (node : CNode) (member : (path, node) ∈ norm.toList)
    (parameter : UInt64) (offset : Nat) (occurs : (parameter, offset) ∈ node.vars.toList)
    (checked : (covered norm offset (path.filter (· != parameter)) &&
      gatesLeakFree norm (path.filter (· != parameter))) = true) :
    univEval ρ (emitGated (gateOrder norm (path.filter (· != parameter)))
      (Univ.addSuccs (.var parameter) offset)) ≤ normEval ρ norm := by
  obtain ⟨coverage, leakage⟩ := Bool.and_eq_true_iff.mp checked
  rw [emitGated_eval, active_gateOrder, addSuccs_eval, univEval]
  exact Nat.max_le.mpr ⟨stripped_atom_le ρ norm wellFormed path node member parameter offset occurs coverage,
    gatesLeakFree_sound norm _ leakage ρ⟩

/-- The guard's self-gating premise is supplied by the actual complete
normalizer, including subsumption. Relating `normEval` back to the input's
`univEval` and accounting for all emitted groups remain separate obligations. -/
theorem stripped_normalized_emission_le (ρ : UInt64 → Nat) (source : Univ)
    (path : CPath) (node : CNode) (member : (path, node) ∈ (normalize source).toList)
    (parameter : UInt64) (offset : Nat) (occurs : (parameter, offset) ∈ node.vars.toList)
    (checked : (covered (normalize source) offset (path.filter (· != parameter)) &&
      gatesLeakFree (normalize source) (path.filter (· != parameter))) = true) :
    univEval ρ (emitGated (gateOrder (normalize source) (path.filter (· != parameter)))
      (Univ.addSuccs (.var parameter) offset)) ≤ normEval ρ (normalize source) :=
  stripped_emission_le ρ (normalize source) (normalize_selfGated source)
    path node member parameter offset occurs checked

end Ix.CompileCert.CanonUnivMeaning

