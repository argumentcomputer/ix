import IxSharingVerify.FamilyProducer
import Ix.Sharing.FamilyNormalizeSpec
import IxSharingVerify.ExpandSuccess

/-! Success of the family stage's internal checks.

Row retention (`retainedResult`) never refuses a family table: the table has
a best row, a least best set, and that set's row at its own count. The
component loop (`familyReferenceComponents`, and so the compiled
`familyComponents`) therefore succeeds whenever its two precharged budgets
cover the declared call and work counts of every component. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

/-- A trimmed table entry is the original entry at the same count. -/
theorem trim_sub {tb : CTable} {slack k : Nat} {e : Entry}
    (row : (tb.trim slack)[k]! = some e) : tb[k]! = some e := by
  rw [trim_getElem!] at row
  cases hb : tb.best with
  | none => rw [hb] at row; exact row
  | some b =>
    rw [hb] at row
    simp only at row
    cases hk : tb[k]! with
    | none => rw [hk] at row; cases row
    | some x =>
      rw [hk] at row
      simp only at row
      split at row
      · cases row
      · exact (Option.some.inj row) ▸ rfl

/-- Trimming keeps the best value of a table. -/
theorem trim_best {tb : CTable} {best : _root_.Int} (hb : tb.best = some best) (slack : Nat) :
    (tb.trim slack).best = some best := by
  obtain ⟨k, e, row, value⟩ := best_attained hb
  have kept : (tb.trim slack)[k]! = some e := by
    rw [trim_getElem!, hb]
    simp only
    rw [row]
    simp only
    rw [ite_eq_right (by omega)]
  obtain ⟨b, hb'⟩ := best_isSome kept
  have upper : b ≤ best := value ▸ best_le hb' kept
  obtain ⟨k', e', row', value'⟩ := best_attained hb'
  have lower : best ≤ b := value' ▸ best_le hb (trim_sub row')
  rw [hb']
  congr 1
  omega

/-- The best-set fold returns a set once a row of the requested value exists. -/
theorem bestStepSet_fold_isSome (bd : _root_.Int) :
    ∀ (rows : List (Option Entry)) (acc : Option (Array Nat)),
      (acc.isSome ∨ ∃ e, some e ∈ rows ∧ e.1 = bd) →
        (rows.foldl (bestStepSet bd) acc).isSome := by
  intro rows
  induction rows with
  | nil =>
    intro acc h
    rcases h with h | ⟨_, member, _⟩
    · exact h
    · cases member
  | cons o rows ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨e, member, value⟩
    · left
      cases o with
      | none => exact h
      | some x =>
        obtain ⟨d, s⟩ := x
        cases acc with
        | none => cases h
        | some a =>
          simp only [bestStepSet]
          split <;> (try split) <;> rfl
    · rcases List.mem_cons.mp member with same | later
      · left
        subst same
        obtain ⟨d, s⟩ := e
        simp only at value
        subst value
        cases acc with
        | none => simp [bestStepSet]
        | some a =>
          simp only [bestStepSet, beq_self_eq_true, ↓reduceIte]
          split <;> rfl
      · exact .inr ⟨e, later, value⟩

theorem bestSetOf_isSome {tb : CTable} {k : Nat} {e : Entry} (row : tb[k]! = some e) :
    ∃ set, bestSetOf tb e.1 = some set := by
  rw [bestSetOf_eq]
  have some := bestStepSet_fold_isSome e.1 tb.toList none (.inr ⟨e, getElem!_mem_toList row, rfl⟩)
  exact Option.isSome_iff_exists.mp some

/-- Row retention succeeds on every table built by the family recipe over
duplicate-free members, whatever the slack and the cost function. -/
theorem retainedResult_ok_of_table (cfg : Config) (slack : Nat) (trace : ComponentTrace)
    (cost : Cost) (hd : trace.members.toList.Nodup)
    (rows : trace.rows = table cfg cost trace.members.toList) :
    ∃ result, retainedResult slack trace = .ok result := by
  have meaning := table_meaning cfg cost trace.members.toList
  obtain ⟨best, hb, _, _⟩ := table_best_exists cfg ⟨trace.members.toList, cost⟩ hd
  have hb : (table cfg cost trace.members.toList).best = some best := hb
  have sorted : SortedT (table cfg cost trace.members.toList) := fun k e row =>
    family_sorted cfg cost trace.members.toList hd e.2 (meaning.sound k e row).2.1
  have entries := trim_entries meaning.sound slack
  have trimmedSorted := (trim_tie slack sorted).1
  have trimmedBest := trim_best hb slack
  obtain ⟨k, e, row, value⟩ := best_attained trimmedBest
  obtain ⟨set, chosen⟩ := bestSetOf_isSome row
  rw [value] at chosen
  obtain ⟨k', row'⟩ := bestSetOf_row trimmedSorted chosen
  have count : set.size = k' := (entries k' _ row').1
  rw [← count] at row'
  rw [← rows] at trimmedBest chosen row'
  refine ⟨CompResult.mk trace.members best set (trace.rows.trim slack), ?_⟩
  unfold retainedResult
  simp [trimmedBest, chosen, row']
  rfl

/-- Row retention never refuses an actual component trace. -/
theorem retainedResult_component_ok (cfg : Config) (ex : Expanded) (sg : UStage)
    (width index : Nat) (members : Array Nat) (hd : members.toList.Nodup) :
    ∃ result, retainedResult sg.slack (component cfg ex sg width index members) = .ok result :=
  retainedResult_ok_of_table cfg sg.slack _ _ hd rfl

/-- A meter step within its limit returns the new count. -/
theorem bump_ok {count n limit : Nat} {r : Resource} (h : count + n ≤ limit) :
    bump count n limit r = .ok (count + n) := by
  unfold bump
  simp only [show ¬ count + n > limit by omega, ↓reduceIte]

/-- The precharged call count of the whole component loop. -/
def familyCallTotal (cfg : Config) (comps : List (Array Nat)) : Nat :=
  (comps.map fun members => familyCalls cfg members.size).sum

/-- The precharged work of the whole component loop: each component's
declared work over its full upward closure. -/
def familyWorkTotal (cfg : Config) (ex : Expanded) (sg : UStage) (comps : List (Array Nat)) : Nat :=
  (comps.map fun members =>
    familyWork cfg members.size (componentContext ex sg members).closure.size).sum

theorem familyReferenceFold_ok (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) :
    ∀ (comps : List (Array Nat)) (results : Array CompResult) (states work : Nat),
      (∀ members ∈ comps, members.toList.Nodup) →
      states + familyCallTotal cfg comps ≤ limits.maxStates →
      work + familyWorkTotal cfg ex sg comps ≤ limits.maxCostEvals →
      ∃ out, comps.foldlM (familyReferenceStep cfg limits ex sg width) (results, states, work) =
        .ok out := by
  intro comps
  induction comps with
  | nil => intro results states work _ _ _; exact ⟨_, rfl⟩
  | cons members rest ih =>
    intro results states work hd stateBound workBound
    simp only [familyCallTotal, familyWorkTotal, List.map_cons, List.sum_cons] at stateBound workBound
    obtain ⟨result, retained⟩ :=
      retainedResult_component_ok cfg ex sg width results.size members (hd members (by simp))
    have b1 : bump states (familyCalls cfg members.size) limits.maxStates .states =
        .ok (states + familyCalls cfg members.size) := bump_ok (by omega)
    have b2 : bump work (familyWork cfg members.size (componentContext ex sg members).closure.size)
        limits.maxCostEvals .costEvals =
        .ok (work + familyWork cfg members.size (componentContext ex sg members).closure.size) :=
      bump_ok (by omega)
    have stepped : familyReferenceStep cfg limits ex sg width (results, states, work) members =
        .ok (results.push result, states + familyCalls cfg members.size,
          work + familyWork cfg members.size (componentContext ex sg members).closure.size) := by
      unfold familyReferenceStep
      simp only [b1, b2, retained, bind, Except.bind, pure, Except.pure]
    rw [List.foldlM_cons, stepped]
    exact ih _ _ _ (fun m inside => hd m (List.mem_cons_of_mem _ inside))
      (by simp only [familyCallTotal]; omega) (by simp only [familyWorkTotal]; omega)

/-- The component loop succeeds when its two budgets cover the declared call
and work totals; no other check of the loop can refuse. -/
theorem familyComponents_ok (cfg : Config) (limits : Limits) (ex : Expanded) (sg : UStage)
    (width : Nat) (hcp : childrenPrecede ex.dag.nodes = true)
    (hd : ∀ members ∈ sg.comps.toList, members.toList.Nodup)
    (states : familyCallTotal cfg sg.comps.toList ≤ limits.maxStates)
    (work : familyWorkTotal cfg ex sg sg.comps.toList ≤ limits.maxCostEvals) :
    ∃ out, familyComponents cfg limits ex sg width (parentsOf ex.dag) = .ok out := by
  rw [familyComponents_eq_reference cfg limits ex sg width hcp]
  unfold familyReferenceComponents
  rw [← Array.foldlM_toList]
  exact familyReferenceFold_ok cfg limits ex sg width _ #[] 0 0 hd (by omega) (by omega)


/-! ## The entry's DAG checks -/

open Ix.Sharing.Verify.SharingExact (CP NodeArity Reach reachMarks_spec reachMarks_eq marksFrom_size
  getElem!_eq_getElem child_eq_getElem Desc)

theorem childrenPrecede_of_cp {temp : Array Node} (h : CP temp) : childrenPrecede temp = true := by
  unfold childrenPrecede
  rw [Array.all_eq_true]
  intro t ht
  have bound : t < temp.size := by simpa using ht
  simp only [Array.getElem_zipIdx, Nat.zero_add]
  rw [Array.all_eq_true]
  intro k hk
  have member : temp[t].children[k] ∈ (temp[t]!).children := by
    rw [getElem!_eq_getElem temp t bound]
    exact Array.getElem_mem hk
  simpa using h t bound _ member

theorem arityCheck_of {temp : Array Node} (h : NodeArity temp) :
    temp.all (fun node => node.children.size == node.head.arity) = true := by
  rw [Array.all_eq_true]
  intro t ht
  have arity := h t ht
  rw [getElem!_eq_getElem temp t ht] at arity
  simp [arity]

theorem reach_of_desc {dag : Dag} {roots : Array Nat} {t u : Nat} (h : Desc dag t u) :
    Reach dag.nodes roots t → Reach dag.nodes roots u := by
  induction h with
  | refl => exact id
  | @child t u k hk _ ih =>
    intro reached
    apply ih
    by_cases bound : t < dag.size
    · have member : (dag.node t).child k ∈ (dag.nodes[t]!).children := by
        rw [← dag_node_eq bound, child_eq_getElem _ k hk]
        exact Array.getElem_mem hk
      exact .child reached member
    · exfalso
      have empty : dag.node t = default := by
        unfold Dag.node
        rw [Array.getElem?_eq_none (by simpa [Dag.size] using bound)]
        rfl
      rw [empty] at hk
      exact Nat.not_lt_zero k hk

/-- The entry's DAG checks pass on every well-formed DAG whose in-range roots
reach every term; `uniformDagChecks_domain` is the converse. -/
theorem uniformDagChecks_ok {ex : Expanded} (wf : DagWF ex.dag)
    (roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size)
    (reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y) :
    uniformDagChecks ex = .ok () := by
  have precede := childrenPrecede_of_cp wf.precede
  have arity := arityCheck_of wf.arity
  have hin : ∀ r ∈ ex.roots, r < ex.dag.nodes.size :=
    fun r member => roots r (Array.mem_toList_iff.mpr member)
  have bounded : ex.roots.all (· < ex.dag.size) = true := by
    rw [Array.all_eq_true]
    intro i hi
    exact decide_eq_true (hin _ (Array.getElem_mem hi))
  have marked : (reachMarks ex.dag.nodes ex.roots).all id = true := by
    rw [Array.all_eq_true]
    intro t ht
    have size : (reachMarks ex.dag.nodes ex.roots).size = ex.dag.nodes.size := by
      rw [reachMarks_eq, marksFrom_size]
    have bound : t < ex.dag.nodes.size := by rw [size] at ht; exact ht
    obtain ⟨r, hr, desc⟩ := reachable t bound
    have reached : Reach ex.dag.nodes ex.roots t :=
      reach_of_desc desc (.root (Array.mem_toList_iff.mp hr))
    have mark := (reachMarks_spec wf.precede hin t bound).mpr reached
    simpa [getElem!_def, Array.getElem?_eq_getElem ht] using mark
  simp only [uniformDagChecks, precede, arity, bounded, marked, ↓reduceIte]
  rfl


/-! ## The knapsack -/

/-- Cells of the count-bracket knapsack table (`uniformKnapsack`), or 0 when
the best merge leaves no lower bracket to search. -/
def knapsackCells (kCS : Nat) (results : Array CompResult) : Nat :=
  let bestX := results.foldl (fun acc r => mergeSorted acc r.bestSet) #[]
  let start := tag0BracketStart (kCS + bestX.size)
  if start > kCS then (results.size + 1) * (start - 1 - kCS + 1) else 0

/-- The knapsack's only refusal is its cell budget. -/
theorem uniformKnapsack_ok (limits : Limits) (kCS : Nat) (results : Array CompResult)
    (cells : knapsackCells kCS results ≤ limits.maxKnapsackCells) :
    ∃ out, uniformKnapsack limits kCS results = .ok out := by
  unfold uniformKnapsack
  unfold knapsackCells at cells
  dsimp only at cells ⊢
  split
  · rename_i above
    rw [ite_eq_left above] at cells
    rw [ite_eq_right (Nat.not_lt.mpr cells)]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩


/-! ## The finisher's stored-set checks -/

/-- The finisher's class check passes on a strictly increasing set of terms
of in-degree at least 2. -/
theorem inClassCheckD_ok {deg stored : Array Nat} (sorted : stored.toList.Pairwise (· < ·))
    (degrees : ∀ t ∈ stored.toList, 2 ≤ deg[t]!) : inClassCheckD deg stored = true := by
  unfold inClassCheckD
  simp only [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    apply decide_eq_true
    intro next
    have := List.pairwise_iff_getElem.mp sorted i (i + 1) (by simpa using hi) (by simpa using next)
      (by omega)
    rw [getElem!_pos stored i hi, getElem!_pos stored (i + 1) next]
    simpa using this
  · rw [Array.all_eq_true']
    intro t member
    exact decide_eq_true (degrees t (Array.mem_toList_iff.mpr member))


/-- Every successful expansion passes the family entry's DAG checks. -/
theorem expand_dagChecks {limits : Limits} {sharing roots : Array Ixon.Expr} {allowShare : Bool}
    {ex : Expanded} (ran : expand limits sharing roots allowShare = .ok ex) :
    uniformDagChecks ex = .ok () := by
  unfold expand at ran
  obtain ⟨⟨⟨resolved, rawIds⟩, state⟩, ingested, tail⟩ := bind_eq_ok ran
  obtain ⟨⟨dag, ids⟩, numbered, finished⟩ := bind_eq_ok tail
  have run := Ix.Sharing.Verify.Ingestion.ingestTable_run limits sharing roots allowShare resolved
    rawIds state ingested
  have result := Ix.Sharing.Verify.CanonicalMeaning.canonicalize_correct state.interner.nodes rawIds
    run dag ids numbered
  have reach := Ix.Sharing.Verify.CanonicalMeaning.canonicalize_reach run numbered
  dsimp only at finished
  split at finished
  · change Except.error _ = Except.ok ex at finished
    cases finished
  · have same : Except.ok ({
        dag, roots := ids, visits := state.visits,
        internedNodes := state.interner.nodes.size } : Expanded) = .ok ex := finished
    cases Except.ok.inj same
    apply uniformDagChecks_ok ⟨result.cp, result.arity⟩
    · intro r member
      obtain ⟨_, bound, _⟩ := Ix.Sharing.Verify.SharingExact.forall₂_mem_right result.terms r member
      exact bound
    · exact reach
end Ix.Sharing.Family

#guard_kernel_axioms Ix.Sharing.Family.trim_best [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.retainedResult_ok_of_table [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.retainedResult_component_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.familyComponents_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.uniformDagChecks_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.uniformKnapsack_ok [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Family.expand_dagChecks [propext, Classical.choice, Quot.sound]
