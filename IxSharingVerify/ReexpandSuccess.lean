import IxSharingVerify.ExpandSuccess
import IxSharingVerify.FamilyExpand
import IxC.Kernel.Audit.Axioms

/-!
# Re-expansion of a materialized encoding never refuses

The finishers re-expand what they materialized against the input DAG and
refuse unless the table entries come back as the table terms and the roots
as the input roots. Over a canonical DAG (well formed, distinct terms denote
distinct expressions) an encoding whose entries only reference earlier
entries, whose roots only reference entries, and whose parts denote their
terms passes this check under large enough budgets (`reexpand_ids`): the
interner seeded with the DAG is complete, every part is interned to the term
it denotes, and injectivity of the denotation pins that term down.

`expand_facts` collects the facts of a successful expansion this needs.
-/

namespace Ix.Sharing.Verify.CanonicalMeaning

open Ix.Sharing.Exact Ix.Sharing.Verify.SharingExact Ix.Sharing.Verify.Ingestion
open Ix.Sharing.Verify.UniformModel (DagWF dag_node_eq)
open Ix.Sharing.Family (substShares_congr_on)

/-- The facts of a successful expansion used downstream. -/
structure ExpandedOK (ex : Expanded) : Prop where
  wf : DagWF ex.dag
  roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size
  reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y
  injective : ∀ a, a < ex.dag.size → ∀ b, b < ex.dag.size →
    termOf ex.dag.nodes a = termOf ex.dag.nodes b → a = b

theorem expand_facts {limits : Limits} {sharing roots : Array Ixon.Expr} {allowShare : Bool}
    {ex : Expanded} (ran : expand limits sharing roots allowShare = .ok ex) : ExpandedOK ex := by
  unfold expand at ran
  obtain ⟨⟨⟨resolved, rawIds⟩, state⟩, ingested, tail⟩ := bind_eq_ok ran
  obtain ⟨⟨dag, ids⟩, numbered, finished⟩ := bind_eq_ok tail
  have run := ingestTable_run limits sharing roots allowShare resolved rawIds state ingested
  have result := canonicalize_correct state.interner.nodes rawIds run dag ids numbered
  have reach := canonicalize_reach run numbered
  have injective := canonicalize_injective run numbered
  dsimp only at finished
  split at finished
  · change Except.error _ = Except.ok ex at finished
    cases finished
  · have same : Except.ok ({
        dag, roots := ids, visits := state.visits,
        internedNodes := state.interner.nodes.size } : Expanded) = .ok ex := finished
    cases Except.ok.inj same
    refine ⟨⟨result.cp, result.arity⟩, ?_, reach, injective⟩
    intro r member
    obtain ⟨_, bound, _⟩ := forall₂_mem_right result.terms r member
    exact bound

/-- An interner seeded with distinct nodes indexes each at its position. -/
theorem complete_ofNodes (nodes : Array Node)
    (distinct : ∀ i, i < nodes.size → ∀ j, j < nodes.size → nodes[i]! = nodes[j]! → i = j) :
    Complete (Interner.ofNodes nodes) := by
  intro i hi
  change (Interner.ofNodes nodes).index.get? nodes[i]! = some i
  rw [ofNodes_get?]
  exact ⟨hi, rfl, fun v lt bound same => absurd (distinct v bound i hi same) (by omega)⟩

/-- Distinct terms of a well-formed DAG with an injective denotation are
distinct nodes. -/
theorem nodes_distinct {dag : Dag} (hwf : DagWF dag)
    (injective : ∀ a, a < dag.size → ∀ b, b < dag.size →
      termOf dag.nodes a = termOf dag.nodes b → a = b) :
    ∀ i, i < dag.nodes.size → ∀ j, j < dag.nodes.size → dag.nodes[i]! = dag.nodes[j]! → i = j := by
  intro i hi j hj same
  apply injective i hi j hj
  rw [termOf_eq, termOf_eq, same]
  apply toExpr_congr
  intro k bound
  have ci : (dag.nodes[j]!).child k < i := by
    have := hwf.childAt_lt (t := i) hi (by rw [dag_node_eq hi, same]; exact bound)
    rwa [dag_node_eq hi, same] at this
  have cj : (dag.nodes[j]!).child k < j := by
    have := hwf.childAt_lt (t := j) hj (by rw [dag_node_eq hj]; exact bound)
    rwa [dag_node_eq hj] at this
  simp only [ci, cj, ↓reduceIte]

/-- The denotation of a well-formed DAG is a model of it. -/
theorem dagModel_termOf {dag : Dag} (hwf : DagWF dag) : DagModel dag (termOf dag.nodes) := by
  intro u
  rw [termOf_eq]
  by_cases hu : u < dag.size
  · rw [← dag_node_eq hu]
    apply toExpr_congr
    intro index bound
    have := hwf.childAt_lt hu bound
    simp only [this, ↓reduceIte]
  · have outside : dag.nodes[u]! = default := getElem!_neg dag.nodes u hu
    have node : dag.node u = default := by
      simp only [Dag.node, Array.getElem?_eq_none (Nat.le_of_not_lt hu), Option.getD_none]
    rw [outside, node]
    rfl

/-- **Re-expansion identifies the table and the roots.** -/
theorem reexpand_ids {dag : Dag} (hwf : DagWF dag)
    (injective : ∀ a, a < dag.size → ∀ b, b < dag.size →
      termOf dag.nodes a = termOf dag.nodes b → a = b)
    {table roots : Array Nat} (tableIn : ∀ t ∈ table.toList, t < dag.size)
    (rootsIn : ∀ r ∈ roots.toList, r < dag.size)
    {es rs : Array Ixon.Expr} (esSize : es.size = table.size) (rsSize : rs.size = roots.size)
    (backward : ∀ k (hk : k < es.size), SharesIn (· < k) es[k])
    (rootsBelow : ∀ r ∈ rs.toList, SharesIn (· < table.size) r)
    (entries : List.Forall₂ (fun t e => substShares (fun i => termOf dag.nodes table[i]!) e =
      termOf dag.nodes t) table.toList es.toList)
    (rootRows : List.Forall₂ (fun r e => substShares (fun i => termOf dag.nodes table[i]!) e =
      termOf dag.nodes r) roots.toList rs.toList)
    (capacity : es.size < wordBound) :
    ∃ limits visits, reexpand limits dag es rs = .ok (table, roots, visits) := by
  let total := rangeNodes es 0 es.size + rangeNodes rs 0 rs.size
  let limits : Limits := { maxExprVisits := total, maxDepth := total, maxNodes := dag.size + total }
  have deepE : ∀ index, index < es.size → treeHeight es[index]! ≤ limits.maxDepth := by
    intro index bound
    have := treeHeight_lt es[index]!
    have := le_rangeNodes es es.size 0 index (by omega) (by omega)
    change _ ≤ total
    omega
  have deepR : ∀ index, index < rs.size → treeHeight rs[index]! ≤ limits.maxDepth := by
    intro index bound
    have := treeHeight_lt rs[index]!
    have := le_rangeNodes rs rs.size 0 index (by omega) (by omega)
    change _ ≤ total
    omega
  obtain ⟨resolved, out, after, ran, resolvedSize, outSize, -⟩ := ingestTable_ok limits es rs true
    { interner := Interner.ofNodes dag.nodes } capacity
    (fun index bound acc size => sharesValid_of_below _ rfl _ (by
      change SharesIn (· < acc.size) es[index]!
      rw [size, getElem!_pos es index bound]
      exact backward index bound))
    (fun index bound resolved size => sharesValid_of_below _ rfl _ (by
      change SharesIn (· < resolved.size) rs[index]!
      rw [size, esSize]
      exact rootsBelow _ (by rw [getElem!_pos rs index bound]; exact Array.getElem_mem_toList bound)))
    deepE deepR (by change 0 + _ + _ ≤ total; omega)
    (by change dag.nodes.size + _ + _ ≤ dag.size + total; simp only [Dag.size]; omega)
  have result := ingestTable_correct limits es rs true _
    (good_seed (tableContext es.size true 0 #[]) rfl dag.nodes hwf.precede hwf.arity)
    resolved out after ran
  have complete := Maintains.ingestTable limits es rs true _
    (complete_ofNodes dag.nodes (nodes_distinct hwf injective)) (resolved, out) after ran
  have retained : Retains dag.nodes after.interner.nodes := result.retained
  have bound : ∀ t, t < dag.size → t < after.interner.nodes.size := fun t ht => retained.bound t ht
  have keep : ∀ t, t < dag.size → termOf after.interner.nodes t = termOf dag.nodes t :=
    fun t ht => termOf_retains retained t ht
  have inj := complete.term_injective result.good.cp result.good.arity
  have tableLt : ∀ i (hi : i < table.size), table[i] < dag.size :=
    fun i hi => tableIn _ (Array.getElem_mem_toList hi)
  have ids : ∀ k (hk : k < resolved.size), resolved[k] = table[k]'(by omega) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk
      have rep := pairs_get result.entries k (by simp; omega) (by simp; omega)
      simp only [Array.getElem_toList] at rep
      obtain ⟨lt, _, meaning⟩ := rep
      have row := pairs_get entries k (by simp; omega) (by simp; omega)
      simp only [Array.getElem_toList] at row
      apply inj _ lt _ (bound _ (tableLt k (by omega)))
      rw [meaning, keep _ (tableLt k (by omega)), ← row]
      apply substShares_congr_on _ (backward k (by omega))
      intro i hi
      have hi' : i < resolved.size := by omega
      simp only [expansion, rootContext, Array.getElem?_eq_getElem hi']
      rw [ih i hi hi', keep _ (tableLt i (by omega)), getElem!_pos table i (by omega)]
  have tableEq : resolved = table :=
    Array.ext (by rw [resolvedSize, esSize]) (fun k h1 _ => ids k h1)
  have rootIds : ∀ k (hk : k < out.size), out[k] = roots[k]'(by omega) := by
    intro k hk
    have rep := pairs_get result.roots k (by simp; omega) (by simp; omega)
    simp only [Array.getElem_toList] at rep
    obtain ⟨lt, _, meaning⟩ := rep
    have row := pairs_get rootRows k (by simp; omega) (by simp; omega)
    simp only [Array.getElem_toList] at row
    have rootLt : roots[k]'(by omega) < dag.size := rootsIn _ (Array.getElem_mem_toList _)
    apply inj _ lt _ (bound _ rootLt)
    rw [meaning, keep _ rootLt, ← row]
    apply substShares_congr_on _ (rootsBelow _ (Array.getElem_mem_toList (by omega)))
    intro i hi
    have hi' : i < resolved.size := by omega
    simp only [expansion, rootContext, Array.getElem?_eq_getElem hi']
    rw [ids i hi', keep _ (tableLt i (by omega)), getElem!_pos table i (by omega)]
  have rootsEq : out = roots := Array.ext (by omega) (fun k h1 _ => rootIds k h1)
  rw [tableEq, rootsEq] at ran
  refine ⟨limits, after.visits, ?_⟩
  unfold reexpand
  dsimp only
  rw [Budget.bind_ok_eq ran]
  rfl

end Ix.Sharing.Verify.CanonicalMeaning

#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.expand_facts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.dagModel_termOf [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.CanonicalMeaning.reexpand_ids [propext, Classical.choice, Quot.sound]
