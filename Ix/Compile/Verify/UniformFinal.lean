import Ix.Compile.Verify.UniformDecomp
import Ix.Compile.Verify.UniformOptimizer

/-!
# Stage 4: the optimizer returns the tie-least minimum

Facts about the run of `optimizeUniformExpanded` that the optimality
theorem needs, discharged from its runtime checks.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (Desc Reach reach_lt reachMarks_spec reachMarks_eq
  marksFrom_size child_eq_getElem)

/-! ## Every term is reachable from a root -/

/-- A path extended by one edge. -/
theorem desc_snoc {dag : Dag} {r t : Nat} (h : Desc dag r t) {k : Nat}
    (hk : k < (dag.node t).children.size) : Desc dag r ((dag.node t).child k) := by
  induction h with
  | refl t => exact .child k hk (.refl _)
  | child k' hk' _ ih => exact .child k' hk' (ih hk)

theorem desc_of_reach {dag : Dag} {roots : Array Nat} (hin : ∀ r ∈ roots, r < dag.size)
    (hcp : Ix.Compile.Verify.SharingExact.CP dag.nodes) {t : Nat}
    (h : Reach dag.nodes roots t) : ∃ r ∈ roots.toList, Desc dag r t := by
  induction h with
  | root hr => exact ⟨_, Array.mem_toList_iff.mpr hr, .refl _⟩
  | @child t c ht hc ih =>
    obtain ⟨r, hr, hd⟩ := ih
    have htn : t < dag.size := reach_lt hcp hin ht
    rw [← dag_node_eq htn] at hc
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hc
    refine ⟨r, hr, ?_⟩
    rw [← child_eq_getElem _ k hk]
    exact desc_snoc hd hk

/-- **Reachability from the optimizer's check.** -/
theorem reach_of_marks {dag : Dag} (hwf : DagWF dag) {roots : Array Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size)
    (hm : (reachMarks dag.nodes roots).all id = true) :
    ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y := by
  intro y hy
  have hin : ∀ r ∈ roots, r < dag.nodes.size := fun r hr => hroots r (Array.mem_toList_iff.mpr hr)
  have hsz : (reachMarks dag.nodes roots).size = dag.nodes.size := by
    rw [reachMarks_eq, marksFrom_size]
  rw [Array.all_eq_true] at hm
  have hy' : y < (reachMarks dag.nodes roots).size := by rw [hsz]; exact hy
  have hmark : (reachMarks dag.nodes roots)[y]! = true := by
    have := hm y hy'
    simp only [id] at this
    simpa [getElem!_def, Array.getElem?_eq_getElem hy'] using this
  exact desc_of_reach hin hwf.precede ((reachMarks_spec hwf.precede hin y hy).mp hmark)

/-- **The optimizer only succeeds on a DAG whose roots reach every term.** -/
theorem optimizeUniform_reach {w : Nat} {limits : Limits} {ex : Expanded}
    {res : UniformSharingResult} (h : optimizeUniformExpanded w limits ex = .ok res) :
    ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y := by
  obtain ⟨_, hwf, hroots, hm, _⟩ := optimizeUniform_parts h
  exact reach_of_marks hwf hroots hm

end Ix.Compile.Verify.UniformModel
