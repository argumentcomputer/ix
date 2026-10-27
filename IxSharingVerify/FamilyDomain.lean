import IxSharingVerify.FamilyTiered
import IxSharingVerify.CanonicalMeaning

/-! Successful family entry guards, format/length and root meaning, independent
of compiler builders. The constant wrapper imports these unchanged facts. -/

namespace Ix.Sharing.Family

open Ix.Sharing.Exact
open Ix.Sharing.Verify
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.Tiered
open Ix.Sharing.Verify.SharingExact (Desc bind_eq_ok)

structure ExpandedDomain (ex : Expanded) : Prop where
  wf : DagWF ex.dag
  roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size
  reachable : ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y

theorem uniformDagChecks_domain {ex : Expanded} (run : uniformDagChecks ex = .ok ()) :
    DagWF ex.dag ∧ (∀ r ∈ ex.roots.toList, r < ex.dag.size) ∧
      ∀ y, y < ex.dag.size → ∃ r ∈ ex.roots.toList, Desc ex.dag r y := by
  by_cases precede : childrenPrecede ex.dag.nodes = true
  · by_cases arity : ex.dag.nodes.all (fun node => node.children.size == node.head.arity) = true
    · by_cases bounded : ex.roots.all (fun r => r < ex.dag.size) = true
      · by_cases marked : (reachMarks ex.dag.nodes ex.roots).all id = true
        ·
          have wf := dagWF_of_checks precede arity
          have roots : ∀ r ∈ ex.roots.toList, r < ex.dag.size := by
            intro r hr
            exact of_decide_eq_true (Array.all_eq_true'.mp bounded r (Array.mem_toList_iff.mp hr))
          exact ⟨wf, roots, reach_of_marks wf roots marked⟩
        · simp only [uniformDagChecks, precede, arity, bounded, marked, ↓reduceIte] at run
          cases run
      · simp [uniformDagChecks, precede, arity, bounded] at run
        all_goals cases run
    · simp [uniformDagChecks, precede, arity] at run
      all_goals cases run
  · simp [uniformDagChecks, precede] at run
    all_goals cases run

/-- These domain facts come from the actual successful entry's guards;
they are no longer caller hypotheses at the wrapper endpoint. -/
theorem familyExpanded_domain {cfg : Config} {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) : ExpandedDomain ex := by
  unfold familyExpanded at run
  obtain ⟨u, dag, _⟩ := bind_eq_ok run
  cases u
  obtain ⟨wf, roots, reachable⟩ := uniformDagChecks_domain dag
  exact ⟨wf, roots, reachable⟩

theorem familyExpanded_output_of_success {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {ex : Expanded} {out : TieredSharingResult} (run : familyExpanded cfg layout limits ex = .ok out) :
    TieredOutput layout limits ex out := by
  have domain := familyExpanded_domain run
  exact (familyExpanded_checked domain.wf domain.roots domain.reachable run).2

theorem familyAtWidth_serialized {cfg : Config} {limits : Limits} {ex : Expanded} {width candidates : Nat}
    {out : TieredSharingResult}
    (run : familyAtWidth cfg .tagN limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
      (parentsOf ex.dag) candidates width = .ok out) :
    out.result.variableBytes = tag0Size out.result.sharing.size +
        (out.result.sharing ++ out.result.roots).foldl (fun n e => n + (Ixon.serExpr e).size) 0 ∧
      out.result.modelBytes = out.result.variableBytes := by
  obtain ⟨uniform, allocation, m, _, _, materialized, rfl⟩ := familyAtWidth_parts run
  obtain ⟨_, _, _, _, wire⟩ := rematerialize_parts materialized
  obtain ⟨measured, bytes⟩ := rematerialize_measured materialized
  exact ⟨measured.trans (layoutBytes_tagN_eq_serialized _ _ wire), bytes⟩

theorem familyExpanded_serialized {cfg : Config} {limits : Limits} {ex : Expanded} {out : TieredSharingResult}
    (run : familyExpanded cfg .tagN limits ex = .ok out) :
    out.result.variableBytes = tag0Size out.result.sharing.size +
        (out.result.sharing ++ out.result.roots).foldl (fun n e => n + (Ixon.serExpr e).size) 0 ∧
      out.result.modelBytes = out.result.variableBytes := by
  obtain ⟨_, _, _, _, selected, rfl⟩ := familyExpanded_selected run
  have serialized := familyAtWidth_serialized selected
  exact serialized

open Ix.Sharing.Verify.Ingestion
open Ix.Sharing.Verify.CanonicalMeaning (SharingMeaning pairs_get)
open Ix.Sharing.Verify.SharingExact (termOf substShares)

theorem paired_maps {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}
    (rows : List.Forall₂ (fun x y => f x = g y) xs ys) : xs.map f = ys.map g := by
  induction rows with
  | nil => rfl
  | cons same _ ih => simp only [List.map_cons, same, ih]

/-- The checked ordered input loop already gives a complete interpretation
of an arbitrary shared table and its ordered roots. -/
theorem tableResult_meaning {sharing roots : Array Ixon.Expr} {resolved ids : Array Nat}
    {before after : IngestState} (table : TableResult sharing roots true resolved ids before after) :
    SharingMeaning (ids.map (termOf after.interner.nodes)) sharing roots := by
  let context := rootContext sharing.size true roots.size resolved
  let substitution := expansion context after.interner.nodes
  refine ⟨substitution, ?_, ?_, ?_⟩
  · intro index bound
    have refBound : index < resolved.size := by rw [table.tableSize]; exact bound
    have row := pairs_get table.entries index (by simpa using bound) (by simpa using refBound)
    refine ⟨?_, table.backward index bound⟩
    change (match resolved[index]? with
      | some id => termOf after.interner.nodes id | none => default) = substShares substitution sharing[index]!
    rw [Array.getElem?_eq_getElem refBound]
    simpa only [Array.getElem_toList, getElem!_pos sharing index bound] using row.2.2
  · intro root member
    obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
    subst root
    have refBound : index < ids.size := by rw [table.rootSize]; exact bound
    have row := pairs_get table.roots index (by simpa using bound) (by simpa using refBound)
    have valid := SharesValid.bounded context _ row.2.1
    simpa only [context, rootContext, table.tableSize, Array.getElem_toList] using valid
  · have rows := paired_maps (pairs_mono (fun _ _ meaning => meaning.2.2.symm) table.roots)
    apply Array.toList_inj.mp
    simpa only [Array.toList_map] using rows

/-- Successful expansion preserves the complete ordered interpretation
of the original shared input, through canonical numbering. -/
theorem expand_shared_meaning {limits : Limits} {sharing roots : Array Ixon.Expr} {expanded : Expanded}
    (run : expand limits sharing roots true = .ok expanded) :
    SharingMeaning (expanded.roots.map (termOf expanded.dag.nodes)) sharing roots := by
  obtain ⟨resolved, ids, state, input, canonical⟩ :=
    Ix.Sharing.Verify.CanonicalMeaning.expand_correct limits sharing roots true expanded run
  have meaning := tableResult_meaning input
  have mapped := paired_maps (pairs_mono (fun _ _ pair => pair.2.symm) canonical.terms)
  have same : ids.map (termOf state.interner.nodes) = expanded.roots.map (termOf expanded.dag.nodes) := by
    apply Array.toList_inj.mp
    simpa only [Array.toList_map] using mapped
  rw [same] at meaning
  exact meaning

theorem familyExpanded_meaning {cfg : Config} {layout : ShareLayout} {limits : Limits} {expanded : Expanded}
    {result : TieredSharingResult} (run : familyExpanded cfg layout limits expanded = .ok result) :
    SharingMeaning (expanded.roots.map (termOf expanded.dag.nodes)) result.result.sharing result.result.roots := by
  have domain := familyExpanded_domain run
  obtain ⟨visits, checked⟩ := (familyExpanded_output_of_success run).reexpanded
  obtain ⟨after, target, _⟩ := reexpand_correct limits expanded.dag result.result.sharing result.result.roots
    domain.wf.precede domain.wf.arity result.result.tableTerms expanded.roots visits checked
  have meaning := tableResult_meaning target
  have same : expanded.roots.map (termOf after.interner.nodes) =
      expanded.roots.map (termOf expanded.dag.nodes) := by
    apply Array.toList_inj.mp
    simp only [Array.toList_map]
    apply List.map_congr_left
    intro id inside
    exact termOf_retains target.retained id (domain.roots id inside)
  rw [same] at meaning
  exact meaning

end Ix.Sharing.Family
