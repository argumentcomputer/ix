import Ix.Compile.SourceGraph.Reverse
import Ix.Cert.SourcePrepass

/-! Complete pre-grounding summary edges. The reference uses final key
winners; the live insert-only error history remains a separate grounding
obligation. Neither graph equality nor the fixed-sub selector proves no-drop,
admission or rewrite value preservation. -/
namespace Ix.Cert.SourceSummaryReverse
open Ix (Name ConstantInfo)
open Ix.Compile.SourceGraph
open Ix.Compile.SourceGraph.Reverse

private theorem fold_iff {α σ : Type} (step : σ → α → σ) (P : σ → Prop) (Q : α → Prop)
    (h : ∀ s x, P (step s x) ↔ P s ∨ Q x) (xs : List α) (s : σ) :
    P (xs.foldl step s) ↔ P s ∨ ∃ x ∈ xs, Q x := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, h, List.mem_cons]; grind

private theorem append_lookup (m : Ix.Map Name (Array α)) (key query : Name) (item : α) :
    (appendAt m key item).getD query #[] =
      if key == query then (m.getD key #[]).push item else m.getD query #[] :=
  SourceReverse.appendAt_lookup m key query item

private def Hit (rs : Recursors) (first n : Name) : Prop :=
  ∃ p ∈ rs.getD first #[], p.1 = first ∧ (n == p.2) = true

private theorem recStep_hit (m : Recursors) (p : Name × Node) (first n : Name) :
    Hit (recStep m p) first n ↔ Hit m first n ∨
      ∃ all, p.2.grouping = .recursor all ∧ all[0]? = some first ∧ (n == p.1) = true := by
  obtain ⟨k, refs, lits, group⟩ := p
  cases group with
  | plain => simp [recStep, Hit]
  | induct all => simp [recStep, Hit]
  | recursor all =>
    cases hf : all[0]? with
    | none => simp [recStep, hf]
    | some f =>
      simp only [recStep, hf, Hit, append_lookup]
      by_cases same : (f == first) = true
      · simp only [same, ite_true, Std.HashMap.getD_congr same, Array.mem_push]
        simp [or_and_right, hf, exists_or]
      · have different : f ≠ first := by intro eq; subst f; simp at same
        simp [same, different, hf]

private theorem recursors_hit (nodes : Ix.Map Name Node) (first n : Name) :
    Hit (recursors nodes) first n ↔
      ∃ node all, nodes.get? n = some node ∧ node.grouping = .recursor all ∧ all[0]? = some first := by
  unfold recursors
  rw [Std.HashMap.fold_eq_foldl_toList]
  change Hit (nodes.toList.foldl recStep {}) first n ↔ _
  rw [fold_iff recStep (fun m => Hit m first n)
    (fun p => ∃ all, p.2.grouping = .recursor all ∧ all[0]? = some first ∧ (n == p.1) = true)
    (fun m p => recStep_hit m p first n)]
  simp only [Hit, Std.HashMap.getD_empty, Array.not_mem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨⟨k, node⟩, stored, all, group, head, same⟩
    refine ⟨node, all, ?_, group, head⟩
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr same]
    exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp stored).2
  · rintro ⟨node, all, found, group, head⟩
    obtain ⟨k, same, stored⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp found
    exact ⟨(k, node), stored, all, group, head, same⟩

private def Coherent (nodes : Ix.Map Name Node) (env : Ix.Environment) : Prop :=
  ∀ n, nodes.get? n = (env.consts.get? n).map capture

private theorem recursors_iff {nodes env} (h : Coherent nodes env) (first n : Name) :
    Hit (recursors nodes) first n ↔
      ∃ rv, env.consts.get? n = some (.recInfo rv) ∧ rv.all[0]? = some first := by
  rw [recursors_hit]
  constructor
  · rintro ⟨node, all, found, group, head⟩
    rw [h n] at found
    obtain ⟨ci, stored, rfl⟩ := Option.map_eq_some_iff.mp found
    cases ci <;> simp only [capture, captureUsing] at group
    all_goals first | contradiction | (cases group; exact ⟨_, stored, head⟩)
  · rintro ⟨rv, found, head⟩
    refine ⟨capture (.recInfo rv), rv.all, ?_, rfl, head⟩
    rw [h n, found]; rfl

private theorem reference_hit (env : Ix.Environment) (first n : Name) :
    Hit (recursorsByBlock env) first n ↔
      ∃ rv, env.consts.get? n = some (.recInfo rv) ∧ rv.all[0]? = some first := by
  constructor
  · rintro ⟨p, stored, eq, same⟩
    obtain ⟨rv, found, head⟩ := Closure.recursors_sound stored
    refine ⟨rv, ?_, head.trans (congrArg some eq)⟩
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr same]
    exact found
  · rintro ⟨rv, found, head⟩
    obtain ⟨k, same, stored⟩ := Closure.recursors_complete found head
    exact ⟨(first, k), stored, rfl, same⟩

private theorem filtered_contains (rs : Recursors) (first n : Name) :
    (((rs.getD first #[]).filter (Ix.Cert.nameEq ·.1 first)).map (·.2)).contains n = true ↔
      Hit rs first n := by
  rw [Array.contains_iff_exists_mem_beq]
  constructor
  · rintro ⟨k, member, same⟩
    obtain ⟨p, filtered, rfl⟩ := Array.mem_map.mp member
    obtain ⟨stored, eq⟩ := Array.mem_filter.mp filtered
    exact ⟨p, stored, (Closure.nameEq_iff ..).mp eq, same⟩
  · rintro ⟨p, stored, eq, same⟩
    exact ⟨p.2, Array.mem_map.mpr ⟨p, Array.mem_filter.mpr
      ⟨stored, (Closure.nameEq_iff ..).mpr eq⟩, rfl⟩, same⟩

private theorem dependency_contains {nodes env} (h : Coherent nodes env) (ci : ConstantInfo) (n : Name) :
    (Ix.Compile.SourceGraph.dependencies (recursors nodes) (capture ci)).contains n =
      (Ix.Cert.dependencies (recursorsByBlock env) ci).contains n := by
  have buckets : ∀ first,
      (((recursors nodes).getD first #[]).filter (Ix.Cert.nameEq ·.1 first) |>.map (·.2)).contains n =
      (((recursorsByBlock env).getD first #[]).filter (Ix.Cert.nameEq ·.1 first) |>.map (·.2)).contains n := by
    intro first
    apply Bool.eq_iff_iff.mpr
    rw [filtered_contains, filtered_contains, recursors_iff h, reference_hit]
  rw [SourceGraph.dependencies_capture]
  cases ci <;> try rfl
  rename_i v
  cases hf : v.all[0]? with
  | none => simp only [Ix.Cert.dependencies, hf]
  | some first => simp only [Ix.Cert.dependencies, hf, Array.contains_append, buckets]

private theorem dependencies_iff {nodes env} (h : Coherent nodes env) {a ci}
    (found : env.consts.get? a = some ci) (d : Name) :
    (Ix.Compile.SourceGraph.dependencies (recursors nodes) (capture ci)).contains d = true ↔
      DependsOn env a d := by
  rw [dependency_contains h]
  constructor
  · intro present
    obtain ⟨k, member, same⟩ := Array.contains_iff_exists_mem_beq.mp present
    exact Closure.dependsOn_congr (Closure.dependencies_sound found member) (BEq.symm same)
  · intro edge
    obtain ⟨k, member, same⟩ := Closure.dependencies_complete found edge
    exact Array.contains_iff_exists_mem_beq.mpr ⟨k, member, same⟩

private theorem append_contains (m : Index) (key caller dependency query : Name) :
    ((appendAt m key caller).getD dependency #[]).contains query = true ↔
      (m.getD dependency #[]).contains query = true ∨
      (key == dependency) = true ∧ (query == caller) = true := by
  rw [append_lookup]
  by_cases h : (key == dependency) = true
  · simp only [h, ite_true, Std.HashMap.getD_congr h, Array.contains_push, Bool.or_eq_true]
    simp
  · simp [h]

private theorem caller_contains (rs : Recursors) (m : Index) (p : Name × Node) (d n : Name) :
    ((addCaller rs m p).getD d #[]).contains n = true ↔
      (m.getD d #[]).contains n = true ∨
      ∃ x ∈ Ix.Compile.SourceGraph.dependencies rs p.2, (x == d) = true ∧ (n == p.1) = true := by
  unfold addCaller
  rw [← Array.foldl_toList, fold_iff (fun m x => appendAt m x p.1)
    (fun m => (m.getD d #[]).contains n = true) (fun x => (x == d) = true ∧ (n == p.1) = true)
    (fun m x => append_contains m x p.1 d n)]
  simp only [Array.mem_toList_iff]

private theorem build_iff {nodes env} (h : Coherent nodes env) (d n : Name) :
    ((build nodes).getD d #[]).contains n = true ↔ DependsOn env n d := by
  unfold build
  rw [Std.HashMap.fold_eq_foldl_toList]
  change ((nodes.toList.foldl (fun m p => addCaller (recursors nodes) m p) {}).getD d #[]).contains n = true ↔ _
  rw [fold_iff (fun m p => addCaller (recursors nodes) m p)
    (fun m => (m.getD d #[]).contains n = true)
    (fun p => ∃ x ∈ Ix.Compile.SourceGraph.dependencies (recursors nodes) p.2,
      (x == d) = true ∧ (n == p.1) = true) (fun m p => caller_contains _ m p d n)]
  simp only [Std.HashMap.getD_empty, Array.contains_empty, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨⟨k, node⟩, stored, x, member, sameD, sameN⟩
    have found : nodes.get? n = some node := by
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr sameN]
      exact (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp stored).2
    rw [h n] at found
    obtain ⟨ci, canonicalFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact Closure.dependsOn_congr ((dependencies_iff h canonicalFound x).mp
      (Array.contains_eq_true_of_mem member)) sameD
  · intro edge
    obtain ⟨ci, found, rest⟩ := edge
    have present : nodes.get? n = some (capture ci) := by rw [h n, found]; rfl
    obtain ⟨k, same, stored⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp present
    obtain ⟨x, member, sameD⟩ := Array.contains_iff_exists_mem_beq.mp
      ((dependencies_iff h found d).mpr ⟨ci, found, rest⟩)
    exact ⟨(k, capture ci), stored, x, member, BEq.symm sameD, same⟩

/-- Exact edges from the actual collector, including forced labelled aliases. -/
theorem collected_edges (rows : List (Name × ConstantInfo)) (d n : Name) :
    ((build (collect (rows.map fun (k, ci) => rowOfCanonical k ci)).nodes).getD d #[]).contains n = true ↔
      DependsOn (SourceGraph.full rows) n d :=
  build_iff (SourceGraph.collect_nodes_get rows) d n

private theorem produced_coherent (reserved : Lean.ConstantInfo → Bool)
    (raw : Array SourcePrepass.Raw) (workers : Nat) :
    Coherent (Prepass.produce reserved raw workers).2.facts.nodes (SourceGraph.full (SourceStream.canonical raw)) := by
  rw [SourcePrepass.produced_facts]
  exact SourceGraph.collect_nodes_get _

/-- Structural first-member filtering, with the actual stored caller names. -/
theorem produced_recursors (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (first n : Name) :
    (((recursors (Prepass.produce reserved raw workers).2.facts.nodes).getD first #[]).filter
      (Ix.Cert.nameEq ·.1 first) |>.map (·.2)).contains n = true ↔
      ∃ rv, (SourceGraph.full (SourceStream.canonical raw)).consts.get? n = some (.recInfo rv) ∧
        rv.all[0]? = some first := by
  rw [filtered_contains, recursors_iff (produced_coherent reserved raw workers)]

theorem produced_edges (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (d n : Name) :
    ((build (Prepass.produce reserved raw workers).2.facts.nodes).getD d #[]).contains n = true ↔
      DependsOn (SourceGraph.full (SourceStream.canonical raw)) n d :=
  build_iff (produced_coherent reserved raw workers) d n

private theorem walk_eq (a b : Index)
    (edges : ∀ d n, (a.getD d #[]).contains n = (b.getD d #[]).contains n)
    (seeds : Std.HashSet Name) (n : Name) :
    (SourceReverse.walk a seeds).seen.contains n = (SourceReverse.walk b seeds).seen.contains n := by
  apply Bool.eq_iff_iff.mpr
  rw [SourceReverse.walk_contains_iff, SourceReverse.walk_contains_iff]
  constructor <;> intro reached
  · induction reached with
    | seed h => exact .seed h
    | step _ edge ih => exact .step ih (by rw [← edges]; exact edge)
  · induction reached with
    | seed h => exact .seed h
    | step _ edge ih => exact .step ih (by rw [edges]; exact edge)

/-- The generic derived budget suffices, including absent changed seeds. -/
theorem produced_affected (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (cs : Ix.Compile.ChangedSet.ChangedSet) (n : Name) :
    (SourceReverse.walk (build (Prepass.produce reserved raw workers).2.facts.nodes) cs.names).seen.contains n =
      SelectedRoots.affected (SourceGraph.full (SourceStream.canonical raw)) cs n := by
  have edges := fun d k => Bool.eq_iff_iff.mpr
    ((produced_edges reserved raw workers d k).trans
      (SourceReverse.build_contains_iff (SourceGraph.full (SourceStream.canonical raw)) d k).symm)
  exact (walk_eq _ _ edges cs.names n).trans (SourceReverse.affectedNames_contains_eq _ cs n)

/-- Unwired proof/test adapter: the supplied publication domain and order
remain exactly the reference's. No original-input enumeration is inferred. -/
def select (nodes : Ix.Map Name Node) (cs : Ix.Compile.ChangedSet.ChangedSet)
    (sub : Ix.Environment) (ixe : Ixon.Env) : List SelectedRoots.Root :=
  let seen := (SourceReverse.walk (build nodes) cs.names).seen
  SelectedRoots.directRoots cs sub ixe ++
    (sub.consts.toList.filterMap fun (n, _) =>
      if cs.contains n = false ∧ seen.contains n = true then
        (SelectedRoots.published? sub ixe n).map fun a => ⟨n, a, .cascade⟩
      else none) ++ SelectedRoots.rowRoots cs sub ixe

/-- Literal ordered-list equality at the SAME cs/sub/ixe, not a publication
adapter, classifier theorem, grounding correspondence or admission result. -/
theorem produced_select (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (cs : Ix.Compile.ChangedSet.ChangedSet) (sub : Ix.Environment) (ixe : Ixon.Env) :
    select (Prepass.produce reserved raw workers).2.facts.nodes cs sub ixe =
      SelectedRoots.select (SourceGraph.full (SourceStream.canonical raw)) cs sub ixe := by
  simp only [select, SelectedRoots.select, SelectedRoots.cascadeRoots, produced_affected]

end Ix.Cert.SourceSummaryReverse
