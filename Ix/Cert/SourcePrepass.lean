import Ix.Compile.SourceGraph.Prepass
import Ix.Cert.SourceStream
import Ix.Cert.Hybrid

namespace Ix.Cert.SourcePrepass
open Ix (Name ConstantInfo)
open Ix.Compile.SourceGraph
open Ix.Compile.SourceGraph.Prepass

abbrev Raw := Lean.Name × Lean.ConstantInfo
def keyed (input : Array Raw) : List (Name × Raw) := input.toList.map fun p => (Canon.nameS p.1, p)
def inserted (xs : List (Name × α)) : Ix.Map Name α := xs.foldl (fun m p => m.insert p.1 p.2) {}

private theorem fields (xs : List Raw) (state : Names) :
    let out := xs.foldl nameStep state
    out.leanByIx = xs.foldl (fun m p => m.insert (Canon.nameS p.1) p) state.leanByIx ∧
    out.thinConsts = xs.foldl (fun m p => m.insert (Canon.nameS p.1) (placeholder p.2)) state.thinConsts ∧
    out.labelled.toList = state.labelled.toList ++ xs.map (fun p => (Canon.nameS p.1, p.2)) := by
  induction xs generalizing state with
  | nil => simp
  | cons p xs ih =>
    dsimp only [List.foldl_cons]
    rw [nameStep, Canon.canonName_run]
    obtain ⟨raw, thin, labels⟩ := ih (addNamed state (Canon.nameS p.1) p)
    exact ⟨raw, thin, by simpa [addNamed, List.append_assoc] using labels⟩

theorem prepass_raw (input : Array Raw) : (run input).leanByIx = inserted (keyed input) := by
  unfold run
  rw [← Array.foldl_toList]
  simpa [inserted, keyed, List.foldl_map] using (fields input.toList {}).1

theorem prepass_thin (input : Array Raw) :
    (run input).thinConsts = inserted ((keyed input).map fun p => (p.1, placeholder p.2.2)) := by
  unfold run
  rw [← Array.foldl_toList]
  simpa [inserted, keyed, List.foldl_map, Function.comp_def] using (fields input.toList {}).2.1

theorem prepass_labels (input : Array Raw) : (run input).labelled = Stream.label input := by
  apply Array.toList_inj.mp
  unfold run
  rw [← Array.foldl_toList]
  simpa [SourceStream.label_eq, Array.toList_map] using (fields input.toList {}).2.2

theorem prepass_length (input : Array Raw) : (run input).labelled.size = input.size := by
  rw [prepass_labels, SourceStream.label_eq, Array.size_map]

private theorem project_fold (xs : List (Name × α)) (f : α → β)
    (a : Ix.Map Name α) (b : Ix.Map Name β)
    (values : ∀ n, b.get? n = (a.get? n).map f) (keys : ∀ n, b.getKey? n = a.getKey? n) :
    let aa := xs.foldl (fun m p => m.insert p.1 p.2) a
    let bb := xs.foldl (fun m p => m.insert p.1 (f p.2)) b
    (∀ n, bb.get? n = (aa.get? n).map f) ∧ (∀ n, bb.getKey? n = aa.getKey? n) := by
  induction xs generalizing a b with
  | nil => exact ⟨values, keys⟩
  | cons p xs ih =>
    apply ih
    · intro n
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      split <;> simp_all
    · intro n
      simp only [Std.HashMap.getKey?_insert]
      split <;> simp_all

theorem inserted_project (xs : List (Name × α)) (f : α → β) :
    (∀ n, (inserted (xs.map fun p => (p.1, f p.2))).get? n = ((inserted xs).get? n).map f) ∧
    (∀ n, (inserted (xs.map fun p => (p.1, f p.2))).getKey? n = (inserted xs).getKey? n) := by
  simpa only [inserted, List.foldl_map] using
    project_fold xs f {} {} (fun n => by simp) (fun n => by simp)

private theorem full_eq (input : Array Raw) : (SourceGraph.full (SourceStream.canonical input)).consts =
    inserted ((keyed input).map fun p => (p.1, Canon.constS p.2.2)) := by
  simp only [SourceGraph.full, SourceStream.canonical, inserted, keyed, List.map_map, Function.comp_def]

theorem canonical_lookup (input : Array Raw) (n : Name) :
    (SourceGraph.full (SourceStream.canonical input)).consts.get? n =
      ((run input).leanByIx.get? n).map (fun p => Canon.constS p.2) := by
  rw [full_eq, prepass_raw]
  exact (inserted_project (keyed input) (fun p : Raw => Canon.constS p.2)).1 n

theorem canonical_key (input : Array Raw) (n : Name) :
    (SourceGraph.full (SourceStream.canonical input)).consts.getKey? n = (run input).leanByIx.getKey? n := by
  rw [full_eq, prepass_raw]
  exact (inserted_project (keyed input) (fun p : Raw => Canon.constS p.2)).2 n

theorem thin_lookup (input : Array Raw) (n : Name) : (run input).thinConsts.get? n =
    ((run input).leanByIx.get? n).map (fun p => placeholder p.2) := by
  rw [prepass_thin, prepass_raw]
  exact (inserted_project (keyed input) (fun p : Raw => placeholder p.2)).1 n

theorem thin_key (input : Array Raw) (n : Name) :
    (run input).thinConsts.getKey? n = (run input).leanByIx.getKey? n := by
  rw [prepass_thin, prepass_raw]
  exact (inserted_project (keyed input) (fun p : Raw => placeholder p.2)).2 n

theorem produced_facts (input : Array Raw) (workers : Nat) :
    (produce input workers).2.facts =
      collect ((SourceStream.canonical input).map fun (n, ci) => rowOfCanonical n ci) := by
  dsimp only [produce]
  rw [prepass_labels]
  exact SourceStream.runSource_facts _ input workers

private theorem keys_values_equiv {a b : Ix.Map Name α}
    (keys : ∀ n, a.getKey? n = b.getKey? n) (values : ∀ n, a.get? n = b.get? n) : Std.HashMap.Equiv a b := by
  apply Std.HashMap.Equiv.of_forall_getKey_eq_of_forall_getElem?_eq
  · intro n ha hb
    exact Option.some.inj ((Std.HashMap.getKey?_eq_some_getKey ha).symm.trans
      ((keys n).trans (Std.HashMap.getKey?_eq_some_getKey hb)))
  · exact values

private theorem mapped_get (m : Ix.Map Name α) (f : α → β) (n : Name) :
    (m.map (fun _ v => f v)).get? n = (m.get? n).map f := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map', Option.pmap_eq_map]

theorem canonical_equiv (input : Array Raw) : Std.HashMap.Equiv
    (SourceGraph.full (SourceStream.canonical input)).consts
    ((run input).leanByIx.map (fun _ p => Canon.constS p.2)) := by
  apply keys_values_equiv
  · intro n; rw [Std.HashMap.getKey?_map]; exact canonical_key input n
  · intro n; rw [mapped_get]; exact canonical_lookup input n

theorem canonical_size (input : Array Raw) :
    (SourceGraph.full (SourceStream.canonical input)).consts.size = (run input).leanByIx.size := by
  rw [(canonical_equiv input).size_eq, Std.HashMap.size_map]

theorem thin_size (input : Array Raw) : (run input).thinConsts.size = (run input).leanByIx.size := by
  have eqv : Std.HashMap.Equiv (run input).thinConsts
      ((run input).leanByIx.map (fun _ p => placeholder p.2)) := by
    apply keys_values_equiv
    · intro n; rw [Std.HashMap.getKey?_map]; exact thin_key input n
    · intro n; rw [mapped_get]; exact thin_lookup input n
  rw [eqv.size_eq, Std.HashMap.size_map]

private def KeptKeys (code full : Ix.Map Name ConstantInfo) : Prop := ∀ n,
  code.getKey? n = if ((full.get? n).bind keep).isSome then full.getKey? n else none

private theorem keptKeys_step (acc : Collected) (full : Ix.Map Name ConstantInfo)
    (h : KeptKeys acc.code full) (n : Name) (ci : ConstantInfo) :
    KeptKeys (mergeRow acc (rowOfCanonical n ci)).code (full.insert n ci) := by
  intro query
  cases kept : keep ci <;>
    simp only [mergeRow, rowOfCanonical, kept, Std.HashMap.getKey?_erase, Std.HashMap.getKey?_insert,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  all_goals split
  all_goals first | simp [kept] | exact h query

private theorem keptKeys_fold (xs : List (Name × ConstantInfo)) (acc : Collected)
    (full : Ix.Map Name ConstantInfo) (h : KeptKeys acc.code full) :
    KeptKeys ((xs.map fun p => rowOfCanonical p.1 p.2).foldl mergeRow acc).code
      (xs.foldl (fun m p => m.insert p.1 p.2) full) := by
  induction xs generalizing acc full with
  | nil => exact h
  | cons p xs ih => exact ih _ _ (keptKeys_step acc full h p.1 p.2)

/-- A kept winner has the exact stored representative of the full map. -/
theorem collect_key (xs : List (Name × ConstantInfo)) (n : Name) :
    (collect (xs.map fun p => rowOfCanonical p.1 p.2)).code.getKey? n =
      if (((SourceGraph.full xs).consts.get? n).bind keep).isSome then
        (SourceGraph.full xs).consts.getKey? n else none :=
  keptKeys_fold xs {} {} (by intro n; simp) n

private theorem filter_get (m : Ix.Map Name ConstantInfo) (n : Name) :
    (m.filterMap (fun _ ci => keep ci)).get? n = (m.get? n).bind keep := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filterMap, Option.pbind_eq_bind]

theorem code_equiv_filter (xs : List (Name × ConstantInfo)) : Std.HashMap.Equiv
    (collect (xs.map fun p => rowOfCanonical p.1 p.2)).code
    ((SourceGraph.full xs).consts.filterMap (fun _ ci => keep ci)) := by
  apply Std.HashMap.Equiv.of_forall_getKey_eq_of_forall_getElem?_eq
  · intro n hc hf
    have present : (((SourceGraph.full xs).consts.get? n).bind keep).isSome = true := by
      rw [← SourceGraph.collect_code_get]
      exact Std.HashMap.mem_iff_isSome_getElem?.mp hc
    have reps := collect_key xs n
    rw [present] at reps
    have eq := Option.some.inj ((Std.HashMap.getKey?_eq_some_getKey hc).symm.trans
      (reps.trans (Std.HashMap.getKey?_eq_some_getKey (Std.HashMap.mem_of_mem_filterMap hf))))
    simpa only [Std.HashMap.getKey_filterMap] using eq
  · intro n
    change _ = (_ : Ix.Map Name ConstantInfo).get? n
    rw [filter_get]
    exact SourceGraph.collect_code_get xs n

theorem code_size (input : Array Raw) (workers : Nat) :
    (produce input workers).2.facts.code.size ≤ (run input).leanByIx.size := by
  rw [produced_facts, (code_equiv_filter _).size_eq, ← canonical_size input]
  exact Std.HashMap.size_filterMap_le_size

theorem code_contains (input : Array Raw) (workers : Nat)
    (n : Name) (h : (produce input workers).2.facts.code.contains n = true) :
    (run input).leanByIx.contains n = true := by
  rw [produced_facts, (code_equiv_filter _).contains_eq] at h
  have present := Std.HashMap.contains_of_contains_filterMap h
  simpa only [(canonical_equiv input).contains_eq, Std.HashMap.contains_map] using present

theorem source_count (input : Array Raw) (workers : Nat) :
    let code := (produce input workers).2.facts.code.size
    code + ((run input).leanByIx.size - code) = (SourceGraph.full (SourceStream.canonical input)).consts.size := by
  have bound := code_size input workers
  have size := canonical_size input
  dsimp only
  omega

private theorem full_get (xs : List (Name × ConstantInfo)) (n : Name) :
    (SourceGraph.full xs).get? n = (SourceGraph.full xs).consts.get? n := by
  unfold Ix.Environment.get?
  cases (SourceGraph.full xs).consts.get? n <;> rfl

theorem produced_hybrid_lookup (input : Array Raw)
    (workers : Nat) (n : Name) :
    (Hybrid.hybridEnv (produce input workers).2.facts.code (run input).leanByIx).get? n =
      (SourceGraph.full (SourceStream.canonical input)).get? n := by
  apply Hybrid.hybrid_lookups
  · intro k
    rw [full_get]
    exact canonical_lookup input k
  · intro k ci found
    rw [produced_facts, SourceGraph.collect_code_get] at found
    obtain ⟨original, stored, kept⟩ := Option.bind_eq_some_iff.mp found
    have same : original = ci := by cases original <;> simp [keep] at kept <;> exact kept
    subst original
    rw [full_get]
    exact stored

theorem stored_inductives (input : Array Raw)
    (workers : Nat) (n : Name) (v : Ix.InductiveVal) :
    (n, ConstantInfo.inductInfo v) ∈ (produce input workers).2.facts.code.toList ↔
      (n, ConstantInfo.inductInfo v) ∈ (SourceGraph.full (SourceStream.canonical input)).consts.toList := by
  rw [produced_facts, Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some,
    Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some]
  change (_ = _ ∧ (collect _).code.get? n = _) ↔ (_ = _ ∧ (_ : Ix.Map Name ConstantInfo).get? n = _)
  rw [collect_key, SourceGraph.collect_code_get]
  constructor
  · rintro ⟨key, value⟩
    obtain ⟨ci, stored, kept⟩ := Option.bind_eq_some_iff.mp value
    have same : ci = .inductInfo v := by
      cases ci <;> simp [keep] at kept
      exact congrArg ConstantInfo.inductInfo kept
    subst ci
    exact ⟨by simpa only [stored, Option.bind_some, keep, Option.isSome_some, ite_true] using key, stored⟩
  · rintro ⟨key, stored⟩
    simp only [stored, Option.bind_some, keep, Option.isSome_some, ite_true, key, and_self]

/-- All four Hybrid inputs are derived from this producer. The condensation
is the same argument on both sides; its grounding provenance is not claimed. -/
theorem produced_fold (input : Array Raw) (workers : Nat)
    (blocks : Ix.CondensedBlocks) (dbg : Bool) (limits : Ix.Sharing.Exact.Limits) (width : Nat) :
    let code := (produce input workers).2.facts.code
    let names := (run input).leanByIx
    Ix.CompileM.compileEnvFold (Hybrid.hybridEnv code names) blocks dbg (names.size - code.size) limits width =
      Hybrid.restore (Hybrid.hybridEnv code names) (names.size - code.size) <$>
        Ix.CompileM.compileEnvFold (SourceGraph.full (SourceStream.canonical input)) blocks false 0 limits
          Ix.CompileM.foldWaveTasks := by
  apply Hybrid.pipeline_fold
  · intro n; rw [full_get]; exact canonical_lookup input n
  · intro n ci stored
    rw [← produced_hybrid_lookup input workers n]
    simp only [Hybrid.hybridEnv, Ix.Environment.get?, stored]
  · exact ⟨code_size input workers, canonical_size input⟩
  · exact stored_inductives input workers

end Ix.Cert.SourcePrepass
