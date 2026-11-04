import Ix.Cert.SourceReplay

/-! # Stable replay through Source collapse and commit

The actual readStep/readLoop execution preserves exact owners, basis-freedom
and replay fixed points, while raw-prefix and retained-prefix replay agree
at all five semantic lookups. SourceRetained supplies the retained generated
boundary needed to recover the index-dependent commit folds.

The generic endpoint keeps its internal owner, basis, stability and raw
classification premises explicit. A concrete quotient-conversion wrapper
supplies classification; extraction from the production scheduled trace and
that trace's StableOwned invariant remain follow-ups. No counter or raw/kept
declaration-array equality, final acceptance or new final premise is claimed.
-/

namespace Ix.Cert.SourceCommit

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude Ix.Cert.SourceReplay

def sideState (st : State .source) (r : Read .source) : State .source :=
  r.blocks.foldl (fun s b => { s with indBlocks := s.indBlocks.insert b.1 b.2 })
    (r.owners.foldl (fun s o => { s with projOwners := s.projOwners.insert o.T o }) st)

def noted (st : State .source) (r : Read .source) : State .source :=
  r.decls.toList.foldl replay (sideState st r)

theorem sideState_fields (st : State .source) (r : Read .source) :
    (sideState st r).constTypes = st.constTypes ∧ (sideState st r).heights = st.heights ∧
      (sideState st r).projLevels = st.projLevels :=
  ⟨CtxAgree.commit_pre_keep _ r st (fun _ _ => rfl) (fun _ _ => rfl),
    CtxAgree.commit_pre_keep _ r st (fun _ _ => rfl) (fun _ _ => rfl),
    CtxAgree.commit_pre_keep _ r st (fun _ _ => rfl) (fun _ _ => rfl)⟩

theorem stable_sideState {s : CollapseState} {st : State .source}
    (h : StableOwned s st) (r : Read .source) : StableOwned s (sideState st r) :=
  let ⟨ht, hh, hl⟩ := sideState_fields st r
  h.fields ht hh hl

def Classified (r : Read .source) : Prop :=
  (∀ d ∈ r.decls.toList.take r.generated, d.isGenerated = true) ∧
    (∀ d ∈ r.decls.toList.drop r.generated, d.isGenerated = false)

theorem Classified.step {r : Read .source} (h : Classified r) {x : Declaration .source × Nat}
    (hx : x ∈ r.decls.toList.zipIdx) (st : State .source) :
    (if x.2 < r.generated then st.noteGenerated x.1 else st.note x.1) = replay st x.1 := by
  have hr := List.mem_zipIdx_iff_getElem?.mp hx
  by_cases early : x.2 < r.generated
  · have hg := h.1 x.1 (List.mem_of_getElem? ((List.getElem?_take_of_lt early).trans hr))
    simp [early, replay, hg]
  · have hi : r.generated + (x.2 - r.generated) = x.2 := by omega
    have hm : x.1 ∈ r.decls.toList.drop r.generated :=
      List.mem_of_getElem? (i := x.2 - r.generated) (by simpa only [List.getElem?_drop, hi] using hr)
    simp [early, replay, h.2 x.1 hm]

theorem fold_eq {α σ : Type} (f g : σ → α → σ) : ∀ (xs : List α),
    (∀ s x, x ∈ xs → f s x = g s x) → ∀ s, xs.foldl f s = xs.foldl g s := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons x xs ih =>
    intro h s
    simp only [List.foldl_cons]
    rw [h s x List.mem_cons_self]
    exact ih (fun s y hy => h s y (List.mem_cons_of_mem _ hy)) _

/-- For a classified read, commit is its replay fold followed by the actual
rewrite-counter update. This does not identify raw and kept states. -/
theorem commit_replay {r : Read .source} (h : Classified r) (st : State .source) :
    st.commit r = { noted st r with projRewrites := (noted st r).projRewrites + r.projRewrites } := by
  have he := fold_eq (fun s (x : Declaration .source × Nat) =>
      if x.2 < r.generated then s.noteGenerated x.1 else s.note x.1)
    (fun s x => replay s x.1) r.decls.toList.zipIdx (fun s x hx => h.step hx s) (sideState st r)
  rw [CtxAgree.foldl_zipIdx_fst] at he
  rw [CtxAgree.commit_eq]
  exact congrArg (fun t : State .source => { t with projRewrites := t.projRewrites + r.projRewrites }) he

def Inv (base : State .source) (pre : List (Declaration .source × Nat)) (a : ReadAcc) : Prop :=
  a.1 = none ∧ OwnerExact a.2.1 ∧ KeptNoBasis a.2.1 ∧
    StableOwned a.2.1 (a.2.2.1.toList.foldl replay base) ∧
    ∀ k, ((pre.map Prod.fst).foldl replay base).SameAt (a.2.2.1.toList.foldl replay base) k

theorem readStep_inv {base : State .source} {pre : List (Declaration .source × Nat)} {a : ReadAcc}
    (ha : Inv base pre a) (first : SKey) (originalSize generated : Nat) (x : Declaration .source × Nat)
    (basis : NoBasis x.1) :
    match readStep first originalSize generated x a with
    | .yield a' => Inv base (pre ++ [x]) a'
    | .done a' => ReadBad a' := by
  rcases hs : a.2.1.step first x.1 with ⟨next, res⟩
  cases res with
  | error e => simp only [readStep, hs, pure]; exact ⟨next.restore originalSize, e, rfl⟩
  | ok kept =>
    have step := step_replay ha.2.1 ha.2.2.1 ha.2.2.2.1 basis hs
    have agree : ∀ k, (replay ((pre.map Prod.fst).foldl replay base) x.1).SameAt
        (if kept then replay (a.2.2.1.toList.foldl replay base) x.1 else a.2.2.1.toList.foldl replay base) k :=
      fun k => sameAt_trans (replay_congr (ha.2.2.2.2 k) x.1) (step.2.2.2 k)
    cases kept with
    | false =>
      simp only [readStep, hs, pure]
      refine ⟨rfl, step.1, step.2.1, step.2.2.1, ?_⟩
      intro k
      simpa only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons,
        List.foldl_nil, Bool.false_eq_true, ite_false] using agree k
    | true =>
      have good (n : Nat) (dropped : Array SKey) :
          Inv base (pre ++ [x]) (none, next, a.2.2.1.push x.1, n, dropped) := by
        refine ⟨rfl, step.1, step.2.1, ?_, ?_⟩
        · simpa only [Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil, ite_true] using step.2.2.1
        · intro k
          simpa only [Array.toList_push, List.map_append, List.map_singleton,
            List.foldl_append, List.foldl_cons, List.foldl_nil, ite_true] using agree k
      by_cases early : x.2 < generated
      · simpa only [readStep, hs, early, ite_true, pure] using good (a.2.2.2.1 + 1) a.2.2.2.2
      · simpa only [readStep, hs, early, ite_false, pure] using good a.2.2.2.1 a.2.2.2.2

theorem collapseRead_replay {s s' : CollapseState} {base : State .source}
    (owner : OwnerExact s) (basis : KeptNoBasis s) (stable : StableOwned s base)
    {first : SKey} {raw kept : Read .source} {dropped : Array SKey}
    (rawBasis : ∀ d ∈ raw.decls.toList, NoBasis d)
    (h : collapseRead s first raw = (s', .ok (kept, dropped))) :
    OwnerExact s' ∧ KeptNoBasis s' ∧ StableOwned s' (kept.decls.toList.foldl replay base) ∧
      ∀ k, (raw.decls.toList.foldl replay base).SameAt (kept.decls.toList.foldl replay base) k := by
  have start : Inv base [] (none, s, #[], 0, #[]) :=
    ⟨rfl, owner, basis, stable, fun k => sameAt_refl _ k⟩
  have inv := forIn_id_inv_or_array (Inv base) ReadBad (readStep first s.kept.size raw.generated)
    raw.decls.zipIdx (fun pre x post a whole ha => by
      have hx : x ∈ raw.decls.toList.zipIdx := by
        rw [← Array.toList_zipIdx, ← whole]
        exact List.mem_append_right _ List.mem_cons_self
      have step := readStep_inv ha first s.kept.size raw.generated x (rawBasis x.1 (List.fst_mem_of_mem_zipIdx hx))
      cases hb : readStep first s.kept.size raw.generated x a <;> simpa only [hb] using step) _ start
  change Inv base raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
  rw [collapseRead_eq] at h
  rcases inv with hi | hb
  · have active := hi.1
    simp only [readFinish, active, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨hst, hkeep, _⟩
    subst s'; subst kept
    simpa only [Array.toList_zipIdx, List.zipIdx_map_fst] using hi.2
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

/-- The actual raw and kept commits agree at all five semantic lookups under
the internal reachable-state invariants. Counters need not agree. -/
theorem collapseRead_commit {s s' : CollapseState} {st : State .source}
    (owner : OwnerExact s) (basis : KeptNoBasis s) (stable : StableOwned s st)
    {first : SKey} {raw kept : Read .source} {dropped : Array SKey}
    (classified : Classified raw) (rawBasis : ∀ d ∈ raw.decls.toList, NoBasis d)
    (h : collapseRead s first raw = (s', .ok (kept, dropped))) :
    OwnerExact s' ∧ KeptNoBasis s' ∧ StableOwned s' (st.commit kept) ∧
      ∀ k, (st.commit raw).SameAt (st.commit kept) k := by
  have ck : Classified kept := (SourceRetained.collapseRead_retained h).transfer classified.1 classified.2
  obtain ⟨_, _, _, _, _, owners, blocks⟩ := collapseRead_facts h
  have sides : sideState st kept = sideState st raw := by simp only [sideState, owners, blocks]
  have loop := collapseRead_replay owner basis (stable_sideState stable raw) rawBasis h
  have out : OwnerExact s' ∧ KeptNoBasis s' ∧ StableOwned s' (noted st kept) ∧
      ∀ k, (noted st raw).SameAt (noted st kept) k := by
    simpa only [noted, sides] using loop
  simp only [commit_replay classified st, commit_replay ck st]
  exact ⟨out.1, out.2.1, out.2.2.1.fields rfl rfl rfl, out.2.2.2⟩

/-- Classification of a concrete production quotient conversion. This does
not extract its witnesses from an arbitrary scheduled trace. -/
theorem quotient_lower_classified {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {gr : Group} {c : Converted} (converted : convert gr = .ok c)
    (hints : CName .source → Option ReducibilityHint) {st : State .source} {raw : Read .source}
    (lowered : lower st ((c.withHints hints).quotient (fiberAliasAt ixe roles)) = .ok raw) : Classified raw :=
  ⟨SourceNames.lower_generated lowered, fun d hd => ReaderUnits.isGenerated_false
    (SourceNames.quotient_lower_ordinary converted hints lowered d hd)⟩

end Ix.Cert.SourceCommit
