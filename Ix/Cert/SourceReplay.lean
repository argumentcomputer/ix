import Ix.Cert.SourceRetained
import Ix.Cert.CtxAgreeProjFields

/-! # Exact owners and stable replay for Source collapse steps

Reachable owner indices identify actual kept declarations, and a successful
drop is exactly one of them. Basis-freedom is proved separately from actual
Source lowering and is required by the name-frame arguments: basisDecl.names
does not describe all of its writes.

Replay fixed points compare the five semantic lookups. Absent height writes
retain earlier entries; repeated keys within one indDecl need no all-entry
equality. Successful individual steps preserve exact owners, basis-freedom
and stable replay. Counters and raw/kept arrays are not equated.

This primitive layer does not yet assemble the actual read-loop invariant,
convert its replay fold to index-dependent commits, or discharge production
Trace stability. Those remain follow-up obligations, not final assumptions.
-/

namespace Ix.Cert.SourceReplay

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude

/-- Owners are precisely the actual kept-array indices of declarations
claiming the key. In particular, a stored index cannot be out of bounds. -/
def OwnerExact (s : CollapseState) : Prop := ∀ (k : SKey) (i : Nat),
  s.owner[k]? = some i ↔ ∃ d : Declaration .source, s.kept[i]? = some d ∧ k ∈ d.names

theorem OwnerExact.empty : OwnerExact {} := by intro k i; simp

theorem OwnerExact.push {s : CollapseState} (h : OwnerExact s) (d : Declaration .source)
    (fresh : ∀ k ∈ d.names, s.owner[k]? = none) :
    OwnerExact { kept := s.kept.push d, owner := claimKeys s.owner d.names s.kept.size } := by
  intro k i
  change (claimKeys s.owner d.names s.kept.size)[k]? = some i ↔
    ∃ e, (s.kept.push d)[i]? = some e ∧ k ∈ e.names
  by_cases hk : k ∈ d.names
  · rw [claimKeys_claimed _ _ _ _ hk]
    by_cases hi : i = s.kept.size
    · subst i; simp [hk]
    · rw [Array.getElem?_push, ite_eq_right hi]
      constructor
      · intro he; exact (hi (Option.some.inj he).symm).elim
      · intro he
        have ho := (h k i).2 he
        rw [fresh k hk] at ho
        cases ho
  · rw [claimKeys_outside _ _ _ _ hk]
    by_cases hi : i = s.kept.size
    · subst i
      have ho : s.owner[k]? ≠ some s.kept.size := by
        intro he
        obtain ⟨e, he, _⟩ := (h k s.kept.size).1 he
        simp at he
      simp [hk, ho]
    · simpa only [Array.getElem?_push, ite_eq_right hi] using h k i

theorem findSome_some {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) {v : β}, xs.findSome? f = some v → ∃ x ∈ xs, f x = some v := by
  intro xs
  induction xs with
  | nil => intro v h; cases h
  | cons x xs ih =>
    intro v h
    cases hx : f x with
    | none =>
      obtain ⟨y, hy, hv⟩ := ih (by simpa [List.findSome?, hx] using h)
      exact ⟨y, List.mem_cons_of_mem _ hy, hv⟩
    | some b =>
      have hb : b = v := by simpa [List.findSome?, hx] using h
      exact ⟨x, List.mem_cons_self, hb ▸ hx⟩

/-- A drop is an exact kept declaration, with a real index rather than an
out-of-bounds default from the implementation's bang lookup. -/
theorem step_drop {s s' : CollapseState} (owner : OwnerExact s) {first : SKey}
    {d : Declaration .source} (h : s.step first d = (s', .ok false)) :
    s' = s ∧ ∃ i, s.kept[i]? = some d ∧ ∀ k ∈ d.names, s.owner[k]? = some i := by
  obtain ⟨ds, owners⟩ := s
  unfold CollapseState.step at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    · rename_i good
      cases h
      obtain ⟨k, _, hk⟩ := findSome_some _ _ hi
      obtain ⟨old, held, _⟩ := (owner k i).1 hk
      have bang : ds[i]! = old := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, held]; rfl
      have hd : d = old := by
        have hb := (Bool.and_eq_true_iff.mp good).2
        simpa only [Declaration.beqF_eq, bang, decide_eq_true_eq] using hb
      rw [← hd] at held
      refine ⟨rfl, i, held, ?_⟩
      intro n hn
      exact beq_iff_eq.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp good).1) n hn)
    · cases h

theorem OwnerExact.step {s s' : CollapseState} (owner : OwnerExact s) {first : SKey}
    {d : Declaration .source} {kept : Bool} (h : s.step first d = (s', .ok kept)) : OwnerExact s' := by
  cases kept with
  | false => rw [(step_drop owner h).1]; exact owner
  | true =>
    obtain ⟨ds, owners⟩ := s
    unfold CollapseState.step at h
    dsimp only at h
    split at h
    · rename_i fresh
      cases h
      exact owner.push d (findSome_none _ _ fresh)
    · split at h <;> cases h

theorem collapseRead_ownerExact {s s' : CollapseState} (owner : OwnerExact s) {first : SKey}
    {raw kept : Read .source} {dropped : Array SKey}
    (h : collapseRead s first raw = (s', .ok (kept, dropped))) : OwnerExact s' := by
  let I (_ : List (Declaration .source × Nat)) (a : ReadAcc) := a.1 = none ∧ OwnerExact a.2.1
  have inv := forIn_id_inv_or_array I ReadBad (readStep first s.kept.size raw.generated)
    raw.decls.zipIdx (fun _ x _ a _ ha => by
      rcases hs : a.2.1.step first x.1 with ⟨next, res⟩
      cases res with
      | error e => simp only [readStep, hs, pure]; exact ⟨next.restore s.kept.size, e, rfl⟩
      | ok b =>
        have hn := OwnerExact.step ha.2 hs
        cases b with
        | false => simp only [readStep, hs, pure]; exact ⟨rfl, hn⟩
        | true =>
          by_cases early : x.2 < raw.generated <;>
            simp only [readStep, hs, early, ite_true, ite_false, pure] <;> exact ⟨rfl, hn⟩)
    (none, s, #[], 0, #[]) ⟨rfl, owner⟩
  change I raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
  rw [collapseRead_eq] at h
  rcases inv with hi | hb
  · have active := hi.1
    simp only [readFinish, active, Prod.mk.injEq, Except.ok.injEq] at h
    rw [← h.1]
    exact hi.2
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

theorem trace_ownerExact {g : Graph} {start st : State .source} {xs rs s kb}
    (h : Trace g start xs rs st s kb) : OwnerExact s := by
  induction h with
  | nil => exact .empty
  | «alias» _ _ ih => exact ih
  | lowered _ _ _ hr _ ih => exact collapseRead_ownerExact ih hr

theorem fold_lookup_eq {α β : Type} (g : α → Option (SKey × β)) (k : SKey) :
    ∀ (xs : List α) (m n : Std.HashMap SKey β),
      (m[k]? = n[k]? ∨ ∃ x ∈ xs, ∃ v, g x = some (k, v)) →
      (xs.foldl (CtxAgree.insOpt g) m)[k]? = (xs.foldl (CtxAgree.insOpt g) n)[k]? := by
  intro xs
  induction xs with
  | nil => intro m n h; simpa using h
  | cons x xs ih =>
    intro m n h
    rw [List.foldl_cons, List.foldl_cons]
    by_cases touch : ∃ v, g x = some (k, v)
    · obtain ⟨v, hv⟩ := touch
      apply ih
      exact .inl (by simp [CtxAgree.insOpt, hv])
    · apply ih
      rcases h with he | ⟨y, hy, v, hv⟩
      · left
        unfold CtxAgree.insOpt
        cases hg : g x with
        | none => exact he
        | some p => simp only [Std.HashMap.getElem?_insert]; split <;> first | rfl | exact he
      · right
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (touch ⟨v, hv⟩).elim
        · exact ⟨y, hy, v, hv⟩

/-- Repeating a fixed overwrite list repeats its last write at each key.
No agreement between duplicate entries is required; absent writes preserve
the previous value, including heights for non-definitions. -/
theorem fold_idem {α β : Type} (g : α → Option (SKey × β)) (k : SKey)
    (xs : List α) (m : Std.HashMap SKey β) :
    (xs.foldl (CtxAgree.insOpt g) (xs.foldl (CtxAgree.insOpt g) m))[k]? =
      (xs.foldl (CtxAgree.insOpt g) m)[k]? := by
  by_cases touch : ∃ x ∈ xs, ∃ v, g x = some (k, v)
  · exact fold_lookup_eq g k xs _ _ (.inr touch)
  · apply fold_ins_other
    intro x hx p hp he
    apply touch
    refine ⟨x, hx, p.2, ?_⟩
    rw [← he]
    exact hp

def replay (st : State .source) (d : Declaration .source) : State .source :=
  if d.isGenerated then st.noteGenerated d else st.note d

def Stable (d : Declaration .source) (st : State .source) : Prop :=
  ∀ k, (replay st d).SameAt st k

def StableOwned (s : CollapseState) (st : State .source) : Prop :=
  ∀ (i : Nat) (d : Declaration .source), s.kept[i]? = some d → Stable d st

def KeptNoBasis (s : CollapseState) : Prop := ∀ d ∈ s.kept.toList, NoBasis d

theorem replay_constTypes (st : State .source) (d : Declaration .source) :
    (replay st d).constTypes = (CtxAgree.noteEntries d).foldl (CtxAgree.insOpt CtxAgree.tyOf) st.constTypes := by
  unfold replay; split
  · rw [(CtxAgree.noteGenerated_fields st d).1, CtxAgree.note_constTypes]
  · exact CtxAgree.note_constTypes st d

theorem replay_heights (st : State .source) (d : Declaration .source) :
    (replay st d).heights = (CtxAgree.noteEntries d).foldl (CtxAgree.insOpt CtxAgree.htOf) st.heights := by
  unfold replay; split
  · rw [(CtxAgree.noteGenerated_fields st d).2.1, CtxAgree.note_heights]
  · exact CtxAgree.note_heights st d

theorem replay_indBlocks (st : State .source) (d : Declaration .source) :
    (replay st d).indBlocks = st.indBlocks := by
  unfold replay; split
  · rw [(CtxAgree.noteGenerated_fields st d).2.2, CtxAgree.note_indBlocks]
  · exact CtxAgree.note_indBlocks st d

theorem replay_projOwners (st : State .source) (d : Declaration .source) :
    (replay st d).projOwners = st.projOwners := by
  unfold replay; split
  · exact CtxAgree.noteGenerated_projOwners st d
  · exact CtxAgree.note_projOwners st d

theorem levelEntry_none {d : Declaration .source} (h : d.isGenerated = false) :
    CtxAgree.projLevelEntry d = none := by
  cases d <;> try rfl
  case thmDecl cv value =>
    cases hn : cv.name with
    | id name => simp [CtxAgree.projLevelEntry, hn, Key.isProjIota]
    | «role» role => simp [CtxAgree.projLevelEntry, hn, Key.isProjIota]
    | aux base shape => simp [Declaration.isGenerated, Declaration.names, hn, Key.isAux] at h

theorem replay_projLevels (st : State .source) (d : Declaration .source) :
    (replay st d).projLevels = CtxAgree.insOpt CtxAgree.projLevelEntry st.projLevels d := by
  unfold replay
  split
  · exact CtxAgree.noteGenerated_projLevels st d
  · rename_i h
    rw [CtxAgree.note_projLevels, CtxAgree.insOpt, levelEntry_none (Bool.eq_false_iff.mpr h)]

theorem sameAt_symm {s t : State .source} {k : SKey} (h : s.SameAt t k) : t.SameAt s k :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem replay_congr {s t : State .source} {k : SKey} (h : s.SameAt t k) (d : Declaration .source) :
    (replay s d).SameAt (replay t d) k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [replay_constTypes, replay_constTypes]
    exact fold_lookup_eq _ _ _ _ _ (.inl h.1)
  · rw [replay_heights, replay_heights]
    exact fold_lookup_eq _ _ _ _ _ (.inl h.2.1)
  · simpa only [replay_indBlocks] using h.2.2.1
  · simpa only [replay_projOwners] using h.2.2.2.1
  · rw [replay_projLevels, replay_projLevels]
    simpa only [List.foldl_cons, List.foldl_nil] using
      fold_lookup_eq CtxAgree.projLevelEntry k [d] s.projLevels t.projLevels (.inl h.2.2.2.2)

theorem replay_idem (st : State .source) (d : Declaration .source) : Stable d (replay st d) := by
  intro k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [replay_constTypes, replay_constTypes]
    exact fold_idem _ _ _ _
  · rw [replay_heights, replay_heights]
    exact fold_idem _ _ _ _
  · rw [replay_indBlocks]
  · rw [replay_projOwners]
  · rw [replay_projLevels, replay_projLevels]
    simpa only [List.foldl_cons, List.foldl_nil] using fold_idem CtxAgree.projLevelEntry k [d] st.projLevels

theorem replay_other (st : State .source) (d : Declaration .source) (k : SKey)
    (basis : NoBasis d) (outside : k ∉ d.names) : (replay st d).SameAt st k := by
  unfold replay; split
  · exact noteGenerated_other st d k basis outside
  · exact note_other st d k basis outside

theorem Stable.frame {d e : Declaration .source} {st : State .source}
    (stable : Stable d st) (bd : NoBasis d) (be : NoBasis e)
    (disjoint : ∀ k ∈ d.names, k ∉ e.names) : Stable d (replay st e) := by
  intro k
  by_cases hk : k ∈ d.names
  · have frame := replay_other st e k be (disjoint k hk)
    exact sameAt_trans (replay_congr frame d) (sameAt_trans (stable k) (sameAt_symm frame))
  · exact replay_other _ d k bd hk

theorem StableOwned.push {s : CollapseState} {st : State .source} (owner : OwnerExact s)
    (basis : KeptNoBasis s) (stable : StableOwned s st) (d : Declaration .source) (bd : NoBasis d)
    (fresh : ∀ k ∈ d.names, s.owner[k]? = none) :
    StableOwned { kept := s.kept.push d, owner := claimKeys s.owner d.names s.kept.size } (replay st d) := by
  intro i e he
  change (s.kept.push d)[i]? = some e at he
  rw [Array.getElem?_push] at he
  split at he
  · cases he; exact replay_idem st d
  · apply (stable i e he).frame (basis e (Array.mem_toList_iff.mpr (Array.mem_of_getElem? he))) bd
    intro k hk hd
    have held := (owner k i).2 ⟨e, he, hk⟩
    rw [fresh k hd] at held
    cases held

theorem trace_keptNoBasis {g : Graph} {start st : State .source} {xs rs s kb}
    (h : Trace g start xs rs st s kb) : KeptNoBasis s := by
  induction h with
  | nil => intro d hd; simp at hd
  | «alias» _ _ ih => exact ih
  | lowered _ _ hl hr _ ih =>
    obtain ⟨_, _, _, subset, kept, _, _⟩ := collapseRead_facts hr
    intro d hd
    rw [kept, Array.toList_append] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih d hd
    · exact lower_noBasis _ _ _ hl d (subset d hd)

/-- Changing the two side maps or counters cannot disturb a replay fixed
point. The three note-written maps are kept exactly, including old heights. -/
theorem Stable.fields {d : Declaration .source} {s t : State .source} (h : Stable d s)
    (types : t.constTypes = s.constTypes) (heights : t.heights = s.heights)
    (levels : t.projLevels = s.projLevels) : Stable d t := by
  intro k
  have hs := h k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [replay_constTypes, types] using hs.1
  · simpa only [replay_heights, heights] using hs.2.1
  · rw [replay_indBlocks]
  · rw [replay_projOwners]
  · simpa only [replay_projLevels, levels] using hs.2.2.2.2

theorem StableOwned.fields {s : CollapseState} {a b : State .source} (h : StableOwned s a)
    (types : b.constTypes = a.constTypes) (heights : b.heights = a.heights)
    (levels : b.projLevels = a.projLevels) : StableOwned s b :=
  fun i d hd => (h i d hd).fields types heights levels

/-- One actual successful collapse step preserves exact owners, basis-freedom
and fixed points. A drop's raw replay agrees at all five lookups with keeping
the state as it was; counters and array equality are not asserted. -/
theorem step_replay {s s' : CollapseState} {st : State .source} (owner : OwnerExact s)
    (basis : KeptNoBasis s) (stable : StableOwned s st) {first : SKey}
    {d : Declaration .source} (bd : NoBasis d) {kept : Bool}
    (hs : s.step first d = (s', .ok kept)) :
    OwnerExact s' ∧ KeptNoBasis s' ∧
      StableOwned s' (if kept then replay st d else st) ∧
      ∀ k, (replay st d).SameAt (if kept then replay st d else st) k := by
  cases kept with
  | false =>
    obtain ⟨rfl, i, hd, _⟩ := step_drop owner hs
    exact ⟨owner, basis, stable, stable i d hd⟩
  | true =>
    have hk : s'.kept = s.kept.push d := by simpa using SourcePrelude.step_kept hs
    have fresh := (step_ownerFacts hs).2.2 rfl
    refine ⟨owner.step hs, ?_, ?_, fun k => sameAt_refl _ k⟩
    · intro e he
      rw [hk, Array.toList_push] at he
      rcases List.mem_append.mp he with he | he
      · exact basis e he
      · have he : e = d := List.mem_singleton.mp he
        exact he ▸ bd
    · intro i e he
      rw [hk] at he
      exact (stable.push owner basis d bd fresh) i e he

end Ix.Cert.SourceReplay
