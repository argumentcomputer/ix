import Ix.Cert.SourcePrelude
import Ix.Cert.SourceNames

/-! # Original indices retained by Source collapse

The actual collapseRead loop retains an ordered subsequence of original
(declaration,index) pairs. Splitting that subsequence at the raw generated
boundary gives exactly the recomputed kept.generated count, including raw
counts larger than the declaration array. Repeated declarations are allowed.

The index witness transfers raw generated/ordinary classification to kept
reads, and the production quotient wrapper supplies those facts. It does
not prove dropped-declaration replay, projection-iota level consistency,
owner coherence, semantic-map equality or whole-stream correspondence.
-/

namespace Ix.Cert.SourceRetained

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude

abbrev Entry := Declaration .source × Nat

theorem zipIdx_order {α : Type} (xs : List α) (start : Nat) :
    (xs.zipIdx start).Pairwise (fun x y => x.2 < y.2) := by
  induction xs generalizing start with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    exact ⟨fun y hy => Nat.lt_of_lt_of_le (Nat.lt_succ_self start) (List.le_snd_of_mem_zipIdx hy), ih _⟩

theorem before_index {α : Type} {xs : List α} {pre post : List (α × Nat)} {x : α × Nat}
    (whole : pre ++ x :: post = xs.zipIdx) : ∀ y ∈ pre, y.2 < x.2 := by
  have ordered := zipIdx_order xs 0
  rw [← whole] at ordered
  exact fun y hy => ordered.rel_of_mem_append hy List.mem_cons_self

/-- Selected original pairs, split at the retained generated boundary. -/
def Retained (raw : Read .source) (pre : List Entry) (keep : Array (Declaration .source))
    (generated : Nat) : Prop :=
  ∃ G O : List Entry, (G ++ O).Sublist pre ∧ keep.toList = (G ++ O).map Prod.fst ∧
    generated = G.length ∧ (∀ x ∈ G, x.2 < raw.generated) ∧ (∀ x ∈ O, raw.generated ≤ x.2)

def Inv (raw : Read .source) (pre : List Entry) (a : ReadAcc) : Prop :=
  a.1 = none ∧ Retained raw pre a.2.2.1 a.2.2.2.1

theorem readStep_inv {raw : Read .source} {pre : List Entry} {a : ReadAcc}
    (ha : Inv raw pre a) (first : SKey) (originalSize : Nat) (x : Entry)
    (before : ∀ y ∈ pre, y.2 < x.2) :
    match readStep first originalSize raw.generated x a with
    | .yield a' => Inv raw (pre ++ [x]) a'
    | .done a' => ReadBad a' := by
  rcases ha with ⟨_, G, O, sub, keep, count, gens, owns⟩
  rcases hs : a.2.1.step first x.1 with ⟨s', res⟩
  cases res with
  | error e =>
    simp only [readStep, hs, pure]
    exact ⟨s'.restore originalSize, e, rfl⟩
  | ok kept =>
    cases kept with
    | false =>
      simp only [readStep, hs, pure]
      exact ⟨rfl, G, O, sub.trans (List.sublist_append_left _ _), keep, count, gens, owns⟩
    | true =>
      by_cases early : x.2 < raw.generated
      · have empty : O = [] := by
          cases O with
          | nil => rfl
          | cons y ys =>
            have low := before y (sub.subset (List.mem_append_right _ List.mem_cons_self))
            have high := owns y List.mem_cons_self
            omega
        subst O
        simp only [readStep, hs, early, ite_true, pure]
        refine ⟨rfl, G ++ [x], [], ?_, ?_, ?_, ?_, by simp⟩
        · simpa only [List.append_nil] using sub.append_right [x]
        · simp only [Array.toList_push, keep, List.append_nil, List.map_append, List.map_singleton]
        · simp [count]
        · intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact gens y hy
          · have hy : y = x := List.mem_singleton.mp hy
            subst y
            exact early
      · simp only [readStep, hs, early, ite_false, pure]
        refine ⟨rfl, G, O ++ [x], ?_, ?_, count, gens, ?_⟩
        · simpa only [List.append_assoc] using sub.append_right [x]
        · simp only [Array.toList_push, keep, List.map_append, List.map_singleton, List.append_assoc]
        · intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact owns y hy
          · have hy : y = x := List.mem_singleton.mp hy
            subst y
            omega

/-- Actual successful collapse retains an ordered subsequence with the exact
generated cutoff, even when the raw generated count exceeds its size. -/
theorem collapseRead_retained {s s' : CollapseState} {first : SKey} {raw kept : Read .source}
    {dropped : Array SKey} (h : collapseRead s first raw = (s', .ok (kept, dropped))) :
    Retained raw raw.decls.toList.zipIdx kept.decls kept.generated := by
  have start : Inv raw [] (none, s, #[], 0, #[]) :=
    ⟨rfl, [], [], .refl [], rfl, rfl, by simp, by simp⟩
  have inv := forIn_id_inv_or_array (Inv raw) ReadBad
    (readStep first s.kept.size raw.generated) raw.decls.zipIdx
    (fun pre x post a whole ha => by
      have ordered : ∀ y ∈ pre, y.2 < x.2 := before_index (by simpa only [Array.toList_zipIdx] using whole)
      have step := readStep_inv ha first s.kept.size x ordered
      cases hb : readStep first s.kept.size raw.generated x a <;> simpa only [hb] using step) _ start
  change Inv raw raw.decls.zipIdx.toList (readLoop s first raw) ∨ ReadBad (readLoop s first raw) at inv
  rw [collapseRead_eq] at h
  rcases inv with hi | hb
  · have active := hi.1
    simp only [readFinish, active, Prod.mk.injEq, Except.ok.injEq] at h
    rcases h with ⟨_, hr, _⟩
    subst kept
    simpa only [Array.toList_zipIdx] using hi.2
  · obtain ⟨t, e, he⟩ := hb
    simp [readFinish, he] at h

theorem Retained.generated_le {raw : Read .source} {pre : List Entry}
    {keep : Array (Declaration .source)} {n : Nat} (h : Retained raw pre keep n) : n ≤ keep.size := by
  obtain ⟨G, O, _, hk, hn, _, _⟩ := h
  have len : keep.size = G.length + O.length := by simpa using congrArg List.length hk
  omega

/-- The selected original indices increase strictly, and classify each kept
position by exactly the raw generated boundary. -/
theorem Retained.indices {raw : Read .source} {keep : Array (Declaration .source)} {n : Nat}
    (h : Retained raw raw.decls.toList.zipIdx keep n) :
    ∃ indices : List Nat, indices.Pairwise (· < ·) ∧ indices.length = keep.size ∧
      ∀ i d, keep.toList[i]? = some d → ∃ j, indices[i]? = some j ∧
        raw.decls.toList[j]? = some d ∧ (i < n ↔ j < raw.generated) := by
  obtain ⟨G, O, sub, hk, hn, gens, owns⟩ := h
  refine ⟨(G ++ O).map Prod.snd, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using (zipIdx_order raw.decls.toList 0).sublist sub
  · simpa only [List.length_map, Array.length_toList] using (congrArg List.length hk).symm
  · intro i d hd
    rw [hk, List.getElem?_map] at hd
    cases hs : (G ++ O)[i]? with
    | none => simp [hs] at hd
    | some p =>
      obtain ⟨d0, j⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq] at hd
      subst d
      refine ⟨j, by simp only [List.getElem?_map, hs, Option.map_some],
        List.mk_mem_zipIdx_iff_getElem?.mp (sub.subset (List.mem_of_getElem? hs)), ?_⟩
      rw [hn]
      by_cases early : i < G.length
      · have hg : G[i]? = some (d0, j) := by rwa [List.getElem?_append_left early] at hs
        have hj := gens _ (List.mem_of_getElem? hg)
        exact ⟨fun _ => hj, fun _ => early⟩
      · have ho : O[i - G.length]? = some (d0, j) := by
          rwa [List.getElem?_append_right (Nat.le_of_not_gt early)] at hs
        have hj := owns _ (List.mem_of_getElem? ho)
        omega

theorem Retained.transfer {raw : Read .source} {keep : Array (Declaration .source)} {n : Nat}
    (h : Retained raw raw.decls.toList.zipIdx keep n) {P Q : Declaration .source → Prop}
    (gen : ∀ d ∈ raw.decls.toList.take raw.generated, P d)
    (own : ∀ d ∈ raw.decls.toList.drop raw.generated, Q d) :
    (∀ d ∈ keep.toList.take n, P d) ∧ (∀ d ∈ keep.toList.drop n, Q d) := by
  obtain ⟨G, O, sub, hk, hn, gens, owns⟩ := h
  constructor
  · intro d hd
    rw [hk, hn, ← List.map_take, List.take_left] at hd
    obtain ⟨⟨d0, j⟩, hm, rfl⟩ := List.mem_map.mp hd
    have hr := List.mk_mem_zipIdx_iff_getElem?.mp (sub.subset (List.mem_append_left O hm))
    apply gen d0
    exact List.mem_of_getElem? ((List.getElem?_take_of_lt (gens _ hm)).trans hr)
  · intro d hd
    rw [hk, hn, ← List.map_drop, List.drop_left] at hd
    obtain ⟨⟨d0, j⟩, hm, rfl⟩ := List.mem_map.mp hd
    have hr := List.mk_mem_zipIdx_iff_getElem?.mp (sub.subset (List.mem_append_right G hm))
    apply own d0
    have hi : raw.generated + (j - raw.generated) = j := by have := owns _ hm; omega
    apply List.mem_of_getElem? (i := j - raw.generated)
    simpa only [List.getElem?_drop, hi] using hr

/-- The production quotient conversion's name classes survive the actual
collapse, with its recomputed generated count. No replay equality is assumed. -/
theorem quotient_collapse_classified {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {gr : Group} {c : Converted} (converted : convert gr = .ok c)
    (hints : CName .source → Option ReducibilityHint) {st : State .source} {raw kept : Read .source}
    (lowered : lower st ((c.withHints hints).quotient (fiberAliasAt ixe roles)) = .ok raw)
    {s s' : CollapseState} {first : SKey} {dropped : Array SKey}
    (collapsed : collapseRead s first raw = (s', .ok (kept, dropped))) :
    (∀ d ∈ kept.decls.toList.take kept.generated, d.isGenerated = true) ∧
      (∀ d ∈ kept.decls.toList.drop kept.generated, ∀ k ∈ d.names, k.isAux = false) :=
  (collapseRead_retained collapsed).transfer (SourceNames.lower_generated lowered)
    (SourceNames.quotient_lower_ordinary converted hints lowered)

end Ix.Cert.SourceRetained
