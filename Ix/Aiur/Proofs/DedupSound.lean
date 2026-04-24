module
public import Ix.Aiur.Compiler.Dedup
public import Ix.Aiur.Semantics.BytecodeEval
public import Ix.Aiur.Semantics.Compatible
public import Ix.Aiur.Proofs.BytecodeLawfulBEq

/-!
Dedup soundness.

Bisimulation up to call-index renaming, with cycles handled by well-founded
induction on fuel. Bytecode-only pass; does not depend on the staged datatypes.
-/

public section

namespace Aiur

open Bytecode Eval

/-! ## Structural invariants of `assignClasses` / `partitionRefine`. -/

/-- `assignClasses` preserves array length. -/
theorem assignClasses_size_eq
    {α : Type _} [BEq α] [Hashable α] (values : Array α) :
    (assignClasses values).1.size = values.size := by
  unfold assignClasses
  apply Array.foldl_induction
    (motive := fun i (s : Array Nat × Std.HashMap α Nat × Nat) => s.1.size = i)
  · rfl
  · intro i s hs
    obtain ⟨classes, map, nextId⟩ := s
    simp only at hs
    simp only
    cases h : map[values[i]]? with
    | none => simp [Array.size_push, hs]
    | some id => simp [Array.size_push, hs]

/-- Inner invariant for `assignClasses`: at every step, every class id in the
output array is `< nextId`, every value in the hashmap is `< nextId`, and
`nextId ≤ i` (elements processed so far). -/
private theorem assignClasses_foldl_invariant
    {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (values : Array α) :
    let r := values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
      fun x v =>
        match x.2.1[v]? with
        | some id => (x.1.push id, x.2.1, x.2.2)
        | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
    (∀ k (hk : k < r.1.size), r.1[k] < r.2.2) ∧
    (∀ (v : α) id, r.2.1[v]? = some id → id < r.2.2) ∧
    r.2.2 ≤ values.size := by
  apply Array.foldl_induction
    (motive := fun i (s : Array Nat × Std.HashMap α Nat × Nat) =>
      (∀ k (hk : k < s.1.size), s.1[k] < s.2.2) ∧
      (∀ (v : α) id, s.2.1[v]? = some id → id < s.2.2) ∧
      s.2.2 ≤ i)
  · refine ⟨?_, ?_, ?_⟩
    · intro k hk; simp at hk
    · intro v id hv; simp at hv
    · simp
  · intro i s ih
    obtain ⟨classes, map, nextId⟩ := s
    simp only at ih
    obtain ⟨ihC, ihM, ihN⟩ := ih
    simp only
    cases hm : map[values[i]]? with
    | some id =>
      simp only []
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        by_cases hkeq : k = classes.size
        · subst hkeq
          simp [Array.getElem_push]
          exact ihM _ _ hm
        · have hk' : k < classes.size := by
            rw [Array.size_push] at hk; omega
          rw [Array.getElem_push_lt hk']
          exact ihC k hk'
      · intro v id' hv
        exact ihM v id' hv
      · omega
    | none =>
      simp only []
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        by_cases hkeq : k = classes.size
        · subst hkeq
          simp [Array.getElem_push]
        · have hk' : k < classes.size := by
            rw [Array.size_push] at hk; omega
          rw [Array.getElem_push_lt hk']
          exact Nat.lt_succ_of_lt (ihC k hk')
      · intro v id' hv
        rw [Std.HashMap.getElem?_insert] at hv
        by_cases hveq : (values[i] == v) = true
        · rw [if_pos hveq] at hv
          rw [Option.some.injEq] at hv
          omega
        · rw [if_neg hveq] at hv
          exact Nat.lt_succ_of_lt (ihM v id' hv)
      · omega

/-- `assignClasses` bounds every output class id by the returned `nextId`. -/
theorem assignClasses_classes_lt_nextId
    {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (values : Array α)
    (i : Nat) (h : i < (assignClasses values).1.size) :
    (assignClasses values).1[i] < (assignClasses values).2 := by
  unfold assignClasses at h ⊢
  have := (assignClasses_foldl_invariant values).1 i
  simp only at this ⊢
  exact this h

private theorem partitionRefineBound_size_eq
    (bound : Nat) (classes : Array Nat) (callees : Array (Array FunIdx)) :
    (partitionRefineBound bound classes callees).size = classes.size := by
  induction bound generalizing classes with
  | zero => unfold partitionRefineBound; rfl
  | succ b ih =>
    unfold partitionRefineBound
    simp only
    split
    · rfl
    · rw [ih]
      have := assignClasses_size_eq (α := Nat × Array Nat)
        (classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!)))
      rw [this, Array.size_mapIdx]

/-- `partitionRefine` preserves the array length of `classes`. -/
theorem partitionRefine_size_eq
    (classes : Array Nat) (callees : Array (Array FunIdx)) :
    (partitionRefine classes callees).size = classes.size := by
  unfold partitionRefine
  exact partitionRefineBound_size_eq _ _ _

/-- Index-erased bound predicate: every element is `≤ n`. Avoids dependent
`GetElem` motive issues that arise when rewriting the array under `[i]'h`. -/
private def BoundedBy (c : Array Nat) (n : Nat) : Prop :=
  ∀ x ∈ c, x ≤ n

private theorem boundedBy_of_assignClasses
    {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (values : Array α) (n : Nat) (hn : values.size ≤ n) :
    BoundedBy (assignClasses values).1 n := by
  intro x hx
  rw [Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hlt : (assignClasses values).1[i] < (assignClasses values).2 :=
    assignClasses_classes_lt_nextId values i hi
  have hnext : (assignClasses values).2 ≤ values.size :=
    (assignClasses_foldl_invariant values).2.2
  omega

/-- Generalized bound: for any `n ≥ classes.size`, if the *input* is bounded
by `n` then the output is too. The `assignClasses` output is always bounded
by `classes.size ≤ n` (via the size-preservation of `mapIdx`), so recursion
preserves the bound. The `== classes` branch returns the input, which is
bounded by hypothesis. -/
private theorem partitionRefineBound_boundedBy
    (bound : Nat) (classes : Array Nat) (callees : Array (Array FunIdx))
    (n : Nat) (hn : classes.size ≤ n) (hin : BoundedBy classes n) :
    BoundedBy (partitionRefineBound bound classes callees) n := by
  induction bound generalizing classes with
  | zero => unfold partitionRefineBound; exact hin
  | succ b ih =>
    unfold partitionRefineBound
    simp only
    split
    · exact hin
    · rename_i hne
      -- Abstract the `mapIdx` subterm with a local `let`.
      have hsz : (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!))).size = classes.size :=
        Array.size_mapIdx
      have hbnd : BoundedBy
          (assignClasses (classes.mapIdx fun i cls =>
            (cls, callees[i]!.map (classes[·]!)))).1 n :=
        boundedBy_of_assignClasses _ n (by rw [hsz]; exact hn)
      have hsz' : (assignClasses (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!)))).1.size = classes.size := by
        rw [assignClasses_size_eq, hsz]
      have hn' : (assignClasses (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!)))).1.size ≤ n := by
        rw [hsz']; exact hn
      exact ih _ hn' hbnd

/-! ### `eval_congr_dedup` decomposition.

The bisimulation theorem `eval_congr_dedup` decomposes into 5 granular
sub-lemmas plus one strong-induction driver. Each is sorried here and tagged
`BLOCKED ON:` with the upstream work it needs. -/

/-- Well-formedness: every callee index in `t`'s function bodies is in range.
Required to prevent partitionRefine's `classes[·]!`-default-0 from silently
unifying functions with different dangling callees. -/
@[expose]
def WellFormedCallees (t : Toplevel) : Prop :=
  ∀ (fi : Nat) (_hfi : fi < t.functions.size),
    ∀ c ∈ collectCalleesBlock t.functions[fi].body,
      c < t.functions.size
/-! (2) Same class ⇒ remapped-callee sequences agree. Fixpoint condition
`(assignClasses signatures).1 = classes` with collision-freeness of
`assignClasses` forces equal signatures for equal class ids. Needs injectivity
of `assignClasses` at `Nat × Array Nat` (natively `LawfulBEq`/`LawfulHashable`). -/

/-- 4-conjunct foldl-invariant for `assignClasses` (size, map tracking, id
bound, injectivity). -/
private theorem assignClasses_inj_foldl_raw
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (values : Array α) :
    let r := values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
      fun x v =>
        match x.2.1[v]? with
        | some id => (x.1.push id, x.2.1, x.2.2)
        | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
    r.1.size = values.size ∧
    (∀ k (hk : k < values.size) (hk' : k < r.1.size),
      r.2.1[values[k]'hk]? = some (r.1[k]'hk')) ∧
    (∀ (v : α) (id : Nat), r.2.1[v]? = some id → id < r.2.2) ∧
    (∀ (v1 v2 : α) (id : Nat), r.2.1[v1]? = some id → r.2.1[v2]? = some id → v1 = v2) := by
  apply Array.foldl_induction
    (motive := fun (n : Nat) (s : Array Nat × Std.HashMap α Nat × Nat) =>
      s.1.size = n ∧
      (∀ k (hk : k < values.size) (hk' : k < s.1.size),
        s.2.1[values[k]'hk]? = some (s.1[k]'hk')) ∧
      (∀ (v : α) (id : Nat), s.2.1[v]? = some id → id < s.2.2) ∧
      (∀ (v1 v2 : α) (id : Nat),
        s.2.1[v1]? = some id → s.2.1[v2]? = some id → v1 = v2))
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro k _ hk'; simp at hk'
    · intro v id hv; simp at hv
    · intro v1 v2 id hv1 _; simp at hv1
  · intro i s ih
    obtain ⟨classes, map, nextId⟩ := s
    simp only at ih
    obtain ⟨ihSz, ihMap, ihBound, ihInj⟩ := ih
    simp only
    cases hm : map[values[i]]? with
    | some id =>
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Array.size_push, ihSz]
      · intro k hk hk'
        by_cases hkeq : k = classes.size
        · subst hkeq
          rw [Array.getElem_push_eq]
          have hvEq : values[classes.size]'hk = values[i] := by
            have : classes.size = i.val := ihSz
            simp [this]
          rw [hvEq]; exact hm
        · have hk'' : k < classes.size := by
            rw [Array.size_push] at hk'; omega
          rw [Array.getElem_push_lt hk'']
          exact ihMap k hk hk''
      · intro v id' hv
        exact ihBound v id' hv
      · intro v1 v2 id' hv1 hv2
        exact ihInj v1 v2 id' hv1 hv2
    | none =>
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Array.size_push, ihSz]
      · intro k hk hk'
        by_cases hkeq : k = classes.size
        · subst hkeq
          rw [Array.getElem_push_eq]
          have hvalEq : values[classes.size]'hk = values[i] := by
            have : classes.size = i.val := ihSz
            simp [this]
          rw [hvalEq]
          rw [Std.HashMap.getElem?_insert]
          simp
        · have hk'' : k < classes.size := by
            rw [Array.size_push] at hk'; omega
          rw [Array.getElem_push_lt hk'']
          rw [Std.HashMap.getElem?_insert]
          have hprev := ihMap k hk hk''
          by_cases hvEq : (values[i] == values[k]'hk) = true
          · have heq : values[i] = values[k]'hk := LawfulBEq.eq_of_beq hvEq
            rw [heq] at hm
            exfalso
            rw [hprev] at hm
            exact (Option.some_ne_none _) hm
          · rw [if_neg hvEq]
            exact hprev
      · intro v id' hv
        rw [Std.HashMap.getElem?_insert] at hv
        by_cases hveq : (values[i] == v) = true
        · rw [if_pos hveq] at hv
          rw [Option.some.injEq] at hv
          omega
        · rw [if_neg hveq] at hv
          exact Nat.lt_succ_of_lt (ihBound v id' hv)
      · intro v1 v2 id' hv1 hv2
        rw [Std.HashMap.getElem?_insert] at hv1 hv2
        by_cases hveq1 : (values[i] == v1) = true
        · rw [if_pos hveq1] at hv1
          rw [Option.some.injEq] at hv1
          by_cases hveq2 : (values[i] == v2) = true
          · rw [if_pos hveq2] at hv2
            have h1 : values[i] = v1 := LawfulBEq.eq_of_beq hveq1
            have h2 : values[i] = v2 := LawfulBEq.eq_of_beq hveq2
            rw [h1] at h2; exact h2
          · rw [if_neg hveq2] at hv2
            have hlt := ihBound v2 id' hv2
            omega
        · rw [if_neg hveq1] at hv1
          by_cases hveq2 : (values[i] == v2) = true
          · rw [if_pos hveq2] at hv2
            rw [Option.some.injEq] at hv2
            have hlt := ihBound v1 id' hv1
            omega
          · rw [if_neg hveq2] at hv2
            exact ihInj v1 v2 id' hv1 hv2

private def assignClasses_map_of
    {α : Type _} [BEq α] [Hashable α] (values : Array α) : Std.HashMap α Nat :=
  (values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
    fun x v =>
      match x.2.1[v]? with
      | some id => (x.1.push id, x.2.1, x.2.2)
      | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.1

private theorem assignClasses_fst_eq_foldl_fst
    {α : Type _} [BEq α] [Hashable α]
    (values : Array α) :
    (assignClasses values).1 =
      (values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1 := by
  unfold assignClasses; rfl

private theorem assignClasses_snd_eq_foldl_snd_snd
    {α : Type _} [BEq α] [Hashable α]
    (values : Array α) :
    (assignClasses values).2 =
      (values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.2 := by
  unfold assignClasses; rfl

private theorem assignClasses_map_tracks
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (values : Array α)
    (k : Nat) (hk : k < values.size) (hk' : k < (assignClasses values).1.size) :
    (assignClasses_map_of values)[values[k]'hk]? =
      some ((assignClasses values).1[k]'hk') := by
  have hinv := assignClasses_inj_foldl_raw values
  simp only at hinv
  obtain ⟨_, hMap, _, _⟩ := hinv
  have hbridge := assignClasses_fst_eq_foldl_fst values
  have hk'' : k <
      (values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1.size := by
    have hszeq : (assignClasses values).1.size =
        (values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
          fun x v =>
            match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1.size := by
      rw [hbridge]
    rw [hszeq] at hk'; exact hk'
  have h := hMap k hk hk''
  unfold assignClasses_map_of
  have bridge_eq : ∀ (arr1 arr2 : Array Nat) (heq : arr1 = arr2) (i : Nat)
      (hi1 : i < arr1.size) (hi2 : i < arr2.size),
      arr1[i]'hi1 = arr2[i]'hi2 := by
    intro arr1 arr2 heq i hi1 hi2
    subst heq; rfl
  rw [bridge_eq _ _ hbridge.symm k hk'' hk'] at h
  exact h

private theorem assignClasses_map_bound
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (values : Array α)
    (v : α) (id : Nat) (hv : (assignClasses_map_of values)[v]? = some id) :
    id < (assignClasses values).2 := by
  have hinv := assignClasses_inj_foldl_raw values
  simp only at hinv
  obtain ⟨_, _, hB, _⟩ := hinv
  have := hB v id hv
  rw [assignClasses_snd_eq_foldl_snd_snd]
  exact this

private theorem assignClasses_map_inj
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (values : Array α)
    (v1 v2 : α) (id : Nat)
    (hv1 : (assignClasses_map_of values)[v1]? = some id)
    (hv2 : (assignClasses_map_of values)[v2]? = some id) :
    v1 = v2 := by
  have hinv := assignClasses_inj_foldl_raw values
  simp only at hinv
  obtain ⟨_, _, _, hI⟩ := hinv
  exact hI v1 v2 id hv1 hv2

/-- Top-level injectivity of `assignClasses`: same class id ⇒ same value. -/
theorem assignClasses_values_eq_of_classes_eq
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (values : Array α) (i j : Nat)
    (hi : i < (assignClasses values).1.size)
    (hj : j < (assignClasses values).1.size)
    (hcls : (assignClasses values).1[i] = (assignClasses values).1[j]) :
    values[i]'(by rw [assignClasses_size_eq] at hi; exact hi) =
      values[j]'(by rw [assignClasses_size_eq] at hj; exact hj) := by
  have hupg : ∀ (k : Nat) (hk : k < values.size) (hk' : k < (assignClasses values).1.size),
      (assignClasses_map_of values)[values[k]'hk]? = some ((assignClasses values).1[k]'hk') :=
    assignClasses_map_tracks values
  have hBound_upg : ∀ (v : α) (id : Nat),
      (assignClasses_map_of values)[v]? = some id → id < (assignClasses values).2 :=
    assignClasses_map_bound values
  have hInj_upg : ∀ (v1 v2 : α) (id : Nat),
      (assignClasses_map_of values)[v1]? = some id →
      (assignClasses_map_of values)[v2]? = some id → v1 = v2 :=
    assignClasses_map_inj values
  have hi_v : i < values.size := by
    rw [assignClasses_size_eq] at hi; exact hi
  have hj_v : j < values.size := by
    rw [assignClasses_size_eq] at hj; exact hj
  have h1 := hupg i hi_v hi
  have h2 := hupg j hj_v hj
  rw [hcls] at h1
  exact hInj_upg _ _ _ h1 h2

private theorem deduplicate_snd_eq_classes_getElem
    (t : Toplevel) (hn : 0 < t.functions.size) (i : Nat) (hi : i < t.functions.size) :
    let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
    let initClasses := (assignClasses skeletons).1
    let callees := t.functions.map fun f => collectCalleesBlock f.body
    let classes := partitionRefine initClasses callees
    (t.deduplicate).2 i =
      classes[i]'(by
        show i < (partitionRefine (assignClasses (t.functions.map _)).1
          (t.functions.map _)).size
        rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
        exact hi) := by
  have hne : ¬ t.functions.size = 0 := Nat.ne_of_gt hn
  show (if t.functions.size == 0 then
          ((t, id) : Toplevel × (FunIdx → FunIdx))
        else
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let (canonical, _top_cls) := deduplicate_canonical classes
          let remapFn := deduplicate_remap classes
          let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
          ({ t with functions := newFunctions }, remapFn)).2 i = _
  rw [if_neg (by simp [hne] : ¬ (t.functions.size == 0) = true)]
  simp only
  show (if h : i < (partitionRefine _ _).size then (partitionRefine _ _)[i]'h else i) = _
  have hcls_sz : (partitionRefine
      (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => collectCalleesBlock f.body)).size = t.functions.size := by
    rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
  have hi_cls : i < (partitionRefine
      (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => collectCalleesBlock f.body)).size := hcls_sz ▸ hi
  rw [dif_pos hi_cls]

private theorem callees_remap_eq_of_same_class
    (t : Toplevel)
    (_hwf : WellFormedCallees t)
    (_hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
             let (initClasses, _) := assignClasses skeletons
             let callees := t.functions.map fun f => collectCalleesBlock f.body
             let classes := partitionRefine initClasses callees
             let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
             (assignClasses signatures).1 = classes) :
    let (_tDedup, remap) := t.deduplicate
    ∀ i j (_hi : i < t.functions.size) (_hj : j < t.functions.size),
      remap i = remap j →
      (collectCalleesBlock t.functions[i].body).map remap =
        (collectCalleesBlock t.functions[j].body).map remap := by
  simp only
  intro i j hi hj hremap
  have hn : 0 < t.functions.size := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) (Nat.le_refl _)
  let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
  let initClasses := (assignClasses skeletons).1
  let callees := t.functions.map fun f => collectCalleesBlock f.body
  let classes := partitionRefine initClasses callees
  let signatures : Array (Nat × Array Nat) :=
    classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
  have hsk_def : skeletons = t.functions.map fun f => (skeletonBlock f.body, f.layout) := rfl
  have hic_def : initClasses = (assignClasses skeletons).1 := rfl
  have hcal_def : callees = t.functions.map fun f => collectCalleesBlock f.body := rfl
  have hcls_def : classes = partitionRefine initClasses callees := rfl
  have hsig_def : signatures =
    classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!)) := rfl
  change (assignClasses signatures).1 = classes at _hfix
  have hsz_classes : classes.size = t.functions.size := by
    rw [hcls_def, partitionRefine_size_eq, hic_def, assignClasses_size_eq, hsk_def,
      Array.size_map]
  have hi_cls : i < classes.size := hsz_classes ▸ hi
  have hj_cls : j < classes.size := hsz_classes ▸ hj
  have hsz_sig : signatures.size = classes.size := by
    rw [hsig_def, Array.size_mapIdx]
  have hi_sig : i < signatures.size := hsz_sig ▸ hi_cls
  have hj_sig : j < signatures.size := hsz_sig ▸ hj_cls
  have hremap_i : (t.deduplicate).2 i = classes[i]'hi_cls := by
    have := deduplicate_snd_eq_classes_getElem t hn i hi
    simp only at this
    rw [this]
  have hremap_j : (t.deduplicate).2 j = classes[j]'hj_cls := by
    have := deduplicate_snd_eq_classes_getElem t hn j hj
    simp only at this
    rw [this]
  have hcls_eq : classes[i] = classes[j] := by
    rw [← hremap_i, ← hremap_j]
    exact hremap
  have h_assign_i : (assignClasses signatures).1[i]'(by
      rw [assignClasses_size_eq]; exact hi_sig) =
        classes[i] := by
    have hh := congrArg (·[i]?) _hfix
    simp at hh
    have hi_acl : i < (assignClasses signatures).1.size := by
      rw [assignClasses_size_eq]; exact hi_sig
    rw [Array.getElem?_eq_getElem hi_acl, Array.getElem?_eq_getElem hi_cls] at hh
    exact Option.some.inj hh
  have h_assign_j : (assignClasses signatures).1[j]'(by
      rw [assignClasses_size_eq]; exact hj_sig) =
        classes[j] := by
    have hh := congrArg (·[j]?) _hfix
    simp at hh
    have hj_acl : j < (assignClasses signatures).1.size := by
      rw [assignClasses_size_eq]; exact hj_sig
    rw [Array.getElem?_eq_getElem hj_acl, Array.getElem?_eq_getElem hj_cls] at hh
    exact Option.some.inj hh
  have h_ac_eq : (assignClasses signatures).1[i]'(by
      rw [assignClasses_size_eq]; exact hi_sig) =
        (assignClasses signatures).1[j]'(by
      rw [assignClasses_size_eq]; exact hj_sig) := by
    rw [h_assign_i, h_assign_j, hcls_eq]
  have hi_acl : i < (assignClasses signatures).1.size := by
    rw [assignClasses_size_eq]; exact hi_sig
  have hj_acl : j < (assignClasses signatures).1.size := by
    rw [assignClasses_size_eq]; exact hj_sig
  have hsig_eq : signatures[i]'hi_sig = signatures[j]'hj_sig :=
    assignClasses_values_eq_of_classes_eq signatures i j hi_acl hj_acl h_ac_eq
  have hsig2 :
      (callees[i]!).map (classes[·]!) = (callees[j]!).map (classes[·]!) := by
    have h_i : signatures[i]'hi_sig = (classes[i], (callees[i]!).map (classes[·]!)) := by
      show (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))[i]'hi_sig = _
      simp [Array.getElem_mapIdx]
    have h_j : signatures[j]'hj_sig = (classes[j], (callees[j]!).map (classes[·]!)) := by
      show (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))[j]'hj_sig = _
      simp [Array.getElem_mapIdx]
    rw [h_i, h_j] at hsig_eq
    exact (Prod.mk.inj hsig_eq).2
  have hcal_i : callees[i]! = collectCalleesBlock t.functions[i].body := by
    have hsz : callees.size = t.functions.size := by
      show (t.functions.map fun f => collectCalleesBlock f.body).size = _
      rw [Array.size_map]
    have hi_cal : i < callees.size := hsz ▸ hi
    rw [getElem!_pos _ i hi_cal]
    show (t.functions.map fun f => collectCalleesBlock f.body)[i] = _
    simp [Array.getElem_map]
  have hcal_j : callees[j]! = collectCalleesBlock t.functions[j].body := by
    have hsz : callees.size = t.functions.size := by
      show (t.functions.map fun f => collectCalleesBlock f.body).size = _
      rw [Array.size_map]
    have hj_cal : j < callees.size := hsz ▸ hj
    rw [getElem!_pos _ j hj_cal]
    show (t.functions.map fun f => collectCalleesBlock f.body)[j] = _
    simp [Array.getElem_map]
  rw [hcal_i, hcal_j] at hsig2
  have hmap_bridge_i :
      (collectCalleesBlock t.functions[i].body).map (classes[·]!) =
        (collectCalleesBlock t.functions[i].body).map (t.deduplicate).2 := by
    apply Array.ext
    · simp
    · intro k hk1 hk2
      simp only [Array.getElem_map]
      have hk1' : k < (collectCalleesBlock t.functions[i].body).size := by simpa using hk1
      have hc_mem : (collectCalleesBlock t.functions[i].body)[k]'hk1' ∈
          collectCalleesBlock t.functions[i].body :=
        Array.getElem_mem _
      have hc_rng : (collectCalleesBlock t.functions[i].body)[k]'hk1' < t.functions.size :=
        _hwf i hi _ hc_mem
      have hc_cls : (collectCalleesBlock t.functions[i].body)[k]'hk1' < classes.size :=
        hsz_classes ▸ hc_rng
      rw [getElem!_pos (classes : Array Nat) _ hc_cls]
      have := deduplicate_snd_eq_classes_getElem t hn _ hc_rng
      simp only at this
      exact this.symm
  have hmap_bridge_j :
      (collectCalleesBlock t.functions[j].body).map (classes[·]!) =
        (collectCalleesBlock t.functions[j].body).map (t.deduplicate).2 := by
    apply Array.ext
    · simp
    · intro k hk1 hk2
      simp only [Array.getElem_map]
      have hk1' : k < (collectCalleesBlock t.functions[j].body).size := by simpa using hk1
      have hc_mem : (collectCalleesBlock t.functions[j].body)[k]'hk1' ∈
          collectCalleesBlock t.functions[j].body :=
        Array.getElem_mem _
      have hc_rng : (collectCalleesBlock t.functions[j].body)[k]'hk1' < t.functions.size :=
        _hwf j hj _ hc_mem
      have hc_cls : (collectCalleesBlock t.functions[j].body)[k]'hk1' < classes.size :=
        hsz_classes ▸ hc_rng
      rw [getElem!_pos (classes : Array Nat) _ hc_cls]
      have := deduplicate_snd_eq_classes_getElem t hn _ hc_rng
      simp only at this
      exact this.symm
  rw [← hmap_bridge_i, ← hmap_bridge_j]
  exact hsig2


/-- Inductive form: `partitionRefineBound` preserves "equal final class ⇒
equal input class". Uses `Array.getElem?` equality form (index-erased) to
avoid dependent-index proof-term drag in the IH. -/
private theorem partitionRefineBound_only_splits
    (bound : Nat) (classes : Array Nat) (callees : Array (Array FunIdx))
    (i j : Nat) (hi : i < classes.size) (hj : j < classes.size)
    (h : (partitionRefineBound bound classes callees)[i]? =
         (partitionRefineBound bound classes callees)[j]?) :
    classes[i] = classes[j] := by
  induction bound generalizing classes with
  | zero =>
    unfold partitionRefineBound at h
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj] at h
    exact Option.some.inj h
  | succ b ih =>
    have hsz_sig : (classes.mapIdx fun k cls =>
        (cls, callees[k]!.map (classes[·]!))).size = classes.size :=
      Array.size_mapIdx
    have hsz_nc : (assignClasses (classes.mapIdx fun k cls =>
        (cls, callees[k]!.map (classes[·]!)))).1.size = classes.size := by
      rw [assignClasses_size_eq, hsz_sig]
    unfold partitionRefineBound at h
    simp only at h
    split at h
    · rename_i hbeq
      rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj] at h
      exact Option.some.inj h
    · rename_i hne
      let signatures : Array (Nat × Array Nat) :=
        classes.mapIdx fun k cls => (cls, callees[k]!.map (classes[·]!))
      let newClasses : Array Nat := (assignClasses signatures).1
      have hi_nc : i < newClasses.size := hsz_nc ▸ hi
      have hj_nc : j < newClasses.size := hsz_nc ▸ hj
      have h_nc_eq : newClasses[i]'hi_nc = newClasses[j]'hj_nc := by
        have hih := ih newClasses hi_nc hj_nc h
        exact hih
      have hi_acl : i < (assignClasses signatures).1.size := hsz_nc ▸ hi
      have hj_acl : j < (assignClasses signatures).1.size := hsz_nc ▸ hj
      have h_acl_eq : (assignClasses signatures).1[i]'hi_acl =
          (assignClasses signatures).1[j]'hj_acl := h_nc_eq
      have hi_sig : i < signatures.size := hsz_sig ▸ hi
      have hj_sig : j < signatures.size := hsz_sig ▸ hj
      have hsig_eq : signatures[i]'hi_sig = signatures[j]'hj_sig :=
        assignClasses_values_eq_of_classes_eq signatures i j hi_acl hj_acl h_acl_eq
      have h_i : signatures[i]'hi_sig =
          (classes[i], callees[i]!.map (classes[·]!)) := by
        show (classes.mapIdx fun k cls =>
          (cls, callees[k]!.map (classes[·]!)))[i]'hi_sig = _
        simp [Array.getElem_mapIdx]
      have h_j : signatures[j]'hj_sig =
          (classes[j], callees[j]!.map (classes[·]!)) := by
        show (classes.mapIdx fun k cls =>
          (cls, callees[k]!.map (classes[·]!)))[j]'hj_sig = _
        simp [Array.getElem_mapIdx]
      rw [h_i, h_j] at hsig_eq
      exact (Prod.mk.inj hsig_eq).1

/-- `partitionRefine` only splits classes: equal final class implies equal
initial class. Wrapper around `partitionRefineBound_only_splits`. -/
theorem partitionRefine_only_splits
    (classes : Array Nat) (callees : Array (Array FunIdx))
    (i j : Nat) (hi : i < classes.size) (hj : j < classes.size) :
    have hi' : i < (partitionRefine classes callees).size := by
      rw [partitionRefine_size_eq]; exact hi
    have hj' : j < (partitionRefine classes callees).size := by
      rw [partitionRefine_size_eq]; exact hj
    (partitionRefine classes callees)[i]'hi' = (partitionRefine classes callees)[j]'hj' →
      classes[i] = classes[j] := by
  intro hi' hj' h
  have h' : (partitionRefine classes callees)[i]? = (partitionRefine classes callees)[j]? := by
    rw [Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hj', h]
  unfold partitionRefine at h'
  exact partitionRefineBound_only_splits _ classes callees i j hi hj h'

/-- (1) Same final class ⇒ same initial class ⇒ same skeleton + layout.
`assignClasses` is collision-free (foldl inserts only on fresh keys); partition
refinement only splits classes, so same-final-class ⇒ same-initial-class key.

Proof is complete modulo a single BLOCKED step: the application of
`assignClasses_values_eq_of_classes_eq` on `skeletons : Array (Block × FunctionLayout)`
needs `LawfulBEq Block`. `Block` is a nested mutual inductive (via `Ctrl` holding
`Array (G × Block)`) so its derived `BEq` is opaque (see TACTICS.md §
"Nested-inductive `deriving BEq` is opaque"). FIX: write manual `Block.beq` +
manual `LawfulBEq Block` instance. Future session. -/
private theorem skeleton_eq_of_same_class
    (t : Toplevel)
    (_hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
             let (initClasses, _) := assignClasses skeletons
             let callees := t.functions.map fun f => collectCalleesBlock f.body
             let classes := partitionRefine initClasses callees
             let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
             (assignClasses signatures).1 = classes) :
    let (_tDedup, remap) := t.deduplicate
    ∀ i j (_hi : i < t.functions.size) (_hj : j < t.functions.size),
      remap i = remap j →
      skeletonBlock t.functions[i].body = skeletonBlock t.functions[j].body ∧
        t.functions[i].layout = t.functions[j].layout := by
  simp only
  intro i j hi hj hremap
  have hn : 0 < t.functions.size := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) (Nat.le_refl _)
  let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
  let initClasses := (assignClasses skeletons).1
  let callees := t.functions.map fun f => collectCalleesBlock f.body
  let classes := partitionRefine initClasses callees
  have hsk_def : skeletons = t.functions.map fun f => (skeletonBlock f.body, f.layout) := rfl
  have hic_def : initClasses = (assignClasses skeletons).1 := rfl
  have hcal_def : callees = t.functions.map fun f => collectCalleesBlock f.body := rfl
  have hcls_def : classes = partitionRefine initClasses callees := rfl
  have hsz_sk : skeletons.size = t.functions.size := by
    rw [hsk_def, Array.size_map]
  have hsz_ic : initClasses.size = t.functions.size := by
    rw [hic_def, assignClasses_size_eq, hsz_sk]
  have hsz_classes : classes.size = t.functions.size := by
    rw [hcls_def, partitionRefine_size_eq, hsz_ic]
  have hi_cls : i < classes.size := hsz_classes ▸ hi
  have hj_cls : j < classes.size := hsz_classes ▸ hj
  have hi_ic : i < initClasses.size := hsz_ic ▸ hi
  have hj_ic : j < initClasses.size := hsz_ic ▸ hj
  have hi_sk : i < skeletons.size := hsz_sk ▸ hi
  have hj_sk : j < skeletons.size := hsz_sk ▸ hj
  have hremap_i : (t.deduplicate).2 i = classes[i]'hi_cls := by
    have := deduplicate_snd_eq_classes_getElem t hn i hi
    simp only at this
    rw [this]
  have hremap_j : (t.deduplicate).2 j = classes[j]'hj_cls := by
    have := deduplicate_snd_eq_classes_getElem t hn j hj
    simp only at this
    rw [this]
  have hcls_eq : classes[i]'hi_cls = classes[j]'hj_cls := by
    rw [← hremap_i, ← hremap_j]
    exact hremap
  have hic_eq : initClasses[i]'hi_ic = initClasses[j]'hj_ic := by
    have := partitionRefine_only_splits initClasses callees i j hi_ic hj_ic
    have h_arg : (partitionRefine initClasses callees)[i]'(by
        rw [partitionRefine_size_eq]; exact hi_ic) =
        (partitionRefine initClasses callees)[j]'(by
        rw [partitionRefine_size_eq]; exact hj_ic) := by
      show classes[i]'hi_cls = classes[j]'hj_cls
      exact hcls_eq
    exact this h_arg
  have hi_acl : i < (assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hi_sk
  have hj_acl : j < (assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hj_sk
  have h_acl_eq : (assignClasses skeletons).1[i]'hi_acl =
      (assignClasses skeletons).1[j]'hj_acl := hic_eq
  have hsk_eq : skeletons[i]'hi_sk = skeletons[j]'hj_sk :=
    assignClasses_values_eq_of_classes_eq skeletons i j hi_acl hj_acl h_acl_eq
  have h_i : skeletons[i]'hi_sk = (skeletonBlock t.functions[i].body, t.functions[i].layout) := by
    show (t.functions.map fun f => (skeletonBlock f.body, f.layout))[i]'hi_sk = _
    simp [Array.getElem_map]
  have h_j : skeletons[j]'hj_sk = (skeletonBlock t.functions[j].body, t.functions[j].layout) := by
    show (t.functions.map fun f => (skeletonBlock f.body, f.layout))[j]'hj_sk = _
    simp [Array.getElem_map]
  rw [h_i, h_j] at hsk_eq
  exact Prod.mk.inj hsk_eq

/-! (3) Structural synthesis: equal skeletons + equal remapped-callee lists ⇒
equal `rewriteBlock` outputs. Proof by mutual induction on Block/Ctrl.
Infrastructure below: op-level, ops-array, size-equality mutual, rewrite mutual. -/

/-- Op-level: equal skeleton and equal mapped-callees forces equal rewrite. -/
private theorem rewriteOp_eq_of_skeleton_and_callee
    (f : FunIdx → FunIdx) (op1 op2 : Op)
    (hsk : skeletonOp op1 = skeletonOp op2)
    (hcs : (collectCalleesOp op1).map f = (collectCalleesOp op2).map f) :
    rewriteOp f op1 = rewriteOp f op2 := by
  cases op1 with
  | call i1 a1 s1 u1 =>
    cases op2 with
    | call i2 a2 s2 u2 =>
      simp only [skeletonOp] at hsk
      injection hsk with _ ha hs hu
      cases ha; cases hs; cases hu
      simp only [collectCalleesOp] at hcs
      have hf : f i1 = f i2 := by
        have := congrArg (·[0]!) hcs
        simpa using this
      simp only [rewriteOp, hf]
    | _ => simp only [skeletonOp] at hsk; exact Op.noConfusion hsk
  | _ =>
    cases op2 with
    | call i2 a2 s2 u2 =>
      simp only [skeletonOp] at hsk; exact Op.noConfusion hsk
    | _ =>
      simp only [skeletonOp] at hsk
      first | (cases hsk; rfl) | (exact Op.noConfusion hsk)

/-- List bridge: foldl over collectCalleesOp equals flatMap toList. -/
private theorem collectCalleesOp_foldl_eq_flatMap (ops : List Op) (acc : Array FunIdx) :
    ops.foldl (fun acc op => acc ++ collectCalleesOp op) acc =
      acc ++ (ops.flatMap (fun op => (collectCalleesOp op).toList)).toArray := by
  induction ops generalizing acc with
  | nil => simp
  | cons o rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih]
    have happ : ((collectCalleesOp o).toList ++
        rest.flatMap (fun op => (collectCalleesOp op).toList)).toArray =
        (collectCalleesOp o) ++
          (rest.flatMap (fun op => (collectCalleesOp op).toList)).toArray := by
      simp
    rw [happ]
    simp [Array.append_assoc]

private theorem list_flatMap_map_collectCalleesOp (ops : List Op) (f : FunIdx → FunIdx) :
    (ops.flatMap (fun op => (collectCalleesOp op).toList)).map f =
      ops.flatMap (fun op => ((collectCalleesOp op).map f).toList) := by
  induction ops with
  | nil => simp
  | cons o rest ih =>
    simp only [List.flatMap_cons, List.map_append, ih]
    congr 1
    simp [Array.toList_map]

private theorem list_rewriteOp_eq_of_skeleton_and_callees
    (f : FunIdx → FunIdx) (ops1 ops2 : List Op)
    (hsk : ops1.map skeletonOp = ops2.map skeletonOp)
    (hcs : ops1.flatMap (fun op => ((collectCalleesOp op).map f).toList) =
           ops2.flatMap (fun op => ((collectCalleesOp op).map f).toList)) :
    ops1.map (rewriteOp f) = ops2.map (rewriteOp f) := by
  induction ops1 generalizing ops2 with
  | nil =>
    cases ops2 with
    | nil => rfl
    | cons o2 rest2 => simp at hsk
  | cons o1 rest1 ih =>
    cases ops2 with
    | nil => simp at hsk
    | cons o2 rest2 =>
      simp only [List.map_cons, List.cons.injEq] at hsk
      obtain ⟨hsk_head, hsk_tail⟩ := hsk
      simp only [List.flatMap_cons] at hcs
      have hsize : (collectCalleesOp o1).size = (collectCalleesOp o2).size := by
        cases o1 <;> cases o2 <;>
          simp only [skeletonOp] at hsk_head <;>
          (first
            | (cases hsk_head; simp [collectCalleesOp])
            | (exact Op.noConfusion hsk_head)
            | simp [collectCalleesOp])
      have hhead_len : ((collectCalleesOp o1).map f).toList.length =
          ((collectCalleesOp o2).map f).toList.length := by
        simp [hsize]
      have ⟨hhead, htail⟩ := List.append_inj hcs hhead_len
      have hop_eq : rewriteOp f o1 = rewriteOp f o2 := by
        apply rewriteOp_eq_of_skeleton_and_callee f o1 o2 hsk_head
        have : ((collectCalleesOp o1).map f).toList = ((collectCalleesOp o2).map f).toList := hhead
        exact Array.toList_inj.mp this
      have htail_eq : rest1.map (rewriteOp f) = rest2.map (rewriteOp f) := ih rest2 hsk_tail htail
      simp [hop_eq, htail_eq]

private theorem array_rewriteOp_eq_of_skeleton_and_callees
    (f : FunIdx → FunIdx) (ops1 ops2 : Array Op)
    (hsk : ops1.map skeletonOp = ops2.map skeletonOp)
    (hcs : (ops1.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).map f =
           (ops2.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).map f) :
    ops1.map (rewriteOp f) = ops2.map (rewriteOp f) := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, Array.toList_map]
  apply list_rewriteOp_eq_of_skeleton_and_callees f
  · have : (ops1.map skeletonOp).toList = (ops2.map skeletonOp).toList := by
      rw [hsk]
    rw [Array.toList_map, Array.toList_map] at this
    exact this
  · have h1 : ops1.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) =
        (ops1.toList.flatMap (fun op => (collectCalleesOp op).toList)).toArray := by
      rw [← Array.foldl_toList]
      have := collectCalleesOp_foldl_eq_flatMap ops1.toList #[]
      simpa using this
    have h2 : ops2.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) =
        (ops2.toList.flatMap (fun op => (collectCalleesOp op).toList)).toArray := by
      rw [← Array.foldl_toList]
      have := collectCalleesOp_foldl_eq_flatMap ops2.toList #[]
      simpa using this
    rw [h1, h2] at hcs
    have hcs_list : (ops1.toList.flatMap (fun op => (collectCalleesOp op).toList)).map f =
        (ops2.toList.flatMap (fun op => (collectCalleesOp op).toList)).map f := by
      have := congrArg Array.toList hcs
      simp [] at this
      exact this
    rw [list_flatMap_map_collectCalleesOp, list_flatMap_map_collectCalleesOp] at hcs_list
    exact hcs_list

private theorem collectCalleesOp_size_eq_of_skeleton_eq
    {o1 o2 : Op} (h : skeletonOp o1 = skeletonOp o2) :
    (collectCalleesOp o1).size = (collectCalleesOp o2).size := by
  cases o1 <;> cases o2 <;>
    simp only [skeletonOp] at h <;>
    (first
      | (cases h; simp [collectCalleesOp])
      | (exact Op.noConfusion h)
      | simp [collectCalleesOp])

private theorem ops_foldl_callees_size_eq
    (ops1 ops2 : Array Op) (hsk : ops1.map skeletonOp = ops2.map skeletonOp) :
    (ops1.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).size =
      (ops2.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).size := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  rw [collectCalleesOp_foldl_eq_flatMap, collectCalleesOp_foldl_eq_flatMap]
  simp only [Array.size_append, Array.size_empty, Nat.zero_add]
  have hlist : ops1.toList.map skeletonOp = ops2.toList.map skeletonOp := by
    have := congrArg Array.toList hsk
    simpa [Array.toList_map] using this
  have key : ∀ ops1 ops2 : List Op, ops1.map skeletonOp = ops2.map skeletonOp →
      (ops1.flatMap (fun op => (collectCalleesOp op).toList)).length =
        (ops2.flatMap (fun op => (collectCalleesOp op).toList)).length := by
    intro l1 l2 hl
    induction l1 generalizing l2 with
    | nil =>
      cases l2 with
      | nil => rfl
      | cons _ _ => simp at hl
    | cons o rest ih =>
      cases l2 with
      | nil => simp at hl
      | cons o' rest' =>
        simp only [List.map_cons, List.cons.injEq] at hl
        obtain ⟨hh, ht⟩ := hl
        simp only [List.flatMap_cons, List.length_append]
        have hsz := collectCalleesOp_size_eq_of_skeleton_eq hh
        have hlen_list : (collectCalleesOp o).toList.length = (collectCalleesOp o').toList.length := by
          simp [Array.length_toList, hsz]
        rw [hlen_list, ih rest' ht]
  have hk := key ops1.toList ops2.toList hlist
  have h1 : (ops1.toList.flatMap (fun op => (collectCalleesOp op).toList)).toArray.size =
      (ops1.toList.flatMap (fun op => (collectCalleesOp op).toList)).length := by
    simp
  have h2 : (ops2.toList.flatMap (fun op => (collectCalleesOp op).toList)).toArray.size =
      (ops2.toList.flatMap (fun op => (collectCalleesOp op).toList)).length := by
    simp
  rw [h1, h2, hk]

private theorem Block.sizeOf_ctrl_lt' (b : Block) : sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩; show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl; omega

private theorem branches_callees_size_eq_of_skeleton_eq
    (br1 br2 : Array (G × Block))
    (hsk : (br1.attach.map fun ⟨(g, b), _⟩ => (g, skeletonBlock b)) =
           (br2.attach.map fun ⟨(g, b), _⟩ => (g, skeletonBlock b))) :
    br1.size = br2.size := by
  have := congrArg Array.size hsk
  simp at this
  exact this

private theorem branches_attach_map_skeleton_eq_map
    (br : Array (G × Block)) :
    (br.attach.map fun ⟨(g, b), _⟩ => (g, skeletonBlock b)) =
      br.map (fun (gb : G × Block) => (gb.1, skeletonBlock gb.2)) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_attach]

private theorem branches_attach_map_rewrite_eq_map
    (f : FunIdx → FunIdx) (br : Array (G × Block)) :
    (br.attach.map fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)) =
      br.map (fun (gb : G × Block) => (gb.1, rewriteBlock f gb.2)) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [Array.getElem_attach]

private theorem list_foldl_attachWith_eq'
    {α β} (l : List α) (P : α → Prop) (H : ∀ x ∈ l, P x)
    (g : β → α → β) (acc : β) :
    (l.attachWith P H).foldl (fun acc x => g acc x.1) acc =
    l.foldl g acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attachWith_cons, List.foldl_cons]
    exact ih (fun y hy => H y (List.mem_cons.mpr (Or.inr hy))) (g acc x)

private theorem attach_foldl_collectCalleesBlock_eq
    (branches : Array (G × Block)) (acc : Array FunIdx) :
    branches.attach.foldl (init := acc) (fun acc ⟨(_, b), _⟩ =>
      acc ++ collectCalleesBlock b) =
    List.foldl (fun acc (p : G × Block) => acc ++ collectCalleesBlock p.2)
      acc branches.toList := by
  rw [← Array.foldl_toList, Array.toList_attach]
  exact list_foldl_attachWith_eq' branches.toList (· ∈ branches) _
    (fun acc (p : G × Block) => acc ++ collectCalleesBlock p.2) acc

private theorem list_foldl_collectCalleesBlock_eq_flatMap
    (branches : List (G × Block)) (acc : Array FunIdx) :
    List.foldl (fun acc (p : G × Block) => acc ++ collectCalleesBlock p.2) acc branches =
      acc ++ (branches.flatMap (fun p => (collectCalleesBlock p.2).toList)).toArray := by
  induction branches generalizing acc with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih]
    have happ : ((collectCalleesBlock p.2).toList ++
        rest.flatMap (fun q => (collectCalleesBlock q.2).toList)).toArray =
        (collectCalleesBlock p.2) ++
          (rest.flatMap (fun q => (collectCalleesBlock q.2).toList)).toArray := by
      simp
    rw [happ]
    simp [Array.append_assoc]

private theorem list_flatMap_map_collectCalleesBlock
    (branches : List (G × Block)) (f : FunIdx → FunIdx) :
    (branches.flatMap (fun p => (collectCalleesBlock p.2).toList)).map f =
      branches.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList) := by
  induction branches with
  | nil => simp
  | cons p rest ih =>
    simp only [List.flatMap_cons, List.map_append, ih]
    congr 1
    simp [Array.toList_map]

mutual
  private theorem collectCalleesBlock_size_eq_of_skeleton_eq
      (b1 b2 : Block) (hsk : skeletonBlock b1 = skeletonBlock b2) :
      (collectCalleesBlock b1).size = (collectCalleesBlock b2).size := by
    have hsk_full : (⟨b1.ops.map skeletonOp, skeletonCtrl b1.ctrl⟩ : Block) =
        ⟨b2.ops.map skeletonOp, skeletonCtrl b2.ctrl⟩ := by
      have h1 : skeletonBlock b1 = ⟨b1.ops.map skeletonOp, skeletonCtrl b1.ctrl⟩ := by
        unfold skeletonBlock; rfl
      have h2 : skeletonBlock b2 = ⟨b2.ops.map skeletonOp, skeletonCtrl b2.ctrl⟩ := by
        unfold skeletonBlock; rfl
      rw [← h1, ← h2]; exact hsk
    injection hsk_full with hsk_ops hsk_ctrl
    have hops := ops_foldl_callees_size_eq b1.ops b2.ops hsk_ops
    have hctrl := collectCalleesCtrl_size_eq_of_skeleton_eq b1.ctrl b2.ctrl hsk_ctrl
    have h1 : collectCalleesBlock b1 =
        b1.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
          collectCalleesCtrl b1.ctrl := by unfold collectCalleesBlock; rfl
    have h2 : collectCalleesBlock b2 =
        b2.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
          collectCalleesCtrl b2.ctrl := by unfold collectCalleesBlock; rfl
    rw [h1, h2, Array.size_append, Array.size_append, hops, hctrl]
  termination_by (sizeOf b1, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt' _)

  private theorem collectCalleesCtrl_size_eq_of_skeleton_eq
      (c1 c2 : Ctrl) (hsk : skeletonCtrl c1 = skeletonCtrl c2) :
      (collectCalleesCtrl c1).size = (collectCalleesCtrl c2).size := by
    cases c1 with
    | «return» s1 vs1 =>
      cases c2 with
      | «return» s2 vs2 => simp [collectCalleesCtrl]
      | _ => unfold skeletonCtrl at hsk; exact Ctrl.noConfusion hsk
    | yield s1 vs1 =>
      cases c2 with
      | yield s2 vs2 => simp [collectCalleesCtrl]
      | _ => unfold skeletonCtrl at hsk; exact Ctrl.noConfusion hsk
    | «match» v1 br1 d1 =>
      cases c2 with
      | «match» v2 br2 d2 =>
        unfold skeletonCtrl at hsk
        injection hsk with _hv hbr hd
        have hbr_size : br1.size = br2.size := branches_callees_size_eq_of_skeleton_eq _ _ hbr
        have hbr_pt : ∀ i (h1 : i < br1.size) (h2 : i < br2.size),
            skeletonBlock br1[i].2 = skeletonBlock br2[i].2 := by
          intro i h1 h2
          have hfun := congrFun (congrArg (fun arr => fun i => arr[i]?) hbr) i
          simp [h1, h2, Array.getElem_attach] at hfun
          exact hfun.2
        have hbr_foldl :
            (br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size =
            (br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size := by
          rw [attach_foldl_collectCalleesBlock_eq, attach_foldl_collectCalleesBlock_eq]
          rw [list_foldl_collectCalleesBlock_eq_flatMap,
              list_foldl_collectCalleesBlock_eq_flatMap]
          simp only [Array.size_append, Nat.zero_add, List.size_toArray,
            List.length_nil]
          have hlist_len : br1.toList.length = br2.toList.length := by simp [hbr_size]
          have hlist_pt : ∀ i (h1 : i < br1.toList.length) (h2 : i < br2.toList.length),
              skeletonBlock br1.toList[i].2 = skeletonBlock br2.toList[i].2 := by
            intro i h1 h2
            have h1' : i < br1.size := by simpa using h1
            have h2' : i < br2.size := by simpa using h2
            have := hbr_pt i h1' h2'
            simp only [Array.getElem_toList]
            exact this
          have hm1 : ∀ p ∈ br1.toList, sizeOf p.2 < sizeOf br1 := by
            rintro ⟨g, b⟩ hp
            have hmem : (g, b) ∈ br1 := Array.mem_toList_iff.mp hp
            have h1 := Array.sizeOf_lt_of_mem hmem
            have h2 := Prod.mk.sizeOf_spec g b
            show sizeOf b < sizeOf br1
            omega
          have hm2 : ∀ p ∈ br2.toList, sizeOf p.2 < sizeOf br2 := by
            rintro ⟨g, b⟩ hp
            have hmem : (g, b) ∈ br2 := Array.mem_toList_iff.mp hp
            have h1 := Array.sizeOf_lt_of_mem hmem
            have h2 := Prod.mk.sizeOf_spec g b
            show sizeOf b < sizeOf br2
            omega
          suffices aux : ∀ (l1 : List (G × Block))
              (hm1 : ∀ p ∈ l1, sizeOf p.2 < sizeOf br1)
              (l2 : List (G × Block))
              (hm2 : ∀ p ∈ l2, sizeOf p.2 < sizeOf br2),
              l1.length = l2.length →
              (∀ i (h1 : i < l1.length) (h2 : i < l2.length),
                skeletonBlock l1[i].2 = skeletonBlock l2[i].2) →
              (l1.flatMap (fun p => (collectCalleesBlock p.2).toList)).length =
                (l2.flatMap (fun p => (collectCalleesBlock p.2).toList)).length by
            exact aux br1.toList hm1 br2.toList hm2 hlist_len hlist_pt
          intro l1
          induction l1 with
          | nil =>
            intro _ l2 _ hlen _
            cases l2 with
            | nil => rfl
            | cons _ _ => simp at hlen
          | cons p1 rest1 ih =>
            intro hm1 l2 hm2 hlen hpt
            cases l2 with
            | nil => simp at hlen
            | cons p2 rest2 =>
              simp only [List.flatMap_cons, List.length_append]
              have hhead : skeletonBlock p1.2 = skeletonBlock p2.2 := by
                have := hpt 0 (by simp) (by simp)
                simpa using this
              have _hsz1 : sizeOf p1.2 < sizeOf br1 := hm1 p1 List.mem_cons_self
              have _hsz2 : sizeOf p2.2 < sizeOf br2 := hm2 p2 List.mem_cons_self
              have hsz_head : (collectCalleesBlock p1.2).size =
                  (collectCalleesBlock p2.2).size :=
                collectCalleesBlock_size_eq_of_skeleton_eq p1.2 p2.2 hhead
              have hlen_head : (collectCalleesBlock p1.2).toList.length =
                  (collectCalleesBlock p2.2).toList.length := by
                simp [Array.length_toList, hsz_head]
              rw [hlen_head]
              have hlen' : rest1.length = rest2.length := by
                simp at hlen; exact hlen
              have hpt' : ∀ i (h1 : i < rest1.length) (h2 : i < rest2.length),
                  skeletonBlock rest1[i].2 = skeletonBlock rest2[i].2 := by
                intro i h1 h2
                have := hpt (i+1) (by simp; omega) (by simp; omega)
                simpa using this
              have hm1' : ∀ p ∈ rest1, sizeOf p.2 < sizeOf br1 :=
                fun p hp => hm1 p (List.mem_cons.mpr (Or.inr hp))
              have hm2' : ∀ p ∈ rest2, sizeOf p.2 < sizeOf br2 :=
                fun p hp => hm2 p (List.mem_cons.mpr (Or.inr hp))
              rw [ih hm1' rest2 hm2' hlen' hpt']
        unfold collectCalleesCtrl
        cases d1 with
        | none =>
          cases d2 with
          | none => simp only; exact hbr_foldl
          | some b2 => simp at hd
        | some b1 =>
          cases d2 with
          | none => simp at hd
          | some b2 =>
            simp only at hd
            injection hd with hd'
            simp only [Array.size_append]
            rw [hbr_foldl, collectCalleesBlock_size_eq_of_skeleton_eq b1 b2 hd']
      | _ => unfold skeletonCtrl at hsk; exact Ctrl.noConfusion hsk
    | matchContinue v1 br1 d1 os1 sa1 sl1 cont1 =>
      cases c2 with
      | matchContinue v2 br2 d2 os2 sa2 sl2 cont2 =>
        unfold skeletonCtrl at hsk
        injection hsk with _hv hbr hd _hos _hsa _hsl hcont
        have hbr_size : br1.size = br2.size := branches_callees_size_eq_of_skeleton_eq _ _ hbr
        have hbr_pt : ∀ i (h1 : i < br1.size) (h2 : i < br2.size),
            skeletonBlock br1[i].2 = skeletonBlock br2[i].2 := by
          intro i h1 h2
          have hfun := congrFun (congrArg (fun arr => fun i => arr[i]?) hbr) i
          simp [h1, h2, Array.getElem_attach] at hfun
          exact hfun.2
        have hbr_foldl :
            (br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size =
            (br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size := by
          rw [attach_foldl_collectCalleesBlock_eq, attach_foldl_collectCalleesBlock_eq]
          rw [list_foldl_collectCalleesBlock_eq_flatMap,
              list_foldl_collectCalleesBlock_eq_flatMap]
          simp only [Array.size_append, Nat.zero_add, List.size_toArray,
            List.length_nil]
          have hlist_pt : ∀ i (h1 : i < br1.toList.length) (h2 : i < br2.toList.length),
              skeletonBlock br1.toList[i].2 = skeletonBlock br2.toList[i].2 := by
            intro i h1 h2
            have h1' : i < br1.size := by simpa using h1
            have h2' : i < br2.size := by simpa using h2
            have := hbr_pt i h1' h2'
            simp only [Array.getElem_toList]
            exact this
          have hlist_len : br1.toList.length = br2.toList.length := by simp [hbr_size]
          have hm1 : ∀ p ∈ br1.toList, sizeOf p.2 < sizeOf br1 := by
            rintro ⟨g, b⟩ hp
            have hmem : (g, b) ∈ br1 := Array.mem_toList_iff.mp hp
            have h1 := Array.sizeOf_lt_of_mem hmem
            have h2 := Prod.mk.sizeOf_spec g b
            show sizeOf b < sizeOf br1
            omega
          have hm2 : ∀ p ∈ br2.toList, sizeOf p.2 < sizeOf br2 := by
            rintro ⟨g, b⟩ hp
            have hmem : (g, b) ∈ br2 := Array.mem_toList_iff.mp hp
            have h1 := Array.sizeOf_lt_of_mem hmem
            have h2 := Prod.mk.sizeOf_spec g b
            show sizeOf b < sizeOf br2
            omega
          suffices aux : ∀ (l1 : List (G × Block))
              (hm1 : ∀ p ∈ l1, sizeOf p.2 < sizeOf br1)
              (l2 : List (G × Block))
              (hm2 : ∀ p ∈ l2, sizeOf p.2 < sizeOf br2),
              l1.length = l2.length →
              (∀ i (h1 : i < l1.length) (h2 : i < l2.length),
                skeletonBlock l1[i].2 = skeletonBlock l2[i].2) →
              (l1.flatMap (fun p => (collectCalleesBlock p.2).toList)).length =
                (l2.flatMap (fun p => (collectCalleesBlock p.2).toList)).length by
            exact aux br1.toList hm1 br2.toList hm2 hlist_len hlist_pt
          intro l1
          induction l1 with
          | nil =>
            intro _ l2 _ hlen _
            cases l2 with
            | nil => rfl
            | cons _ _ => simp at hlen
          | cons p1 rest1 ih =>
            intro hm1 l2 hm2 hlen hpt
            cases l2 with
            | nil => simp at hlen
            | cons p2 rest2 =>
              simp only [List.flatMap_cons, List.length_append]
              have hhead : skeletonBlock p1.2 = skeletonBlock p2.2 := by
                have := hpt 0 (by simp) (by simp)
                simpa using this
              have _hsz1 : sizeOf p1.2 < sizeOf br1 := hm1 p1 List.mem_cons_self
              have _hsz2 : sizeOf p2.2 < sizeOf br2 := hm2 p2 List.mem_cons_self
              have hsz_head : (collectCalleesBlock p1.2).size =
                  (collectCalleesBlock p2.2).size :=
                collectCalleesBlock_size_eq_of_skeleton_eq p1.2 p2.2 hhead
              have hlen_head : (collectCalleesBlock p1.2).toList.length =
                  (collectCalleesBlock p2.2).toList.length := by
                simp [Array.length_toList, hsz_head]
              rw [hlen_head]
              have hlen' : rest1.length = rest2.length := by
                simp at hlen; exact hlen
              have hpt' : ∀ i (h1 : i < rest1.length) (h2 : i < rest2.length),
                  skeletonBlock rest1[i].2 = skeletonBlock rest2[i].2 := by
                intro i h1 h2
                have := hpt (i+1) (by simp; omega) (by simp; omega)
                simpa using this
              have hm1' : ∀ p ∈ rest1, sizeOf p.2 < sizeOf br1 :=
                fun p hp => hm1 p (List.mem_cons.mpr (Or.inr hp))
              have hm2' : ∀ p ∈ rest2, sizeOf p.2 < sizeOf br2 :=
                fun p hp => hm2 p (List.mem_cons.mpr (Or.inr hp))
              rw [ih hm1' rest2 hm2' hlen' hpt']
        have hcont_size := collectCalleesBlock_size_eq_of_skeleton_eq cont1 cont2 hcont
        unfold collectCalleesCtrl
        cases d1 with
        | none =>
          cases d2 with
          | none =>
            simp only [Array.size_append]
            rw [hbr_foldl, hcont_size]
          | some b2 => simp at hd
        | some b1 =>
          cases d2 with
          | none => simp at hd
          | some b2 =>
            simp only at hd
            injection hd with hd'
            simp only [Array.size_append]
            rw [hbr_foldl, collectCalleesBlock_size_eq_of_skeleton_eq b1 b2 hd', hcont_size]
      | _ => unfold skeletonCtrl at hsk; exact Ctrl.noConfusion hsk
  termination_by (sizeOf c1, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left
         first
           | (have _hm := ‹sizeOf _ < sizeOf _›; grind)
           | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
           | grind)
end

mutual
  private theorem rewriteCtrl_eq_of_skeleton_and_callees
      (f : FunIdx → FunIdx) (c1 c2 : Ctrl)
      (hsk : skeletonCtrl c1 = skeletonCtrl c2)
      (hcs : (collectCalleesCtrl c1).map f = (collectCalleesCtrl c2).map f) :
      rewriteCtrl f c1 = rewriteCtrl f c2 := by
    cases c1 with
    | «return» s1 vs1 =>
      cases c2 with
      | «return» s2 vs2 =>
        simp only [skeletonCtrl] at hsk
        injection hsk with hs hv
        cases hs; cases hv
        rfl
      | _ =>
        unfold skeletonCtrl at hsk
        exact Ctrl.noConfusion hsk
    | yield s1 vs1 =>
      cases c2 with
      | yield s2 vs2 =>
        simp only [skeletonCtrl] at hsk
        injection hsk with hs hv
        cases hs; cases hv
        rfl
      | _ =>
        unfold skeletonCtrl at hsk
        exact Ctrl.noConfusion hsk
    | «match» v1 br1 d1 =>
      cases c2 with
      | «match» v2 br2 d2 =>
        unfold skeletonCtrl at hsk
        injection hsk with hv hbr hd
        cases hv
        have hbr_size : br1.size = br2.size := branches_callees_size_eq_of_skeleton_eq _ _ hbr
        have hbr_pt : ∀ i (h1 : i < br1.size) (h2 : i < br2.size),
            br1[i].1 = br2[i].1 ∧ skeletonBlock br1[i].2 = skeletonBlock br2[i].2 := by
          intro i h1 h2
          have hfun := congrFun (congrArg (fun arr => fun i => arr[i]?) hbr) i
          simp [h1, h2, Array.getElem_attach] at hfun
          exact hfun
        unfold collectCalleesCtrl at hcs
        simp only at hcs
        have hbr_foldl_size :
            (br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size =
            (br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size := by
          have hsk_match_none :
              skeletonCtrl (Ctrl.match v1 br1 (none : Option Block)) =
              skeletonCtrl (Ctrl.match v1 br2 (none : Option Block)) := by
            unfold skeletonCtrl; rw [hbr]
          have := collectCalleesCtrl_size_eq_of_skeleton_eq
            (Ctrl.match v1 br1 (none : Option Block))
            (Ctrl.match v1 br2 (none : Option Block)) hsk_match_none
          unfold collectCalleesCtrl at this
          simpa using this
        have hbr_callees_eq :
            (br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).map f =
            (br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).map f ∧
          (match d1 with
            | none => (#[] : Array FunIdx)
            | some b => collectCalleesBlock b).map f =
          (match d2 with
            | none => (#[] : Array FunIdx)
            | some b => collectCalleesBlock b).map f := by
          have hsize_map :
              ((br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
                acc ++ collectCalleesBlock b)).map f).size =
              ((br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
                acc ++ collectCalleesBlock b)).map f).size := by
            simp only [Array.size_map]; exact hbr_foldl_size
          cases d1 with
          | none =>
            cases d2 with
            | none =>
              refine ⟨?_, ?_⟩
              · exact hcs
              · simp
            | some b2 => simp at hd
          | some b1 =>
            cases d2 with
            | none => simp at hd
            | some b2 =>
              simp only at hcs
              rw [Array.map_append, Array.map_append] at hcs
              exact Array.append_inj hcs hsize_map
        obtain ⟨hbr_map_eq, hd_map_eq⟩ := hbr_callees_eq
        have hbr_flatMap_map :
            (br1.toList.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) =
            (br2.toList.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) := by
          have h1 : br1.attach.foldl (init := #[]) (fun acc (x : {x // x ∈ br1}) =>
              match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b) =
              (br1.toList.flatMap (fun p => (collectCalleesBlock p.2).toList)).toArray := by
            rw [attach_foldl_collectCalleesBlock_eq]
            have := list_foldl_collectCalleesBlock_eq_flatMap br1.toList #[]
            simpa using this
          have h2 : br2.attach.foldl (init := #[]) (fun acc (x : {x // x ∈ br2}) =>
              match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b) =
              (br2.toList.flatMap (fun p => (collectCalleesBlock p.2).toList)).toArray := by
            rw [attach_foldl_collectCalleesBlock_eq]
            have := list_foldl_collectCalleesBlock_eq_flatMap br2.toList #[]
            simpa using this
          rw [h1, h2] at hbr_map_eq
          have := congrArg Array.toList hbr_map_eq
          simp [] at this
          rw [list_flatMap_map_collectCalleesBlock, list_flatMap_map_collectCalleesBlock] at this
          exact this
        have hlist_len : br1.toList.length = br2.toList.length := by simp [hbr_size]
        have hlist_pt : ∀ i (h1 : i < br1.toList.length) (h2 : i < br2.toList.length),
            br1.toList[i].1 = br2.toList[i].1 ∧
            skeletonBlock br1.toList[i].2 = skeletonBlock br2.toList[i].2 := by
          intro i h1 h2
          have h1' : i < br1.size := by simpa using h1
          have h2' : i < br2.size := by simpa using h2
          have := hbr_pt i h1' h2'
          simp only [Array.getElem_toList]
          exact this
        have hm1 : ∀ p ∈ br1.toList, sizeOf p.2 < sizeOf br1 := by
          rintro ⟨g, b⟩ hp
          have hmem : (g, b) ∈ br1 := Array.mem_toList_iff.mp hp
          have h1 := Array.sizeOf_lt_of_mem hmem
          have h2 := Prod.mk.sizeOf_spec g b
          show sizeOf b < sizeOf br1
          omega
        have hm2 : ∀ p ∈ br2.toList, sizeOf p.2 < sizeOf br2 := by
          rintro ⟨g, b⟩ hp
          have hmem : (g, b) ∈ br2 := Array.mem_toList_iff.mp hp
          have h1 := Array.sizeOf_lt_of_mem hmem
          have h2 := Prod.mk.sizeOf_spec g b
          show sizeOf b < sizeOf br2
          omega
        have hlist_rewrite_eq :
            br1.toList.map (fun p => (p.1, rewriteBlock f p.2)) =
            br2.toList.map (fun p => (p.1, rewriteBlock f p.2)) := by
          suffices aux : ∀ (l1 : List (G × Block))
              (hm1 : ∀ p ∈ l1, sizeOf p.2 < sizeOf br1)
              (l2 : List (G × Block))
              (hm2 : ∀ p ∈ l2, sizeOf p.2 < sizeOf br2),
              l1.length = l2.length →
              (∀ i (h1 : i < l1.length) (h2 : i < l2.length),
                l1[i].1 = l2[i].1 ∧ skeletonBlock l1[i].2 = skeletonBlock l2[i].2) →
              (l1.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) =
                (l2.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) →
              l1.map (fun p => (p.1, rewriteBlock f p.2)) =
                l2.map (fun p => (p.1, rewriteBlock f p.2)) by
            exact aux br1.toList hm1 br2.toList hm2 hlist_len hlist_pt hbr_flatMap_map
          intro l1
          induction l1 with
          | nil =>
            intro _ l2 _ hlen _ _
            cases l2 with
            | nil => rfl
            | cons _ _ => simp at hlen
          | cons p1 rest1 ih =>
            intro hm1 l2 hm2 hlen hpt hcs_list
            cases l2 with
            | nil => simp at hlen
            | cons p2 rest2 =>
              simp only [List.map_cons, List.cons.injEq]
              have hhead := hpt 0 (by simp) (by simp)
              have hhd_g : p1.1 = p2.1 := by simpa using hhead.1
              have hhd_sk : skeletonBlock p1.2 = skeletonBlock p2.2 := by simpa using hhead.2
              have _hsz1 : sizeOf p1.2 < sizeOf br1 := hm1 p1 List.mem_cons_self
              have _hsz2 : sizeOf p2.2 < sizeOf br2 := hm2 p2 List.mem_cons_self
              simp only [List.flatMap_cons] at hcs_list
              have hsz_head : (collectCalleesBlock p1.2).size =
                  (collectCalleesBlock p2.2).size :=
                collectCalleesBlock_size_eq_of_skeleton_eq p1.2 p2.2 hhd_sk
              have hlen_head_map : ((collectCalleesBlock p1.2).map f).toList.length =
                  ((collectCalleesBlock p2.2).map f).toList.length := by
                simp [Array.length_toList, hsz_head]
              have ⟨hhd_cs, htl_cs⟩ := List.append_inj hcs_list hlen_head_map
              have hhd_cs_arr : (collectCalleesBlock p1.2).map f =
                  (collectCalleesBlock p2.2).map f := by
                have : ((collectCalleesBlock p1.2).map f).toList =
                    ((collectCalleesBlock p2.2).map f).toList := hhd_cs
                exact Array.toList_inj.mp this
              have hblock_eq : rewriteBlock f p1.2 = rewriteBlock f p2.2 :=
                rewriteBlock_eq_of_skeleton_and_callees_aux f p1.2 p2.2 hhd_sk hhd_cs_arr
              refine ⟨?_, ?_⟩
              · exact Prod.ext hhd_g hblock_eq
              · have hlen' : rest1.length = rest2.length := by simp at hlen; exact hlen
                have hpt' : ∀ i (h1 : i < rest1.length) (h2 : i < rest2.length),
                    rest1[i].1 = rest2[i].1 ∧
                    skeletonBlock rest1[i].2 = skeletonBlock rest2[i].2 := by
                  intro i h1 h2
                  have := hpt (i+1) (by simp; omega) (by simp; omega)
                  simpa using this
                have hm1' : ∀ p ∈ rest1, sizeOf p.2 < sizeOf br1 :=
                  fun p hp => hm1 p (List.mem_cons.mpr (Or.inr hp))
                have hm2' : ∀ p ∈ rest2, sizeOf p.2 < sizeOf br2 :=
                  fun p hp => hm2 p (List.mem_cons.mpr (Or.inr hp))
                exact ih hm1' rest2 hm2' hlen' hpt' htl_cs
        have hbr_attach_map_eq :
            br1.attach.map (fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)) =
            br2.attach.map (fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)) := by
          rw [branches_attach_map_rewrite_eq_map, branches_attach_map_rewrite_eq_map]
          apply Array.toList_inj.mp
          rw [Array.toList_map, Array.toList_map]
          exact hlist_rewrite_eq
        cases d1 with
        | none =>
          cases d2 with
          | none =>
            show rewriteCtrl f (Ctrl.match v1 br1 none) =
              rewriteCtrl f (Ctrl.match v1 br2 none)
            simp only [rewriteCtrl]
            rw [hbr_attach_map_eq]
          | some b2 => simp at hd
        | some b1 =>
          cases d2 with
          | none => simp at hd
          | some b2 =>
            show rewriteCtrl f (Ctrl.match v1 br1 (some b1)) =
              rewriteCtrl f (Ctrl.match v1 br2 (some b2))
            simp only [rewriteCtrl]
            rw [hbr_attach_map_eq]
            simp only at hd
            injection hd with hd_sk
            exact congrArg _ (congrArg _
              (rewriteBlock_eq_of_skeleton_and_callees_aux f b1 b2 hd_sk hd_map_eq))
      | _ =>
        unfold skeletonCtrl at hsk
        exact Ctrl.noConfusion hsk
    | matchContinue v1 br1 d1 os1 sa1 sl1 cont1 =>
      cases c2 with
      | matchContinue v2 br2 d2 os2 sa2 sl2 cont2 =>
        unfold skeletonCtrl at hsk
        injection hsk with hv hbr hd hos hsa hsl hcont
        cases hv; cases hos; cases hsa; cases hsl
        have hbr_size : br1.size = br2.size := branches_callees_size_eq_of_skeleton_eq _ _ hbr
        have hbr_pt : ∀ i (h1 : i < br1.size) (h2 : i < br2.size),
            br1[i].1 = br2[i].1 ∧ skeletonBlock br1[i].2 = skeletonBlock br2[i].2 := by
          intro i h1 h2
          have hfun := congrFun (congrArg (fun arr => fun i => arr[i]?) hbr) i
          simp [h1, h2, Array.getElem_attach] at hfun
          exact hfun
        unfold collectCalleesCtrl at hcs
        simp only at hcs
        have hcont_size := collectCalleesBlock_size_eq_of_skeleton_eq cont1 cont2 hcont
        have hbr_foldl_size :
            (br1.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size =
            (br2.attach.foldl (init := #[]) (fun acc ⟨(_, b), _⟩ =>
              acc ++ collectCalleesBlock b)).size := by
          have hsk_match_none :
              skeletonCtrl (Ctrl.match v1 br1 (none : Option Block)) =
              skeletonCtrl (Ctrl.match v1 br2 (none : Option Block)) := by
            unfold skeletonCtrl; rw [hbr]
          have := collectCalleesCtrl_size_eq_of_skeleton_eq
            (Ctrl.match v1 br1 (none : Option Block))
            (Ctrl.match v1 br2 (none : Option Block)) hsk_match_none
          unfold collectCalleesCtrl at this
          simpa using this
        let brFold1 : Array FunIdx := br1.attach.foldl (init := #[])
          (fun acc (x : {x // x ∈ br1}) =>
            match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b)
        let brFold2 : Array FunIdx := br2.attach.foldl (init := #[])
          (fun acc (x : {x // x ∈ br2}) =>
            match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b)
        have hwd_size :
            (match d1 with
              | none => brFold1
              | some b => brFold1 ++ collectCalleesBlock b).size =
            (match d2 with
              | none => brFold2
              | some b => brFold2 ++ collectCalleesBlock b).size := by
          cases d1 with
          | none =>
            cases d2 with
            | none => exact hbr_foldl_size
            | some b2 => simp at hd
          | some b1 =>
            cases d2 with
            | none => simp at hd
            | some b2 =>
              simp only at hd
              injection hd with hd_sk
              simp only [Array.size_append]
              rw [hbr_foldl_size,
                  collectCalleesBlock_size_eq_of_skeleton_eq b1 b2 hd_sk]
        rw [Array.map_append, Array.map_append] at hcs
        have hwd_map_size :
            ((match d1 with
              | none => brFold1
              | some b => brFold1 ++ collectCalleesBlock b).map f).size =
            ((match d2 with
              | none => brFold2
              | some b => brFold2 ++ collectCalleesBlock b).map f).size := by
          simp [hwd_size]
        have ⟨hwd_map_eq, hcont_map_eq⟩ := Array.append_inj hcs hwd_map_size
        have hbr_callees : brFold1.map f = brFold2.map f ∧
          (match d1 with
            | none => (#[] : Array FunIdx)
            | some b => collectCalleesBlock b).map f =
          (match d2 with
            | none => (#[] : Array FunIdx)
            | some b => collectCalleesBlock b).map f := by
          have hsize_map : (brFold1.map f).size = (brFold2.map f).size := by
            simp only [Array.size_map]; exact hbr_foldl_size
          cases d1 with
          | none =>
            cases d2 with
            | none => refine ⟨hwd_map_eq, ?_⟩; simp
            | some b2 => simp at hd
          | some b1 =>
            cases d2 with
            | none => simp at hd
            | some b2 =>
              simp only at hwd_map_eq
              rw [Array.map_append, Array.map_append] at hwd_map_eq
              exact Array.append_inj hwd_map_eq hsize_map
        obtain ⟨hbr_map_eq, hd_map_eq⟩ := hbr_callees
        have hbr_flatMap_map :
            (br1.toList.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) =
            (br2.toList.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) := by
          have h1 : brFold1 =
              (br1.toList.flatMap (fun p => (collectCalleesBlock p.2).toList)).toArray := by
            change br1.attach.foldl (init := #[])
              (fun acc (x : {x // x ∈ br1}) =>
                match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b) = _
            rw [attach_foldl_collectCalleesBlock_eq]
            have := list_foldl_collectCalleesBlock_eq_flatMap br1.toList #[]
            simpa using this
          have h2 : brFold2 =
              (br2.toList.flatMap (fun p => (collectCalleesBlock p.2).toList)).toArray := by
            change br2.attach.foldl (init := #[])
              (fun acc (x : {x // x ∈ br2}) =>
                match x with | ⟨(_, b), _⟩ => acc ++ collectCalleesBlock b) = _
            rw [attach_foldl_collectCalleesBlock_eq]
            have := list_foldl_collectCalleesBlock_eq_flatMap br2.toList #[]
            simpa using this
          rw [h1, h2] at hbr_map_eq
          have := congrArg Array.toList hbr_map_eq
          simp [] at this
          rw [list_flatMap_map_collectCalleesBlock, list_flatMap_map_collectCalleesBlock] at this
          exact this
        have hlist_len : br1.toList.length = br2.toList.length := by simp [hbr_size]
        have hlist_pt : ∀ i (h1 : i < br1.toList.length) (h2 : i < br2.toList.length),
            br1.toList[i].1 = br2.toList[i].1 ∧
            skeletonBlock br1.toList[i].2 = skeletonBlock br2.toList[i].2 := by
          intro i h1 h2
          have h1' : i < br1.size := by simpa using h1
          have h2' : i < br2.size := by simpa using h2
          have := hbr_pt i h1' h2'
          simp only [Array.getElem_toList]
          exact this
        have hm1 : ∀ p ∈ br1.toList, sizeOf p.2 < sizeOf br1 := by
          rintro ⟨g, b⟩ hp
          have hmem : (g, b) ∈ br1 := Array.mem_toList_iff.mp hp
          have h1 := Array.sizeOf_lt_of_mem hmem
          have h2 := Prod.mk.sizeOf_spec g b
          show sizeOf b < sizeOf br1
          omega
        have hm2 : ∀ p ∈ br2.toList, sizeOf p.2 < sizeOf br2 := by
          rintro ⟨g, b⟩ hp
          have hmem : (g, b) ∈ br2 := Array.mem_toList_iff.mp hp
          have h1 := Array.sizeOf_lt_of_mem hmem
          have h2 := Prod.mk.sizeOf_spec g b
          show sizeOf b < sizeOf br2
          omega
        have hlist_rewrite_eq :
            br1.toList.map (fun p => (p.1, rewriteBlock f p.2)) =
            br2.toList.map (fun p => (p.1, rewriteBlock f p.2)) := by
          suffices aux : ∀ (l1 : List (G × Block))
              (hm1 : ∀ p ∈ l1, sizeOf p.2 < sizeOf br1)
              (l2 : List (G × Block))
              (hm2 : ∀ p ∈ l2, sizeOf p.2 < sizeOf br2),
              l1.length = l2.length →
              (∀ i (h1 : i < l1.length) (h2 : i < l2.length),
                l1[i].1 = l2[i].1 ∧ skeletonBlock l1[i].2 = skeletonBlock l2[i].2) →
              (l1.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) =
                (l2.flatMap (fun p => ((collectCalleesBlock p.2).map f).toList)) →
              l1.map (fun p => (p.1, rewriteBlock f p.2)) =
                l2.map (fun p => (p.1, rewriteBlock f p.2)) by
            exact aux br1.toList hm1 br2.toList hm2 hlist_len hlist_pt hbr_flatMap_map
          intro l1
          induction l1 with
          | nil =>
            intro _ l2 _ hlen _ _
            cases l2 with
            | nil => rfl
            | cons _ _ => simp at hlen
          | cons p1 rest1 ih =>
            intro hm1 l2 hm2 hlen hpt hcs_list
            cases l2 with
            | nil => simp at hlen
            | cons p2 rest2 =>
              simp only [List.map_cons, List.cons.injEq]
              have hhead := hpt 0 (by simp) (by simp)
              have hhd_g : p1.1 = p2.1 := by simpa using hhead.1
              have hhd_sk : skeletonBlock p1.2 = skeletonBlock p2.2 := by simpa using hhead.2
              have _hsz1 : sizeOf p1.2 < sizeOf br1 := hm1 p1 List.mem_cons_self
              have _hsz2 : sizeOf p2.2 < sizeOf br2 := hm2 p2 List.mem_cons_self
              simp only [List.flatMap_cons] at hcs_list
              have hsz_head : (collectCalleesBlock p1.2).size =
                  (collectCalleesBlock p2.2).size :=
                collectCalleesBlock_size_eq_of_skeleton_eq p1.2 p2.2 hhd_sk
              have hlen_head_map : ((collectCalleesBlock p1.2).map f).toList.length =
                  ((collectCalleesBlock p2.2).map f).toList.length := by
                simp [Array.length_toList, hsz_head]
              have ⟨hhd_cs, htl_cs⟩ := List.append_inj hcs_list hlen_head_map
              have hhd_cs_arr : (collectCalleesBlock p1.2).map f =
                  (collectCalleesBlock p2.2).map f := by
                have : ((collectCalleesBlock p1.2).map f).toList =
                    ((collectCalleesBlock p2.2).map f).toList := hhd_cs
                exact Array.toList_inj.mp this
              have hblock_eq : rewriteBlock f p1.2 = rewriteBlock f p2.2 :=
                rewriteBlock_eq_of_skeleton_and_callees_aux f p1.2 p2.2 hhd_sk hhd_cs_arr
              have hhd_pair : (p1.1, rewriteBlock f p1.2) = (p2.1, rewriteBlock f p2.2) := by
                rw [hhd_g, hblock_eq]
              refine ⟨?_, ?_⟩
              · exact hhd_pair
              · have hlen' : rest1.length = rest2.length := by simp at hlen; exact hlen
                have hpt' : ∀ i (h1 : i < rest1.length) (h2 : i < rest2.length),
                    rest1[i].1 = rest2[i].1 ∧
                    skeletonBlock rest1[i].2 = skeletonBlock rest2[i].2 := by
                  intro i h1 h2
                  have := hpt (i+1) (by simp; omega) (by simp; omega)
                  simpa using this
                have hm1' : ∀ p ∈ rest1, sizeOf p.2 < sizeOf br1 :=
                  fun p hp => hm1 p (List.mem_cons.mpr (Or.inr hp))
                have hm2' : ∀ p ∈ rest2, sizeOf p.2 < sizeOf br2 :=
                  fun p hp => hm2 p (List.mem_cons.mpr (Or.inr hp))
                exact ih hm1' rest2 hm2' hlen' hpt' htl_cs
        have hbr_attach_map_eq :
            br1.attach.map (fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)) =
            br2.attach.map (fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)) := by
          rw [branches_attach_map_rewrite_eq_map, branches_attach_map_rewrite_eq_map]
          apply Array.toList_inj.mp
          rw [Array.toList_map, Array.toList_map]
          exact hlist_rewrite_eq
        have hcont_eq : rewriteBlock f cont1 = rewriteBlock f cont2 :=
          rewriteBlock_eq_of_skeleton_and_callees_aux f cont1 cont2 hcont hcont_map_eq
        cases d1 with
        | none =>
          cases d2 with
          | none =>
            show rewriteCtrl f (Ctrl.matchContinue v1 br1 none os1 sa1 sl1 cont1) =
              rewriteCtrl f (Ctrl.matchContinue v1 br2 none os1 sa1 sl1 cont2)
            simp only [rewriteCtrl]
            rw [hbr_attach_map_eq, hcont_eq]
          | some b2 => simp at hd
        | some b1 =>
          cases d2 with
          | none => simp at hd
          | some b2 =>
            show rewriteCtrl f (Ctrl.matchContinue v1 br1 (some b1) os1 sa1 sl1 cont1) =
              rewriteCtrl f (Ctrl.matchContinue v1 br2 (some b2) os1 sa1 sl1 cont2)
            simp only [rewriteCtrl]
            rw [hbr_attach_map_eq, hcont_eq]
            simp only at hd
            injection hd with hd_sk
            have hb_eq : rewriteBlock f b1 = rewriteBlock f b2 :=
              rewriteBlock_eq_of_skeleton_and_callees_aux f b1 b2 hd_sk hd_map_eq
            rw [hb_eq]
      | _ =>
        unfold skeletonCtrl at hsk
        exact Ctrl.noConfusion hsk
  termination_by (sizeOf c1, 0)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left
         have _h := ‹sizeOf _ < sizeOf _›
         grind)
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

  private theorem rewriteBlock_eq_of_skeleton_and_callees_aux
      (f : FunIdx → FunIdx) (b1 b2 : Block)
      (hsk : skeletonBlock b1 = skeletonBlock b2)
      (hcs : (collectCalleesBlock b1).map f = (collectCalleesBlock b2).map f) :
      rewriteBlock f b1 = rewriteBlock f b2 := by
    have hsk_full : (⟨b1.ops.map skeletonOp, skeletonCtrl b1.ctrl⟩ : Block) =
        ⟨b2.ops.map skeletonOp, skeletonCtrl b2.ctrl⟩ := by
      have h1 : skeletonBlock b1 = ⟨b1.ops.map skeletonOp, skeletonCtrl b1.ctrl⟩ := by
        unfold skeletonBlock; rfl
      have h2 : skeletonBlock b2 = ⟨b2.ops.map skeletonOp, skeletonCtrl b2.ctrl⟩ := by
        unfold skeletonBlock; rfl
      rw [← h1, ← h2]; exact hsk
    injection hsk_full with hsk_ops hsk_ctrl
    have hcs_full : (b1.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
        collectCalleesCtrl b1.ctrl).map f =
        (b2.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
          collectCalleesCtrl b2.ctrl).map f := by
      have h1 : collectCalleesBlock b1 =
          b1.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
            collectCalleesCtrl b1.ctrl := by unfold collectCalleesBlock; rfl
      have h2 : collectCalleesBlock b2 =
          b2.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op) ++
            collectCalleesCtrl b2.ctrl := by unfold collectCalleesBlock; rfl
      rw [← h1, ← h2]; exact hcs
    rw [Array.map_append, Array.map_append] at hcs_full
    have hop_sizes := ops_foldl_callees_size_eq b1.ops b2.ops hsk_ops
    have hop_map_size :
        ((b1.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).map f).size =
        ((b2.ops.foldl (init := #[]) (fun acc op => acc ++ collectCalleesOp op)).map f).size := by
      simp only [Array.size_map]; exact hop_sizes
    have ⟨hops_eq, hctrl_eq⟩ := Array.append_inj hcs_full hop_map_size
    have hops_rewrite := array_rewriteOp_eq_of_skeleton_and_callees f b1.ops b2.ops hsk_ops hops_eq
    have hctrl_rewrite := rewriteCtrl_eq_of_skeleton_and_callees f b1.ctrl b2.ctrl hsk_ctrl hctrl_eq
    unfold rewriteBlock
    congr
  termination_by (sizeOf b1, 1)
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (apply Prod.Lex.left; exact Block.sizeOf_ctrl_lt' _)
end

/-- Composition (1)+(2)+(3): rewritten same-class bodies are syntactically equal. -/
private theorem rewriteBlock_eq_of_same_class
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (_tDedup, remap) := t.deduplicate
    ∀ i j (hi : i < t.functions.size) (hj : j < t.functions.size),
      remap i = remap j →
      rewriteBlock remap t.functions[i].body =
        rewriteBlock remap t.functions[j].body := by
  intro i j hi hj hremap
  have hsk := skeleton_eq_of_same_class t hfix i j hi hj hremap
  have hcs := callees_remap_eq_of_same_class t hwf hfix i j hi hj hremap
  simp only at hsk hcs
  exact rewriteBlock_eq_of_skeleton_and_callees_aux _ _ _ hsk.1 hcs

/-- Same-class function bodies produce observationally equal `evalBlock`
computations under `rewriteBlock remap`. Crux of dedup soundness: at fixpoint,
same-class bodies become SYNTACTICALLY equal after rewrite, so the whole
`evalBlock` equality reduces to `rw` on the body equality.

HYPOTHESES:
- `_hwf`: no out-of-range callees — prevents `classes[·]!`'s silent 0-default
  from collapsing distinct dangling references into same signature.
- `_hfix`: partitionRefine reached fixpoint (bound sufficed). Separately
  provable from increasing-class-count monotonicity. -/
private theorem partitionRefine_same_class_eval
    (t : Toplevel)
    (_hwf : WellFormedCallees t)
    (_hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
             let (initClasses, _) := assignClasses skeletons
             let callees := t.functions.map fun f => collectCalleesBlock f.body
             let classes := partitionRefine initClasses callees
             let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
             (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    ∀ i j (hi : i < t.functions.size) (hj : j < t.functions.size),
      remap i = remap j →
      ∀ fuel st,
        Eval.evalBlock tDedup fuel (rewriteBlock remap t.functions[i].body) st =
          Eval.evalBlock tDedup fuel (rewriteBlock remap t.functions[j].body) st := by
  intro i j hi hj hremap fuel st
  have hrw := rewriteBlock_eq_of_same_class t _hwf _hfix i j hi hj hremap
  simp only at hrw
  rw [hrw]

/-
`needsCircuit` irrelevance: `Bytecode.Eval.runFunction` does not read
`Bytecode.Function.constrained`, so overwriting the field (as the final step
of `Source.Toplevel.compile` does via `needsCircuit` + `mapIdx`) does not
change the evaluator's output. Used by top-level preservation to discharge the
`needsCircuit` step when composing the pipeline preservation proof.
-/

/-- Helper: `mapIdx` preserves functions.size. -/
private theorem functions_size_mapIdx (t : Bytecode.Toplevel)
    (f : Nat → Bytecode.Function → Bytecode.Function) :
    ({ t with functions := t.functions.mapIdx f } : Bytecode.Toplevel).functions.size =
      t.functions.size := by
  simp [Array.size_mapIdx]

/-- Helper: `mapIdx` with a field-only transformation preserves body/layout. -/
private theorem functions_body_layout_mapIdx
    (t : Bytecode.Toplevel) (flags : Array Bool)
    (i : Nat) (h : i < t.functions.size) :
    let t' : Bytecode.Toplevel :=
      { t with functions := t.functions.mapIdx fun i f =>
          { f with constrained := flags[i]! } }
    have h' : i < t'.functions.size := by
      rw [functions_size_mapIdx]; exact h
    t'.functions[i].body = t.functions[i].body ∧
    t'.functions[i].layout = t.functions[i].layout := by
  simp [Array.getElem_mapIdx]

/-- Mutual congruence: `evalOp`/`runOps`/`evalBlock`/`evalCtrl`/`evalMatchArm`/
`evalDefaultBlock` all agree between `t` and `t'` when `t'` is a mapIdx with
constrained-only transformation.

The proof uses `evalOp.mutual_induct` with 6 motives stating equality between
evaluation under `t` and `t'`. For non-`.call` ops and leaf ctrls, both sides
compute identical outputs without consulting `t.functions`, so the equality is
pure structural congruence. For `.call`, `functions_body_layout_mapIdx` shows
the looked-up function has identical `body` and `layout`; the recursive
`evalBlock` at the inner fuel is handled by the IH embedded in the induction
principle via the `match fuel with | 0 => True | succ => motive2` clause. -/
private theorem eval_congr_constrained
    (t : Bytecode.Toplevel) (flags : Array Bool) :
    let t' : Bytecode.Toplevel :=
      { t with functions := t.functions.mapIdx fun i f =>
          { f with constrained := flags[i]! } }
    (∀ fuel op st,
      Bytecode.Eval.evalOp t fuel op st = Bytecode.Eval.evalOp t' fuel op st)
    ∧ (∀ fuel b st,
      Bytecode.Eval.evalBlock t fuel b st = Bytecode.Eval.evalBlock t' fuel b st)
    ∧ (∀ fuel c st,
      Bytecode.Eval.evalCtrl t fuel c st = Bytecode.Eval.evalCtrl t' fuel c st) := by
  intro t'
  have hsize : t'.functions.size = t.functions.size :=
    functions_size_mapIdx t (fun i f => { f with constrained := flags[i]! })
  have hbl : ∀ i (h : i < t.functions.size),
      (t'.functions[i]'(hsize ▸ h)).body = t.functions[i].body ∧
      (t'.functions[i]'(hsize ▸ h)).layout = t.functions[i].layout := by
    intro i h
    exact functions_body_layout_mapIdx t flags i h
  -- Apply `evalOp.mutual_induct` with 6 motives stating equality.
  have big :=
    @Bytecode.Eval.evalOp.mutual_induct t
      (fun fuel op st => Bytecode.Eval.evalOp t fuel op st = Bytecode.Eval.evalOp t' fuel op st)
      (fun fuel b st => Bytecode.Eval.evalBlock t fuel b st = Bytecode.Eval.evalBlock t' fuel b st)
      (fun fuel c st => Bytecode.Eval.evalCtrl t fuel c st = Bytecode.Eval.evalCtrl t' fuel c st)
      (fun fuel cases db scrut st i =>
        Bytecode.Eval.evalMatchArm t fuel cases db scrut st i =
        Bytecode.Eval.evalMatchArm t' fuel cases db scrut st i)
      (fun fuel db st =>
        Bytecode.Eval.evalDefaultBlock t fuel db st =
        Bytecode.Eval.evalDefaultBlock t' fuel db st)
      (fun fuel ops st i =>
        Bytecode.Eval.runOps t fuel ops st i = Bytecode.Eval.runOps t' fuel ops st i)
  -- Supply the ~43 cases. Most are trivial `rfl`/unfold because the
  -- non-`.call` evaluator arms do not consult `t.functions`.
  -- Helper tactic: unfold both sides of evalOp for trivial ops.
  have triv : ∀ (fuel : Nat) (st : Bytecode.Eval.EvalState) (op : Bytecode.Op),
      (∀ (h_not_call : ∀ fi args outSz uc, op ≠ Bytecode.Op.call fi args outSz uc),
        Bytecode.Eval.evalOp t fuel op st = Bytecode.Eval.evalOp t' fuel op st) := by
    intro fuel st op h
    unfold Bytecode.Eval.evalOp
    cases op with
    | call fi args outSz uc => exact absurd rfl (h fi args outSz uc)
    | _ => rfl
  have P := big
    -- Op cases: all non-call are rfl after unfolding.
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    -- Op.call case
    (fun fuel st fi args outSz uc ih => by
      show Bytecode.Eval.evalOp t fuel (.call fi args outSz uc) st =
           Bytecode.Eval.evalOp t' fuel (.call fi args outSz uc) st
      cases fuel with
      | zero =>
        unfold Bytecode.Eval.evalOp
        simp only
        cases hreadArgs : Bytecode.Eval.readIdxs st args with
        | error e => simp only [bind, Except.bind]
        | ok argGs =>
          simp only [bind, Except.bind]
          by_cases hfi : fi < t.functions.size
          · have hfi' : fi < t'.functions.size := by rw [hsize]; exact hfi
            have ⟨_, hlayout⟩ := hbl fi hfi
            simp only [hfi, hfi', ↓reduceDIte]
            rw [hlayout]
          · have hfi' : ¬ fi < t'.functions.size := by rw [hsize]; exact hfi
            simp only [hfi, hfi', ↓reduceDIte]
      | succ fuel' =>
        unfold Bytecode.Eval.evalOp
        simp only
        cases hreadArgs : Bytecode.Eval.readIdxs st args with
        | error e => simp only [bind, Except.bind]
        | ok argGs =>
          simp only [bind, Except.bind]
          by_cases hfi : fi < t.functions.size
          · have hfi' : fi < t'.functions.size := by rw [hsize]; exact hfi
            have ⟨hbody, hlayout⟩ := hbl fi hfi
            simp only [hfi, hfi', ↓reduceDIte]
            rw [hbody, hlayout]
            split
            · rfl
            · have ihb := ih argGs hfi
              simp only at ihb
              rw [ihb]
          · have hfi' : ¬ fi < t'.functions.size := by rw [hsize]; exact hfi
            simp only [hfi, hfi', ↓reduceDIte])
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    (fun _ _ _ _ => by unfold Bytecode.Eval.evalOp; rfl)
    -- Block cases
    (fun fuel b st e herr ih_ops => by
      unfold Bytecode.Eval.evalBlock
      rw [← ih_ops, herr])
    (fun fuel b st st' hok ih_ops ih_ctrl => by
      unfold Bytecode.Eval.evalBlock
      rw [← ih_ops, hok]
      exact ih_ctrl)
    -- Ctrl cases
    (fun _ _ _ _ _ herr => by unfold Bytecode.Eval.evalCtrl; rw [herr])
    (fun _ _ _ _ _ hok => by unfold Bytecode.Eval.evalCtrl; rw [hok])
    (fun _ _ _ _ _ herr => by unfold Bytecode.Eval.evalCtrl; rw [herr])
    (fun _ _ _ _ _ hok => by unfold Bytecode.Eval.evalCtrl; rw [hok])
    (fun _ _ _ _ _ _ herr => by unfold Bytecode.Eval.evalCtrl; rw [herr])
    (fun _ _ _ _ _ _ hok ih_arm => by
      unfold Bytecode.Eval.evalCtrl
      simp only [hok]; exact ih_arm)
    (fun _ _ _ _ _ _ _ _ _ _ herr => by
      unfold Bytecode.Eval.evalCtrl; rw [herr])
    (fun _ _ _ _ _ _ _ _ _ _ hok _ harm ih_arm => by
      unfold Bytecode.Eval.evalCtrl
      simp only [hok, harm, ← ih_arm])
    (fun _ _ _ _ _ _ _ _ _ _ hok _ _ harm ih_arm ih_block => by
      unfold Bytecode.Eval.evalCtrl
      simp only [hok, harm, ← ih_arm]
      exact ih_block)
    -- MatchArm cases
    -- hit: (cases[i].fst == scrut) = true → motive4 via motive2
    (fun _ _ _ _ _ _ hlt heq ih_hit => by
      unfold Bytecode.Eval.evalMatchArm
      simp only [hlt, heq, ↓reduceIte, ↓reduceDIte]
      exact ih_hit)
    -- miss: ¬ (cases[i].fst == scrut) → motive4 via recursion
    (fun _ _ _ _ _ _ hlt hne ih_rec => by
      unfold Bytecode.Eval.evalMatchArm
      simp only [hlt, hne, ↓reduceDIte]
      exact ih_rec)
    -- oob: ¬ i < cases.size → motive4 via defaultBlock
    (fun _ _ _ _ _ _ hnot ih_def => by
      unfold Bytecode.Eval.evalMatchArm
      simp only [hnot, ↓reduceDIte]
      exact ih_def)
    -- DefaultBlock cases
    (fun fuel st block ih_block => by
      unfold Bytecode.Eval.evalDefaultBlock
      exact ih_block)
    (fun fuel st => by
      unfold Bytecode.Eval.evalDefaultBlock; rfl)
    -- runOps cases
    (fun _ _ _ _ h _ herr ih_op => by
      unfold Bytecode.Eval.runOps
      simp only [h, ↓reduceDIte]
      -- ih_op : evalOp t fuel ops[i] st = evalOp t' fuel ops[i] st
      -- herr  : evalOp t fuel ops[i] st = .error e
      have herr' : Bytecode.Eval.evalOp _ _ _ _ = _ := ih_op ▸ herr
      simp only [herr, herr'])
    (fun _ _ _ _ h _ hok ih_op ih_rest => by
      unfold Bytecode.Eval.runOps
      simp only [h, ↓reduceDIte]
      have hok' : Bytecode.Eval.evalOp _ _ _ _ = _ := ih_op ▸ hok
      simp only [hok, hok']
      exact ih_rest)
    (fun _ _ _ _ hnot => by
      unfold Bytecode.Eval.runOps
      simp only [hnot, ↓reduceDIte])
  exact ⟨P.1, P.2.1, P.2.2.1⟩

theorem Bytecode.Eval.runFunction_constrained_irrelevant
    (t : Bytecode.Toplevel) (flags : Array Bool) (funIdx : FunIdx)
    (args : Array G) (io : IOBuffer) (fuel : Nat) :
    Bytecode.Eval.runFunction t funIdx args io fuel =
      Bytecode.Eval.runFunction
        { t with functions := t.functions.mapIdx fun i f =>
            { f with constrained := flags[i]! } }
        funIdx args io fuel := by
  unfold Bytecode.Eval.runFunction
  -- Size equality: both sides use .functions.size, which mapIdx preserves.
  have hsize := functions_size_mapIdx t (fun i f => { f with constrained := flags[i]! })
  -- Body/layout equality at funIdx.
  by_cases h : funIdx < t.functions.size
  · have h' : funIdx < ({ t with functions := t.functions.mapIdx fun i f =>
        { f with constrained := flags[i]! } } : Bytecode.Toplevel).functions.size := by
      rw [hsize]; exact h
    simp only [h, h', ↓reduceDIte]
    have ⟨hbody, hlayout⟩ := functions_body_layout_mapIdx t flags funIdx h
    rw [hbody, hlayout]
    -- Both sides now have the same arity-check condition and same body.
    split
    · rfl  -- arity mismatch branch
    · -- evalBlock branch: use mutual congruence.
      have ⟨_, hBlock, _⟩ := eval_congr_constrained t flags
      rw [hBlock]
  · have h' : ¬ (funIdx < ({ t with functions := t.functions.mapIdx fun i f =>
        { f with constrained := flags[i]! } } : Bytecode.Toplevel).functions.size) := by
      rw [hsize]; exact h
    simp only [h, h', ↓reduceDIte]

/-! ## Post-conditions of `Bytecode.Toplevel.deduplicate` (sorried).

The two top-level theorems project from three local sorry-stubs capturing
upstream `Toplevel.deduplicate` invariants. Supporting these are the
`partitionRefine`/`assignClasses` output lemmas below, which capture the
bounded-output property of those recursive helpers. -/

/- The `partitionRefine` / `assignClasses` structural invariants
(`partitionRefine_size_eq`, `partitionRefine_classes_bounded`,
`assignClasses_size_eq`, `assignClasses_classes_lt_nextId`) now live in
`Ix/Aiur/Compiler/Dedup.lean` next to the definitions they constrain. -/

/-! ## Joint post-condition of `Toplevel.deduplicate`.

Decomposed into three sub-lemmas. Post-refactor (dedup now uses pure folds),
`deduplicate_remap_eq_classes` closes by `simp` on the pure definitions. The
other two still require fold-induction on `deduplicate_canonical` /
`deduplicate_newFunctions` but no longer blocked on imperative loops. -/

@[expose]
def deduplicate_classes_of
    (t : Toplevel) : Array Nat :=
  if t.functions.size == 0 then #[]
  else
    let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
    let (initClasses, _) := assignClasses skeletons
    let callees := t.functions.map fun f => collectCalleesBlock f.body
    partitionRefine initClasses callees

/-! ### Canonical-count bound for `partitionRefine` outputs.

Strategy: define `IsAssignClassesOutput c n` to mean "c arose as the first
component of an `assignClasses` call returning `n` as the second component".
Two key facts:
1. Every `assignClasses values` call returns a pair satisfying this predicate
   with `n = (assignClasses values).2`.
2. For any `c` satisfying this predicate, `(deduplicate_canonical c).2 = n`
   (the foldls simulate each other: `top_cls` in `deduplicate_canonical` stays
   in lock-step with `nextId` in `assignClasses`).

Combined with `assignClasses_classes_lt_nextId`, every `c[i] < n`, so
`c[i] < (deduplicate_canonical c).2`.

For `partitionRefine`, the output is always either the input `initClasses`
(itself an `assignClasses` output) or a later `assignClasses` output, so the
bound transfers directly. -/

/-- The induced predicate over arbitrary `Array Nat`s — used to chain through
`partitionRefine`. -/
private def CanonicalCountBound (c : Array Nat) : Prop :=
  ∀ i (h : i < c.size), c[i] < (deduplicate_canonical c).2

/-- The `deduplicate_canonical`'s foldl tracks `top_cls = nextId` when applied
to an `assignClasses` output. We prove this via a strong combined invariant
on `assignClasses`'s foldl. -/
private theorem assignClasses_canonical_top_eq
    {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (values : Array α) :
    (deduplicate_canonical (assignClasses values).1).2 = (assignClasses values).2 := by
  -- Establish the invariant on the inner foldl, then project.
  have inner :
      let r := values.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      (∀ k (hk : k < r.1.size), r.1[k] < r.2.2) ∧
      (∀ (v : α) id, r.2.1[v]? = some id → id < r.2.2) ∧
      (deduplicate_canonical r.1).2 = r.2.2 := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (s : Array Nat × Std.HashMap α Nat × Nat) =>
        (∀ k (hk : k < s.1.size), s.1[k] < s.2.2) ∧
        (∀ (v : α) id, s.2.1[v]? = some id → id < s.2.2) ∧
        (deduplicate_canonical s.1).2 = s.2.2)
    · refine ⟨?_, ?_, ?_⟩
      · intro k hk; simp at hk
      · intro v id hv; simp at hv
      · show (deduplicate_canonical (#[] : Array Nat)).2 = 0
        rfl
    · intro i s ih
      obtain ⟨classes, map, nextId⟩ := s
      simp only at ih
      obtain ⟨ihC, ihM, ihTop⟩ := ih
      simp only
      cases hm : map[values[i]]? with
      | some id =>
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          by_cases hkeq : k = classes.size
          · subst hkeq
            simp [Array.getElem_push]
            exact ihM _ _ hm
          · have hk' : k < classes.size := by
              rw [Array.size_push] at hk; omega
            rw [Array.getElem_push_lt hk']
            exact ihC k hk'
        · intro v id' hv
          exact ihM v id' hv
        · -- Repeat case: id < nextId; push False, top unchanged.
          have hid_lt : id < nextId := ihM _ _ hm
          show (deduplicate_canonical (classes.push id)).2 = nextId
          unfold deduplicate_canonical
          rw [Array.foldl_push]
          have hcd : classes.foldl
              (fun (acc : Array Bool × Nat) cls =>
                let (flags, top_cls) := acc
                if cls == top_cls then (flags.push True, top_cls + 1)
                else (flags.push False, top_cls))
              (#[], 0) = (deduplicate_canonical classes) := rfl
          rw [hcd]
          cases hd : deduplicate_canonical classes with
          | mk flags top_cls =>
            show (if id == top_cls then (flags.push True, top_cls + 1)
                  else (flags.push False, top_cls)).2 = nextId
            have htop_d : top_cls = nextId := by rw [hd] at ihTop; exact ihTop
            have hne_d : ¬ (id == top_cls) = true := by
              simp; rw [htop_d]; exact Nat.ne_of_lt hid_lt
            rw [if_neg hne_d]
            exact htop_d
      | none =>
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          by_cases hkeq : k = classes.size
          · subst hkeq
            simp [Array.getElem_push]
          · have hk' : k < classes.size := by
              rw [Array.size_push] at hk; omega
            rw [Array.getElem_push_lt hk']
            exact Nat.lt_succ_of_lt (ihC k hk')
        · intro v id' hv
          show id' < nextId + 1
          rw [Std.HashMap.getElem?_insert] at hv
          by_cases hveq : (values[i] == v) = true
          · rw [if_pos hveq] at hv
            rw [Option.some.injEq] at hv
            omega
          · rw [if_neg hveq] at hv
            exact Nat.lt_succ_of_lt (ihM v id' hv)
        · -- Fresh case: pushes nextId, increments.
          show (deduplicate_canonical (classes.push nextId)).2 = nextId + 1
          unfold deduplicate_canonical
          rw [Array.foldl_push]
          have hcd : classes.foldl
              (fun (acc : Array Bool × Nat) cls =>
                let (flags, top_cls) := acc
                if cls == top_cls then (flags.push True, top_cls + 1)
                else (flags.push False, top_cls))
              (#[], 0) = (deduplicate_canonical classes) := rfl
          rw [hcd]
          cases hd : deduplicate_canonical classes with
          | mk flags top_cls =>
            show (if nextId == top_cls then (flags.push True, top_cls + 1)
                  else (flags.push False, top_cls)).2 = nextId + 1
            have htop_d : top_cls = nextId := by rw [hd] at ihTop; exact ihTop
            have heq_d : (nextId == top_cls) = true := by
              simp; exact htop_d.symm
            rw [if_pos heq_d]
            omega
  -- Project the third conjunct of the inner foldl invariant.
  unfold assignClasses
  exact inner.2.2


private theorem canonicalCountBound_of_assignClasses
    {α : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (values : Array α) :
    CanonicalCountBound (assignClasses values).1 := by
  intro i h
  rw [assignClasses_canonical_top_eq]
  exact assignClasses_classes_lt_nextId values i h

/-- `partitionRefineBound` output satisfies `CanonicalCountBound`, given the
input does. The recursive case's input becomes an `assignClasses` output, which
satisfies the predicate by `canonicalCountBound_of_assignClasses`. The
fixpoint case returns the input. -/
private theorem partitionRefineBound_canonicalCountBound
    (bound : Nat) (classes : Array Nat) (callees : Array (Array FunIdx))
    (hin : CanonicalCountBound classes) :
    CanonicalCountBound (partitionRefineBound bound classes callees) := by
  induction bound generalizing classes with
  | zero => unfold partitionRefineBound; exact hin
  | succ b ih =>
    unfold partitionRefineBound
    simp only
    split
    · exact hin
    · -- The recursive call's input is an `assignClasses` output.
      apply ih
      exact canonicalCountBound_of_assignClasses _

/-- Main bound on `partitionRefine` output: NO input hypothesis needed.
`partitionRefine = partitionRefineBound (size+1) initClasses _`, which always
takes at least one step. The first step's split is either:
- fixpoint: return `(assignClasses signatures).1` (when newClasses == initClasses,
  but newClasses is an `assignClasses` output of `Nat × Array Nat`, so
  CanonicalCountBound applies via `canonicalCountBound_of_assignClasses`).
- recursion: input becomes `(assignClasses signatures).1`, same reasoning.

This avoids needing typeclass instances on the original input element type
(e.g., `Block × FunctionLayout`). -/
private theorem partitionRefine_canonicalCountBound
    (classes : Array Nat) (callees : Array (Array FunIdx)) :
    CanonicalCountBound (partitionRefine classes callees) := by
  unfold partitionRefine
  -- Bound = size + 1 ≥ 1, so we go into the succ branch.
  unfold partitionRefineBound
  simp only
  -- The split: == branch returns `classes`, but in this branch, classes
  -- equals newClasses, which IS an assignClasses output.
  split
  · -- == branch: classes = newClasses (assignClasses output of Nat × Array Nat).
    rename_i hbeq
    -- `hbeq : (newClasses == classes) = true` ⇒ `newClasses = classes`.
    have heq : (assignClasses (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))).1 = classes := by
      have : ((assignClasses (classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!)))).1 == classes) = true := hbeq
      exact beq_iff_eq.mp this
    -- Goal: `CanonicalCountBound classes`. Rewrite via heq.
    rw [← heq]
    exact canonicalCountBound_of_assignClasses _
  · -- Recursive branch: apply partitionRefineBound_canonicalCountBound on
    -- the assignClasses-output input.
    exact partitionRefineBound_canonicalCountBound _ _ _
      (canonicalCountBound_of_assignClasses _)

/-- Count of `true` values in `canonical[0:n]`, defined by recursion on `n`. -/
private def countTruesUpTo (canonical : Array Bool) : Nat → Nat
  | 0 => 0
  | n+1 =>
    if h : n < canonical.size then
      if canonical[n]'h then countTruesUpTo canonical n + 1
      else countTruesUpTo canonical n
    else countTruesUpTo canonical n

/-- `countTruesUpTo` only depends on the prefix `arr[0:n]`. Pushing a new
element doesn't affect the count up to a position before the push. -/
private theorem countTruesUpTo_push_irrelevant
    (arr : Array Bool) (b : Bool) (n : Nat) (hn : n ≤ arr.size) :
    countTruesUpTo (arr.push b) n = countTruesUpTo arr n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold countTruesUpTo
    have hk_lt : k < arr.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
    have hk_lt' : k < (arr.push b).size := by rw [Array.size_push]; omega
    rw [dif_pos hk_lt, dif_pos hk_lt']
    rw [Array.getElem_push_lt hk_lt]
    rw [ih (Nat.le_of_lt hk_lt)]

/-- Closing equation: `countTruesUpTo canonical canonical.size = canonical.foldl ...`. -/
private theorem countTruesUpTo_size_eq_foldl (canonical : Array Bool) :
    countTruesUpTo canonical canonical.size =
      canonical.foldl (fun (acc : Nat) (b : Bool) => if b then acc + 1 else acc) 0 := by
  let countTrue : Nat → Bool → Nat := fun acc b => if b then acc + 1 else acc
  show countTruesUpTo canonical canonical.size = canonical.foldl countTrue 0
  symm
  apply Array.foldl_induction
    (motive := fun (i : Nat) (acc : Nat) =>
      acc = countTruesUpTo canonical i)
  · rfl
  · intro i acc ih
    show countTrue acc canonical[i.val] = countTruesUpTo canonical (i.val + 1)
    unfold countTruesUpTo
    have hi_lt : i.val < canonical.size := i.isLt
    rw [dif_pos hi_lt]
    by_cases hb : canonical[i.val]'hi_lt = true
    · rw [if_pos hb]
      show (if canonical[i.val]'hi_lt then acc + 1 else acc) = countTruesUpTo canonical i.val + 1
      rw [if_pos hb]
      rw [ih]
    · rw [if_neg hb]
      show (if canonical[i.val]'hi_lt then acc + 1 else acc) = countTruesUpTo canonical i.val
      rw [if_neg hb]
      exact ih

/-- Key class-match invariant of `deduplicate_canonical`: whenever `canonical`
flags position `j`, `classes[j]` equals the number of canonical flags seen in
the prefix `canonical[0..j]` — i.e., exactly the position in the
deduplicated-array where `j`'s push will land. Proved via a combined-motive
foldl induction that simultaneously tracks the flag array, its size, the
`top_cls` counter, and the correctness of each pushed flag. -/
private theorem deduplicate_canonical_classes_eq_count
    (classes : Array Nat) :
    let canonical := (deduplicate_canonical classes).1
    ∀ (j : Nat) (hj : j < classes.size)
      (hj' : j < canonical.size) (_hcan : canonical[j]'hj' = true),
      classes[j]'hj = countTruesUpTo canonical j := by
  simp only
  intro j hj hj' hcan
  -- Key: the `deduplicate_canonical` foldl builds `canonical` one push at a
  -- time. Push at step `i` sets `canonical[i] = (classes[i] == top_cls_i)`.
  -- If that push is `true`, then `classes[i] = top_cls_i = countTruesUpTo canonical i`.
  -- Other flags `canonical[k]` for `k < i` have their count-match from the IH.
  -- Package the 3-conjunct invariant as a single Prop via a local abbrev
  -- (avoids HOU with `∧ ∧ ∀` chain inside `Array.foldl_induction`'s motive).
  let Inv : Nat → Array Bool × Nat → Prop := fun i s =>
    s.1.size = i ∧ s.2 = countTruesUpTo s.1 s.1.size ∧
    ∀ (k : Nat) (hk_cls : k < classes.size) (hk_can : k < s.1.size),
      s.1[k]'hk_can = true → classes[k]'hk_cls = countTruesUpTo s.1 k
  have key : Inv classes.size (deduplicate_canonical classes) := by
    unfold deduplicate_canonical
    exact Array.foldl_induction (motive := Inv)
      (by
        refine ⟨rfl, ?_, ?_⟩
        · show (0 : Nat) = countTruesUpTo (#[] : Array Bool) 0; rfl
        · intro k hk_cls hk_can; simp at hk_can)
      (by
        intro i s ih
        obtain ⟨flags, top_cls⟩ := s
        simp only [Inv] at ih
        obtain ⟨ihSz, ihCount, ihFlags⟩ := ih
        show Inv (i.val + 1)
          (if classes[i.val] == top_cls then (flags.push True, top_cls + 1)
           else (flags.push False, top_cls))
        simp only [Inv]
        by_cases hc : (classes[i.val] == top_cls) = true
        · rw [if_pos hc]
          refine ⟨?_, ?_, ?_⟩
          · show (flags.push True).size = i.val + 1
            rw [Array.size_push, ihSz]
          · show top_cls + 1 =
              countTruesUpTo (flags.push True) (flags.push True).size
            rw [Array.size_push]
            unfold countTruesUpTo
            have hflag_lt : flags.size < (flags.push True).size := by
              rw [Array.size_push]; omega
            rw [dif_pos hflag_lt, Array.getElem_push_eq]
            have hpos : (decide True = true) := by simp
            rw [if_pos hpos]
            have heq : countTruesUpTo (flags.push True) flags.size =
                countTruesUpTo flags flags.size :=
              countTruesUpTo_push_irrelevant flags True flags.size (Nat.le_refl _)
            rw [heq, ← ihCount]
          · intro k hk_cls hk_can hk_true
            by_cases hk_eq : k = flags.size
            · subst hk_eq
              have hclasses_eq_top : classes[flags.size]'hk_cls = top_cls := by
                have hflags_i : flags.size = i.val := ihSz
                have hcls_eq_cls : classes[flags.size]'hk_cls =
                    classes[i.val] := by congr 1
                rw [hcls_eq_cls]
                exact beq_iff_eq.mp hc
              have hcount : countTruesUpTo (flags.push True) flags.size =
                  countTruesUpTo flags flags.size :=
                countTruesUpTo_push_irrelevant flags True flags.size (Nat.le_refl _)
              rw [hcount, ← ihCount]
              exact hclasses_eq_top
            · have hk_lt_flags : k < flags.size := by
                rw [Array.size_push] at hk_can; omega
              have hk_can_flags : flags[k]'hk_lt_flags = true := by
                rw [Array.getElem_push_lt hk_lt_flags] at hk_true
                exact hk_true
              have := ihFlags k hk_cls hk_lt_flags hk_can_flags
              have hcount : countTruesUpTo (flags.push True) k =
                  countTruesUpTo flags k :=
                countTruesUpTo_push_irrelevant flags True k (Nat.le_of_lt hk_lt_flags)
              rw [hcount]; exact this
        · rw [if_neg hc]
          refine ⟨?_, ?_, ?_⟩
          · show (flags.push False).size = i.val + 1
            rw [Array.size_push, ihSz]
          · show top_cls =
              countTruesUpTo (flags.push False) (flags.push False).size
            rw [Array.size_push]
            unfold countTruesUpTo
            have hflag_lt : flags.size < (flags.push False).size := by
              rw [Array.size_push]; omega
            rw [dif_pos hflag_lt, Array.getElem_push_eq]
            have hneg : ¬ (decide False = true) := by simp
            rw [if_neg hneg]
            have heq : countTruesUpTo (flags.push False) flags.size =
                countTruesUpTo flags flags.size :=
              countTruesUpTo_push_irrelevant flags False flags.size (Nat.le_refl _)
            rw [heq, ← ihCount]
          · intro k hk_cls hk_can hk_true
            by_cases hk_eq : k = flags.size
            · subst hk_eq
              rw [Array.getElem_push_eq] at hk_true
              exact absurd hk_true (by simp)
            · have hk_lt_flags : k < flags.size := by
                rw [Array.size_push] at hk_can; omega
              have hk_can_flags : flags[k]'hk_lt_flags = true := by
                rw [Array.getElem_push_lt hk_lt_flags] at hk_true
                exact hk_true
              have := ihFlags k hk_cls hk_lt_flags hk_can_flags
              have hcount : countTruesUpTo (flags.push False) k =
                  countTruesUpTo flags k :=
                countTruesUpTo_push_irrelevant flags False k (Nat.le_of_lt hk_lt_flags)
              rw [hcount]; exact this)
  exact key.2.2 j hj hj' hcan

/-- `deduplicate_canonical` preserves the array length: its first component
has the same size as the input. -/
private theorem deduplicate_canonical_size
    (classes : Array Nat) :
    (deduplicate_canonical classes).1.size = classes.size := by
  unfold deduplicate_canonical
  apply Array.foldl_induction
    (motive := fun i (s : Array Bool × Nat) => s.1.size = i)
  · rfl
  · intro i s hs
    obtain ⟨flags, top_cls⟩ := s
    simp only at hs
    show ((if classes[i.val] == top_cls then (flags.push True, top_cls + 1)
           else (flags.push False, top_cls)) : Array Bool × Nat).1.size = i.val + 1
    by_cases hc : (classes[i.val] == top_cls) = true
    · rw [if_pos hc]
      show (flags.push True).size = i.val + 1
      rw [Array.size_push, hs]
    · rw [if_neg hc]
      show (flags.push False).size = i.val + 1
      rw [Array.size_push, hs]

/-- `deduplicate_canonical`'s `top_cls` (second component) equals the count
of `True` flags in its first component. -/
private theorem deduplicate_canonical_top_eq_count_true
    (classes : Array Nat) :
    (deduplicate_canonical classes).2 =
      (deduplicate_canonical classes).1.foldl
        (fun (acc : Nat) (b : Bool) => if b then acc + 1 else acc) 0 := by
  rw [← countTruesUpTo_size_eq_foldl]
  -- Strong invariant: at step i, .2 = countTruesUpTo .1 .1.size AND .1.size = i.
  have key : (deduplicate_canonical classes).1.size = classes.size ∧
      (deduplicate_canonical classes).2 =
        countTruesUpTo (deduplicate_canonical classes).1
          (deduplicate_canonical classes).1.size := by
    unfold deduplicate_canonical
    apply Array.foldl_induction
      (motive := fun (i : Nat) (s : Array Bool × Nat) =>
        s.1.size = i ∧ s.2 = countTruesUpTo s.1 s.1.size)
    · refine ⟨rfl, ?_⟩
      show (0 : Nat) = countTruesUpTo (#[] : Array Bool) 0
      rfl
    · intro i s ih
      obtain ⟨flags, top_cls⟩ := s
      simp only at ih
      obtain ⟨ihSz, ihCount⟩ := ih
      simp only
      by_cases hc : (classes[i] == top_cls) = true
      · rw [if_pos hc]
        refine ⟨?_, ?_⟩
        · show (flags.push True).size = i.val + 1
          rw [Array.size_push, ihSz]
        · show top_cls + 1 = countTruesUpTo (flags.push True) (flags.push True).size
          rw [Array.size_push]
          unfold countTruesUpTo
          have hflag_lt : flags.size < (flags.push True).size := by
            rw [Array.size_push]; omega
          rw [dif_pos hflag_lt]
          rw [Array.getElem_push_eq]
          have hpos : (decide True = true) := by simp
          rw [if_pos hpos]
          have heq : countTruesUpTo (flags.push True) flags.size =
              countTruesUpTo flags flags.size :=
            countTruesUpTo_push_irrelevant flags True flags.size (Nat.le_refl _)
          rw [heq, ← ihCount]
      · rw [if_neg hc]
        refine ⟨?_, ?_⟩
        · show (flags.push False).size = i.val + 1
          rw [Array.size_push, ihSz]
        · show top_cls = countTruesUpTo (flags.push False) (flags.push False).size
          rw [Array.size_push]
          unfold countTruesUpTo
          have hflag_lt : flags.size < (flags.push False).size := by
            rw [Array.size_push]; omega
          rw [dif_pos hflag_lt]
          rw [Array.getElem_push_eq]
          have hneg : ¬ (decide False = true) := by simp
          rw [if_neg hneg]
          have heq : countTruesUpTo (flags.push False) flags.size =
              countTruesUpTo flags flags.size :=
            countTruesUpTo_push_irrelevant flags False flags.size (Nat.le_refl _)
          rw [heq, ← ihCount]
  obtain ⟨hSz, hCount⟩ := key
  rw [hCount, hSz]

/-- Size of `deduplicate_newFunctions` equals the count of `True` flags in
`canonical`, when sizes line up. -/
private theorem deduplicate_newFunctions_size_eq_count_true
    (functions : Array Function) (classes : Array Nat) (canonical : Array Bool)
    (remapFn : FunIdx → FunIdx)
    (hsz_cf : classes.size = functions.size)
    (hsz_cn : classes.size = canonical.size) :
    (deduplicate_newFunctions functions classes canonical remapFn).size =
      canonical.foldl (fun (acc : Nat) (b : Bool) => if b then acc + 1 else acc) 0 := by
  rw [← countTruesUpTo_size_eq_foldl]
  have hsz1 : (classes.zip canonical).size = classes.size := by
    rw [Array.size_zip]; omega
  have hsz2 : ((classes.zip canonical).zip functions).size = classes.size := by
    rw [Array.size_zip, hsz1]; omega
  have hsz2_can : ((classes.zip canonical).zip functions).size = canonical.size := by
    rw [hsz2, hsz_cn]
  -- Prove the equality at the index `((classes.zip canonical).zip functions).size`
  -- via foldl_induction, then rewrite to `canonical.size`.
  have key :
      (deduplicate_newFunctions functions classes canonical remapFn).size =
        countTruesUpTo canonical ((classes.zip canonical).zip functions).size := by
    unfold deduplicate_newFunctions
    apply Array.foldl_induction
      (motive := fun (i : Nat) (acc : Array Function) =>
        acc.size = countTruesUpTo canonical i)
    · rfl
    · intro i acc ih
      have hi_lt : i.val < ((classes.zip canonical).zip functions).size := i.isLt
      have hi_lt' : i.val < classes.size := hsz2 ▸ hi_lt
      have hi_lt_can : i.val < canonical.size := by omega
      have hi_lt_fn : i.val < functions.size := by omega
      have hi_lt_cz : i.val < (classes.zip canonical).size := hsz1 ▸ hi_lt'
      have hzip_eq : ((classes.zip canonical).zip functions)[i.val]'hi_lt =
          ((classes.zip canonical)[i.val]'hi_lt_cz, functions[i.val]'hi_lt_fn) :=
        Array.getElem_zip
      have hcz_eq : (classes.zip canonical)[i.val]'hi_lt_cz =
          (classes[i.val]'hi_lt', canonical[i.val]'hi_lt_can) :=
        Array.getElem_zip
      show (match ((classes.zip canonical).zip functions)[i.val]'hi_lt with
            | ((cls, can), f) =>
              if can = true then
                acc.push { body := rewriteBlock remapFn f.body,
                           layout := f.layout,
                           entry := deduplicate_class_entry functions classes cls,
                           constrained := false }
              else acc).size = _
      rw [hzip_eq, hcz_eq]
      simp only
      show (if canonical[i.val]'hi_lt_can = true then _ else acc).size = _
      unfold countTruesUpTo
      rw [dif_pos hi_lt_can]
      by_cases hcan : canonical[i.val]'hi_lt_can = true
      · rw [if_pos hcan, if_pos hcan]
        rw [Array.size_push]
        omega
      · rw [if_neg hcan, if_neg hcan]
        exact ih
  rw [key, hsz2_can]

/-- Combined: `deduplicate_newFunctions`'s size equals `(deduplicate_canonical classes).2`. -/
private theorem deduplicate_newFunctions_size_eq_top
    (functions : Array Function) (classes : Array Nat) (remapFn : FunIdx → FunIdx)
    (hsz_cf : classes.size = functions.size) :
    (deduplicate_newFunctions functions classes (deduplicate_canonical classes).1 remapFn).size =
      (deduplicate_canonical classes).2 := by
  have hsz_cn : classes.size = (deduplicate_canonical classes).1.size :=
    (deduplicate_canonical_size classes).symm
  rw [deduplicate_newFunctions_size_eq_count_true functions classes _ remapFn hsz_cf hsz_cn]
  exact (deduplicate_canonical_top_eq_count_true classes).symm

/-- Equation lemma for `t.deduplicate` in the if-then-else form. -/
private theorem deduplicate_eq_ite (t : Toplevel) :
    t.deduplicate =
      if t.functions.size == 0 then (t, id)
      else
        let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
        let initClasses := (assignClasses skeletons).1
        let callees := t.functions.map fun f => collectCalleesBlock f.body
        let classes := partitionRefine initClasses callees
        let canonical := (deduplicate_canonical classes).1
        let remapFn := deduplicate_remap classes
        let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
        ({ t with functions := newFunctions }, remapFn) := rfl

/-- Sub-lemma 1: canonical-count bound. Every `classes[i]` is less than
`tDedup.functions.size`, which equals the canonical count. -/
private theorem deduplicate_top_cls_bound
    (t : Toplevel) :
    let (tDedup, _remap) := t.deduplicate
    ∀ i, i < t.functions.size →
      (deduplicate_classes_of t)[i]! < tDedup.functions.size := by
  show ∀ i, i < t.functions.size →
    (deduplicate_classes_of t)[i]! < t.deduplicate.1.functions.size
  by_cases hn : t.functions.size = 0
  · intro i hi
    exact absurd hi (hn ▸ Nat.not_lt_zero i)
  · intro i hi
    have hne_bool : (t.functions.size == 0) = false := by simp [hn]
    -- Reduce `deduplicate_classes_of` to `partitionRefine ...`.
    have hdc_eq :
        deduplicate_classes_of t =
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          partitionRefine initClasses callees := by
      unfold deduplicate_classes_of
      rw [hne_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
    -- Reduce `t.deduplicate.1.functions` to `deduplicate_newFunctions ...`.
    have hded_eq :
        t.deduplicate.1.functions =
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let canonical := (deduplicate_canonical classes).1
          let remapFn := deduplicate_remap classes
          deduplicate_newFunctions t.functions classes canonical remapFn := by
      rw [deduplicate_eq_ite]
      rw [hne_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hdc_eq, hded_eq]
    -- Now goal:
    --   (let ... partitionRefine ...)[i]! < (let ... deduplicate_newFunctions ...).size
    simp only
    -- After `simp only`, `let`s reduce and we get:
    --   (partitionRefine (assignClasses (...).map _).1 (...).map _)[i]!
    --     < (deduplicate_newFunctions ...).size
    -- Now apply the chain of facts.
    -- Step 1: size of `classes` (the partitionRefine output) = t.functions.size.
    have hsz_class :
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)).size = t.functions.size := by
      rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
    have hi_class : i <
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)).size := by
      rw [hsz_class]; exact hi
    -- Step 2: CanonicalCountBound on the output.
    have hcan := partitionRefine_canonicalCountBound
        (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => collectCalleesBlock f.body)
    have hcb := hcan i hi_class
    -- Step 3: size of `deduplicate_newFunctions` = top.
    have hnewSz := deduplicate_newFunctions_size_eq_top t.functions
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body))
        (deduplicate_remap (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)))
        hsz_class
    rw [hnewSz]
    rw [getElem!_pos _ i hi_class]
    exact hcb

/-- Index-erased predicate: every function in `acc` has body of the form
`rewriteBlock remapFn functions[j].body` and matching `layout` for some
in-range `j`. -/
private def AllRewrittenFromInput
    (functions : Array Function) (remapFn : FunIdx → FunIdx)
    (acc : Array Function) : Prop :=
  ∀ f' ∈ acc, ∃ j, ∃ (_ : j < functions.size),
    f'.body = rewriteBlock remapFn functions[j].body ∧
    f'.layout = functions[j].layout

/-- Stronger index-based predicate: for every position `fi` in the acc, there
is a raw index `j` such that `acc[fi]`'s body/layout match `functions[j]`'s
body/layout AND `classes[j] = fi`. This is the "class-match" invariant of
`deduplicate_newFunctions`: each canonical push occurs at a point where the
running canonical-count equals `classes[j]`, so the push-position equals
`classes[j]`. The fourth component (state.2 = acc.size) tracks the coupling
between `top_cls` and the accumulator size (both increment on canonical
pushes). -/
private def IndexedProvenanceFromInput
    (functions : Array Function) (classes : Array Nat)
    (remapFn : FunIdx → FunIdx) (acc : Array Function) : Prop :=
  ∀ (fi : Nat) (hfi : fi < acc.size),
    ∃ j, ∃ (_ : j < functions.size) (hj_cls : j < classes.size),
      (acc[fi]'hfi).body = rewriteBlock remapFn functions[j].body ∧
      (acc[fi]'hfi).layout = functions[j].layout ∧
      classes[j]'hj_cls = fi

/-- The foldl building `deduplicate_newFunctions` preserves
`AllRewrittenFromInput`. Key step: each element at position `i` of the zipped
array is `((classes[i], canonical[i]), functions[i])` via `Array.getElem_zip`,
so when we push its rewritten body we pick `j := i.val` as the witness. -/
private theorem deduplicate_newFunctions_all_rewritten
    (functions : Array Function) (classes : Array Nat)
    (canonical : Array Bool) (remapFn : FunIdx → FunIdx) :
    AllRewrittenFromInput functions remapFn
      (deduplicate_newFunctions functions classes canonical remapFn) := by
  unfold deduplicate_newFunctions
  apply Array.foldl_induction
    (motive := fun _ (acc : Array Function) =>
      AllRewrittenFromInput functions remapFn acc)
  · intro f' hf'
    exact absurd hf' (Array.not_mem_empty f')
  · intro i acc ih
    -- Step-hypothesis `i : Fin ((classes.zip canonical).zip functions).size`.
    -- From this, `i.val < functions.size` (zip truncates to the min).
    have hiLt : i.val < ((classes.zip canonical).zip functions).size := i.isLt
    have hsz1 : ((classes.zip canonical).zip functions).size =
        min (classes.zip canonical).size functions.size := Array.size_zip
    have hsz2 : (classes.zip canonical).size =
        min classes.size canonical.size := Array.size_zip
    have hiLt' : i.val < min (classes.zip canonical).size functions.size :=
      hsz1 ▸ hiLt
    have hi_fn : i.val < functions.size := by omega
    have hi_cz : i.val < (classes.zip canonical).size := by omega
    have hi_cz' : i.val < min classes.size canonical.size := hsz2 ▸ hi_cz
    have hcz_fn1 : i.val < classes.size := by omega
    have hcz_fn2 : i.val < canonical.size := by omega
    -- The element at index `i.val` has the form
    --   `((classes[i], canonical[i]), functions[i])` via `Array.getElem_zip`.
    have hzip_eq :
        ((classes.zip canonical).zip functions)[i.val]'hiLt =
          ((classes.zip canonical)[i.val]'hi_cz, functions[i.val]'hi_fn) :=
      Array.getElem_zip
    have hcz_eq :
        (classes.zip canonical)[i.val]'hi_cz =
          (classes[i.val]'hcz_fn1, canonical[i.val]'hcz_fn2) :=
      Array.getElem_zip
    -- Now analyze the push/skip case split.
    intro f' hf'
    -- `hf'` mentions `((classes.zip canonical).zip functions)[i]` which is
    -- `...[i.val]'i.isLt` definitionally. Replace with the explicit pair.
    change f' ∈ (match ((classes.zip canonical).zip functions)[i.val]'hiLt with
                   | ((cls, can), f) =>
                     if can = true then
                       acc.push { body := rewriteBlock remapFn f.body,
                                  layout := f.layout,
                                  entry := deduplicate_class_entry functions classes cls,
                                  constrained := false }
                     else acc) at hf'
    rw [hzip_eq, hcz_eq] at hf'
    simp only at hf'
    by_cases hcan : canonical[i.val]'hcz_fn2 = true
    · rw [hcan] at hf'
      simp only [↓reduceIte] at hf'
      rw [Array.mem_push] at hf'
      cases hf' with
      | inl hprev => exact ih f' hprev
      | inr hpush =>
        -- `f'` is the pushed new function; its body is
        -- `rewriteBlock remapFn (functions[i.val]'hi_fn).body`
        -- and its layout is `(functions[i.val]'hi_fn).layout`.
        refine ⟨i.val, hi_fn, ?_, ?_⟩
        · rw [hpush]
        · rw [hpush]
    · have hcan' : canonical[i.val]'hcz_fn2 = false := by
        match heq : canonical[i.val]'hcz_fn2 with
        | false => rfl
        | true => exact absurd heq hcan
      rw [hcan'] at hf'
      simp only [Bool.false_eq_true, ↓reduceIte] at hf'
      exact ih f' hf'

/-- Foldl-invariant strengthening: for `canonical = (deduplicate_canonical classes).1`,
the final `deduplicate_newFunctions` has, at every output position `fi`, a
matching raw index `j` with `classes[j] = fi` (plus body/layout provenance).
Uses `deduplicate_canonical_classes_eq_count` to convert the push's local
position (= `countTruesUpTo canonical j`) into `classes[j]`. -/
private theorem deduplicate_newFunctions_indexed_provenance
    (functions : Array Function) (classes : Array Nat)
    (remapFn : FunIdx → FunIdx)
    (hsz_cn : classes.size ≤ functions.size) :
    let canonical := (deduplicate_canonical classes).1
    IndexedProvenanceFromInput functions classes remapFn
      (deduplicate_newFunctions functions classes canonical remapFn) := by
  simp only
  have hcan_sz : (deduplicate_canonical classes).1.size = classes.size :=
    deduplicate_canonical_size classes
  -- Package the combined foldl invariant.
  let CanInv : Nat → Array Function → Prop := fun i acc =>
    (∀ (fi : Nat) (hfi : fi < acc.size),
      ∃ j, ∃ (hj : j < functions.size)
        (hj_can : j < (deduplicate_canonical classes).1.size)
        (hj_lt_i : j < i),
        (acc[fi]'hfi).body =
          rewriteBlock remapFn functions[j].body ∧
        (acc[fi]'hfi).layout = functions[j].layout ∧
        (deduplicate_canonical classes).1[j]'hj_can = true ∧
        countTruesUpTo (deduplicate_canonical classes).1 j = fi) ∧
    acc.size = countTruesUpTo (deduplicate_canonical classes).1 i
  -- Apply foldl_induction with CanInv.
  have hinv : CanInv ((classes.zip (deduplicate_canonical classes).1).zip functions).size
    (deduplicate_newFunctions functions classes (deduplicate_canonical classes).1 remapFn) := by
    unfold deduplicate_newFunctions
    refine Array.foldl_induction (motive := CanInv) ?_ ?_
    · refine ⟨?_, rfl⟩
      intro fi hfi; exact absurd hfi (Nat.not_lt_zero _)
    · intro i acc ih
      obtain ⟨ihProv, ihSz⟩ := ih
      have hiLt : i.val < ((classes.zip (deduplicate_canonical classes).1).zip functions).size :=
        i.isLt
      have hsz1 : ((classes.zip (deduplicate_canonical classes).1).zip functions).size =
          min (classes.zip (deduplicate_canonical classes).1).size functions.size :=
        Array.size_zip
      have hsz2 : (classes.zip (deduplicate_canonical classes).1).size =
          min classes.size (deduplicate_canonical classes).1.size :=
        Array.size_zip
      have hiLt' : i.val < min (classes.zip (deduplicate_canonical classes).1).size
          functions.size := hsz1 ▸ hiLt
      have hi_fn : i.val < functions.size := by omega
      have hi_cz : i.val < (classes.zip (deduplicate_canonical classes).1).size := by omega
      have hi_cz' : i.val <
          min classes.size (deduplicate_canonical classes).1.size := hsz2 ▸ hi_cz
      have hcz_fn1 : i.val < classes.size := by omega
      have hcz_fn2 : i.val < (deduplicate_canonical classes).1.size := by omega
      have hzip_eq :
          ((classes.zip (deduplicate_canonical classes).1).zip functions)[i.val]'hiLt =
            ((classes.zip (deduplicate_canonical classes).1)[i.val]'hi_cz,
             functions[i.val]'hi_fn) :=
        Array.getElem_zip
      have hcz_eq :
          (classes.zip (deduplicate_canonical classes).1)[i.val]'hi_cz =
            (classes[i.val]'hcz_fn1,
             (deduplicate_canonical classes).1[i.val]'hcz_fn2) :=
        Array.getElem_zip
      -- Change the goal via the zip rewrite.
      show CanInv (i.val + 1) _
      simp only [CanInv]
      change (∀ (fi : Nat)
          (hfi : fi <
            (match ((classes.zip (deduplicate_canonical classes).1).zip functions)[i.val]'hiLt with
              | ((cls, can), f) =>
                if can = true then
                  acc.push { body := rewriteBlock remapFn f.body,
                             layout := f.layout,
                             entry := deduplicate_class_entry functions classes cls,
                             constrained := false }
                else acc).size),
          ∃ j, ∃ (hj : j < functions.size)
            (hj_can : j < (deduplicate_canonical classes).1.size)
            (_ : j < i.val + 1),
            ((match ((classes.zip (deduplicate_canonical classes).1).zip functions)[i.val]'hiLt with
              | ((cls, can), f) =>
                if can = true then
                  acc.push { body := rewriteBlock remapFn f.body,
                             layout := f.layout,
                             entry := deduplicate_class_entry functions classes cls,
                             constrained := false }
                else acc)[fi]'hfi).body = rewriteBlock remapFn functions[j].body ∧
            ((match ((classes.zip (deduplicate_canonical classes).1).zip functions)[i.val]'hiLt with
              | ((cls, can), f) =>
                if can = true then
                  acc.push { body := rewriteBlock remapFn f.body,
                             layout := f.layout,
                             entry := deduplicate_class_entry functions classes cls,
                             constrained := false }
                else acc)[fi]'hfi).layout = functions[j].layout ∧
            (deduplicate_canonical classes).1[j]'hj_can = true ∧
            countTruesUpTo (deduplicate_canonical classes).1 j = fi) ∧
        (match ((classes.zip (deduplicate_canonical classes).1).zip functions)[i.val]'hiLt with
              | ((cls, can), f) =>
                if can = true then
                  acc.push { body := rewriteBlock remapFn f.body,
                             layout := f.layout,
                             entry := deduplicate_class_entry functions classes cls,
                             constrained := false }
                else acc).size =
          countTruesUpTo (deduplicate_canonical classes).1 (i.val + 1)
      rw [hzip_eq, hcz_eq]
      simp only
      by_cases hcan : (deduplicate_canonical classes).1[i.val]'hcz_fn2 = true
      · rw [hcan]
        simp only [↓reduceIte]
        -- Pushed branch. New size = acc.size + 1 = count + 1.
        -- After push, position acc.size gets the new entry.
        refine ⟨?_, ?_⟩
        · intro fi hfi
          have hfi_push : fi < acc.size + 1 := by
            rw [Array.size_push] at hfi; exact hfi
          by_cases hfi_eq : fi = acc.size
          · -- New entry at position acc.size.
            subst hfi_eq
            refine ⟨i.val, hi_fn, hcz_fn2, Nat.lt_succ_self _, ?_, ?_, ?_, ?_⟩
            · rw [Array.getElem_push_eq]
            · rw [Array.getElem_push_eq]
            · exact hcan
            · -- countTruesUpTo canonical i.val = acc.size (= fi) by ihSz.
              exact ihSz.symm
          · -- Prior entry. Use ih.
            have hfi_lt : fi < acc.size := by omega
            rw [Array.getElem_push_lt hfi_lt]
            obtain ⟨j, hj, hj_can, hj_lt_i, hbody, hlayout, hj_true, hcount⟩ :=
              ihProv fi hfi_lt
            exact ⟨j, hj, hj_can, Nat.lt_of_lt_of_le hj_lt_i (Nat.le_succ _),
                   hbody, hlayout, hj_true, hcount⟩
        · -- Size-count equation.
          rw [Array.size_push, ihSz]
          -- countTruesUpTo canonical (i.val + 1) = countTruesUpTo canonical i.val + 1
          -- because canonical[i.val] = true.
          show _ = countTruesUpTo (deduplicate_canonical classes).1 (i.val + 1)
          have : countTruesUpTo (deduplicate_canonical classes).1 (i.val + 1) =
              if h : i.val < (deduplicate_canonical classes).1.size
              then if (deduplicate_canonical classes).1[i.val]'h
                then countTruesUpTo (deduplicate_canonical classes).1 i.val + 1
                else countTruesUpTo (deduplicate_canonical classes).1 i.val
              else countTruesUpTo (deduplicate_canonical classes).1 i.val := rfl
          rw [this, dif_pos hcz_fn2, if_pos hcan]
      · have hcan' : (deduplicate_canonical classes).1[i.val]'hcz_fn2 = false := by
          match heq : (deduplicate_canonical classes).1[i.val]'hcz_fn2 with
          | false => rfl
          | true => exact absurd heq hcan
        rw [hcan']
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · intro fi hfi
          obtain ⟨j, hj, hj_can, hj_lt_i, hbody, hlayout, hj_true, hcount⟩ :=
            ihProv fi hfi
          exact ⟨j, hj, hj_can, Nat.lt_of_lt_of_le hj_lt_i (Nat.le_succ _),
                 hbody, hlayout, hj_true, hcount⟩
        · rw [ihSz]
          show _ = countTruesUpTo (deduplicate_canonical classes).1 (i.val + 1)
          have : countTruesUpTo (deduplicate_canonical classes).1 (i.val + 1) =
              if h : i.val < (deduplicate_canonical classes).1.size
              then if (deduplicate_canonical classes).1[i.val]'h
                then countTruesUpTo (deduplicate_canonical classes).1 i.val + 1
                else countTruesUpTo (deduplicate_canonical classes).1 i.val
              else countTruesUpTo (deduplicate_canonical classes).1 i.val := rfl
          rw [this, dif_pos hcz_fn2,
              show ((deduplicate_canonical classes).1[i.val]'hcz_fn2) = false from hcan']
          simp only [Bool.false_eq_true, ↓reduceIte]
  -- Extract IndexedProvenanceFromInput from CanInv.
  intro fi hfi
  obtain ⟨hprov, _hsz⟩ := hinv
  obtain ⟨j, hj, hj_can, _, hbody, hlayout, hj_true, hcount⟩ := hprov fi hfi
  have hj_cls : j < classes.size := hcan_sz ▸ hj_can
  refine ⟨j, hj, hj_cls, hbody, hlayout, ?_⟩
  have := deduplicate_canonical_classes_eq_count classes j hj_cls hj_can hj_true
  simp only at this
  rw [this, hcount]

/-- Sub-lemma 2: body-provenance. Every `fi` in `tDedup.functions` comes from
some canonical raw index `j` via `deduplicate_newFunctions`'s push — so
`tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body`. -/
private theorem deduplicate_body_provenance
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ fi (_hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (_hj : j < t.functions.size),
        tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body := by
  -- First reduce `t.deduplicate` to the concrete cases via `by_cases`.
  show ∀ fi (_hfi : fi < t.deduplicate.1.functions.size),
    ∃ j, ∃ (_hj : j < t.functions.size),
      t.deduplicate.1.functions[fi].body =
        rewriteBlock t.deduplicate.2 t.functions[j].body
  -- Compute the dedup output via case analysis on `t.functions.size == 0`.
  have hdedup_eq :
      t.deduplicate =
        if t.functions.size == 0 then (t, id)
        else
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let canonical := (deduplicate_canonical classes).1
          let remapFn := deduplicate_remap classes
          let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
          ({ t with functions := newFunctions }, remapFn) := by
    rfl
  rw [hdedup_eq]
  by_cases hn : t.functions.size = 0
  · -- Empty case: `t.deduplicate = (t, id)`.
    have hne : (t.functions.size == 0) = true := by simp [hn]
    rw [if_pos hne]
    intro fi hfi
    exact absurd hfi (hn ▸ Nat.not_lt_zero fi)
  · -- Non-empty case.
    have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
    rw [if_neg hne]
    simp only
    intro fi hfi
    have hmem := Array.getElem_mem hfi
    obtain ⟨j, hj, hbody, _hlayout⟩ :=
      deduplicate_newFunctions_all_rewritten _ _ _ _ _ hmem
    exact ⟨j, hj, hbody⟩

/-- Sub-lemma 2b: layout-provenance. Every `fi` in `tDedup.functions` comes from
some canonical raw index `j` via `deduplicate_newFunctions`'s push — that push
copies the raw `f.layout` verbatim, so
`tDedup.functions[fi].layout = t.functions[j].layout` (and the `j` is the same
one that witnesses body-provenance, but we state it independently for use-case
clarity). -/
private theorem deduplicate_layout_provenance
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ fi (_hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (_hj : j < t.functions.size),
        tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body ∧
        tDedup.functions[fi].layout = t.functions[j].layout := by
  show ∀ fi (_hfi : fi < t.deduplicate.1.functions.size),
    ∃ j, ∃ (_hj : j < t.functions.size),
      t.deduplicate.1.functions[fi].body =
        rewriteBlock t.deduplicate.2 t.functions[j].body ∧
      t.deduplicate.1.functions[fi].layout = t.functions[j].layout
  have hdedup_eq :
      t.deduplicate =
        if t.functions.size == 0 then (t, id)
        else
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let canonical := (deduplicate_canonical classes).1
          let remapFn := deduplicate_remap classes
          let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
          ({ t with functions := newFunctions }, remapFn) := by
    rfl
  rw [hdedup_eq]
  by_cases hn : t.functions.size = 0
  · have hne : (t.functions.size == 0) = true := by simp [hn]
    rw [if_pos hne]
    intro fi hfi
    exact absurd hfi (hn ▸ Nat.not_lt_zero fi)
  · have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
    rw [if_neg hne]
    simp only
    intro fi hfi
    have hmem := Array.getElem_mem hfi
    exact deduplicate_newFunctions_all_rewritten _ _ _ _ _ hmem

/-- Sub-lemma 2c: indexed layout-provenance. Additionally records that the
class-id of the raw witness equals the output position: `classes[j] = fi`. This
is the key fact tying raw and dedup indices together via the shared class. -/
private theorem deduplicate_indexed_provenance
    (t : Toplevel) :
    let (tDedup, _remap) := t.deduplicate
    ∀ fi (_hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (_hj : j < t.functions.size),
        tDedup.functions[fi].layout = t.functions[j].layout ∧
        ∃ (hj_cls : j < (deduplicate_classes_of t).size),
          (deduplicate_classes_of t)[j]'hj_cls = fi := by
  show ∀ fi (_hfi : fi < t.deduplicate.1.functions.size),
    ∃ j, ∃ (_hj : j < t.functions.size),
      t.deduplicate.1.functions[fi].layout = t.functions[j].layout ∧
      ∃ (hj_cls : j < (deduplicate_classes_of t).size),
        (deduplicate_classes_of t)[j]'hj_cls = fi
  have hdedup_eq :
      t.deduplicate =
        if t.functions.size == 0 then (t, id)
        else
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let canonical := (deduplicate_canonical classes).1
          let remapFn := deduplicate_remap classes
          let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
          ({ t with functions := newFunctions }, remapFn) := rfl
  by_cases hn : t.functions.size = 0
  · rw [hdedup_eq]
    have hne : (t.functions.size == 0) = true := by simp [hn]
    rw [if_pos hne]
    intro fi hfi
    exact absurd hfi (hn ▸ Nat.not_lt_zero fi)
  · rw [hdedup_eq]
    have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
    rw [if_neg hne]
    simp only
    intro fi hfi
    -- Set up the classes array we'll feed to `deduplicate_newFunctions_indexed_provenance`.
    have hcls_sz :
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)).size = t.functions.size := by
      rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
    have hle : (partitionRefine
        (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => collectCalleesBlock f.body)).size ≤ t.functions.size := by
      rw [hcls_sz]; exact Nat.le_refl _
    have hprov := deduplicate_newFunctions_indexed_provenance
      t.functions
      (partitionRefine
        (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => collectCalleesBlock f.body))
      (deduplicate_remap
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)))
      hle
    simp only [IndexedProvenanceFromInput] at hprov
    obtain ⟨j, hj, hj_cls, _hbody, hlayout, hclasses⟩ := hprov fi hfi
    refine ⟨j, hj, hlayout, ?_⟩
    -- Convert `hj_cls` / `hclasses` stated in terms of `partitionRefine ...` into
    -- form keyed on `deduplicate_classes_of t`.
    have hdc_eq : deduplicate_classes_of t =
        partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body) := by
      unfold deduplicate_classes_of
      have hne' : (t.functions.size == 0) = false := by simp [hn]
      rw [hne']
      simp only [Bool.false_eq_true, ↓reduceIte]
    have hj_cls_dc : j < (deduplicate_classes_of t).size := by
      rw [hdc_eq]; exact hj_cls
    refine ⟨hj_cls_dc, ?_⟩
    -- Rewrite the getElem on the partitionRefine-form to getElem on
    -- `deduplicate_classes_of t` form via `hdc_eq`.
    have hgeq : (deduplicate_classes_of t)[j]'hj_cls_dc =
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body))[j]'hj_cls :=
      getElem_congr_coll hdc_eq
    rw [hgeq]
    exact hclasses

/-- Equation lemma: the second component of `t.deduplicate` is exactly
`deduplicate_remap` applied to the classes array. Follows by definitional
unfolding + `funext` on the empty-functions case. -/
private theorem deduplicate_snd_eq_remap (t : Toplevel) :
    (t.deduplicate).2 = deduplicate_remap (deduplicate_classes_of t) := by
  unfold Toplevel.deduplicate deduplicate_classes_of
  by_cases hn : t.functions.size = 0
  · have hne : (t.functions.size == 0) = true := by simp [hn]
    simp only [hne, ↓reduceIte]
    -- LHS: id. RHS: deduplicate_remap #[]. Show they agree via funext.
    funext i
    unfold deduplicate_remap
    simp
  · have hne : (t.functions.size == 0) = false := by simp [hn]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]

/-- Sub-lemma 3: `remap i = classes[i]` for in-range `i`. -/
theorem deduplicate_remap_eq_classes
    (t : Toplevel) :
    ∀ i (_hi : i < t.functions.size),
      (t.deduplicate).2 i = (deduplicate_classes_of t)[i]! := by
  intro i hi
  have hne : ¬ t.functions.size = 0 := fun h => absurd hi (h ▸ Nat.not_lt_zero i)
  have hcls_size : (deduplicate_classes_of t).size = t.functions.size := by
    unfold deduplicate_classes_of
    have hne_bool : (t.functions.size == 0) = false := by simp [hne]
    rw [hne_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
  have hi_cls : i < (deduplicate_classes_of t).size := hcls_size ▸ hi
  -- Step 1: fold-unfolding — prove the functional equation.
  have heq := deduplicate_snd_eq_remap t
  -- Step 2: apply at i — this gives equation with both sides reducing equally.
  have happ : (t.deduplicate).2 i = deduplicate_remap (deduplicate_classes_of t) i :=
    congrFun heq i
  -- Step 3: evaluate RHS via dite_pos.
  have heval : deduplicate_remap (deduplicate_classes_of t) i =
      (deduplicate_classes_of t)[i]! := by
    show (if h : i < (deduplicate_classes_of t).size
          then (deduplicate_classes_of t)[i]'h else i) = _
    rw [dif_pos hi_cls]
    exact (getElem!_pos _ i hi_cls).symm
  exact happ.trans heval

/-- Composed from the three sub-lemmas above. -/
private theorem deduplicate_loop_invariant
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    (∀ i, i < t.functions.size → remap i < tDedup.functions.size) ∧
    (∀ fi (_hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (_hj : j < t.functions.size),
        tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hremap := deduplicate_remap_eq_classes t i hi
    have hbound := deduplicate_top_cls_bound t i hi
    simp only at hbound ⊢
    exact hremap ▸ hbound
  · exact deduplicate_body_provenance t

/-- `Toplevel.deduplicate` maps in-range inputs to in-range outputs. -/
private theorem dedup_classes_lt_newFunctions_size
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ i, i < t.functions.size → remap i < tDedup.functions.size :=
  (deduplicate_loop_invariant t).1

private theorem dedup_remap_lt_size_stub
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (h : bytecodeRaw.deduplicate = (bytecodeDedup, remap)) :
    ∀ i, i < bytecodeRaw.functions.size → remap i < bytecodeDedup.functions.size := by
  have := dedup_classes_lt_newFunctions_size bytecodeRaw
  simp only [h] at this
  exact this

/-- Every dedup function body is `rewriteBlock remap` of some raw body.
Projected from `deduplicate_loop_invariant`. -/
private theorem dedup_body_from_raw_aux
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ fi (hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (hj : j < t.functions.size),
        tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body :=
  (deduplicate_loop_invariant t).2

/-- Strengthened provenance: dedup function body + layout both trace back to
the same raw-index witness. -/
private theorem dedup_body_and_layout_from_raw_aux
    (t : Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ fi (hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (hj : j < t.functions.size),
        tDedup.functions[fi].body = rewriteBlock remap t.functions[j].body ∧
        tDedup.functions[fi].layout = t.functions[j].layout :=
  deduplicate_layout_provenance t

/-- Indexed provenance: the raw-index witness `j` for position `fi` in dedup
satisfies `classes[j] = fi`, where `classes := deduplicate_classes_of t`. Plus
the usual body/layout pointwise match. This is the class-coupling fact that
the StructCompatible `deduplicate_layout_loop_invariant` needs to combine with
`skeleton_eq_of_same_class`. -/
theorem dedup_indexed_provenance_aux
    (t : Toplevel) :
    let (tDedup, _remap) := t.deduplicate
    ∀ fi (hfi : fi < tDedup.functions.size),
      ∃ j, ∃ (hj : j < t.functions.size),
        tDedup.functions[fi].layout = t.functions[j].layout ∧
        ∃ (hj_cls : j < (deduplicate_classes_of t).size),
          (deduplicate_classes_of t)[j]'hj_cls = fi :=
  deduplicate_indexed_provenance t

/-- Strengthened body provenance: the dedup function body at position `fi` equals
`rewriteBlock remap t.functions[j].body` for some `j` such that
`(deduplicate_classes_of t)[j] = fi`. This combines body provenance with class
equality in the SAME witness `j`, enabling the `.call` arm of
`dedup_mutual_congr` to bridge body-rewrite (via `partitionRefine_same_class_eval`)
with layout-match (via `skeleton_eq_of_same_class`) through a single class. -/
private theorem dedup_body_with_class_aux
    (t : Toplevel) :
    ∀ fi (hfi : fi < (t.deduplicate).1.functions.size),
      ∃ j, ∃ (hj : j < t.functions.size),
        (t.deduplicate).1.functions[fi].body =
          rewriteBlock (t.deduplicate).2 t.functions[j].body ∧
        ∃ (hj_cls : j < (deduplicate_classes_of t).size),
          (deduplicate_classes_of t)[j]'hj_cls = fi := by
  show ∀ fi (_hfi : fi < t.deduplicate.1.functions.size),
    ∃ j, ∃ (_hj : j < t.functions.size),
      t.deduplicate.1.functions[fi].body =
        rewriteBlock (t.deduplicate).2 t.functions[j].body ∧
      ∃ (hj_cls : j < (deduplicate_classes_of t).size),
        (deduplicate_classes_of t)[j]'hj_cls = fi
  have hdedup_eq :
      t.deduplicate =
        if t.functions.size == 0 then (t, id)
        else
          let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
          let initClasses := (assignClasses skeletons).1
          let callees := t.functions.map fun f => collectCalleesBlock f.body
          let classes := partitionRefine initClasses callees
          let canonical := (deduplicate_canonical classes).1
          let remapFn := deduplicate_remap classes
          let newFunctions := deduplicate_newFunctions t.functions classes canonical remapFn
          ({ t with functions := newFunctions }, remapFn) := rfl
  by_cases hn : t.functions.size = 0
  · intro fi hfi
    have hsz : (t.deduplicate).1.functions.size = 0 := by
      rw [hdedup_eq]
      have hne : (t.functions.size == 0) = true := by simp [hn]
      rw [if_pos hne]
      exact hn
    exact absurd hfi (hsz ▸ Nat.not_lt_zero fi)
  · intro fi hfi
    have hcls_sz :
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)).size = t.functions.size := by
      rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
    have hle : (partitionRefine
        (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => collectCalleesBlock f.body)).size ≤ t.functions.size := by
      rw [hcls_sz]; exact Nat.le_refl _
    have hprov := deduplicate_newFunctions_indexed_provenance
      t.functions
      (partitionRefine
        (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => collectCalleesBlock f.body))
      (deduplicate_remap
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body)))
      hle
    simp only [IndexedProvenanceFromInput] at hprov
    -- Compute the size of dedup functions under the non-empty branch.
    have hfi' : fi < (deduplicate_newFunctions t.functions
        (partitionRefine
          (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
          (t.functions.map fun f => collectCalleesBlock f.body))
        (deduplicate_canonical
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body))).1
        (deduplicate_remap
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body)))).size := by
      have : (t.deduplicate).1.functions.size = (deduplicate_newFunctions t.functions
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body))
          (deduplicate_canonical
            (partitionRefine
              (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
              (t.functions.map fun f => collectCalleesBlock f.body))).1
          (deduplicate_remap
            (partitionRefine
              (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
              (t.functions.map fun f => collectCalleesBlock f.body)))).size := by
        rw [hdedup_eq]
        have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
        rw [if_neg hne]
      rw [← this]; exact hfi
    obtain ⟨j, hj, hj_cls, hbody, _hlayout, hclasses⟩ := hprov fi hfi'
    refine ⟨j, hj, ?_, ?_⟩
    · -- Body match. Rewrite t.deduplicate.1.functions[fi].body via hbody.
      -- Need: t.deduplicate.1.functions[fi].body = rewriteBlock (t.deduplicate).2 t.functions[j].body
      -- hbody gives: (deduplicate_newFunctions ...)[fi].body = rewriteBlock (deduplicate_remap ...) t.functions[j].body
      -- Under non-empty branch, t.deduplicate.1.functions = deduplicate_newFunctions ... and (t.deduplicate).2 = deduplicate_remap ...
      have hfun_eq : (t.deduplicate).1.functions = deduplicate_newFunctions t.functions
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body))
          (deduplicate_canonical
            (partitionRefine
              (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
              (t.functions.map fun f => collectCalleesBlock f.body))).1
          (deduplicate_remap
            (partitionRefine
              (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
              (t.functions.map fun f => collectCalleesBlock f.body))) := by
        rw [hdedup_eq]
        have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
        rw [if_neg hne]
      have hremap_eq : (t.deduplicate).2 = deduplicate_remap
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body)) := by
        rw [hdedup_eq]
        have hne : ¬ (t.functions.size == 0) = true := by simp [hn]
        rw [if_neg hne]
      have hgb : (t.deduplicate).1.functions[fi]'hfi =
          (deduplicate_newFunctions t.functions
            (partitionRefine
              (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
              (t.functions.map fun f => collectCalleesBlock f.body))
            (deduplicate_canonical
              (partitionRefine
                (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
                (t.functions.map fun f => collectCalleesBlock f.body))).1
            (deduplicate_remap
              (partitionRefine
                (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
                (t.functions.map fun f => collectCalleesBlock f.body))))[fi]'hfi' :=
        getElem_congr_coll hfun_eq
      rw [hgb, hbody, hremap_eq]
    · have hdc_eq : deduplicate_classes_of t =
          partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body) := by
        unfold deduplicate_classes_of
        have hne' : (t.functions.size == 0) = false := by simp [hn]
        rw [hne']
        simp only [Bool.false_eq_true, ↓reduceIte]
      have hj_cls_dc : j < (deduplicate_classes_of t).size := by
        rw [hdc_eq]; exact hj_cls
      refine ⟨hj_cls_dc, ?_⟩
      have hgeq : (deduplicate_classes_of t)[j]'hj_cls_dc =
          (partitionRefine
            (assignClasses (t.functions.map fun f => (skeletonBlock f.body, f.layout))).1
            (t.functions.map fun f => collectCalleesBlock f.body))[j]'hj_cls :=
        getElem_congr_coll hdc_eq
      rw [hgeq]
      exact hclasses

/-! ## Mutual congruence + derived `.ok`-transport theorems.
These are placed AFTER the provenance helpers because they depend on
`dedup_classes_lt_newFunctions_size`, `dedup_indexed_provenance_aux`,
`dedup_body_with_class_aux`, and `deduplicate_remap_eq_classes`. -/

/-- Consolidated mutual congruence: for `t.deduplicate = (tDedup, remap)`, the
three eval functions agree between `t` and `tDedup` modulo `rewriteOp`/
`rewriteBlock`/`rewriteCtrl remap`. Proved by a single
`Bytecode.Eval.evalOp.mutual_induct` with 6 coordinated motives (op/block/ctrl/
matchArm/defaultBlock/runOps). The individual congruence theorems below are
trivial projections from this.

Weakened to one-directional `.ok`-transport to sidestep the arity-mismatch
error-payload divergence (raw-side raises `.arityMismatch funIdx`, dedup-side
raises `.arityMismatch (remap funIdx)`). The `.call` arm composes
`dedup_body_with_class_aux` + `dedup_indexed_provenance_aux` +
`partitionRefine_same_class_eval` + `skeleton_eq_of_same_class` + block IH. -/
private theorem dedup_mutual_congr
    (t : Toplevel)
    (_hwf : WellFormedCallees t)
    (_hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
             let (initClasses, _) := assignClasses skeletons
             let callees := t.functions.map fun f => collectCalleesBlock f.body
             let classes := partitionRefine initClasses callees
             let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
             (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    (∀ fuel op st x,
      Bytecode.Eval.evalOp t fuel op st = .ok x →
        Bytecode.Eval.evalOp tDedup fuel (rewriteOp remap op) st = .ok x)
    ∧ (∀ fuel b st x,
      Bytecode.Eval.evalBlock t fuel b st = .ok x →
        Bytecode.Eval.evalBlock tDedup fuel (rewriteBlock remap b) st = .ok x)
    ∧ (∀ fuel c st x,
      Bytecode.Eval.evalCtrl t fuel c st = .ok x →
        Bytecode.Eval.evalCtrl tDedup fuel (rewriteCtrl remap c) st = .ok x) := by
  let tDedup : Bytecode.Toplevel := t.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := t.deduplicate.2
  show (∀ fuel op st x,
      Bytecode.Eval.evalOp t fuel op st = .ok x →
        Bytecode.Eval.evalOp tDedup fuel (rewriteOp remap op) st = .ok x)
    ∧ (∀ fuel b st x,
      Bytecode.Eval.evalBlock t fuel b st = .ok x →
        Bytecode.Eval.evalBlock tDedup fuel (rewriteBlock remap b) st = .ok x)
    ∧ (∀ fuel c st x,
      Bytecode.Eval.evalCtrl t fuel c st = .ok x →
        Bytecode.Eval.evalCtrl tDedup fuel (rewriteCtrl remap c) st = .ok x)
  have big :=
    @Bytecode.Eval.evalOp.mutual_induct t
      (fun fuel op st => ∀ x,
        Bytecode.Eval.evalOp t fuel op st = .ok x →
          Bytecode.Eval.evalOp tDedup fuel (rewriteOp remap op) st = .ok x)
      (fun fuel b st => ∀ x,
        Bytecode.Eval.evalBlock t fuel b st = .ok x →
          Bytecode.Eval.evalBlock tDedup fuel (rewriteBlock remap b) st = .ok x)
      (fun fuel c st => ∀ x,
        Bytecode.Eval.evalCtrl t fuel c st = .ok x →
          Bytecode.Eval.evalCtrl tDedup fuel (rewriteCtrl remap c) st = .ok x)
      (fun fuel cases db scrut st i => ∀ x,
        Bytecode.Eval.evalMatchArm t fuel cases db scrut st i = .ok x →
          Bytecode.Eval.evalMatchArm tDedup fuel
            (cases.attach.map (fun ⟨(g, b), _⟩ => (g, rewriteBlock remap b)))
            (match db with | none => none | some b => some (rewriteBlock remap b))
            scrut st i = .ok x)
      (fun fuel db st => ∀ x,
        Bytecode.Eval.evalDefaultBlock t fuel db st = .ok x →
          Bytecode.Eval.evalDefaultBlock tDedup fuel
            (match db with | none => none | some b => some (rewriteBlock remap b)) st = .ok x)
      (fun fuel ops st i => ∀ x,
        Bytecode.Eval.runOps t fuel ops st i = .ok x →
          Bytecode.Eval.runOps tDedup fuel (ops.map (rewriteOp remap)) st i = .ok x)
  have P := big
    -- const
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- add / sub / mul / eqZero
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- Op.call: the crux.
    (fun fuel st fi args outSz uc _ih => by
      intro x hax
      simp only [rewriteOp]
      unfold Bytecode.Eval.evalOp at hax ⊢
      cases hreadIdx : Bytecode.Eval.readIdxs st args with
      | error e =>
        simp only [hreadIdx, bind, Except.bind] at hax
        cases hax
      | ok argGs =>
        simp only [hreadIdx, bind, Except.bind] at hax ⊢
        by_cases hfi : fi < t.functions.size
        · simp only [hfi, ↓reduceDIte] at hax
          by_cases harity : (t.functions[fi].layout.inputSize != argGs.size) = true
          · simp only [harity, ↓reduceIte] at hax
            cases hax
          · have harity_false : (t.functions[fi].layout.inputSize != argGs.size) = false := by
              cases h : (t.functions[fi].layout.inputSize != argGs.size)
              · rfl
              · exact absurd h harity
            simp only [harity_false, Bool.false_eq_true, ↓reduceIte] at hax
            cases fuel with
            | zero => simp only at hax; cases hax
            | succ fuel' =>
              simp only at hax
              cases hbod : Bytecode.Eval.evalBlock t fuel' t.functions[fi].body
                            { map := argGs, memory := st.memory, ioBuffer := st.ioBuffer } with
              | error e =>
                simp only [hbod] at hax; cases hax
              | ok inner =>
                simp only [hbod] at hax
                obtain ⟨outs, innerSt'⟩ := inner
                by_cases houtSz : (outs.size != outSz) = true
                · simp only [houtSz, ↓reduceIte] at hax; cases hax
                · have houtSz_false : (outs.size != outSz) = false := by
                    cases h : (outs.size != outSz)
                    · rfl
                    · exact absurd h houtSz
                  simp only [houtSz_false, Bool.false_eq_true, ↓reduceIte] at hax
                  have hremap_fi_lt : remap fi < tDedup.functions.size :=
                    dedup_classes_lt_newFunctions_size t fi hfi
                  have hbody_prov := dedup_body_with_class_aux t (remap fi) hremap_fi_lt
                  obtain ⟨j, hj, hbody_j, hj_cls, hcls_eq⟩ := hbody_prov
                  have hremap_j_eq : remap j = remap fi := by
                    have hre : remap j = (deduplicate_classes_of t)[j]! :=
                      deduplicate_remap_eq_classes t j hj
                    rw [hre, getElem!_pos _ j hj_cls]
                    exact hcls_eq
                  have hprov := dedup_indexed_provenance_aux t (remap fi) hremap_fi_lt
                  obtain ⟨j2, hj2, hlayout_j2, hj2_cls, hcls2_eq⟩ := hprov
                  have hremap_j2_eq : remap j2 = remap fi := by
                    have hre : remap j2 = (deduplicate_classes_of t)[j2]! :=
                      deduplicate_remap_eq_classes t j2 hj2
                    rw [hre, getElem!_pos _ j2 hj2_cls]
                    exact hcls2_eq
                  have hsk2 := skeleton_eq_of_same_class t _hfix fi j2 hfi hj2 hremap_j2_eq.symm
                  have hlayout_dedup : tDedup.functions[remap fi].layout =
                      t.functions[fi].layout :=
                    hlayout_j2.trans hsk2.2.symm
                  have harity_dedup :
                      (tDedup.functions[remap fi].layout.inputSize != argGs.size) = false := by
                    rw [hlayout_dedup]; exact harity_false
                  simp only [hremap_fi_lt, ↓reduceDIte, harity_dedup, Bool.false_eq_true,
                    ↓reduceIte]
                  rw [hbody_j]
                  have hbridge :
                      Bytecode.Eval.evalBlock tDedup fuel' (rewriteBlock remap t.functions[fi].body)
                          { map := argGs, memory := st.memory, ioBuffer := st.ioBuffer } =
                        Bytecode.Eval.evalBlock tDedup fuel' (rewriteBlock remap t.functions[j].body)
                          { map := argGs, memory := st.memory, ioBuffer := st.ioBuffer } := by
                    have := partitionRefine_same_class_eval t _hwf _hfix fi j hfi hj
                              hremap_j_eq.symm fuel'
                              { map := argGs, memory := st.memory, ioBuffer := st.ioBuffer }
                    exact this
                  rw [← hbridge]
                  have ih_inst := _ih argGs hfi
                  simp only at ih_inst
                  have hdedup_block := ih_inst (outs, innerSt') hbod
                  rw [hdedup_block]
                  simp only [houtSz_false, Bool.false_eq_true, ↓reduceIte]
                  exact hax
        · simp only [hfi, ↓reduceDIte] at hax
          cases hax)
    -- store / load / assertEq
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- ioGetInfo / ioSetInfo / ioRead / ioWrite
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- u8BitDecomposition / u8ShiftLeft / u8ShiftRight
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- u8Xor / u8Add / u8Sub / u8And / u8Or / u8LessThan / u32LessThan
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- debug
    (fun _ _ _ _ x hax => by simp only [rewriteOp]; unfold Bytecode.Eval.evalOp at hax ⊢; exact hax)
    -- Block arms: runOps-err / runOps-ok
    (fun _fuel _b _st _e herr _ih_ops x hax => by
      unfold Bytecode.Eval.evalBlock at hax
      simp only [herr] at hax
      cases hax)
    (fun _fuel _b _st _st' hok ih_ops ih_ctrl x hax => by
      unfold Bytecode.Eval.evalBlock at hax ⊢
      simp only [rewriteBlock]
      simp only [hok] at hax
      have hok' := ih_ops _st' hok
      rw [hok']
      exact ih_ctrl x hax)
    -- Ctrl arms
    (fun _ _ _ _ _ herr _ hax => by
      simp only [rewriteCtrl]
      unfold Bytecode.Eval.evalCtrl at hax
      simp only [herr] at hax
      cases hax)
    (fun _ _ _ _ _ hok _ hax => by
      simp only [rewriteCtrl]
      unfold Bytecode.Eval.evalCtrl at hax ⊢
      simp only [hok] at hax ⊢
      exact hax)
    (fun _ _ _ _ _ herr _ hax => by
      simp only [rewriteCtrl]
      unfold Bytecode.Eval.evalCtrl at hax
      simp only [herr] at hax
      cases hax)
    (fun _ _ _ _ _ hok _ hax => by
      simp only [rewriteCtrl]
      unfold Bytecode.Eval.evalCtrl at hax ⊢
      simp only [hok] at hax ⊢
      exact hax)
    (fun _ _ _ _ _ _ herr _ hax => by
      unfold rewriteCtrl
      unfold Bytecode.Eval.evalCtrl at hax
      simp only [herr] at hax
      cases hax)
    -- match-ok
    (fun _fuel _st _scrutIdx _cases _db _scrut hok ih_arm x hax => by
      unfold rewriteCtrl
      unfold Bytecode.Eval.evalCtrl at hax ⊢
      simp only [hok] at hax ⊢
      exact ih_arm x hax)
    -- matchContinue-err on scrut
    (fun _fuel _st _scrutIdx _branches _db _outputSize _sharedAux _sharedLookups _cont
         _scrut herr _x hax => by
      cases _db
      all_goals {
        unfold rewriteCtrl at *
        unfold Bytecode.Eval.evalCtrl at hax
        simp only [herr] at hax
        cases hax
      })
    -- matchContinue-err2
    (fun _fuel _st _scrutIdx _branches _db _outputSize _sharedAux _sharedLookups _cont
        _scrut hok _e harm _ih_arm _ hax => by
      cases _db
      all_goals {
        unfold rewriteCtrl at *
        unfold Bytecode.Eval.evalCtrl at hax
        simp only [hok, harm] at hax
        cases hax
      })
    -- matchContinue-ok
    (fun _fuel _st _scrutIdx _branches _db _outputSize _sharedAux _sharedLookups _cont
        _scrut hok _gs _st' harm ih_arm ih_block x hax => by
      cases _db
      all_goals {
        unfold rewriteCtrl at *
        unfold Bytecode.Eval.evalCtrl at hax ⊢
        simp only [hok] at hax ⊢
        have harm' := ih_arm (_gs, _st') harm
        rw [harm']
        simp only [harm] at hax
        exact ih_block x hax
      })
    -- MatchArm hit
    (fun _fuel cases _db _scrut _st i hlt heq ih_hit x hax => by
      unfold Bytecode.Eval.evalMatchArm at hax ⊢
      have hlt' : i < (cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block))).size := by
        rw [Array.size_map, Array.size_attach]; exact hlt
      simp only [hlt, hlt', ↓reduceDIte] at hax ⊢
      have hgetelem : (cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block)))[i]'hlt' =
          (cases[i].1, rewriteBlock remap cases[i].2) := by
        rw [Array.getElem_map, Array.getElem_attach]
      rw [hgetelem]
      simp only [heq, ↓reduceIte] at hax ⊢
      exact ih_hit x hax)
    -- MatchArm miss
    (fun _fuel cases _db _scrut _st i hlt hne ih_rec x hax => by
      unfold Bytecode.Eval.evalMatchArm at hax ⊢
      have hattach : cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block)) =
          cases.map (fun (gb : G × Block) => (gb.1, rewriteBlock remap gb.2)) :=
        branches_attach_map_rewrite_eq_map remap cases
      have hlt' : i < (cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block))).size := by
        rw [hattach, Array.size_map]; exact hlt
      simp only [hlt, hlt', ↓reduceDIte] at hax ⊢
      have hgetelem : (cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block)))[i]'hlt' =
          (cases[i].1, rewriteBlock remap cases[i].2) := by
        rw [Array.getElem_map, Array.getElem_attach]
      rw [hgetelem]
      simp only [hne] at hax ⊢
      exact ih_rec x hax)
    -- MatchArm oob
    (fun _fuel cases _db _scrut _st i hnot ih_def x hax => by
      unfold Bytecode.Eval.evalMatchArm at hax ⊢
      have hnot' : ¬ i < (cases.attach.map (fun (x : {x // x ∈ cases}) =>
          ((x.val.1, rewriteBlock remap x.val.2) : G × Block))).size := by
        rw [Array.size_map, Array.size_attach]; exact hnot
      simp only [hnot, hnot', ↓reduceDIte] at hax ⊢
      exact ih_def x hax)
    -- DefaultBlock some
    (fun _fuel _st _block ih_block x hax => by
      unfold Bytecode.Eval.evalDefaultBlock at hax ⊢
      exact ih_block x hax)
    -- DefaultBlock none
    (fun _ _ x hax => by
      simp only [Bytecode.Eval.evalDefaultBlock] at hax
      cases hax)
    -- runOps-err
    (fun _fuel ops st i h _e herr _ih_op x hax => by
      unfold Bytecode.Eval.runOps at hax
      simp only [h, ↓reduceDIte, herr] at hax
      cases hax)
    -- runOps-ok
    (fun _fuel ops st i h st' hok ih_op ih_rest x hax => by
      unfold Bytecode.Eval.runOps at hax ⊢
      have hmap : i < (ops.map (rewriteOp remap)).size := by
        rw [Array.size_map]; exact h
      simp only [h, hmap, ↓reduceDIte] at hax ⊢
      rw [Array.getElem_map]
      simp only [hok] at hax
      have hok' := ih_op st' hok
      rw [hok']
      exact ih_rest x hax)
    -- runOps-oob
    (fun _fuel ops _st i hnot x hax => by
      unfold Bytecode.Eval.runOps at hax ⊢
      have hnot' : ¬ i < (ops.map (rewriteOp remap)).size := by
        rw [Array.size_map]; exact hnot
      simp only [hnot, hnot', ↓reduceDIte] at hax ⊢
      exact hax)
  exact ⟨P.1, P.2.1, P.2.2.1⟩

/-- Op-level `.ok`-transport, projected from `dedup_mutual_congr`. -/
private theorem evalOp_congr
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    ∀ fuel op st x,
      Eval.evalOp t fuel op st = .ok x →
        Eval.evalOp tDedup fuel (rewriteOp remap op) st = .ok x :=
  (dedup_mutual_congr t hwf hfix).1

/-- Block-level `.ok`-transport, projected from `dedup_mutual_congr`. -/
private theorem evalBlock_congr
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    ∀ fuel b st x,
      Eval.evalBlock t fuel b st = .ok x →
        Eval.evalBlock tDedup fuel (rewriteBlock remap b) st = .ok x :=
  (dedup_mutual_congr t hwf hfix).2.1

/-- Ctrl-level `.ok`-transport, projected from `dedup_mutual_congr`. -/
private theorem evalCtrl_congr
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    ∀ fuel c st x,
      Eval.evalCtrl t fuel c st = .ok x →
        Eval.evalCtrl tDedup fuel (rewriteCtrl remap c) st = .ok x :=
  (dedup_mutual_congr t hwf hfix).2.2

/-- Driver: block-level `.ok`-transport for every raw-toplevel body. Direct
projection from `evalBlock_congr` applied at `t.functions[fi].body`. -/
private theorem runFunction_congr_at_fuel
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (tDedup, remap) := t.deduplicate
    ∀ fuel fi (_hfi : fi < t.functions.size) st x,
      Eval.evalBlock t fuel t.functions[fi].body st = .ok x →
        Eval.evalBlock tDedup fuel (rewriteBlock remap t.functions[fi].body) st = .ok x := by
  intro fuel fi _hfi st x hx
  exact (evalBlock_congr t hwf hfix) fuel t.functions[fi].body st x hx

/-- Bisimulation: `runFunction` `.ok`-transports between `t` and its dedup under
`remap`. Composed from `runFunction_congr_at_fuel` + range/body/layout
preservation helpers. Upstream fixes applied (both prior findings resolved):
(1) Layout preservation: dedup's skeleton key now includes full
    `FunctionLayout` (Compiler/Dedup.lean:211), so same-class functions
    share every layout field.
(2) `remap` out-of-domain: `remapFn i` returns `i` for `i ≥ classes.size`
    (Compiler/Dedup.lean:227), making out-of-range agreement vacuous. -/
private theorem eval_congr_dedup
    (t : Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes) :
    let (t', remap) := t.deduplicate
    ∀ fuel funIdx args io x,
      Eval.runFunction t funIdx args io fuel = .ok x →
        Eval.runFunction t' (remap funIdx) args io fuel = .ok x := by
  intro fuel funIdx args io x hrun
  show Eval.runFunction (t.deduplicate).1 ((t.deduplicate).2 funIdx) args io fuel = .ok x
  unfold Eval.runFunction at hrun ⊢
  by_cases hfi : funIdx < t.functions.size
  · simp only [hfi, ↓reduceDIte] at hrun
    by_cases harity : (t.functions[funIdx].layout.inputSize != args.size) = true
    · simp only [harity, ↓reduceIte] at hrun; cases hrun
    · have harity_false : (t.functions[funIdx].layout.inputSize != args.size) = false := by
        cases h : (t.functions[funIdx].layout.inputSize != args.size)
        · rfl
        · exact absurd h harity
      simp only [harity_false, Bool.false_eq_true, ↓reduceIte] at hrun
      cases hbod : Eval.evalBlock t fuel t.functions[funIdx].body
                    { map := args, ioBuffer := io } with
      | error e => simp only [hbod] at hrun; cases hrun
      | ok inner =>
        simp only [hbod] at hrun
        obtain ⟨outs, innerSt'⟩ := inner
        have hremap_fi_lt : (t.deduplicate).2 funIdx < (t.deduplicate).1.functions.size :=
          dedup_classes_lt_newFunctions_size t funIdx hfi
        simp only [hremap_fi_lt, ↓reduceDIte]
        have hprov := dedup_indexed_provenance_aux t ((t.deduplicate).2 funIdx) hremap_fi_lt
        obtain ⟨j2, hj2, hlayout_j2, hj2_cls, hcls2_eq⟩ := hprov
        have hremap_j2_eq : (t.deduplicate).2 j2 = (t.deduplicate).2 funIdx := by
          have hre : (t.deduplicate).2 j2 = (deduplicate_classes_of t)[j2]! :=
            deduplicate_remap_eq_classes t j2 hj2
          rw [hre, getElem!_pos _ j2 hj2_cls]
          exact hcls2_eq
        have hsk2 := skeleton_eq_of_same_class t hfix funIdx j2 hfi hj2 hremap_j2_eq.symm
        have hlayout_dedup :
            (t.deduplicate).1.functions[(t.deduplicate).2 funIdx].layout =
              t.functions[funIdx].layout :=
          hlayout_j2.trans hsk2.2.symm
        have harity_dedup :
            ((t.deduplicate).1.functions[(t.deduplicate).2 funIdx].layout.inputSize
              != args.size) = false := by
          rw [hlayout_dedup]; exact harity_false
        simp only [harity_dedup, Bool.false_eq_true, ↓reduceIte]
        have hbody_prov := dedup_body_with_class_aux t ((t.deduplicate).2 funIdx) hremap_fi_lt
        obtain ⟨j, hj, hbody_j, hj_cls, hcls_eq⟩ := hbody_prov
        have hremap_j_eq : (t.deduplicate).2 j = (t.deduplicate).2 funIdx := by
          have hre : (t.deduplicate).2 j = (deduplicate_classes_of t)[j]! :=
            deduplicate_remap_eq_classes t j hj
          rw [hre, getElem!_pos _ j hj_cls]
          exact hcls_eq
        have hdedup_block_at_j :
            Eval.evalBlock (t.deduplicate).1 fuel
                (rewriteBlock (t.deduplicate).2 t.functions[j].body)
                { map := args, ioBuffer := io } = .ok (outs, innerSt') := by
          have hmc := (dedup_mutual_congr t hwf hfix).2.1
          have hdedup_block_fi := hmc fuel t.functions[funIdx].body
                                      { map := args, ioBuffer := io } (outs, innerSt') hbod
          have hbridge :
              Eval.evalBlock (t.deduplicate).1 fuel
                  (rewriteBlock (t.deduplicate).2 t.functions[funIdx].body)
                  { map := args, ioBuffer := io } =
                Eval.evalBlock (t.deduplicate).1 fuel
                  (rewriteBlock (t.deduplicate).2 t.functions[j].body)
                  { map := args, ioBuffer := io } := by
            have := partitionRefine_same_class_eval t hwf hfix funIdx j hfi hj
                      hremap_j_eq.symm fuel { map := args, ioBuffer := io }
            exact this
          rw [← hbridge]; exact hdedup_block_fi
        have hbody_eq :
            Eval.evalBlock (t.deduplicate).1 fuel
                (t.deduplicate).1.functions[(t.deduplicate).2 funIdx].body
                { map := args, ioBuffer := io } = .ok (outs, innerSt') := by
          rw [hbody_j]; exact hdedup_block_at_j
        rw [hbody_eq]
        simp only at hrun ⊢
        exact hrun
  · simp only [hfi, ↓reduceDIte] at hrun
    cases hrun

/-- Preservation: deduplication preserves bytecode `.ok` observations when
reachable via the index remap function.

Weakened from an equational bisimulation to one-directional `.ok`-transport:
for any input that yields `.ok x` on the raw toplevel, the dedup toplevel
produces the same `.ok x` at the remapped index. The weakening sidesteps the
error-payload divergence (raw side raises `.error (.arityMismatch funIdx)`
while dedup raises `.error (.arityMismatch (remap funIdx))`) — the compiler-
correctness chain cares only about output preservation.

The proof is a bisimulation up to call-index renaming. The key invariant:
if `partitionRefine` assigns `i` and `j` to the same equivalence class,
then `t.functions[i].body` and `t.functions[j].body` (after `rewrite remap`)
produce identical observations on identical inputs at every fuel level.

Cycles in the call graph are handled by well-founded induction on `fuel`:
the `Op.call` case decreases `fuel` by 1, so the IH at `fuel - 1` discharges
the recursive equivalence regardless of self/mutual recursion. -/
theorem Bytecode.Toplevel.deduplicate_preservation
    (t : Bytecode.Toplevel)
    (hwf : WellFormedCallees t)
    (hfix : let skeletons := t.functions.map fun f => (skeletonBlock f.body, f.layout)
            let (initClasses, _) := assignClasses skeletons
            let callees := t.functions.map fun f => collectCalleesBlock f.body
            let classes := partitionRefine initClasses callees
            let signatures := classes.mapIdx fun i cls => (cls, callees[i]!.map (classes[·]!))
            (assignClasses signatures).1 = classes)
    (funIdx : FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) (x : Array G × IOBuffer) :
    let (t', remap) := t.deduplicate
    Eval.runFunction t funIdx args io fuel = .ok x →
      Eval.runFunction t' (remap funIdx) args io fuel = .ok x := by
  have := eval_congr_dedup t hwf hfix
  simp only at this
  exact this fuel funIdx args io x

/-- The op-level callee collector used by `Block.collectAllCallees`. -/
private abbrev callCollector : Array FunIdx → Op → Array FunIdx := fun acc op =>
  match op with | .call idx _ _ _ => acc.push idx | _ => acc

/-- Generalized list-level foldl lemma: if every element of `acc1` has a
preimage via `f` in `acc2`, then every element of
`foldl callCollector acc1 (ops.map (rewriteOp f))` has a preimage in
`foldl callCollector acc2 ops`. -/
private theorem list_foldl_rewriteOp_mem_gen
    (f : FunIdx → FunIdx) (ops : List Op) (acc1 acc2 : Array FunIdx)
    (hacc : ∀ c, c ∈ acc1 → ∃ c', c' ∈ acc2 ∧ c = f c') :
    ∀ c, c ∈ List.foldl callCollector acc1 (ops.map (rewriteOp f)) →
    ∃ c', c' ∈ List.foldl callCollector acc2 ops ∧ c = f c' := by
  induction ops generalizing acc1 acc2 with
  | nil => simp [List.foldl]; exact hacc
  | cons op ops ih =>
    simp only [List.map_cons, List.foldl_cons]
    cases op with
    | call idx args sz u =>
      simp only [rewriteOp, callCollector]
      exact ih (acc1.push (f idx)) (acc2.push idx) (fun c hc' => by
        rw [Array.mem_push] at hc'
        cases hc' with
        | inl h =>
          have ⟨c', hc'', heq⟩ := hacc c h
          exact ⟨c', Array.mem_push.mpr (Or.inl hc''), heq⟩
        | inr h => exact ⟨idx, Array.mem_push.mpr (Or.inr rfl), h⟩)
    | _ => simp only [rewriteOp, callCollector]; exact ih acc1 acc2 hacc

private theorem foldl_rewriteOp_callee_mem
    (f : FunIdx → FunIdx) (ops : Array Op) (c : FunIdx) :
    c ∈ (ops.map (rewriteOp f)).foldl (init := #[]) (fun acc op =>
      match op with | .call idx _ _ _ => acc.push idx | _ => acc) →
    ∃ c', c' ∈ ops.foldl (init := #[]) (fun acc op =>
      match op with | .call idx _ _ _ => acc.push idx | _ => acc) ∧ c = f c' := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  exact list_foldl_rewriteOp_mem_gen f ops.toList #[] #[]
    (fun c hc => absurd hc (Array.not_mem_empty c)) c

/-- Generalized list-level foldl for branch callees. -/
private theorem list_foldl_branch_callees_mem
    (f : FunIdx → FunIdx)
    (branches : List (G × Block))
    (ih_branches : ∀ p ∈ branches, ∀ x,
      x ∈ Block.collectAllCallees (rewriteBlock f p.2) →
      ∃ x', x' ∈ Block.collectAllCallees p.2 ∧ x = f x')
    (acc1 acc2 : Array FunIdx)
    (hacc : ∀ x, x ∈ acc1 → ∃ x', x' ∈ acc2 ∧ x = f x') :
    ∀ x,
      x ∈ List.foldl (fun acc (p : G × Block) =>
        acc ++ Block.collectAllCallees (rewriteBlock f p.2)) acc1 branches →
      ∃ x', x' ∈ List.foldl (fun acc (p : G × Block) =>
        acc ++ Block.collectAllCallees p.2) acc2 branches ∧ x = f x' := by
  induction branches generalizing acc1 acc2 with
  | nil => simp [List.foldl]; exact hacc
  | cons p branches ih_list =>
    simp only [List.foldl_cons]
    intro x hx
    have ih_p := ih_branches p (List.mem_cons.mpr (Or.inl rfl))
    have hacc' : ∀ x,
        x ∈ acc1 ++ Block.collectAllCallees (rewriteBlock f p.2) →
        ∃ x', x' ∈ acc2 ++ Block.collectAllCallees p.2 ∧ x = f x' := by
      intro x hx'
      rw [Array.mem_append] at hx'
      cases hx' with
      | inl h =>
        have ⟨x', hx', heq⟩ := hacc x h
        exact ⟨x', Array.mem_append.mpr (Or.inl hx'), heq⟩
      | inr h =>
        have ⟨x', hx', heq⟩ := ih_p x h
        exact ⟨x', Array.mem_append.mpr (Or.inr hx'), heq⟩
    exact ih_list (fun q hq => ih_branches q (List.mem_cons.mpr (Or.inr hq)))
      (acc1 ++ Block.collectAllCallees (rewriteBlock f p.2))
      (acc2 ++ Block.collectAllCallees p.2)
      hacc' x hx

/-- Helper: `List.foldl` over `attachWith` equals the plain `List.foldl`. -/
private theorem list_foldl_attachWith_eq
    {α β} (l : List α) (P : α → Prop) (H : ∀ x ∈ l, P x)
    (g : β → α → β) (acc : β) :
    (l.attachWith P H).foldl (fun acc x => g acc x.1) acc =
    l.foldl g acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.attachWith_cons, List.foldl_cons]
    exact ih (fun y hy => H y (List.mem_cons.mpr (Or.inr hy))) (g acc x)

/-- Bridge: `Array.attach.foldl` over branch callees equals `List.foldl` over
the array's `toList`. -/
private theorem attach_foldl_collectAllCallees_eq
    (branches : Array (G × Block)) (acc : Array FunIdx) :
    branches.attach.foldl (init := acc) (fun acc ⟨(_, block), _⟩ =>
      acc ++ block.collectAllCallees) =
    List.foldl (fun acc (p : G × Block) => acc ++ p.2.collectAllCallees)
      acc branches.toList := by
  rw [← Array.foldl_toList, Array.toList_attach]
  exact list_foldl_attachWith_eq branches.toList (· ∈ branches) _
    (fun acc (p : G × Block) => acc ++ p.2.collectAllCallees) acc

/-- Bridge for the rewritten branches (attach.map.attach.foldl). -/
private theorem attach_foldl_rewrite_collectAllCallees_eq
    (f : FunIdx → FunIdx) (branches : Array (G × Block)) (acc : Array FunIdx) :
    (branches.attach.map fun ⟨(g, b), _⟩ => (g, rewriteBlock f b)).attach.foldl
      (init := acc) (fun acc ⟨(_, block), _⟩ => acc ++ block.collectAllCallees) =
    List.foldl (fun acc (p : G × Block) =>
      acc ++ Block.collectAllCallees (rewriteBlock f p.2))
      acc branches.toList := by
  rw [← Array.foldl_toList, Array.toList_attach,
      list_foldl_attachWith_eq _ _ _
        (fun acc (p : G × Block) => acc ++ p.2.collectAllCallees) acc]
  rw [Array.toList_map, Array.toList_attach]
  rw [List.foldl_map]
  exact list_foldl_attachWith_eq branches.toList (· ∈ branches) _
    (fun acc (p : G × Block) =>
      acc ++ Block.collectAllCallees (rewriteBlock f p.2)) acc

/-- Termination helper. -/
private theorem sizeOf_ctrl_lt (b : Block) : sizeOf b.ctrl < sizeOf b := by
  rcases b with ⟨ops, ctrl⟩; show sizeOf ctrl < 1 + sizeOf ops + sizeOf ctrl; omega

/-! Mutual induction: `rewriteBlock`/`rewriteCtrl` preserve the callee-preimage
property. Modulo `attach_foldl` bridges (sorried above), the structural
reasoning is complete: ops via `foldl_rewriteOp_callee_mem`, branches via
`list_foldl_branch_callees_mem`, ctrl/block via mutual well-founded recursion. -/
mutual
private theorem rewriteBlock_callee_mem_aux
    (f : FunIdx → FunIdx) (b : Block) (x : FunIdx) :
    x ∈ Block.collectAllCallees (rewriteBlock f b) →
    ∃ x', x' ∈ Block.collectAllCallees b ∧ x = f x' := by
  unfold rewriteBlock Block.collectAllCallees
  intro hmem
  rw [Array.mem_append] at hmem
  cases hmem with
  | inl hop =>
    have ⟨c', hc'_mem, hc'_eq⟩ := foldl_rewriteOp_callee_mem f b.ops x hop
    exact ⟨c', Array.mem_append.mpr (Or.inl hc'_mem), hc'_eq⟩
  | inr hctrl =>
    have ⟨c', hc'_mem, hc'_eq⟩ := rewriteCtrl_callee_mem_aux f b.ctrl x hctrl
    exact ⟨c', Array.mem_append.mpr (Or.inr hc'_mem), hc'_eq⟩
termination_by (sizeOf b, 1)
decreasing_by apply Prod.Lex.left; exact sizeOf_ctrl_lt b

private theorem rewriteCtrl_callee_mem_aux
    (f : FunIdx → FunIdx) (c : Ctrl) (x : FunIdx) :
    x ∈ Ctrl.collectAllCallees (rewriteCtrl f c) →
    ∃ x', x' ∈ Ctrl.collectAllCallees c ∧ x = f x' := by
  cases c with
  | «return» s vs =>
    unfold rewriteCtrl Ctrl.collectAllCallees
    intro h; exact absurd h (Array.not_mem_empty x)
  | yield s vs =>
    unfold rewriteCtrl Ctrl.collectAllCallees
    intro h; exact absurd h (Array.not_mem_empty x)
  | «match» v branches def_ =>
    unfold rewriteCtrl Ctrl.collectAllCallees
    intro hmem
    rw [attach_foldl_rewrite_collectAllCallees_eq] at hmem
    have ih_branches : ∀ p ∈ branches.toList, ∀ x,
        x ∈ Block.collectAllCallees (rewriteBlock f p.2) →
        ∃ x', x' ∈ Block.collectAllCallees p.2 ∧ x = f x' := by
      intro ⟨g, b⟩ hmem x hx
      have _hsz : sizeOf b < sizeOf branches :=
        have h1 := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hmem)
        have h2 := Prod.mk.sizeOf_spec g b
        by omega
      exact rewriteBlock_callee_mem_aux f b x hx
    cases def_ with
    | none =>
      rw [attach_foldl_collectAllCallees_eq]
      exact list_foldl_branch_callees_mem f branches.toList ih_branches #[] #[]
        (fun x hx => absurd hx (Array.not_mem_empty x)) x hmem
    | some db =>
      rw [attach_foldl_collectAllCallees_eq]
      rw [Array.mem_append] at hmem
      cases hmem with
      | inl hbr =>
        have ⟨x', hx', heq⟩ := list_foldl_branch_callees_mem f branches.toList
          ih_branches #[] #[]
          (fun x hx => absurd hx (Array.not_mem_empty x)) x hbr
        exact ⟨x', Array.mem_append.mpr (Or.inl hx'), heq⟩
      | inr hdef =>
        have ⟨x', hx', heq⟩ := rewriteBlock_callee_mem_aux f db x hdef
        exact ⟨x', Array.mem_append.mpr (Or.inr hx'), heq⟩
  | matchContinue v branches def_ outputSize sharedAux sharedLookups cont =>
    unfold rewriteCtrl Ctrl.collectAllCallees
    intro hmem
    simp only at hmem
    rw [attach_foldl_rewrite_collectAllCallees_eq] at hmem
    have ih_branches : ∀ p ∈ branches.toList, ∀ x,
        x ∈ Block.collectAllCallees (rewriteBlock f p.2) →
        ∃ x', x' ∈ Block.collectAllCallees p.2 ∧ x = f x' := by
      intro ⟨g, b⟩ hmem x hx
      have _hsz : sizeOf b < sizeOf branches :=
        have h1 := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hmem)
        have h2 := Prod.mk.sizeOf_spec g b
        by omega
      exact rewriteBlock_callee_mem_aux f b x hx
    rw [Array.mem_append] at hmem
    cases hmem with
    | inl hwd =>
      -- withDefault case
      cases def_ with
      | none =>
        rw [attach_foldl_collectAllCallees_eq]
        have ⟨x', hx', heq⟩ := list_foldl_branch_callees_mem f branches.toList
          ih_branches #[] #[]
          (fun x hx => absurd hx (Array.not_mem_empty x)) x hwd
        exact ⟨x', Array.mem_append.mpr (Or.inl hx'), heq⟩
      | some db =>
        rw [attach_foldl_collectAllCallees_eq]
        simp only at hwd
        rw [Array.mem_append] at hwd
        cases hwd with
        | inl hbr =>
          have ⟨x', hx', heq⟩ := list_foldl_branch_callees_mem f branches.toList
            ih_branches #[] #[]
            (fun x hx => absurd hx (Array.not_mem_empty x)) x hbr
          exact ⟨x', Array.mem_append.mpr (Or.inl (Array.mem_append.mpr (Or.inl hx'))), heq⟩
        | inr hdef =>
          have ⟨x', hx', heq⟩ := rewriteBlock_callee_mem_aux f db x hdef
          exact ⟨x', Array.mem_append.mpr (Or.inl (Array.mem_append.mpr (Or.inr hx'))), heq⟩
    | inr hcont =>
      -- continuation case
      have ⟨x', hx', heq⟩ := rewriteBlock_callee_mem_aux f cont x hcont
      refine ⟨x', ?_, heq⟩
      cases def_ with
      | none =>
        rw [attach_foldl_collectAllCallees_eq]
        exact Array.mem_append.mpr (Or.inr hx')
      | some db =>
        rw [attach_foldl_collectAllCallees_eq]
        exact Array.mem_append.mpr (Or.inr hx')
termination_by (sizeOf c, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | grind
end

/-- Every callee collected from `rewriteBlock f b` is `f` applied to some
callee of `b`. Composed from op-level + ctrl-level helpers. -/
private theorem rewriteBlock_callee_mem_stub
    (f : Bytecode.FunIdx → Bytecode.FunIdx) (b : Bytecode.Block) (c : Bytecode.FunIdx) :
    c ∈ Bytecode.Block.collectAllCallees (Bytecode.rewriteBlock f b) →
      ∃ c', c' ∈ Bytecode.Block.collectAllCallees b ∧ c = f c' := by
  unfold rewriteBlock Block.collectAllCallees
  simp only
  intro hmem
  rw [Array.mem_append] at hmem
  cases hmem with
  | inl hop =>
    have ⟨c', hc'_mem, hc'_eq⟩ := foldl_rewriteOp_callee_mem f b.ops c hop
    exact ⟨c', Array.mem_append.mpr (Or.inl hc'_mem), hc'_eq⟩
  | inr hctrl =>
    have ⟨c', hc'_mem, hc'_eq⟩ := rewriteCtrl_callee_mem_aux f b.ctrl c hctrl
    exact ⟨c', Array.mem_append.mpr (Or.inr hc'_mem), hc'_eq⟩

/-- `deduplicate`'s `remap` maps in-range inputs to in-range outputs. -/
theorem deduplicate_remap_in_range
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (h : bytecodeRaw.deduplicate = (bytecodeDedup, remap)) :
    ∀ i, i < bytecodeRaw.functions.size → remap i < bytecodeDedup.functions.size :=
  dedup_remap_lt_size_stub h

/-- `rewriteBlock remap` preserves the "callees in range" property through
deduplication. Composes the three stubs above. -/
theorem deduplicate_preserves_callee_range
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap))
    (hraw_range : ∀ fi (_h : fi < bytecodeRaw.functions.size),
      ∀ callee,
        callee ∈ (Bytecode.Block.collectAllCallees bytecodeRaw.functions[fi].body) →
        callee < bytecodeRaw.functions.size) :
    ∀ fi (_h : fi < bytecodeDedup.functions.size),
      ∀ callee,
        callee ∈ (Bytecode.Block.collectAllCallees bytecodeDedup.functions[fi].body) →
        callee < bytecodeDedup.functions.size := by
  intro fi hfi callee hcallee
  have hraw_from_dedup := dedup_body_from_raw_aux bytecodeRaw
  simp only [hdedup] at hraw_from_dedup
  obtain ⟨j, hj, hbody⟩ := hraw_from_dedup fi hfi
  rw [hbody] at hcallee
  obtain ⟨c', hc'_mem, hc'_eq⟩ := rewriteBlock_callee_mem_stub remap _ callee hcallee
  have hc'_raw := hraw_range j hj c' hc'_mem
  have hc'_dedup := dedup_remap_lt_size_stub hdedup c' hc'_raw
  rw [hc'_eq]
  exact hc'_dedup

end Aiur

/-! ## `partitionRefine` reaches a fixpoint.

Ported verbatim from `HFixRawCloseScratch.lean`. Establishes strict monotonicity
of `numClasses` under non-fix iteration and size preservation; strong induction
on the measure `classes.size - numClasses classes` closes the fixpoint theorem.
`h_fix_raw_goal` below is the exact shape consumed by
`CompilerPreservation.compile_preservation`. -/

namespace Aiur.HFixRawCloseScratch

open Bytecode Aiur

/-! ## numClasses and its size bound -/

/-- `numClasses c` = number of distinct values in `c`. -/
def numClasses (c : Array Nat) : Nat := (assignClasses c).2

/-- `numClasses c ≤ c.size`. -/
theorem numClasses_le_size (c : Array Nat) : numClasses c ≤ c.size := by
  unfold numClasses assignClasses
  apply Array.foldl_induction
    (motive := fun (i : Nat) (s : Array Nat × Std.HashMap Nat Nat × Nat) =>
      s.2.2 ≤ i)
  · simp
  · intro i s ih
    obtain ⟨classes, map, nextId⟩ := s
    simp only at ih
    simp only
    cases hm : map[c[i]]? with
    | some _ => simp only; omega
    | none => simp only; omega

/-! ## Refinement of partition by one iteration -/

/-- Non-fix step preserves size. -/
private theorem step_size_preserved (c : Array Nat) (callees : Array (Array FunIdx)) :
    let sigs := c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))
    let c' := (assignClasses sigs).1
    c'.size = c.size := by
  simp only
  rw [assignClasses_size_eq, Array.size_mapIdx]

/-! ## Canonicality and strict monotonicity

`Canonical c := c = (assignClasses c).1` — `c` is an `assignClasses` fixed point.
Every partitionRefine input (when `bound ≥ 1` applies at least once) becomes
canonical after one step. The initial `initClasses` in `h_fix_raw` is also
canonical (it's `(assignClasses skeletons).1`).

**Strict monotonicity** requires canonicality of `classes`:
counterexample without canonicality: `c=[1,0,1]` with sigs second-projection
uniform over positions 0 and 2 ⇒ `c' = [0,1,0] ≠ c` yet `numClasses c' =
numClasses c = 2`. The step merely RELABELS to canonical form.

With `Canonical c`: `c' ≠ c` implies a genuine partition split (not just
relabel), so `numClasses c' > numClasses c`.
-/

/-- `c` is in canonical form: re-running assignClasses gives back `c`. -/
def Canonical (c : Array Nat) : Prop := c = (assignClasses c).1

/-- Every `assignClasses` output is canonical. Idempotence of `assignClasses`
on its output. -/
theorem Canonical_of_assignClasses
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (vs : Array α) : Canonical (assignClasses vs).1 := by
  unfold Canonical
  unfold assignClasses
  simp only
  have hinv :
      let r := vs.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      let ir := r.1.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      ir.1 = r.1 ∧ ir.2.2 = r.2.2 ∧
      (∀ id, ir.2.1[id]? = if id < r.2.2 then some id else none) ∧
      (∀ (v : α) id, r.2.1[v]? = some id → id < r.2.2) := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (s : Array Nat × Std.HashMap α Nat × Nat) =>
        let ir := s.1.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v =>
            match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
        ir.1 = s.1 ∧ ir.2.2 = s.2.2 ∧
        (∀ id, ir.2.1[id]? = if id < s.2.2 then some id else none) ∧
        (∀ (v : α) id, s.2.1[v]? = some id → id < s.2.2))
    · simp only
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro id; simp
      · intro v id hv; simp at hv
    · intro i s ih
      obtain ⟨classes, map, nextId⟩ := s
      simp only at ih
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      generalize hir_eq : (classes.foldl (init :=
          ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v =>
            match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = ir
      rw [hir_eq] at ih1 ih2 ih3
      obtain ⟨irC, irM, irN⟩ := ir
      simp only at ih1 ih2 ih3
      simp only
      cases hm : map[vs[i]]? with
      | some id =>
        have hid_lt : id < nextId := ih4 _ _ hm
        simp only []
        rw [Array.foldl_push]
        rw [hir_eq]
        have hlookup : irM[id]? = some id := by
          rw [ih3 id]; rw [if_pos hid_lt]
        simp only
        rw [hlookup]
        simp only
        refine ⟨?_, ih2, ih3, ?_⟩
        · rw [ih1]
        · intro v id' hv; exact ih4 v id' hv
      | none =>
        simp only []
        rw [Array.foldl_push]
        rw [hir_eq]
        have hlookup : irM[nextId]? = none := by
          rw [ih3 nextId]; rw [if_neg (Nat.lt_irrefl _)]
        simp only
        rw [hlookup]
        simp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [ih1]; rw [ih2]
        · rw [ih2]
        · intro id'
          rw [Std.HashMap.getElem?_insert]
          by_cases hcase : (nextId == id') = true
          · rw [if_pos hcase]
            have heq : nextId = id' := LawfulBEq.eq_of_beq hcase
            subst heq
            rw [if_pos (Nat.lt_succ_self _)]
            rw [ih2]
          · rw [if_neg hcase]
            rw [ih3 id']
            by_cases hlt : id' < nextId
            · rw [if_pos hlt]
              rw [if_pos (Nat.lt_succ_of_lt hlt)]
            · rw [if_neg hlt]
              have hnlt : ¬ id' < nextId + 1 := by
                intro h
                have hle : id' ≤ nextId := Nat.lt_succ_iff.mp h
                have hne : id' ≠ nextId := by
                  intro h'; apply hcase
                  subst h'; simp
                omega
              rw [if_neg hnlt]
        · intro v id' hv
          rw [Std.HashMap.getElem?_insert] at hv
          by_cases hveq : (vs[i] == v) = true
          · rw [if_pos hveq] at hv
            rw [Option.some.injEq] at hv
            omega
          · rw [if_neg hveq] at hv
            exact Nat.lt_succ_of_lt (ih4 v id' hv)
  simp only at hinv
  exact hinv.1.symm

/-! ### Supporting lemmas for `step_refine_numClasses_strict` -/

/-- `numClasses` of an `assignClasses` output equals the `.2` component. -/
private theorem numClasses_of_assignClasses_fst
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (vs : Array α) :
    numClasses (assignClasses vs).1 = (assignClasses vs).2 := by
  unfold numClasses
  unfold assignClasses
  simp only
  have hinv :
      let r := vs.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap α Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      let ir := r.1.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
        fun x v =>
          match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      ir.1 = r.1 ∧ ir.2.2 = r.2.2 ∧
      (∀ id, ir.2.1[id]? = if id < r.2.2 then some id else none) ∧
      (∀ (v : α) id, r.2.1[v]? = some id → id < r.2.2) := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (s : Array Nat × Std.HashMap α Nat × Nat) =>
        let ir := s.1.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v =>
            match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
        (ir.1 = s.1 ∧ ir.2.2 = s.2.2 ∧
         (∀ id, ir.2.1[id]? = if id < s.2.2 then some id else none) ∧
         (∀ (v : α) id, s.2.1[v]? = some id → id < s.2.2)))
    · simp only
      refine ⟨rfl, rfl, ?_, ?_⟩
      · intro id; simp
      · intro v id hv; simp at hv
    · intro i s ih
      obtain ⟨classes, map, nextId⟩ := s
      simp only at ih
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
      generalize hir_eq : (classes.foldl (init :=
          ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v =>
            match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = ir
      rw [hir_eq] at ih1 ih2 ih3
      obtain ⟨irC, irM, irN⟩ := ir
      simp only at ih1 ih2 ih3
      simp only
      cases hm : map[vs[i]]? with
      | some id =>
        have hid_lt : id < nextId := ih4 _ _ hm
        simp only []
        rw [Array.foldl_push]
        rw [hir_eq]
        have hlookup : irM[id]? = some id := by
          rw [ih3 id]; rw [if_pos hid_lt]
        simp only
        rw [hlookup]
        simp only
        refine ⟨?_, ih2, ih3, ?_⟩
        · rw [ih1]
        · intro v id' hv; exact ih4 v id' hv
      | none =>
        simp only []
        rw [Array.foldl_push]
        rw [hir_eq]
        have hlookup : irM[nextId]? = none := by
          rw [ih3 nextId]; rw [if_neg (Nat.lt_irrefl _)]
        simp only
        rw [hlookup]
        simp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [ih1]; rw [ih2]
        · rw [ih2]
        · intro id'
          rw [Std.HashMap.getElem?_insert]
          by_cases hcase : (nextId == id') = true
          · rw [if_pos hcase]
            have heq : nextId = id' := LawfulBEq.eq_of_beq hcase
            subst heq
            rw [if_pos (Nat.lt_succ_self _)]
            rw [ih2]
          · rw [if_neg hcase]
            rw [ih3 id']
            by_cases hlt : id' < nextId
            · rw [if_pos hlt]
              rw [if_pos (Nat.lt_succ_of_lt hlt)]
            · rw [if_neg hlt]
              have hnlt : ¬ id' < nextId + 1 := by
                intro h
                have hle : id' ≤ nextId := Nat.lt_succ_iff.mp h
                have hne : id' ≠ nextId := by
                  intro h'; apply hcase
                  subst h'; simp
                omega
              rw [if_neg hnlt]
        · intro v id' hv
          rw [Std.HashMap.getElem?_insert] at hv
          by_cases hveq : (vs[i] == v) = true
          · rw [if_pos hveq] at hv
            rw [Option.some.injEq] at hv
            omega
          · rw [if_neg hveq] at hv
            exact Nat.lt_succ_of_lt (ih4 v id' hv)
  simp only at hinv
  exact hinv.2.1

/-! ### Helper: canonical prefix-fold pointwise equals prefix. -/

private theorem canonical_prefix_fold_eq
    (c : Array Nat) (hcan : Canonical c) (k : Nat) (hk : k ≤ c.size) :
    ((c.extract 0 k).foldl
        (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
        fun x v => match x.2.1[v]? with
          | some id => (x.1.push id, x.2.1, x.2.2)
          | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1 =
      c.extract 0 k := by
  have hsize : ∀ (k' : Nat) (_ : k' ≤ c.size),
      ((c.extract 0 k').foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1.size = k' := by
    intro k' hk'
    have h1 : ((c.extract 0 k').foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1.size =
        (c.extract 0 k').size := by
      apply Array.foldl_induction
        (motive := fun i (s : Array Nat × Std.HashMap Nat Nat × Nat) => s.1.size = i)
      · rfl
      · intro i s hs
        obtain ⟨classes, map, nextId⟩ := s
        simp only at hs
        simp only
        cases hmm : map[(c.extract 0 k')[i]]? with
        | none => simp [Array.size_push, hs]
        | some _ => simp [Array.size_push, hs]
    rw [h1, Array.size_extract]; omega
  have hmain : ∀ (d : Nat) (hd : d + k ≤ c.size),
      ((c.extract 0 (c.size - d)).foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).1 =
        c.extract 0 (c.size - d) := by
    intro d _
    induction d with
    | zero =>
      simp only [Nat.sub_zero]
      rw [Array.extract_size]
      exact hcan.symm
    | succ d' ih =>
      by_cases hd'_lt : d' < c.size
      · have hk1_eq : c.size - d' = (c.size - (d' + 1)) + 1 := by omega
        have hk2_lt : c.size - (d' + 1) < c.size := by omega
        have ih' := ih (by omega)
        have hc_ext : c.extract 0 (c.size - d') =
            (c.extract 0 (c.size - (d' + 1))).push (c[c.size - (d' + 1)]'hk2_lt) := by
          rw [hk1_eq]
          exact Array.extract_succ_right (by omega) hk2_lt
        rw [hc_ext] at ih'
        rw [Array.foldl_push] at ih'
        generalize hstate : (c.extract 0 (c.size - (d' + 1))).foldl
            (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
            (fun x v => match x.2.1[v]? with
              | some id => (x.1.push id, x.2.1, x.2.2)
              | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = st
        rw [hstate] at ih'
        obtain ⟨cls, map, nextId⟩ := st
        simp only at ih'
        have push_inj_fst : ∀ {α : Type _} (a b : Array α) (x y : α), a.push x = b.push y →
            a = b := by
          intro α a b x y hpush
          have hsz : a.size = b.size := by
            have := congrArg Array.size hpush
            rw [Array.size_push, Array.size_push] at this
            omega
          apply Array.ext
          · exact hsz
          · intro j hj1 hj2
            have hj_push1 : j < (a.push x).size := by rw [Array.size_push]; omega
            have hj_push2 : j < (b.push y).size := by rw [Array.size_push]; omega
            have key : (a.push x)[j]'hj_push1 = (b.push y)[j]'hj_push2 := by
              have := congrArg (fun (arr : Array α) =>
                if h : j < arr.size then some (arr[j]'h) else none) hpush
              simp only [hj_push1, hj_push2, dif_pos] at this
              exact Option.some.inj this
            rw [Array.getElem_push_lt hj1, Array.getElem_push_lt hj2] at key
            exact key
        cases hmm : map[c[c.size - (d' + 1)]'hk2_lt]? with
        | some id =>
          rw [hmm] at ih'
          simp only at ih'
          exact push_inj_fst _ _ _ _ ih'
        | none =>
          rw [hmm] at ih'
          simp only at ih'
          exact push_inj_fst _ _ _ _ ih'
      · have h0 : c.size - (d' + 1) = 0 := by omega
        rw [h0]; simp [Array.extract_zero]
  have := hmain (c.size - k) (by omega)
  have : c.size - (c.size - k) = k := by omega
  rw [this] at *
  have hd_val : c.size - (c.size - k) = k := by omega
  have hfinal := hmain (c.size - k) (by omega)
  rw [hd_val] at hfinal
  exact hfinal

set_option linter.unusedVariables false in
/-- Canonical arrays with identical partition-structure are equal pointwise. -/
private theorem canonical_unique_of_partition_eq
    (c : Array Nat) (sigs : Array (Nat × Array Nat))
    (hcan : Canonical c)
    (hsz : sigs.size = c.size)
    (href : ∀ i j (hi : i < sigs.size) (hj : j < sigs.size),
      sigs[i]'hi = sigs[j]'hj → c[i]'(hsz ▸ hi) = c[j]'(hsz ▸ hj))
    (hnc : numClasses c = (assignClasses sigs).2) :
    (assignClasses sigs).1 = c := by
  unfold assignClasses
  simp only
  have hc_ext_full : c.extract 0 c.size = c := Array.extract_size
  have hs_ext_full : sigs.extract 0 sigs.size = sigs := Array.extract_size
  have hjoint : ∀ (k : Nat) (hk : k ≤ c.size),
      let c_state := (c.extract 0 k).foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      let sigs_state := (sigs.extract 0 k).foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
      c_state.2.2 ≤ sigs_state.2.2 ∧
      (∀ j (hj : j < k), c_state.2.1[c[j]'(by omega)]? ≠ none) ∧
      (∀ j (hj : j < k), sigs_state.2.1[sigs[j]'(by omega : j < sigs.size)]? ≠ none) ∧
      (∀ v id, sigs_state.2.1[v]? = some id →
          ∃ j, ∃ _ : j < k, sigs[j]'(by omega : j < sigs.size) = v) ∧
      (∀ v id, c_state.2.1[v]? = some id →
          ∃ j, ∃ _ : j < k, c[j]'(by omega) = v) ∧
      c_state.1 = c.extract 0 k ∧
      (∀ id, c_state.2.1[id]? = if id < c_state.2.2 then some id else none) ∧
      (c_state.2.2 = sigs_state.2.2 →
        sigs_state.1 = c.extract 0 k ∧
        (∀ j (hj : j < k), sigs_state.2.1[sigs[j]'(by omega : j < sigs.size)]? =
          some (c[j]'(by omega)))) := by
    intro k hk
    induction k with
    | zero =>
      simp only [Array.extract_zero, Array.foldl_empty]
      refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj; exact absurd hj (Nat.not_lt_zero _)
      · intro j hj; exact absurd hj (Nat.not_lt_zero _)
      · intro v id hv; simp at hv
      · intro v id hv; simp at hv
      · simp
      · intro id; simp
      · intro _
        refine ⟨?_, ?_⟩
        · simp
        · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k' ih =>
      have hk' : k' ≤ c.size := Nat.le_of_succ_le hk
      have hk_c : k' < c.size := by omega
      have hk_sigs : k' < sigs.size := by omega
      have hc_ext : c.extract 0 (k' + 1) = (c.extract 0 k').push (c[k']'hk_c) :=
        Array.extract_succ_right (by omega) hk_c
      have hsigs_ext : sigs.extract 0 (k' + 1) =
          (sigs.extract 0 k').push (sigs[k']'hk_sigs) :=
        Array.extract_succ_right (by omega) hk_sigs
      rw [hc_ext, hsigs_ext]
      rw [Array.foldl_push, Array.foldl_push]
      specialize ih hk'
      simp only at ih
      obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7, ih8⟩ := ih
      generalize hc_st_eq : (c.extract 0 k').foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          (fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = cst
      generalize hs_st_eq : (sigs.extract 0 k').foldl
          (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
          (fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = sst
      rw [hc_st_eq] at ih1 ih2 ih5 ih6 ih7 ih8
      rw [hs_st_eq] at ih1 ih3 ih4 ih8
      obtain ⟨ccls, cmap, cnext⟩ := cst
      obtain ⟨scls, smap, snext⟩ := sst
      simp only at ih1 ih2 ih3 ih4 ih5 ih6 ih7 ih8
      cases hcm : cmap[c[k']'hk_c]? with
      | some cid =>
        have hcid_eq : cid = c[k']'hk_c ∧ c[k']'hk_c < cnext := by
          have hI := ih7 (c[k']'hk_c)
          rw [hcm] at hI
          by_cases hlt : c[k']'hk_c < cnext
          · rw [if_pos hlt] at hI
            refine ⟨?_, hlt⟩
            have : some cid = some (c[k']'hk_c) := hI
            injection this
          · rw [if_neg hlt] at hI; exact absurd hI (Option.some_ne_none _)
        obtain ⟨hcid_val, hck'_lt⟩ := hcid_eq
        subst hcid_val
        cases hsm : smap[sigs[k']'hk_sigs]? with
        | some sid =>
          refine ⟨ih1, ?_, ?_, ?_, ?_, ?_, ih7, ?_⟩
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk; rw [hcm]; exact Option.some_ne_none _
            · exact ih2 j (by omega)
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk; rw [hsm]; exact Option.some_ne_none _
            · exact ih3 j (by omega)
          · intro v id hv
            obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
            exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          · intro v id hv
            obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
            exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          · rw [ih6]
          · intro hdiff
            obtain ⟨ihJ1, ihJ2⟩ := ih8 hdiff
            obtain ⟨j, hj, hsig_eq⟩ := ih4 _ _ hsm
            have hsid : smap[sigs[j]'(by omega : j < sigs.size)]? = some (c[j]'(by omega)) :=
              ihJ2 j hj
            rw [hsig_eq] at hsid
            rw [hsm] at hsid
            have hsid_val : sid = c[j]'(by omega) := by
              have : some sid = some (c[j]'(by omega)) := hsid
              injection this
            have hcj_eq : c[j]'(by omega) = c[k']'hk_c := by
              have hj_sigs : j < sigs.size := by omega
              have hk_sigs' : k' < sigs.size := hk_sigs
              exact href j k' hj_sigs hk_sigs' hsig_eq
            refine ⟨?_, ?_⟩
            · rw [ihJ1]; rw [hsid_val]; rw [hcj_eq]
            · intro i hi
              by_cases hik : i = k'
              · subst hik
                rw [hsm]
                rw [hsid_val]; rw [hcj_eq]
              · exact ihJ2 i (by omega)
        | none =>
          refine ⟨Nat.le_succ_of_le ih1, ?_, ?_, ?_, ?_, ?_, ih7, ?_⟩
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk; rw [hcm]; exact Option.some_ne_none _
            · exact ih2 j (by omega)
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk
              rw [Std.HashMap.getElem?_insert]
              simp
            · have hj_sig : j < sigs.size := by omega
              rw [Std.HashMap.getElem?_insert]
              by_cases hkey : (sigs[k']'hk_sigs == sigs[j]'hj_sig) = true
              · rw [if_pos hkey]; exact Option.some_ne_none _
              · rw [if_neg hkey]; exact ih3 j (by omega)
          · intro v id hv
            rw [Std.HashMap.getElem?_insert] at hv
            by_cases hkey : (sigs[k']'hk_sigs == v) = true
            · have heq : sigs[k']'hk_sigs = v := LawfulBEq.eq_of_beq hkey
              exact ⟨k', Nat.lt_succ_self _, heq⟩
            · rw [if_neg hkey] at hv
              obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          · intro v id hv
            obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
            exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          · rw [ih6]
          · intro hdiff
            exfalso
            have hih1 : cnext ≤ snext := ih1
            have hd : cnext = snext + 1 := hdiff
            omega
      | none =>
        have hck_eq_cnext : c[k']'hk_c = cnext := by
          have hhelp := canonical_prefix_fold_eq c hcan (k' + 1) hk
          rw [hc_ext, Array.foldl_push, hc_st_eq] at hhelp
          simp only at hhelp
          rw [hcm] at hhelp
          simp only at hhelp
          have hccls_size : ccls.size = (c.extract 0 k').size := by rw [ih6]
          have hk'_ccls : k' = ccls.size := by
            rw [hccls_size, Array.size_extract]; omega
          have hk'_ext : k' = (c.extract 0 k').size := by
            rw [Array.size_extract]; omega
          have key : (ccls.push cnext)[k']'(by rw [Array.size_push]; omega) =
              ((c.extract 0 k').push (c[k']'hk_c))[k']'(by rw [Array.size_push]; omega) := by
            have := congrArg (fun (arr : Array Nat) =>
              if h : k' < arr.size then some (arr[k']'h) else none) hhelp
            simp only at this
            have h1 : k' < (ccls.push cnext).size := by rw [Array.size_push]; omega
            have h2 : k' < ((c.extract 0 k').push (c[k']'hk_c)).size := by
              rw [Array.size_push, Array.size_extract]; omega
            rw [dif_pos h1, dif_pos h2] at this
            exact Option.some.inj this
          rw [Array.getElem_push, dif_neg (by omega : ¬ k' < ccls.size)] at key
          rw [Array.getElem_push, dif_neg (by
              rw [Array.size_extract]; omega : ¬ k' < (c.extract 0 k').size)] at key
          exact key.symm
        have hsm_none : smap[sigs[k']'hk_sigs]? = none := by
          cases hsm : smap[sigs[k']'hk_sigs]? with
          | none => rfl
          | some sid =>
            exfalso
            obtain ⟨j, hj, hsig_eq⟩ := ih4 _ _ hsm
            have hj_sigs : j < sigs.size := by omega
            have hcj_eq : c[j]'(by omega) = c[k']'hk_c :=
              href j k' hj_sigs hk_sigs hsig_eq
            have hcj_not_none := ih2 j hj
            rw [hcj_eq] at hcj_not_none
            exact hcj_not_none hcm
        rw [hsm_none]
        simp only
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro j hj
          rw [Std.HashMap.getElem?_insert]
          by_cases hjk : j = k'
          · subst hjk
            have hrefl : (c[j]'hk_c == c[j]'hk_c) = true := by simp
            rw [if_pos hrefl]; exact Option.some_ne_none _
          · have hj_c : j < c.size := by omega
            by_cases hkey : (c[k']'hk_c == c[j]'hj_c) = true
            · rw [if_pos hkey]; exact Option.some_ne_none _
            · rw [if_neg hkey]; exact ih2 j (by omega)
        · intro j hj
          rw [Std.HashMap.getElem?_insert]
          by_cases hjk : j = k'
          · subst hjk
            have hrefl : (sigs[j]'hk_sigs == sigs[j]'hk_sigs) = true := by simp
            rw [if_pos hrefl]; exact Option.some_ne_none _
          · have hj_sig : j < sigs.size := by omega
            by_cases hkey : (sigs[k']'hk_sigs == sigs[j]'hj_sig) = true
            · rw [if_pos hkey]; exact Option.some_ne_none _
            · rw [if_neg hkey]; exact ih3 j (by omega)
        · intro v id hv
          rw [Std.HashMap.getElem?_insert] at hv
          by_cases hkey : (sigs[k']'hk_sigs == v) = true
          · have heq : sigs[k']'hk_sigs = v := LawfulBEq.eq_of_beq hkey
            exact ⟨k', Nat.lt_succ_self _, heq⟩
          · rw [if_neg hkey] at hv
            obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
            exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
        · intro v id hv
          rw [Std.HashMap.getElem?_insert] at hv
          by_cases hkey : (c[k']'hk_c == v) = true
          · have heq : c[k']'hk_c = v := LawfulBEq.eq_of_beq hkey
            exact ⟨k', Nat.lt_succ_self _, heq⟩
          · rw [if_neg hkey] at hv
            obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
            exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
        · rw [ih6]; rw [hck_eq_cnext]
        · intro id
          rw [Std.HashMap.getElem?_insert]
          by_cases hcase : (c[k']'hk_c == id) = true
          · rw [if_pos hcase]
            have heq : c[k']'hk_c = id := LawfulBEq.eq_of_beq hcase
            rw [hck_eq_cnext] at heq
            subst heq
            rw [if_pos (Nat.lt_succ_self _)]
          · rw [if_neg hcase]
            rw [ih7 id]
            by_cases hlt : id < cnext
            · rw [if_pos hlt]; rw [if_pos (Nat.lt_succ_of_lt hlt)]
            · rw [if_neg hlt]
              have hnlt : ¬ id < cnext + 1 := by
                intro h
                have hle : id ≤ cnext := Nat.lt_succ_iff.mp h
                have hne : id ≠ cnext := by
                  intro h'; apply hcase
                  rw [hck_eq_cnext]; rw [h']; simp
                omega
              rw [if_neg hnlt]
        · intro hdiff
          have hdiff' : cnext = snext := by omega
          obtain ⟨ihJ1, ihJ2⟩ := ih8 hdiff'
          refine ⟨?_, ?_⟩
          · rw [ihJ1]; rw [← hdiff']; rw [hck_eq_cnext]
          · intro i hi
            rw [Std.HashMap.getElem?_insert]
            by_cases hik : i = k'
            · subst hik
              have hrefl : (sigs[i]'hk_sigs == sigs[i]'hk_sigs) = true := by simp
              rw [if_pos hrefl]
              rw [← hdiff', ← hck_eq_cnext]
            · have hi_sigs : i < sigs.size := by omega
              by_cases hkey : (sigs[k']'hk_sigs == sigs[i]'hi_sigs) = true
              · exfalso
                have heq_sig : sigs[k']'hk_sigs = sigs[i]'hi_sigs :=
                  LawfulBEq.eq_of_beq hkey
                have hk_sigs' : k' < sigs.size := hk_sigs
                have hci_eq : c[k']'hk_c = c[i]'(by omega) :=
                  href k' i hk_sigs' hi_sigs heq_sig
                have hci_not_none := ih2 i (by omega)
                rw [← hci_eq] at hci_not_none
                exact hci_not_none hcm
              · rw [if_neg hkey]
                exact ihJ2 i (by omega)
  have hfull := hjoint c.size (Nat.le_refl _)
  simp only at hfull
  rw [hc_ext_full] at hfull
  have hs_ext_csz : sigs.extract 0 c.size = sigs := by rw [← hsz]; exact Array.extract_size
  rw [hs_ext_csz] at hfull
  obtain ⟨_, _, _, _, _, _, _, hJ⟩ := hfull
  have hdiff0 : (c.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.2 =
      (sigs.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.2 := by
    have h1 : (assignClasses c).2 =
        (c.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.2 := rfl
    have h2 : (assignClasses sigs).2 =
        (sigs.foldl (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
          fun x v => match x.2.1[v]? with
            | some id => (x.1.push id, x.2.1, x.2.2)
            | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)).2.2 := rfl
    rw [← h1, ← h2]
    have : numClasses c = (assignClasses c).2 := rfl
    omega
  obtain ⟨hJ1, _⟩ := hJ hdiff0
  exact hJ1

/-- **CORE LEMMA.** Strict monotonicity of numClasses under non-fix step,
assuming `c` is canonical. -/
theorem step_refine_numClasses_strict
    (c : Array Nat) (callees : Array (Array FunIdx))
    (hcan : Canonical c) :
    let sigs := c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))
    let c' := (assignClasses sigs).1
    c' ≠ c → numClasses c' > numClasses c := by
  simp only
  intro hne
  have hsz_sig : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))).size = c.size :=
    Array.size_mapIdx
  have hnc_c' : numClasses (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).1 =
      (assignClasses (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))).2 :=
    numClasses_of_assignClasses_fst _
  rw [hnc_c']
  have hnc_c : numClasses c = (assignClasses c).2 := rfl
  rw [hnc_c]
  have href : ∀ i j (hi : i < (c.mapIdx fun i cls =>
        (cls, callees[i]!.map (c[·]!))).size) (hj : j < (c.mapIdx fun i cls =>
        (cls, callees[i]!.map (c[·]!))).size),
      (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[i]'hi =
      (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[j]'hj →
      c[i]'(hsz_sig ▸ hi) = c[j]'(hsz_sig ▸ hj) := by
    intro i j hi hj heq
    have h_i : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[i]'hi =
        (c[i], callees[i]!.map (c[·]!)) := by
      simp [Array.getElem_mapIdx]
    have h_j : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[j]'hj =
        (c[j], callees[j]!.map (c[·]!)) := by
      simp [Array.getElem_mapIdx]
    rw [h_i, h_j] at heq
    exact (Prod.mk.inj heq).1
  by_cases hle_case : (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).2 > (assignClasses c).2
  · exact hle_case
  exfalso
  have hle : (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).2 ≤ (assignClasses c).2 :=
    Nat.le_of_not_lt hle_case
  have hge : (assignClasses c).2 ≤ (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).2 := by
    unfold assignClasses
    simp only
    have hjoint : ∀ (k : Nat) (hk : k ≤ (c.mapIdx fun i cls =>
        (cls, callees[i]!.map (c[·]!))).size),
        let sigs_state := ((c.mapIdx fun i cls =>
          (cls, callees[i]!.map (c[·]!))).extract 0 k).foldl
            (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
            fun x v =>
              match x.2.1[v]? with
              | some id => (x.1.push id, x.2.1, x.2.2)
              | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
        let c_state := (c.extract 0 k).foldl
            (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
            fun x v =>
              match x.2.1[v]? with
              | some id => (x.1.push id, x.2.1, x.2.2)
              | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)
        c_state.2.2 ≤ sigs_state.2.2 ∧
        (∀ j (hj : j < k),
          c_state.2.1[c[j]'(by
            have : k ≤ c.size := by rw [Array.size_mapIdx] at hk; exact hk
            omega)]? ≠ none) ∧
        (∀ j (hj : j < k),
          sigs_state.2.1[(c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!)))[j]'(by omega)]? ≠ none) ∧
        (∀ v id, sigs_state.2.1[v]? = some id →
          ∃ j, ∃ _ : j < k, (c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!)))[j]'(by omega) = v) ∧
        (∀ v id, c_state.2.1[v]? = some id →
          ∃ j, ∃ _ : j < k, c[j]'(by
            have : k ≤ c.size := by rw [Array.size_mapIdx] at hk; exact hk
            omega) = v) := by
      intro k hk
      induction k with
      | zero =>
        simp only [Array.extract_zero, Array.foldl_empty]
        refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero _)
        · intro j hj; exact absurd hj (Nat.not_lt_zero _)
        · intro v id hv; simp at hv
        · intro v id hv; simp at hv
      | succ k' ih =>
        have hk' : k' ≤ (c.mapIdx fun i cls =>
          (cls, callees[i]!.map (c[·]!))).size := Nat.le_of_succ_le hk
        have hk_c : k' < c.size := by
          have hsz : (c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!))).size = c.size := Array.size_mapIdx
          rw [hsz] at hk
          omega
        have hk_sigs : k' < (c.mapIdx fun i cls =>
          (cls, callees[i]!.map (c[·]!))).size := by omega
        have hc_ext : c.extract 0 (k' + 1) = (c.extract 0 k').push (c[k']'hk_c) :=
          Array.extract_succ_right (by omega) hk_c
        have hsigs_ext : (c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!))).extract 0 (k' + 1) =
          ((c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!))).extract 0 k').push
            ((c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))[k']'hk_sigs) :=
          Array.extract_succ_right (by omega) hk_sigs
        rw [hc_ext, hsigs_ext]
        rw [Array.foldl_push, Array.foldl_push]
        specialize ih hk'
        simp only at ih
        obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
        generalize hc_st_eq : (c.extract 0 k').foldl
            (init := ((#[] : Array Nat), (∅ : Std.HashMap Nat Nat), 0))
            (fun x v => match x.2.1[v]? with
              | some id => (x.1.push id, x.2.1, x.2.2)
              | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = cst
        generalize hs_st_eq : ((c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!))).extract 0 k').foldl
            (init := ((#[] : Array Nat), (∅ : Std.HashMap (Nat × Array Nat) Nat), 0))
            (fun x v => match x.2.1[v]? with
              | some id => (x.1.push id, x.2.1, x.2.2)
              | none => (x.1.push x.2.2, x.2.1.insert v x.2.2, x.2.2 + 1)) = sst
        rw [hc_st_eq] at ih1 ih2 ih5
        rw [hs_st_eq] at ih1 ih3 ih4
        obtain ⟨ccls, cmap, cnext⟩ := cst
        obtain ⟨scls, smap, snext⟩ := sst
        simp only at ih1 ih2 ih3 ih4 ih5
        have hsig_k : (c.mapIdx fun i cls =>
            (cls, callees[i]!.map (c[·]!)))[k']'hk_sigs =
            (c[k'], callees[k']!.map (c[·]!)) := by
          simp [Array.getElem_mapIdx]
        rw [hsig_k]
        simp only
        cases hcm : cmap[c[k']'hk_c]? with
        | some cid =>
          cases hsm : smap[(c[k'], callees[k']!.map (c[·]!))]? with
          | some sid =>
            refine ⟨ih1, ?_, ?_, ?_, ?_⟩
            · intro j hj
              by_cases hjk : j = k'
              · subst hjk
                rw [hcm]; exact Option.some_ne_none _
              · have hjk' : j < k' := by omega
                exact ih2 j hjk'
            · intro j hj
              by_cases hjk : j = k'
              · subst hjk
                simp only [Array.getElem_mapIdx]
                rw [hsm]; exact Option.some_ne_none _
              · have hjk' : j < k' := by omega
                exact ih3 j hjk'
            · intro v id hv
              obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
            · intro v id hv
              obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          | none =>
            refine ⟨Nat.le_succ_of_le ih1, ?_, ?_, ?_, ?_⟩
            · intro j hj
              by_cases hjk : j = k'
              · subst hjk
                rw [hcm]; exact Option.some_ne_none _
              · have hjk' : j < k' := by omega
                exact ih2 j hjk'
            · intro j hj
              by_cases hjk : j = k'
              · subst hjk
                simp only [Array.getElem_mapIdx]
                rw [Std.HashMap.getElem?_insert]
                simp
              · have hjk' : j < k' := by omega
                simp only [Array.getElem_mapIdx]
                rw [Std.HashMap.getElem?_insert]
                by_cases hkey : ((c[k'], callees[k']!.map (c[·]!)) == (c[j], callees[j]!.map (c[·]!))) = true
                · rw [if_pos hkey]; exact Option.some_ne_none _
                · rw [if_neg hkey]
                  have := ih3 j hjk'
                  simp only [Array.getElem_mapIdx] at this
                  exact this
            · intro v id hv
              rw [Std.HashMap.getElem?_insert] at hv
              by_cases hkey : ((c[k'], callees[k']!.map (c[·]!)) == v) = true
              · rw [if_pos hkey] at hv
                have heq : (c[k'], callees[k']!.map (c[·]!)) = v := LawfulBEq.eq_of_beq hkey
                refine ⟨k', Nat.lt_succ_self _, ?_⟩
                simp [Array.getElem_mapIdx, heq]
              · rw [if_neg hkey] at hv
                obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
                exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
            · intro v id hv
              obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
        | none =>
          have hsm_none : smap[(c[k'], callees[k']!.map (c[·]!))]? = none := by
            cases hsm : smap[(c[k'], callees[k']!.map (c[·]!))]? with
            | none => rfl
            | some sid =>
              exfalso
              obtain ⟨j, hj, hjEq⟩ := ih4 _ _ hsm
              have hsig_j : (c.mapIdx fun i cls =>
                  (cls, callees[i]!.map (c[·]!)))[j]'(by omega) =
                  (c[j]'(by
                    have : k' < c.size := hk_c
                    omega), callees[j]!.map (c[·]!)) := by
                simp [Array.getElem_mapIdx]
              rw [hsig_j] at hjEq
              have hcj_eq : c[j]'(by omega) = c[k'] := by
                exact (Prod.mk.inj hjEq).1
              have hcj_not_none := ih2 j hj
              rw [hcj_eq] at hcj_not_none
              exact hcj_not_none hcm
          rw [hsm_none]
          simp only
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · omega
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk
              rw [Std.HashMap.getElem?_insert]
              simp
            · have hjk' : j < k' := by omega
              rw [Std.HashMap.getElem?_insert]
              by_cases hkey : (c[k'] == c[j]) = true
              · rw [if_pos hkey]; exact Option.some_ne_none _
              · rw [if_neg hkey]; exact ih2 j hjk'
          · intro j hj
            by_cases hjk : j = k'
            · subst hjk
              simp only [Array.getElem_mapIdx]
              rw [Std.HashMap.getElem?_insert]
              simp
            · have hjk' : j < k' := by omega
              simp only [Array.getElem_mapIdx]
              rw [Std.HashMap.getElem?_insert]
              by_cases hkey : ((c[k'], callees[k']!.map (c[·]!)) == (c[j], callees[j]!.map (c[·]!))) = true
              · rw [if_pos hkey]; exact Option.some_ne_none _
              · rw [if_neg hkey]
                have := ih3 j hjk'
                simp only [Array.getElem_mapIdx] at this
                exact this
          · intro v id hv
            rw [Std.HashMap.getElem?_insert] at hv
            by_cases hkey : ((c[k'], callees[k']!.map (c[·]!)) == v) = true
            · have heq : (c[k'], callees[k']!.map (c[·]!)) = v := LawfulBEq.eq_of_beq hkey
              refine ⟨k', Nat.lt_succ_self _, ?_⟩
              simp [Array.getElem_mapIdx, heq]
            · rw [if_neg hkey] at hv
              obtain ⟨j, hj, hjEq⟩ := ih4 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
          · intro v id hv
            rw [Std.HashMap.getElem?_insert] at hv
            by_cases hkey : (c[k']'hk_c == v) = true
            · have heq : c[k']'hk_c = v := LawfulBEq.eq_of_beq hkey
              exact ⟨k', Nat.lt_succ_self _, heq⟩
            · rw [if_neg hkey] at hv
              obtain ⟨j, hj, hjEq⟩ := ih5 v id hv
              exact ⟨j, Nat.lt_succ_of_lt hj, hjEq⟩
    have hsz : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))).size = c.size :=
      Array.size_mapIdx
    have hle : c.size ≤ (c.mapIdx fun i cls =>
        (cls, callees[i]!.map (c[·]!))).size := by omega
    have hfull := hjoint c.size hle
    simp only at hfull
    rw [Array.extract_size] at hfull
    have hs_ext : (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))).extract 0 c.size =
        (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!))) := by
      rw [← hsz]; exact Array.extract_size
    rw [hs_ext] at hfull
    exact hfull.1
  have heq : (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).2 = (assignClasses c).2 := by
    omega
  have : (assignClasses (c.mapIdx fun i cls =>
      (cls, callees[i]!.map (c[·]!)))).1 = c := by
    apply canonical_unique_of_partition_eq c _ hcan hsz_sig href
    unfold numClasses
    exact heq.symm
  exact hne this

/-! ## Main fixpoint theorem via strong induction -/

/-- `partitionRefineBound` at sufficient budget (assuming canonical input)
reaches a fixpoint. -/
theorem partitionRefineBound_fixpoint
    (bound : Nat) (classes : Array Nat) (callees : Array (Array FunIdx))
    (hcan : Canonical classes)
    (hbound : classes.size - numClasses classes < bound) :
    let c := partitionRefineBound bound classes callees
    (assignClasses (c.mapIdx fun i cls => (cls, callees[i]!.map (c[·]!)))).1 = c := by
  induction bound generalizing classes with
  | zero =>
    exact absurd hbound (Nat.not_lt_zero _)
  | succ b ih =>
    simp only
    unfold partitionRefineBound
    simp only
    split
    · rename_i hfix
      have : (assignClasses (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!)))).1 = classes :=
        beq_iff_eq.mp hfix
      exact this
    · rename_i hne
      let newClasses := (assignClasses (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!)))).1
      have hnc_def : newClasses = (assignClasses (classes.mapIdx fun i cls =>
          (cls, callees[i]!.map (classes[·]!)))).1 := rfl
      have hne' : newClasses ≠ classes := by
        intro h
        apply hne
        rw [hnc_def] at h
        rw [h]
        simp
      have hstrict : numClasses newClasses > numClasses classes := by
        have := step_refine_numClasses_strict classes callees hcan
        simp only at this
        exact this hne'
      have hsz : newClasses.size = classes.size := by
        rw [hnc_def]
        exact step_size_preserved classes callees
      have hmeasure : newClasses.size - numClasses newClasses < b := by
        have hle : numClasses classes ≤ classes.size := numClasses_le_size classes
        have hle' : numClasses newClasses ≤ newClasses.size := numClasses_le_size newClasses
        rw [hsz]
        rw [hsz] at hle'
        omega
      have hcan' : Canonical newClasses := by
        rw [hnc_def]
        exact Canonical_of_assignClasses _
      have := ih newClasses hcan' hmeasure
      exact this

/-- The exact shape of h_fix_raw. -/
theorem h_fix_raw_goal
    (t : Toplevel) :
    let skeletons := t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout)
    let initClasses := (Bytecode.assignClasses skeletons).1
    let callees := t.functions.map fun f =>
        Bytecode.collectCalleesBlock f.body
    let classes := Bytecode.partitionRefine initClasses callees
    let signatures := classes.mapIdx fun i cls =>
        (cls, callees[i]!.map (classes[·]!))
    (Bytecode.assignClasses signatures).1 = classes := by
  simp only
  unfold partitionRefine
  apply partitionRefineBound_fixpoint
  · exact Canonical_of_assignClasses _
  · have : numClasses ((Bytecode.assignClasses
        (t.functions.map fun f => (Bytecode.skeletonBlock f.body, f.layout))).1) ≤
        ((Bytecode.assignClasses
        (t.functions.map fun f => (Bytecode.skeletonBlock f.body, f.layout))).1).size :=
      numClasses_le_size _
    omega

end Aiur.HFixRawCloseScratch

end -- public section
