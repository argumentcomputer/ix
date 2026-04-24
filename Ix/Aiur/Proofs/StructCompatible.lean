module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Semantics.Compatible
public import Ix.Aiur.Compiler
public import Ix.Aiur.Proofs.LowerShared
public import Ix.Aiur.Proofs.LowerCalleesFromLayout
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Semantics.WellFormed

/-!
`StructCompatible` standalone lemma.

The structural part of the simulation invariant is established by induction on
the compilation passes, independently of the semantic preservation claim.
-/

public section

namespace Aiur

open Source

/-! ## Compile post-conditions (relocated from `Ix/Aiur/Compiler.lean`)

Pure structural facts about `Source.Toplevel.compile`'s output. Kept in the
proof layer so the compiler implementation file doesn't churn when proofs
evolve. -/

/-- `preNameMap.fold (init := ∅) fun acc n i => acc.insert n (remap i)`
computes the pointwise `Option.map remap`. -/
theorem nameMap_value_via_remap
    (preNameMap : Std.HashMap Global Bytecode.FunIdx)
    (remap : Bytecode.FunIdx → Bytecode.FunIdx) :
    ∀ (name : Global),
      (preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i))[name]? =
      (preNameMap[name]?).map remap := by
  intro name
  rw [Std.HashMap.fold_eq_foldl_toList]
  have hfold_eq :
      preNameMap.toList.foldl
          (fun a (b : Global × Bytecode.FunIdx) => a.insert b.1 (remap b.2))
          (∅ : Std.HashMap Global Bytecode.FunIdx)
        = (preNameMap.toList.map (fun p => (p.1, remap p.2))).foldl
          (fun acc (p : Global × Bytecode.FunIdx) => acc.insert p.1 p.2)
          (∅ : Std.HashMap Global Bytecode.FunIdx) := by
    rw [List.foldl_map]
  rw [hfold_eq]
  have hdist_pre : preNameMap.toList.Pairwise
      (fun a b : Global × Bytecode.FunIdx => (a.1 == b.1) = false) :=
    Std.HashMap.distinct_keys_toList
  have hdist : (preNameMap.toList.map (fun p => (p.1, remap p.2))).Pairwise
      (fun a b : Global × Bytecode.FunIdx => (a.1 == b.1) = false) := by
    rw [List.pairwise_map]
    exact hdist_pre
  rw [Std.HashMap.getElem?_foldl_insert_of_pairwise_distinct
        (preNameMap.toList.map (fun p => (p.1, remap p.2))) name hdist]
  rw [List.find?_map]
  show (Option.map Prod.snd
          ((preNameMap.toList.find? (fun x => x.1 == name)).map
             (fun p => (p.1, remap p.2))))
        = (preNameMap[name]?).map remap
  cases hfind : preNameMap.toList.find? (fun x => x.1 == name) with
  | none =>
    have hnot : ¬ name ∈ preNameMap := by
      rw [← Std.HashMap.find?_toList_eq_none_iff_not_mem]; exact hfind
    have hpre : preNameMap[name]? = none := Std.HashMap.getElem?_eq_none hnot
    rw [hpre]
    rfl
  | some p =>
    have htlr := Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some
        (m := preNameMap) (k := name) (k' := p.1) (v := p.2)
    rw [show (⟨p.1, p.2⟩ : Global × Bytecode.FunIdx) = p from rfl] at htlr
    rw [(htlr.mp hfind).2]
    rfl





















/-! ## `compile_ok_implies_struct_compatible_entry` — Wire B closure.

Per-entry version of the deleted FullyMono predecessor `compile_ok_implies_struct_compatible`.
Discharges three of four `StructCompatible` conjuncts directly (no entry hypothesis
needed, no FullyMono needed). The fourth (`input_layout_matches`) is captured as
a single named entry-bridge stub with documented closure path. -/

/-- Every index inserted by `toBytecode` into `preNameMap` is strictly less
than the final `functions.size`. -/
private theorem preNameMap_in_range
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (h : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap)) :
    ∀ (name : Global) (i : Bytecode.FunIdx),
      preNameMap[name]? = some i → i < bytecodeRaw.functions.size :=
  (toBytecode_fold_invariant h).1

/-- Shape of `ct.bytecode.functions`: the dedup output with a `constrained`
field patched in by `needsCircuit`. Direct definitional unpacking of
`Source.Toplevel.compile`. -/
private theorem compile_ct_functions_shape
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (hct : t.compile = .ok ct)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap)) :
    ∃ needs : Array Bool,
      ct.bytecode.functions =
        bytecodeDedup.functions.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }) := by
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  refine ⟨bytecodeDedup.needsCircuit, ?_⟩
  rw [← hct_eq]

/-- `mapIdx` with a `constrained`-only record update preserves `size` and
every `body`. -/
private theorem needsCircuit_preserves_body
    (fs : Array Bytecode.Function) (needs : Array Bool) :
    (fs.mapIdx (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size
      = fs.size ∧
    ∀ fi (hfi : fi < fs.size),
      have hfi' : fi < (fs.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size := by
        have : (fs.mapIdx
          (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size = fs.size :=
          Array.size_mapIdx
        exact this ▸ hfi
      (fs.mapIdx (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }))[fi].body
        = fs[fi].body := by
  refine ⟨Array.size_mapIdx, ?_⟩
  intro fi hfi
  simp [Array.getElem_mapIdx]

/-! ### Per-conjunct sub-lemmas.

Layout-transport helpers used inside `compile_ok_input_layout_matches_entry`:
`needsCircuit_preserves_layout`, `deduplicate_layout_loop_invariant`,
`deduplicate_preserves_layout`, and `toBytecode_function_layout`. -/

/-- Joint layout invariant of `Toplevel.deduplicate`'s canonicalization loop.
Provable because dedup's skeleton key uses the full `FunctionLayout`
(see `Compiler/Dedup.lean`): same-class functions agree on every layout
field. The witness `j` at position `fi := remap preIdx` is a raw index with
`classes[j] = fi = remap preIdx = classes[preIdx]`; same-final-class implies
same-initial-class (`partitionRefine` only splits, never merges) which implies
equal skeletons-with-layout (`assignClasses` collision-free). -/
private theorem deduplicate_layout_loop_invariant
    (t : Bytecode.Toplevel) :
    let (tDedup, remap) := t.deduplicate
    ∀ preIdx (_hpre : preIdx < t.functions.size)
      (_hremap : remap preIdx < tDedup.functions.size),
      t.functions[preIdx].layout = tDedup.functions[remap preIdx].layout := by
  simp only
  intro preIdx hpre hremap_lt
  -- Step 1: extract a raw index `j` whose layout matches `tDedup`'s at
  -- position `(t.deduplicate).2 preIdx`, plus `classes[j] = (t.deduplicate).2 preIdx`.
  have hprov := dedup_indexed_provenance_aux t ((t.deduplicate).2 preIdx) hremap_lt
  simp only at hprov
  obtain ⟨j, hj, hlayout, hj_cls, hclasses⟩ := hprov
  -- Step 2: `remap preIdx = classes[preIdx]` (in-range).
  have hremap_eq : (t.deduplicate).2 preIdx =
      (deduplicate_classes_of t)[preIdx]! :=
    deduplicate_remap_eq_classes t preIdx hpre
  simp only at hremap_eq
  have hpre_cls : preIdx < (deduplicate_classes_of t).size := by
    unfold deduplicate_classes_of
    by_cases hn : t.functions.size = 0
    · exact absurd hpre (hn ▸ Nat.not_lt_zero _)
    · have hne_bool : (t.functions.size == 0) = false := by simp [hn]
      rw [hne_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [partitionRefine_size_eq, assignClasses_size_eq, Array.size_map]
      exact hpre
  have hremap_eq' : (t.deduplicate).2 preIdx =
      (deduplicate_classes_of t)[preIdx]'hpre_cls := by
    rw [hremap_eq, getElem!_pos _ preIdx hpre_cls]
  -- Step 3: `classes[j] = classes[preIdx]`.
  have hcls_eq : (deduplicate_classes_of t)[j]'hj_cls =
      (deduplicate_classes_of t)[preIdx]'hpre_cls := by
    rw [hclasses, hremap_eq']
  -- Step 4: Unfold `deduplicate_classes_of` to expose `partitionRefine`.
  have hn_bool : (t.functions.size == 0) = false := by
    have hn : ¬ t.functions.size = 0 := fun h => absurd hpre (h ▸ Nat.not_lt_zero _)
    simp [hn]
  have hdc_eq : deduplicate_classes_of t =
      Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body) := by
    unfold deduplicate_classes_of
    rw [hn_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
  have hj_pr : j < (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body)).size := by
    rw [← hdc_eq]; exact hj_cls
  have hpre_pr : preIdx < (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body)).size := by
    rw [← hdc_eq]; exact hpre_cls
  have hcls_eq_pr : (Bytecode.partitionRefine
      (Bytecode.assignClasses (t.functions.map fun f =>
        (Bytecode.skeletonBlock f.body, f.layout))).1
      (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[j]'hj_pr =
      (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[preIdx]'hpre_pr := by
    have h1 : (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[j]'hj_pr =
        (deduplicate_classes_of t)[j]'hj_cls :=
      (getElem_congr_coll hdc_eq).symm
    have h2 : (Bytecode.partitionRefine
        (Bytecode.assignClasses (t.functions.map fun f =>
          (Bytecode.skeletonBlock f.body, f.layout))).1
        (t.functions.map fun f => Bytecode.collectCalleesBlock f.body))[preIdx]'hpre_pr =
        (deduplicate_classes_of t)[preIdx]'hpre_cls :=
      (getElem_congr_coll hdc_eq).symm
    rw [h1, h2, hcls_eq]
  -- Step 5: Apply `partitionRefine_only_splits` for initial-class equality.
  let skeletons := t.functions.map fun f =>
    (Bytecode.skeletonBlock f.body, f.layout)
  let initClasses := (Bytecode.assignClasses skeletons).1
  let callees := t.functions.map fun f => Bytecode.collectCalleesBlock f.body
  have hic_sz : initClasses.size = t.functions.size := by
    show (Bytecode.assignClasses skeletons).1.size = t.functions.size
    rw [assignClasses_size_eq]
    show skeletons.size = _
    simp [skeletons]
  have hj_ic : j < initClasses.size := hic_sz ▸ hj
  have hpre_ic : preIdx < initClasses.size := hic_sz ▸ hpre
  have hic_eq : initClasses[j]'hj_ic = initClasses[preIdx]'hpre_ic := by
    have := partitionRefine_only_splits initClasses callees j preIdx hj_ic hpre_ic
    apply this
    show (Bytecode.partitionRefine initClasses callees)[j]'_ =
      (Bytecode.partitionRefine initClasses callees)[preIdx]'_
    exact hcls_eq_pr
  -- Step 6: lift to same skeletons-with-layout.
  have hsk_sz : skeletons.size = t.functions.size := by simp [skeletons]
  have hj_sk : j < skeletons.size := hsk_sz ▸ hj
  have hpre_sk : preIdx < skeletons.size := hsk_sz ▸ hpre
  have hi_acl : preIdx < (Bytecode.assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hpre_sk
  have hj_acl : j < (Bytecode.assignClasses skeletons).1.size := by
    rw [assignClasses_size_eq]; exact hj_sk
  have h_acl_eq : (Bytecode.assignClasses skeletons).1[j]'hj_acl =
      (Bytecode.assignClasses skeletons).1[preIdx]'hi_acl := hic_eq
  have hsk_eq : skeletons[j]'hj_sk = skeletons[preIdx]'hpre_sk :=
    assignClasses_values_eq_of_classes_eq skeletons j preIdx hj_acl hi_acl h_acl_eq
  have h_j : skeletons[j]'hj_sk =
      (Bytecode.skeletonBlock t.functions[j].body, t.functions[j].layout) := by
    show (t.functions.map fun f =>
      (Bytecode.skeletonBlock f.body, f.layout))[j]'hj_sk = _
    simp [Array.getElem_map]
  have h_pre : skeletons[preIdx]'hpre_sk =
      (Bytecode.skeletonBlock t.functions[preIdx].body,
       t.functions[preIdx].layout) := by
    show (t.functions.map fun f =>
      (Bytecode.skeletonBlock f.body, f.layout))[preIdx]'hpre_sk = _
    simp [Array.getElem_map]
  rw [h_j, h_pre] at hsk_eq
  have hlayout_eq : t.functions[j].layout = t.functions[preIdx].layout :=
    (Prod.mk.inj hsk_eq).2
  -- Step 7: combine with `hlayout`. Goal has dedup-layout on RHS; `hlayout`
  -- equates that to `functions[j].layout`, then `hlayout_eq` finishes.
  rw [← hlayout_eq]; exact hlayout.symm

/-- `Toplevel.deduplicate` preserves per-function `layout`. -/
private theorem deduplicate_preserves_layout
    {bytecodeRaw bytecodeDedup : Bytecode.Toplevel}
    {remap : Bytecode.FunIdx → Bytecode.FunIdx}
    (hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap))
    (preIdx : Bytecode.FunIdx) (hlt : preIdx < bytecodeRaw.functions.size)
    (hlt' : remap preIdx < bytecodeDedup.functions.size) :
    bytecodeRaw.functions[preIdx].layout =
      bytecodeDedup.functions[remap preIdx].layout := by
  have hloop := deduplicate_layout_loop_invariant bytecodeRaw
  simp only [hdedup] at hloop
  exact hloop preIdx hlt hlt'

/-- `mapIdx (fun i f => { f with constrained := needs[i]! })` preserves
`layout` pointwise — only `constrained` changes. Companion of
`needsCircuit_preserves_body`. -/
private theorem needsCircuit_preserves_layout
    (fs : Array Bytecode.Function) (needs : Array Bool)
    (fi : Nat) (hfi : fi < fs.size) :
    have hfi' : fi < (fs.mapIdx
        (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size := by
      have : (fs.mapIdx
        (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! })).size = fs.size :=
        Array.size_mapIdx
      exact this ▸ hfi
    (fs.mapIdx
      (fun i (f : Bytecode.Function) => { f with constrained := needs[i]! }))[fi].layout
        = fs[fi].layout := by
  simp [Array.getElem_mapIdx]

/-- `toBytecode`'s fold yields bytecode functions whose `FunctionLayout` is
the one produced by `Concrete.Function.compile` on the corresponding concrete
function. Signature adds `hNameAgrees` (needed to identify
`(xname, .function f)` pair with `f.name = xname`); callers thread
`concretize_nameAgrees` in. -/
private theorem toBytecode_function_layout
    {cd : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {layoutMap : LayoutMap}
    (hlayout : cd.layoutMap = .ok layoutMap)
    (hbc : cd.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (name : Global) (concF : Concrete.Function) (preIdx : Bytecode.FunIdx)
    (hget : cd.getByKey name = some (.function concF))
    (hnamePre : preNameMap[name]? = some preIdx)
    (hlt : preIdx < bytecodeRaw.functions.size) :
    ∃ body lms, Concrete.Function.compile layoutMap concF = .ok (body, lms) ∧
      bytecodeRaw.functions[preIdx].layout = lms.functionLayout := by
  rw [Concrete.Decls.toBytecode_unfold] at hbc
  simp only [bind, Except.bind, pure, Except.pure] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  rename_i layout' hlayout'
  have hlm_eq : layout' = layoutMap := by
    have := Except.ok.inj (hlayout' ▸ hlayout); exact this
  simp only [IndexMap.foldlM] at hbc
  split at hbc
  · exact absurd hbc (by intro heq; cases heq)
  rename_i triple htriple
  obtain ⟨functions, memSizes, nameMap⟩ := triple
  simp only at hbc
  have hEq := Prod.mk.inj (Except.ok.inj hbc)
  have hBC : (⟨functions, memSizes.toArray⟩ : Bytecode.Toplevel) = bytecodeRaw := hEq.1
  have hNM : nameMap = preNameMap := hEq.2
  rw [← Array.foldlM_toList, hlm_eq] at htriple
  let P : (Array Bytecode.Function × Lean.RBTree Nat compare ×
      Std.HashMap Global Bytecode.FunIdx) → Prop :=
    fun acc =>
      ∀ nm idx, (acc.2.2 : Std.HashMap Global Bytecode.FunIdx)[nm]? = some idx →
        idx < acc.1.size ∧
        ∃ (f : Concrete.Function) (body : Bytecode.Block) (lms : Concrete.Bytecode.LayoutMState),
          cd.getByKey nm = some (.function f) ∧
          Concrete.Function.compile layoutMap f = .ok (body, lms) ∧
          acc.1[idx]?.map (·.layout) = some lms.functionLayout
  have hP_init : P (#[], (Lean.RBTree.empty : Lean.RBTree Nat compare), {}) := by
    intro nm idx hget'; simp at hget'
  have hP_step : ∀ acc x acc',
      x ∈ cd.pairs.toList →
      (match x.2 with
        | Concrete.Declaration.function function => do
          let (body, layoutMState) ← Concrete.Function.compile layoutMap function
          let nameMap := acc.2.2.insert function.name acc.1.size
          let function' : Bytecode.Function :=
            ⟨body, layoutMState.functionLayout, function.entry, false⟩
          let memSizes := layoutMState.memSizes.fold (·.insert ·) acc.2.1
          pure (acc.1.push function', memSizes, nameMap)
        | _ => pure acc : Except String _) = .ok acc' →
      P acc → P acc' := by
    rintro ⟨accF, accM, accN⟩ ⟨xname, decl⟩ ⟨accF', accM', accN'⟩ hmem hok hP
    match decl with
    | .function function =>
      simp only [bind, Except.bind] at hok
      split at hok
      · exact absurd hok (by intro heq; cases heq)
      rename_i res hcomp
      obtain ⟨body, layoutMState⟩ := res
      simp only [pure, Except.pure] at hok
      have hprod := Prod.mk.inj (Except.ok.inj hok)
      have hF : accF' = accF.push
          ⟨body, layoutMState.functionLayout, function.entry, false⟩ := hprod.1.symm
      have hinner := Prod.mk.inj hprod.2
      have hN' : accN' = accN.insert function.name accF.size := hinner.2.symm
      subst hF; subst hN'
      intro nm idx hget'
      by_cases hname : (function.name == nm) = true
      · rw [Std.HashMap.getElem?_insert] at hget'
        simp only [hname, ↓reduceIte] at hget'
        have hi : idx = accF.size := (Option.some.inj hget').symm
        subst hi
        refine ⟨?_, function, body, layoutMState, ?_, hcomp, ?_⟩
        · rw [Array.size_push]; exact Nat.lt_succ_self _
        · have hxname : xname = function.name := hNameAgrees xname function hmem
          have hgbk : cd.getByKey xname = some (.function function) :=
            IndexMap.getByKey_of_mem_pairs cd xname _ hmem
          have hxn : (xname == nm) = true := by rw [hxname]; exact hname
          unfold IndexMap.getByKey at hgbk ⊢
          rw [Std.HashMap.getElem?_congr (hab := hxn)] at hgbk
          exact hgbk
        · have hh : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[accF.size]? =
              some ⟨body, layoutMState.functionLayout, function.entry, false⟩ := by
            simp
          rw [hh]
          rfl
      · have hname' : (function.name == nm) = false :=
          Bool.not_eq_true _ |>.mp hname
        rw [Std.HashMap.getElem?_insert] at hget'
        simp only [hname'] at hget'
        have ⟨hidx, f', body', lms', hgbk, hcmp, hlayoutEq⟩ := hP nm idx hget'
        have hidx' : idx < accF.size := hidx
        refine ⟨?_, f', body', lms', hgbk, hcmp, ?_⟩
        · rw [Array.size_push]; exact Nat.lt_succ_of_lt hidx'
        · have h1 : (accF.push ⟨body, layoutMState.functionLayout,
              function.entry, false⟩)[idx]? = some accF[idx] :=
            Array.getElem?_push_lt (h := hidx')
          rw [h1]
          have h2 : (accF[idx]? : Option Bytecode.Function) = some accF[idx] := by
            simp [getElem?_pos, hidx']
          rw [h2] at hlayoutEq
          exact hlayoutEq
    | .dataType _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
    | .constructor _ _ =>
      simp only [pure, Except.pure] at hok
      have heq := Except.ok.inj hok
      have hF : accF' = accF := ((Prod.mk.inj heq).1).symm
      have hN' : accN' = accN := ((Prod.mk.inj (Prod.mk.inj heq).2).2).symm
      subst hF; subst hN'
      exact hP
  have hP_final : P (functions, memSizes, nameMap) :=
    List.foldlM_except_invariant cd.pairs.toList _ _ hP_init hP_step htriple
  rw [← hNM] at hnamePre
  obtain ⟨_hidx, f, body, lms, hgbk, hcmp, hlayoutBc⟩ := hP_final name preIdx hnamePre
  have hfeq : f = concF := by
    rw [hgbk] at hget
    exact Concrete.Declaration.function.inj (Option.some.inj hget)
  subst hfeq
  refine ⟨body, lms, hcmp, ?_⟩
  have hfun_eq : bytecodeRaw.functions = functions := by cases hBC; rfl
  have hlt' : preIdx < functions.size := by rw [hfun_eq] at hlt; exact hlt
  have hget?eq : functions[preIdx]? = some functions[preIdx] :=
    Array.getElem?_eq_getElem hlt'
  rw [hget?eq] at hlayoutBc
  simp only [Option.map_some, Option.some.injEq] at hlayoutBc
  have heq_rec : bytecodeRaw.functions[preIdx]'hlt = functions[preIdx]'hlt' :=
    getElem_congr_coll hfun_eq
  rw [heq_rec, hlayoutBc]

/-- Sub-lemma: reachability is tautological under the restated definition. -/
private theorem compile_ok_total_on_reachable
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (_hdecls : t.mkDecls = .ok decls)
    (_hct : t.compile = .ok ct) :
    ∀ (name : Global), reachableFromEntries decls (fun g => ct.nameMap[g]?) name →
      ∃ fi, ct.nameMap[name]? = some fi := by
  intro name h
  simp only [reachableFromEntries] at h
  exact Option.isSome_iff_exists.mp h

/-- Sub-lemma: every `FunIdx` in `nameMap` is in range of `bc.functions`. -/
private theorem compile_ok_funIdx_valid
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (hct : t.compile = .ok ct) :
    ∀ (name : Global) (fi : Bytecode.FunIdx),
      ct.nameMap[name]? = some fi → fi < ct.bytecode.functions.size := by
  intro name fi hname
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  have hname_eq : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by rw [← hct_eq]
  have hbc_eq : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name] at hname
  match hpre : preNameMap[name]? with
  | none => rw [hpre] at hname; simp at hname
  | some preIdx =>
    rw [hpre, Option.map_some] at hname
    have hfi : fi = remap preIdx := (Option.some.injEq _ _).mp hname.symm
    have hpre_lt : preIdx < bytecodeRaw.functions.size :=
      preNameMap_in_range hbc name preIdx hpre
    have hremap_lt : remap preIdx < bytecodeDedup.functions.size :=
      deduplicate_remap_in_range hdedup preIdx hpre_lt
    have hsize : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
      rw [hbc_eq]; simp [Array.size_mapIdx]
    rw [hsize, hfi]
    exact hremap_lt

/-- Sub-lemma: the bytecode call graph is closed. -/
private theorem compile_ok_call_graph_closed
    {t : Source.Toplevel} {ct : CompiledToplevel}
    (hct : t.compile = .ok ct) :
    ∀ fi (h : fi < ct.bytecode.functions.size),
      ∀ callee, callee ∈ (Bytecode.Block.collectAllCallees ct.bytecode.functions[fi].body) →
      callee < ct.bytecode.functions.size := by
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  have hraw := toBytecode_callees_in_range (concDecls := concDecls) hbc
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  have hdd := deduplicate_preserves_callee_range hdedup hraw
  obtain ⟨needs, hshape⟩ := compile_ct_functions_shape hct hts hconc hbc hdedup
  have hmap := needsCircuit_preserves_body bytecodeDedup.functions needs
  have hsize : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
    rw [hshape]; exact hmap.1
  intro fi h callee hmem
  have hfi' : fi < bytecodeDedup.functions.size := hsize ▸ h
  have hbody : ct.bytecode.functions[fi].body = bytecodeDedup.functions[fi].body := by
    have hbody_mapped := hmap.2 fi hfi'
    have hct_body :
        ct.bytecode.functions[fi]'h
          = (bytecodeDedup.functions.mapIdx
              (fun i (f : Bytecode.Function) =>
                { f with constrained := needs[i]! }))[fi]'(hshape ▸ h) :=
      getElem_congr_coll hshape
    rw [congrArg Bytecode.Function.body hct_body, hbody_mapped]
  rw [hbody] at hmem
  exact hsize ▸ hdd fi hfi' callee hmem

/-! ### Entry-restricted `input_layout_matches`.

Witness shape for the entry hypothesis as it appears at top level: there
exists a function in `decls` keyed at `name` with `entry = true`. Mirrors
`HasEntryFn` in `CompilerPreservation.lean`. -/

@[expose, reducible]
def StructCompatibleHasEntryFn (decls : Source.Decls) : Prop :=
  ∃ (name : Global) (f : Source.Function),
    decls.getByKey name = some (.function f) ∧ f.entry = true

/-! ### Granular decomposition of the per-key flat-size/typSize bridge.

The bridge (`concretize_extract_concF_flat_size_bridge_wf`, below) is split
into three named sub-bridges:

* `concretize_input_pairs_match_wf` — per-position `MatchesConcreteFM`
  between typed-side `tf.inputs[i].snd` and concrete-side `concF.inputs[i].snd`
  (plus length agreement). Derived from `concretizeBuild`'s structural
  rewrite + `step4Lower`'s `typToConcrete` mapM.
* `typFlatSize_eq_typSize_under_match_wf` — per-pair flat-size/typSize
  agreement under `MatchesConcreteFM` and decls/layoutMap data-type agreement.
* `concretize_inputs_foldl_via_match_wf` — composition: per-position match
  + per-pair agreement implies the fold-sums agree.

Each sub-bridge carries its own `BLOCKED-<tag>` granular sorry with a
documented closure path. The outer bridge body composes them.
-/

/-- Per-position structural lemma: for any source `Typ` `t`, the result of
`typToConcrete ∅ (rewriteTyp emptySubst mono t)` (when it succeeds) is related
to `t` by `MatchesConcreteFM`. The `.mvar` arm fails (so the conclusion is
vacuous when `t` contains `.mvar`). -/
private theorem match_typToConcrete_rewriteTyp
    (mono : MonoMap) :
    ∀ (t : Typ) (ct : Concrete.Typ),
      typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)
          (rewriteTyp (fun _ => none) mono t) = .ok ct →
      Typ.MatchesConcreteFM t ct
  | .unit, ct, h => by
    simp [rewriteTyp, typToConcrete, pure, Except.pure] at h
    subst h; exact .unit
  | .field, ct, h => by
    simp [rewriteTyp, typToConcrete, pure, Except.pure] at h
    subst h; exact .field
  | .ref g, ct, h => by
    simp [rewriteTyp, typToConcrete, pure, Except.pure] at h
    subst h; exact .ref
  | .pointer t, ct, h => by
    -- rewriteTyp (.pointer t) = .pointer (rewriteTyp t).
    -- typToConcrete (.pointer t') = do let ct' ← typToConcrete t'; pure (.pointer ct').
    unfold rewriteTyp at h
    unfold typToConcrete at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i ct' hct'
    cases h
    exact .pointer (match_typToConcrete_rewriteTyp mono t ct' hct')
  | .array t n, ct, h => by
    unfold rewriteTyp at h
    unfold typToConcrete at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i ct' hct'
    cases h
    exact .array (match_typToConcrete_rewriteTyp mono t ct' hct')
  | .tuple ts, ct, h => by
    -- rewriteTyp (.tuple ts) = .tuple (ts.attach.map fun ⟨t, _⟩ => rewriteTyp t).
    -- typToConcrete (.tuple ts') = do let cts ← ts'.attach.mapM ...; pure (.tuple cts).
    unfold rewriteTyp at h
    unfold typToConcrete at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i cts hcts
    cases h
    -- Use `Array.mapM_eq_mapM_toList` to convert the Array.attach.mapM into a
    -- List.mapM, then use `List.mapM_except_ok_length` and `_getElem`.
    have hcts_list := hcts
    rw [Array.mapM_eq_mapM_toList] at hcts_list
    -- hcts_list : List.toArray <$> (...).attach.toList.mapM ... = .ok cts.
    -- Analyze the Functor.map / Except.map structure by cases on inner result.
    cases h_inner :
        ((ts.attach.map fun (p : {x // x ∈ ts}) =>
            rewriteTyp (fun _ => none) mono p.val).attach.toList.mapM
            fun (p : {x // x ∈ _}) =>
              typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) p.val) with
    | error _ =>
      rw [h_inner] at hcts_list
      simp [Functor.map, Except.map] at hcts_list
    | ok cts_list =>
    rw [h_inner] at hcts_list
    have hcts_eq_ofList : cts = cts_list.toArray := by
      simp only [Functor.map, Except.map, Except.ok.injEq] at hcts_list
      exact hcts_list.symm
    have hcts_list2 := h_inner
    -- Length agreement.
    have hlen_list := List.mapM_except_ok_length hcts_list2
    -- (ts.attach.map _).attach.toList.length = ts.size.
    have hlen_attach_list :
        ((ts.attach.map (fun (p : {x // x ∈ ts}) =>
          rewriteTyp (fun _ => none) mono p.val)).attach.toList).length = ts.size := by
      rw [Array.length_toList, Array.size_attach, Array.size_map, Array.size_attach]
    have hcts_size : cts.size = ts.size := by
      rw [hcts_eq_ofList]
      simp [List.size_toArray]
      omega
    refine .tuple (by omega) ?_
    intro i h₁ h₂
    -- Per-position: cts_list[i] (and so cts[i]) = result of typToConcrete on
    -- the (attach.map _).attach.toList[i].val = rewriteTyp (...) ts[i].
    have hi_attach : i < ((ts.attach.map (fun (p : {x // x ∈ ts}) =>
        rewriteTyp (fun _ => none) mono p.val)).attach.toList).length := by
      rw [hlen_attach_list]; exact h₁
    have hperpos := List.mapM_except_ok_getElem hcts_list2 i hi_attach
    have hi_cts_list : i < cts_list.length := by omega
    -- hperpos : typToConcrete ∅ ((...attach.toList)[i].val) = .ok cts_list[i].
    -- Identify the lhs.
    have hidx_attach :
        (((ts.attach.map (fun (p : {x // x ∈ ts}) =>
          rewriteTyp (fun _ => none) mono p.val)).attach.toList)[i]'hi_attach).val =
        rewriteTyp (fun _ => none) mono (ts[i]'h₁) := by
      simp [Array.getElem_toList, Array.getElem_attach, Array.getElem_map]
    rw [hidx_attach] at hperpos
    -- cts[i] = cts_list.toArray[i] = cts_list[i].
    have hcts_idx : cts[i]'h₂ = cts_list[i]'hi_cts_list := by
      subst hcts_eq_ofList
      exact List.getElem_toArray hi_cts_list
    rw [hcts_idx]
    exact match_typToConcrete_rewriteTyp mono (ts[i]'h₁) (cts_list[i]'hi_cts_list) hperpos
  | .function ins out, ct, h => by
    -- rewriteTyp (.function ins out) = .function (ins.attach.map ...) (rewriteTyp out).
    -- typToConcrete: do let ins' ← (ins.attach.map ...).attach.mapM ...; let out' ← typToConcrete out; pure ...
    unfold rewriteTyp at h
    unfold typToConcrete at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i cins hcins
    split at h
    · cases h
    rename_i cout hcout
    cases h
    -- hcins : (ins.attach.map (fun ⟨t, _⟩ => rewriteTyp ... t)).attach.mapM ... = .ok cins
    -- Reduce attach.mapM via the underlying list. Use mapM length/getElem helpers.
    have hattach_len :
        (ins.attach.map (fun (p : {x // x ∈ ins}) =>
          rewriteTyp (fun _ => none) mono p.val)).length = ins.length := by
      rw [List.length_map, List.length_attach]
    have hattach_attach_len :
        (ins.attach.map (fun (p : {x // x ∈ ins}) =>
          rewriteTyp (fun _ => none) mono p.val)).attach.length = ins.length := by
      rw [List.length_attach]; exact hattach_len
    have hcins_len : cins.length = ins.length := by
      have := List.mapM_except_ok_length hcins
      omega
    refine .function ?_ ?_ (match_typToConcrete_rewriteTyp mono out cout hcout)
    · omega
    · intro i h₁ h₂
      -- Per-position
      have hi_attach : i < (ins.attach.map (fun (p : {x // x ∈ ins}) =>
            rewriteTyp (fun _ => none) mono p.val)).attach.length := by
        omega
      have hperpos := List.mapM_except_ok_getElem hcins i hi_attach
      -- hperpos : typToConcrete ∅ ((attach...)[i].val) = .ok cins[i].
      -- Identify (attach...)[i].val = rewriteTyp ... ins[i].
      have hidx_attach :
          (((ins.attach.map (fun (p : {x // x ∈ ins}) =>
            rewriteTyp (fun _ => none) mono p.val)).attach)[i]'hi_attach).val =
          rewriteTyp (fun _ => none) mono (ins[i]'h₁) := by
        simp [List.getElem_attach, List.getElem_map]
      rw [hidx_attach] at hperpos
      exact match_typToConcrete_rewriteTyp mono (ins[i]'h₁) (cins[i]'h₂) hperpos
  | .app g args, ct, h => by
    -- rewriteTyp (.app g args) = match mono[(g, args)]? with
    --   | some concName => .ref concName
    --   | none => .app g (args.attach.map ...)
    -- Then typToConcrete on result.
    unfold rewriteTyp at h
    split at h
    · -- mono hit: rewriteTyp returns .ref concName; typToConcrete returns .ref concName.
      rename_i concName hcontain
      simp [typToConcrete, pure, Except.pure] at h
      subst h
      exact .appResolved
    · -- mono miss: rewriteTyp returns .app g (args.attach.map ...).
      -- typToConcrete on .app: looks up (∅) which always fails, so returns .ref g.
      rename_i hmiss
      unfold typToConcrete at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      -- The `match mono[(g, args')]?` here uses `∅` so always misses.
      have hempty : (∅ : Std.HashMap (Global × Array Typ) Global)[(
          g, args.attach.map fun (p : {x // x ∈ args}) =>
            rewriteTyp (fun _ => none) mono p.val)]? = none :=
        Std.HashMap.getElem?_empty
      rw [hempty] at h
      cases h
      exact .appUnresolved
  | .mvar n, ct, h => by
    -- rewriteTyp on .mvar returns .mvar (default arm); typToConcrete on .mvar errors.
    unfold rewriteTyp at h
    unfold typToConcrete at h
    cases h
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
    | (have hmem : ins[i] ∈ ins := List.getElem_mem _
       have := List.sizeOf_lt_of_mem hmem
       grind)

/-- **Granular sub-bridge A — per-input-position `MatchesConcreteFM`.**

For an entry-shaped function (`tf.params = []` so `concretizeBuild`'s srcStep
inserts at `name`), the concrete inputs at the same key are obtained by
`typToConcrete ∘ rewriteTyp emptySubst mono` of the typed inputs. Each
`(rewriteTyp _ mono t, typToConcrete ∅ _)` pair is structurally related by
`Typ.MatchesConcreteFM` (per its `appEmpty`/`appResolved`/`appUnresolved` arms
and structural arms for tuples/arrays/etc).

Closure path:
  1. Lift `htyped` through `concretizeBuild_at_typed_function_explicit`
     (CtorKind.lean:2018) to get `monoF.inputs = tf.inputs.map (fun (l,t) =>
     (l, rewriteTyp emptySubst mono t))`. Origin-split for the case where
     `name` is overridden by a newFn entry; uses `NewFnFullShape` +
     `ConcretizeUniqueNames` to identify the override as the empty-substitution
     collapse of `tf`.
  2. Lift through `step4Lower_function_explicit` (Shapes.lean:1369) to get
     `concF.inputs = monoF.inputs.mapM (fun (l,t) => (l, ← typToConcrete ∅ t)).ok`.
  3. Per-position structural induction on the source `Typ` via
     `match_typToConcrete_rewriteTyp`.

Wired from `concretize_extract_concF_flat_size_bridge_wf` below. -/
private theorem concretize_input_pairs_match_wf
    {t : Source.Toplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    {name : Global} {tf : Typed.Function} {concF : Concrete.Function}
    (htyped : typedDecls.getByKey name = some (.function tf))
    (hconcF : concDecls.getByKey name = some (.function concF)) :
    tf.inputs.length = concF.inputs.length ∧
    ∀ i (h₁ : i < tf.inputs.length) (h₂ : i < concF.inputs.length),
      Typ.MatchesConcreteFM ((tf.inputs[i]'h₁).snd) ((concF.inputs[i]'h₂).snd) := by
  -- Step 1: derive `tf.params = []` via the F=0 primitive.
  have hparams_empty : tf.params = [] :=
    typed_function_at_concrete_function_key_params_empty hwf hdecls hts hconc htyped hconcF
  -- Step 2: unfold `typedDecls.concretize` to extract `drained` and
  -- the `monoDecls.foldlM step4Lower` step.
  have hconc_unfold := hconc
  unfold Typed.Decls.concretize at hconc_unfold
  simp only [bind, Except.bind] at hconc_unfold
  split at hconc_unfold
  · contradiction
  rename_i drained hdrain
  -- Drain invariants we will need.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  have hNFFS : drained.NewFnFullShape typedDecls :=
    concretize_drain_preserves_NewFnFullShape _ _
      (DrainState.NewFnFullShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  have hUnique : Typed.Decls.ConcretizeUniqueNames typedDecls :=
    hwf.noNameCollisions typedDecls hts
  -- Step 3: backward step4Lower lift to `monoDecls.getByKey name = some (.function md_f)`.
  obtain ⟨md_f, hmd_get⟩ :=
    step4Lower_backward_function_kind_at_key hconcF hconc_unfold
  -- Step 4: forward step4Lower explicit yields `concF.inputs = mapM typToConcrete md_f.inputs`.
  obtain ⟨cd_f', hcd_get_full, _hname_eq, hinputs_witness, _houtput_witness⟩ :=
    step4Lower_function_explicit hmd_get hconc_unfold
  have heq_f : cd_f' = concF := by
    rw [hcd_get_full] at hconcF
    have h1 : Concrete.Declaration.function cd_f' = .function concF := Option.some.inj hconcF
    injection h1
  rw [heq_f] at hinputs_witness
  -- `hinputs_witness : md_f.inputs.mapM (fun p => do let t' ← typToConcrete ∅ p.2; pure (p.1, t'))
  --                  = .ok concF.inputs`.
  -- Step 5: identify `md_f.inputs` in terms of `tf.inputs`. Origin split.
  have hcd_at_name : ∃ d, concDecls.getByKey name = some d := ⟨_, hconcF⟩
  have hname_self : concretizeName name #[] = name := concretizeName_empty_args name
  have hmd_inputs_eq : md_f.inputs =
      tf.inputs.map (fun (lt : Local × Typ) =>
        (lt.1, rewriteTyp (fun _ => none) drained.mono lt.2)) := by
    -- Disjointness premises for `concretizeBuild_at_typed_function_explicit`.
    have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
      intro dt' hmem heq
      obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, _, _⟩ :=
        hSNN.2 dt' hmem
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hname_eq', heq, concretizeName_empty_args]
      have hKey : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hdt_orig_get
      rw [htyped] at hdt_orig_get
      cases (Option.some.inj hdt_orig_get : Typed.Declaration.function tf = .dataType dt_orig)
    have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ name := by
      intro dt' hmem c hc heq
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
      have heq_concName :
          concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
        rw [hLHS_eq, heq, concretizeName_empty_args]
      have hKey : ∃ d, concDecls.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_name
      obtain ⟨_, hargs_eq⟩ :=
        hUnique hconc dt'.name name #[collisionArg] #[] heq_concName hKey
      have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
      have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
      omega
    -- Origin split: monoF was inserted by either srcStep (case A) or fnStep (case B).
    by_cases hOverride : ∃ f' ∈ drained.newFunctions, f'.name = name
    · -- Case B: an override f' from newFunctions.
      obtain ⟨f', hf'_mem, hf'_name⟩ := hOverride
      obtain ⟨g_orig, args, f_orig, _hin_seen, hf_orig_get, _hsz, hf'_shape⟩ :=
        hNFFS f' hf'_mem
      have hf'_name' : f'.name = concretizeName g_orig args := by rw [hf'_shape]
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hf'_name', hf'_name, concretizeName_empty_args]
      have hKey : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hf_orig_get
      rw [htyped] at hf_orig_get
      have hf_orig_eq : f_orig = tf := by
        have h1 : Typed.Declaration.function tf = .function f_orig :=
          Option.some.inj hf_orig_get
        injection h1.symm
      have hsubst_empty : mkParamSubst f_orig.params args = fun _ => none := by
        rw [hf_orig_eq, hparams_empty, hargs_eq]
        funext g; simp [mkParamSubst]
      have hOtherFnNotKey : ∀ f'' ∈ drained.newFunctions, f'' ≠ f' →
          f''.name ≠ f'.name := by
        intro f'' hf''_mem hne heq2
        obtain ⟨g2, args2, f_orig2, _, hf_orig2_get, _, hf''_shape⟩ :=
          hNFFS f'' hf''_mem
        obtain ⟨g1, args1, f_orig1, _, hf_orig1_get, _, hf'_shape'⟩ :=
          hNFFS f' hf'_mem
        have hname_f'' : f''.name = concretizeName g2 args2 := by rw [hf''_shape]
        have hname_f' : f'.name = concretizeName g1 args1 := by rw [hf'_shape']
        have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
          rw [← hname_f'', heq2, hname_f']
        have hKey1 : ∃ d, concDecls.getByKey (concretizeName g2 args2) = some d := by
          rw [heq1, ← hname_f', hf'_name]; exact hcd_at_name
        obtain ⟨hg_eq', hargs_eq'⟩ :=
          hUnique hconc g2 g1 args2 args1 heq1 hKey1
        rw [hg_eq'] at hf_orig2_get
        rw [hf_orig1_get] at hf_orig2_get
        have hf_orig_eq' : f_orig2 = f_orig1 := by
          have h1 : Typed.Declaration.function f_orig1 =
              .function f_orig2 := Option.some.inj hf_orig2_get
          injection h1.symm
        apply hne
        rw [hf''_shape, hf'_shape', hg_eq', hargs_eq', hf_orig_eq']
      obtain ⟨md_f_at, hmd_at_get_fn, _hName_fn, hInputs_fn, _hOutput_fn, _hBody_fn⟩ :=
        PhaseA2.concretizeBuild_at_newFn_name_full_explicit typedDecls drained.mono
          drained.newFunctions drained.newDataTypes hf'_mem hOtherFnNotKey
      rw [hf'_name] at hmd_at_get_fn
      rw [hmd_at_get_fn] at hmd_get
      have hmd_eq : md_f_at = md_f := by
        have h1 : Typed.Declaration.function md_f_at = .function md_f :=
          Option.some.inj hmd_get
        injection h1
      rw [hmd_eq] at hInputs_fn
      -- f'.inputs collapses to tf.inputs via empty subst (hsubst_empty + hf_orig_eq).
      have hf'_inputs_proj : f'.inputs = f_orig.inputs.map fun (l, t) =>
          (l, Typ.instantiate (mkParamSubst f_orig.params args) t) := by
        rw [hf'_shape]
      have hf'_inputs_id : f'.inputs = tf.inputs := by
        rw [hf'_inputs_proj, hsubst_empty, hf_orig_eq]
        induction tf.inputs with
        | nil => rfl
        | cons hd tl ih =>
          cases hd with
          | mk l ty =>
            show (l, Typ.instantiate (fun _ => none) ty) ::
                tl.map (fun (lt : Local × Typ) =>
                  (lt.1, Typ.instantiate (fun _ => none) lt.2)) =
              (l, ty) :: tl
            rw [Typ.instantiate_empty_id, ih]
      rw [hf'_inputs_id] at hInputs_fn
      exact hInputs_fn
    · -- Case A: no override; monoF comes from srcStep's rewrite of tf.
      have hFnNotKey : ∀ f' ∈ drained.newFunctions, f'.name ≠ name := by
        intro f' hf'_mem hf'_name
        exact hOverride ⟨f', hf'_mem, hf'_name⟩
      have hexplicit :=
        PhaseA2.concretizeBuild_at_typed_function_explicit typedDecls drained.mono
          drained.newFunctions drained.newDataTypes htyped hparams_empty
          hDtNotKey hFnNotKey hCtorNotKey
      rw [hexplicit] at hmd_get
      -- hmd_get : some (.function monoF) = some (.function md_f)
      let monoF : Typed.Function :=
        { tf with
          inputs := tf.inputs.map fun (l, t) =>
            (l, rewriteTyp (fun _ => none) drained.mono t),
          output := rewriteTyp (fun _ => none) drained.mono tf.output,
          body := rewriteTypedTerm typedDecls (fun _ => none) drained.mono tf.body }
      have hmd_f_eq : md_f = monoF := by
        have h1 : Typed.Declaration.function monoF = .function md_f :=
          Option.some.inj hmd_get
        have h2 : monoF = md_f := by injection h1
        exact h2.symm
      rw [hmd_f_eq]
  -- Step 6: combine the inputs-shape with the typToConcrete mapM witness via
  -- `match_typToConcrete_rewriteTyp` (defined above) to conclude length
  -- agreement and per-position MatchesConcreteFM.
  refine ⟨?_, ?_⟩
  · -- Length agreement: `concF.inputs = md_f.inputs.mapM (...).ok`, so
    -- `concF.inputs.length = md_f.inputs.length = tf.inputs.length`.
    have hlen_md : md_f.inputs.length = tf.inputs.length := by
      rw [hmd_inputs_eq, List.length_map]
    have hmapM_len : concF.inputs.length = md_f.inputs.length :=
      List.mapM_except_ok_length hinputs_witness
    omega
  · intro i h₁ h₂
    -- Per-position MatchesConcreteFM. Use `hinputs_witness` to identify
    -- `concF.inputs[i].snd = typToConcrete ∅ (md_f.inputs[i].snd)`, then
    -- `hmd_inputs_eq` to identify `md_f.inputs[i].snd = rewriteTyp emptySubst
    -- mono (tf.inputs[i].snd)`. Then apply the structural lemma.
    have hmapM_len : concF.inputs.length = md_f.inputs.length :=
      List.mapM_except_ok_length hinputs_witness
    have h_md_lt : i < md_f.inputs.length := by omega
    have hperpos := List.mapM_except_ok_getElem hinputs_witness i h_md_lt
    -- hperpos : (do let t' ← typToConcrete ∅ (md_f.inputs[i]).snd; pure ((md_f.inputs[i]).fst, t'))
    --             = .ok (concF.inputs[i]'(...))
    -- Reduce do-block.
    simp only [bind, Except.bind, pure, Except.pure] at hperpos
    split at hperpos
    · cases hperpos
    rename_i ct' hct'
    -- ct' : Concrete.Typ, hct' : typToConcrete ∅ (md_f.inputs[i]).snd = .ok ct'
    -- hperpos becomes: .ok (md_f.inputs[i].fst, ct') = .ok concF.inputs[i].
    have h_pair : ((md_f.inputs[i]'h_md_lt).fst, ct') = concF.inputs[i]'h₂ := by
      simp only [Except.ok.injEq] at hperpos
      exact hperpos
    have h_snd : (concF.inputs[i]'h₂).snd = ct' := by rw [← h_pair]
    rw [h_snd]
    -- Now goal: MatchesConcreteFM (tf.inputs[i]).snd ct'.
    -- Identify (md_f.inputs[i]).snd via hmd_inputs_eq.
    -- md_f.inputs = tf.inputs.map (fun lt => (lt.1, rewriteTyp ... lt.2)).
    -- So md_f.inputs[i].snd = rewriteTyp ... (tf.inputs[i]).snd.
    have h_md_snd : (md_f.inputs[i]'h_md_lt).snd =
        rewriteTyp (fun _ => none) drained.mono (tf.inputs[i]'h₁).snd := by
      have : md_f.inputs[i]'h_md_lt =
          ((tf.inputs.map (fun (lt : Local × Typ) =>
            (lt.fst, rewriteTyp (fun _ => none) drained.mono lt.snd)))[i]'(by
              rw [List.length_map]; exact h₁)) := by
        congr 1
      rw [this, List.getElem_map]
    rw [h_md_snd] at hct'
    exact match_typToConcrete_rewriteTyp drained.mono _ _ hct'

/-- **Granular sub-bridge B — per-pair flat-size/typSize agreement under
`MatchesConcreteFM`.**

For any matched typed/concrete `Typ` pair, the typed-side `typFlatSize`
(over source decls) and the concrete-side `typSize` (over layoutMap, with
errors mapped to 0) agree.

Closure path (`BLOCKED-typ-flat-size-bridge`, ~150 LoC):
  Structural induction on `MatchesConcreteFM`:
  * `unit`/`field`/`pointer`/`function`: closed-form constants
    (`typFlatSizeBound_leaf_*` lemmas in `ConcretizeSound/RefClosed.lean:144+`).
  * `tuple`/`array`: structural recursion under fold/multiplication
    (componentwise via the IH).
  * `ref g`/`appEmpty g`: `typFlatSize decls {} (.ref g) =
    dataTypeFlatSize decls {} dt` for typed dt at `g`; `typSize layoutMap
    (.ref g) = (layoutMap[g]?).bind (·.dataType?)`. Agreement requires:
      - decls/concDecls dt-key agreement at `g` (via
        `concretize_preserves_function_kind_fwd_wf`-style infra).
      - `layoutMap[g]? = some (.dataType (dataTypeFlatSize ...))` agreement
        (via `concretize_layoutMap_progress` + per-dt closure).
  * `function`: opaque leaf, both sides constant 1.

Companion bridge `dataTypeFlatSize_eq_layoutMap_size_wf` (below) handles
the dt-side agreement that the `.ref` arm consumes. -/
private theorem typFlatSize_eq_typSize_under_match_wf
    {t : Source.Toplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hwf : WellFormed t)
    {layoutMap : LayoutMap} (_hlayout : concDecls.layoutMap = .ok layoutMap)
    -- Hoisted (relaxed-rule-11): the structural recursive arms of the
    -- `MatchesConcreteFM` induction. The leaf arms (unit/field/pointer/function)
    -- are closed inline via `Decidable.decide`-grade unfolding; the structural
    -- arms (tuple/array) and ref-shaped arms (ref/appEmpty/appResolved/
    -- appUnresolved) require either bound-saturation (the source-side
    -- `typFlatSizeBound (decls.size + 1)` body recurses at `decls.size`, while
    -- the IH is stated at the outer bound) or dispatch into the Layout chain
    -- (`dataTypeFlatSize_eq_layoutMap_size_wf` plus `layoutMap_dataType_size_extract`).
    -- These three premises are discharged at the consumer
    -- (`concretize_extract_concF_flat_size_bridge_wf`) by composing the per-arm
    -- saturation argument with the Layout-chain primitives. See PLAN.md
    -- "Sorry #11 cascade impact".
    (_hTupleArm :
      ∀ {ts : Array Typ} {cts : Array Concrete.Typ}
        (_hLen : ts.size = cts.size)
        (_hAll : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          Typ.MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂))
        (_hIH : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          typFlatSize decls {} (ts[i]'h₁) =
            (typSize layoutMap (cts[i]'h₂)).toOption.getD 0),
        typFlatSize decls {} (.tuple ts) =
          (typSize layoutMap (.tuple cts)).toOption.getD 0)
    (_hArrayArm :
      ∀ {t' : Typ} {ct' : Concrete.Typ} {n : Nat}
        (_hInner : Typ.MatchesConcreteFM t' ct')
        (_hIH : typFlatSize decls {} t' =
          (typSize layoutMap ct').toOption.getD 0),
        typFlatSize decls {} (.array t' n) =
          (typSize layoutMap (.array ct' n)).toOption.getD 0)
    -- Hoisted: per-ref-shaped-arm dispatch into the Layout chain. The four
    -- caller-provided continuations encode the `dataTypeFlatSize_eq_layoutMap_size_wf`
    -- + `layoutMap_dataType_size_extract` composition at the four ref-shaped
    -- constructors of `MatchesConcreteFM`. Each is discharged at the consumer
    -- by constructing the three Layout-chain premises (`_hLKM`,
    -- `_hCdTdLenAgree`, `_hDtFlatSizeAtTopBounds`) at the call site.
    (_hRefDispatch :
      ∀ (g : Global),
        typFlatSize decls {} (.ref g) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppEmptyDispatch :
      ∀ (g : Global),
        typFlatSize decls {} (.app g #[]) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppResolvedDispatch :
      ∀ (g : Global) (args : Array Typ) (concName : Global),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref concName)).toOption.getD 0)
    (_hAppUnresolvedDispatch :
      ∀ (g : Global) (args : Array Typ),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_t_typed : Typ) (_t_conc : Concrete.Typ)
    (_hmatch : Typ.MatchesConcreteFM _t_typed _t_conc) :
    typFlatSize decls {} _t_typed = (typSize layoutMap _t_conc).toOption.getD 0 := by
  -- Reachability keepalives — the closed Layout-chain primitives are consumed
  -- transitively at the consumer site to discharge the hoisted ref-dispatch
  -- premises above (`_hRefDispatch`, `_hAppEmptyDispatch`, etc.).
  let _ := @dataTypeFlatSize_eq_layoutMap_size_wf
  let _ := @layoutMap_dataType_size_extract
  -- Structural induction on the `MatchesConcreteFM` evidence. Leaves close
  -- inline via unfolding; structural and ref-shaped arms dispatch through the
  -- hoisted premises above.
  induction _hmatch with
  | unit =>
    show typFlatSize decls {} (.unit) = (typSize layoutMap (.unit)).toOption.getD 0
    unfold typFlatSize typFlatSizeBound typSize
    rfl
  | field =>
    show typFlatSize decls {} (.field) = (typSize layoutMap (.field)).toOption.getD 0
    unfold typFlatSize typFlatSizeBound typSize
    rfl
  | @pointer t' ct' _hInner _ihInner =>
    show typFlatSize decls {} (.pointer t') =
      (typSize layoutMap (.pointer ct')).toOption.getD 0
    unfold typFlatSize typFlatSizeBound typSize
    rfl
  | @function ins out cins cout _hLen _hAll _hOut _ihAllList _ihOut =>
    -- `function` is a closed-form opaque leaf: both sides return 1 regardless
    -- of inputs/output. Source: `typFlatSizeBound _ (_+1) _ (.function _ _) = 1`.
    -- Concrete: `typSize _ (.function _ _) = pure 1`, `.toOption.getD 0 = 1`.
    show typFlatSize decls {} (.function ins out) =
      (typSize layoutMap (.function cins cout)).toOption.getD 0
    unfold typFlatSize typFlatSizeBound typSize
    rfl
  | @tuple ts cts hLen hAll ihAll =>
    exact _hTupleArm hLen hAll ihAll
  | @array t' ct' n hInner ihInner =>
    exact _hArrayArm hInner ihInner
  | @ref g => exact _hRefDispatch g
  | @appEmpty g => exact _hAppEmptyDispatch g
  | @appResolved g args concName => exact _hAppResolvedDispatch g args concName
  | @appUnresolved g args => exact _hAppUnresolvedDispatch g args

/-- **Granular sub-bridge C — fold-sum lifting from per-position to
componentwise totals.**

Given length agreement and per-position pair agreement, the foldl-sums
agree. Pure list/`Nat` algebra; no concretize-specific content. -/
private theorem concretize_inputs_foldl_via_match_wf
    {decls : Source.Decls} {layoutMap : LayoutMap}
    (typedInputs : List (Local × Typ)) (concInputs : List (Local × Concrete.Typ))
    (hlen : typedInputs.length = concInputs.length)
    (hmatch : ∀ i (h₁ : i < typedInputs.length) (h₂ : i < concInputs.length),
      Typ.MatchesConcreteFM ((typedInputs[i]'h₁).snd) ((concInputs[i]'h₂).snd))
    (hpair : ∀ (t_typed : Typ) (t_conc : Concrete.Typ),
      Typ.MatchesConcreteFM t_typed t_conc →
      typFlatSize decls {} t_typed = (typSize layoutMap t_conc).toOption.getD 0) :
    (typedInputs.map Prod.snd).foldl
        (fun acc t => acc + typFlatSize decls {} t) 0 =
      (concInputs.map Prod.snd).foldl
        (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  -- Reduce to the displaced-accumulator form, then induct on the lists.
  have hgen : ∀ (n : Nat)
      (xs : List (Local × Typ)) (ys : List (Local × Concrete.Typ)),
      xs.length = ys.length →
      (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length),
        Typ.MatchesConcreteFM ((xs[i]'h₁).snd) ((ys[i]'h₂).snd)) →
      (xs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) n =
        (ys.map Prod.snd).foldl
          (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) n := by
    intro n xs
    induction xs generalizing n with
    | nil =>
      intro ys hl _
      have : ys = [] := List.length_eq_zero_iff.mp hl.symm
      subst this; simp
    | cons x xs ih =>
      intro ys hl hm
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.map_cons, List.foldl_cons]
        have hl' : xs.length = ys.length := by simp at hl; exact hl
        -- Head equality.
        have hhead : Typ.MatchesConcreteFM x.snd y.snd := by
          have h0₁ : 0 < (x :: xs).length := by simp
          have h0₂ : 0 < (y :: ys).length := by simp
          exact hm 0 h0₁ h0₂
        have heq_head :
            typFlatSize decls {} x.snd = (typSize layoutMap y.snd).toOption.getD 0 :=
          hpair _ _ hhead
        rw [heq_head]
        -- Tail induction.
        have hm' : ∀ i (h₁ : i < xs.length) (h₂ : i < ys.length),
            Typ.MatchesConcreteFM ((xs[i]'h₁).snd) ((ys[i]'h₂).snd) := by
          intro i h₁ h₂
          have hi₁ : i + 1 < (x :: xs).length := by simp; omega
          have hi₂ : i + 1 < (y :: ys).length := by simp; omega
          exact hm (i + 1) hi₁ hi₂
        exact ih (n + (typSize layoutMap y.snd).toOption.getD 0) ys hl' hm'
  exact hgen 0 typedInputs concInputs hlen hmatch

/-- **Per-key flat-size/typSize bridge (F=0 composition over 3 sub-bridges).**

Composes the granular sub-bridges A/B/C to discharge the per-key flat-size
identity. Closure structure:

  A) `concretize_input_pairs_match_wf` — per-position `MatchesConcreteFM`.
  B) `typFlatSize_eq_typSize_under_match_wf` — per-pair size agreement.
  C) `concretize_inputs_foldl_via_match_wf` — fold-lifting.

Wired from `concretize_extract_concF_at_reachable_wf` below. -/
private theorem concretize_extract_concF_flat_size_bridge_wf
    {t : Source.Toplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    {name : Global} {f : Source.Function} {tf : Typed.Function}
    {concF : Concrete.Function}
    (_hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf))
    (hconcF : concDecls.getByKey name = some (.function concF))
    -- Sig amendment 2026-05-04 (Defect 1, #11 layoutMap-binding): the
    -- universal `∀ (layoutMap : LayoutMap), <equation>` shape is provably
    -- False (counterexample: `layoutMap = ∅` makes
    -- `typSize ∅ (.ref g) = .error`, so RHS = 0 while LHS may be 1). Each
    -- premise is now guarded by the existence of the actual layoutMap
    -- derived from `concDecls.layoutMap = .ok layoutMap`. Discharged at
    -- the consumer (`compile_ok_implies_struct_compatible_of_entry`) by
    -- introducing `layoutMap` and `hlayout` from
    -- `toBytecode_layoutMap_ok hbc`.
    (_hTupleArm :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {ts : Array Typ} {cts : Array Concrete.Typ}
        (_hLen : ts.size = cts.size)
        (_hAll : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          Typ.MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂))
        (_hIH : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          typFlatSize decls {} (ts[i]'h₁) =
            (typSize layoutMap (cts[i]'h₂)).toOption.getD 0),
        typFlatSize decls {} (.tuple ts) =
          (typSize layoutMap (.tuple cts)).toOption.getD 0)
    (_hArrayArm :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {t' : Typ} {ct' : Concrete.Typ} {n : Nat}
        (_hInner : Typ.MatchesConcreteFM t' ct')
        (_hIH : typFlatSize decls {} t' =
          (typSize layoutMap ct').toOption.getD 0),
        typFlatSize decls {} (.array t' n) =
          (typSize layoutMap (.array ct' n)).toOption.getD 0)
    (_hRefDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.ref g) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppEmptyDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.app g #[]) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppResolvedDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ) (concName : Global),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref concName)).toOption.getD 0)
    (_hAppUnresolvedDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref g)).toOption.getD 0) :
    ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
      (tf.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 =
        (concF.inputs.map Prod.snd).foldl
          (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  intro layoutMap hlayout
  -- A: per-position MatchesConcreteFM.
  obtain ⟨hlen, hmatch⟩ :=
    concretize_input_pairs_match_wf hdecls hts hconc hwf htyped hconcF
  -- B: per-pair size agreement (curry over t_typed/t_conc/hmatch). Dispatches
  -- to the hoisted per-arm premises above; each premise is now constrained
  -- to layoutMap derived from `hlayout`.
  have hpair : ∀ (t_typed : Typ) (t_conc : Concrete.Typ),
      Typ.MatchesConcreteFM t_typed t_conc →
      typFlatSize decls {} t_typed = (typSize layoutMap t_conc).toOption.getD 0 :=
    fun t_typed t_conc hmatch =>
      typFlatSize_eq_typSize_under_match_wf hdecls hts hconc hwf hlayout
        (_hTupleArm hlayout)
        (_hArrayArm hlayout)
        (_hRefDispatch hlayout)
        (_hAppEmptyDispatch hlayout)
        (_hAppResolvedDispatch hlayout)
        (_hAppUnresolvedDispatch hlayout)
        t_typed t_conc hmatch
  -- C: fold-sum lifting.
  exact concretize_inputs_foldl_via_match_wf tf.inputs concF.inputs hlen hmatch hpair

/-- **Entry-reachability extraction bridge.**

At any source name reachable in the bytecode (witnessed by `ct.nameMap[name]?
= some _` and `decls.getByKey name = some (.function f)`), the concrete
declaration table has `concDecls.getByKey name = some (.function concF)`,
AND the source's flat-size sum over inputs matches the concrete function's
`typSize` sum over inputs (under any successful `layoutMap`).

Closure (post-A.6 refactor): the existence half (concDecls extraction)
closes at F=0 by walking back through `nameMap_value_via_remap` to recover
`preNameMap[name]? = some preIdx`, then applying `toBytecode_function_extract`
to extract `concF` from `concDecls`. The flat-size identity delegates to
`concretize_extract_concF_flat_size_bridge_wf` (F=1 sub-bridge above). -/
private theorem concretize_extract_concF_at_reachable_wf
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls) (hct : t.compile = .ok ct)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    (_hentry : StructCompatibleHasEntryFn decls)
    {name : Global} {fi : Bytecode.FunIdx} {f : Source.Function}
    {tf : Typed.Function}
    (hname : ct.nameMap[name]? = some fi)
    (hsrc : decls.getByKey name = some (.function f))
    (htyped : typedDecls.getByKey name = some (.function tf))
    -- Sig amendment 2026-05-04 (Defect 1, #11 layoutMap-binding): each
    -- premise is guarded by `concDecls.layoutMap = .ok layoutMap` to rule
    -- out the `layoutMap = ∅` counterexample (RHS = 0, LHS = 1 ⟹ False).
    -- Threaded verbatim into `concretize_extract_concF_flat_size_bridge_wf`.
    (_hTupleArm :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {ts : Array Typ} {cts : Array Concrete.Typ}
        (_hLen : ts.size = cts.size)
        (_hAll : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          Typ.MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂))
        (_hIH : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          typFlatSize decls {} (ts[i]'h₁) =
            (typSize layoutMap (cts[i]'h₂)).toOption.getD 0),
        typFlatSize decls {} (.tuple ts) =
          (typSize layoutMap (.tuple cts)).toOption.getD 0)
    (_hArrayArm :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {t' : Typ} {ct' : Concrete.Typ} {n : Nat}
        (_hInner : Typ.MatchesConcreteFM t' ct')
        (_hIH : typFlatSize decls {} t' =
          (typSize layoutMap ct').toOption.getD 0),
        typFlatSize decls {} (.array t' n) =
          (typSize layoutMap (.array ct' n)).toOption.getD 0)
    (_hRefDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.ref g) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppEmptyDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.app g #[]) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppResolvedDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ) (concName : Global),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref concName)).toOption.getD 0)
    (_hAppUnresolvedDispatch :
      ∀ {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref g)).toOption.getD 0) :
    ∃ concF : Concrete.Function,
      concDecls.getByKey name = some (.function concF) ∧
      ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
        (tf.inputs.map Prod.snd).foldl
            (fun acc t => acc + typFlatSize decls {} t) 0 =
          (concF.inputs.map Prod.snd).foldl
            (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  -- Step 1: unfold `hct` to expose `preNameMap` (toBytecode output) and the
  -- `nameMap = preNameMap.fold ... (insert n (remap i))` shape. Mirrors the
  -- pattern used in `compile_ok_input_layout_matches_entry` below; uniqueness
  -- of the stage outputs is captured via direct `bind/Except.bind` unfolding
  -- (no `subst` needed since `hts`/`hconc` are passed in directly).
  have hbc : ∃ bytecodeRaw preNameMap,
      concDecls.toBytecode = .ok (bytecodeRaw, preNameMap) := by
    obtain ⟨typedDecls', concDecls', bytecodeRaw, preNameMap, hts', hconc', hbc⟩ :=
      Source.Toplevel.compile_stages_of_ok hct
    have htyped_eq : typedDecls' = typedDecls := by
      rw [hts'] at hts; exact Except.ok.inj hts
    have hconcD_eq : concDecls' = concDecls := by
      subst htyped_eq; rw [hconc'] at hconc; exact Except.ok.inj hconc
    subst htyped_eq
    subst hconcD_eq
    exact ⟨bytecodeRaw, preNameMap, hbc⟩
  obtain ⟨bytecodeRaw, preNameMap, hbc⟩ := hbc
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  have hct' := hct
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct'
  injection hct' with hct_eq
  have hname_eq : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by rw [← hct_eq]
  -- Step 2: derive `preNameMap[name]? = some preIdx`.
  have hname' : ct.nameMap[name]? = some fi := hname
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name] at hname'
  match hpre : preNameMap[name]? with
  | none => rw [hpre] at hname'; simp at hname'
  | some preIdx =>
    rw [hpre, Option.map_some] at hname'
    -- Step 3: extract `concF` via `toBytecode_function_extract`.
    obtain ⟨layoutMap, hlayout⟩ := toBytecode_layoutMap_ok hbc
    have htdna := checkAndSimplify_preserves_nameAgrees hts
    have hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
        (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name :=
      concretize_nameAgrees htdna hconc
    obtain ⟨concF, _body, _lms, _hpre_lt, hconcGet, _hcomp, _hbody_eq⟩ :=
      toBytecode_function_extract hbc hlayout hNameAgrees name preIdx hpre
    refine ⟨concF, hconcGet, ?_⟩
    -- Step 4: delegate flat-size identity to the per-key bridge. The 6
    -- hoisted per-arm premises are propagated through.
    exact concretize_extract_concF_flat_size_bridge_wf hdecls hts hconc hwf
      hsrc htyped hconcGet
      _hTupleArm _hArrayArm _hRefDispatch _hAppEmptyDispatch
      _hAppResolvedDispatch _hAppUnresolvedDispatch

/-- **Entry-restricted `input_layout_matches`.** Per-entry version of the
deleted FullyMono predecessor `compile_ok_input_layout_matches`. Body
structurally mirrors the FullyMono proof, but rewires
`concretize_extract_function_at_name` (itself a sorry under FullyMono) into
the named entry-reachability sub-bridge
`concretize_extract_concF_at_reachable_wf` (F=1), which packages both the
existence of `concF` in `concDecls` and the flat-size identity. All other
steps (typed extraction, dedup/needsCircuit layout transport,
`Concrete.Function.compile_inputSize`) close at F=0. -/
private theorem compile_ok_input_layout_matches_entry
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct) (hwf : WellFormed t)
    (hentry : StructCompatibleHasEntryFn decls)
    -- Sig amendment 2026-05-04 (Defect 1, #11 layoutMap-binding): each
    -- premise constrained to layoutMap derived from the actual
    -- `concDecls.layoutMap = .ok layoutMap` (which exists because
    -- `t.compile = .ok ct` succeeds, transitively requiring layoutMap
    -- success). The previous universal-over-layoutMap form was provably
    -- False at `layoutMap = ∅`. The premises here use a fresh
    -- `concDecls`-existential (we don't have `concDecls` in scope here,
    -- so we existentially quantify it from the compilation chain).
    (_hTupleArm :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {ts : Array Typ} {cts : Array Concrete.Typ}
        (_hLen : ts.size = cts.size)
        (_hAll : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          Typ.MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂))
        (_hIH : ∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
          typFlatSize decls {} (ts[i]'h₁) =
            (typSize layoutMap (cts[i]'h₂)).toOption.getD 0),
        typFlatSize decls {} (.tuple ts) =
          (typSize layoutMap (.tuple cts)).toOption.getD 0)
    (_hArrayArm :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap),
      ∀ {t' : Typ} {ct' : Concrete.Typ} {n : Nat}
        (_hInner : Typ.MatchesConcreteFM t' ct')
        (_hIH : typFlatSize decls {} t' =
          (typSize layoutMap ct').toOption.getD 0),
        typFlatSize decls {} (.array t' n) =
          (typSize layoutMap (.array ct' n)).toOption.getD 0)
    (_hRefDispatch :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.ref g) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppEmptyDispatch :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global),
        typFlatSize decls {} (.app g #[]) =
          (typSize layoutMap (.ref g)).toOption.getD 0)
    (_hAppResolvedDispatch :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ) (concName : Global),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref concName)).toOption.getD 0)
    (_hAppUnresolvedDispatch :
      ∀ {concDecls : Concrete.Decls} {typedDecls : Typed.Decls}
        (_hts : t.checkAndSimplify = .ok typedDecls)
        (_hconc : typedDecls.concretize = .ok concDecls)
        {layoutMap : LayoutMap} (_hLM : concDecls.layoutMap = .ok layoutMap)
        (g : Global) (args : Array Typ),
        typFlatSize decls {} (.app g args) =
          (typSize layoutMap (.ref g)).toOption.getD 0) :
    ∀ name fi f, ct.nameMap[name]? = some fi →
      decls.getByKey name = some (.function f) →
      ∀ h : fi < ct.bytecode.functions.size,
        (f.inputs.map Prod.snd).foldl
          (fun acc t => acc + typFlatSize decls {} t) 0 =
        ct.bytecode.functions[fi].layout.inputSize := by
  intro name fi f hname hsrc h
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap, hts, hconc, hbc⟩ :=
    Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  have hct' := hct
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct'
  injection hct' with hct_eq
  have hname_eq : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by rw [← hct_eq]
  have hbc_eq : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  have htdna := checkAndSimplify_preserves_nameAgrees hts
  have hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name :=
    concretize_nameAgrees htdna hconc
  obtain ⟨tf, htyped, hsum_ts⟩ :=
    checkAndSimplify_extract_typed_function hdecls hts hsrc
  -- Sig amendment 2026-05-04 (Defect 1): instantiate the per-arm premises
  -- at this `concDecls`/`typedDecls` (extracted from `compile_stages_of_ok`)
  -- before forwarding them to `concretize_extract_concF_at_reachable_wf`,
  -- whose premises take `concDecls.layoutMap = .ok layoutMap` directly.
  obtain ⟨concF, hconcGet, hflat_tc⟩ :=
    concretize_extract_concF_at_reachable_wf hdecls hct hts hconc hwf hentry
      hname hsrc htyped
      (_hTupleArm hts hconc) (_hArrayArm hts hconc) (_hRefDispatch hts hconc)
      (_hAppEmptyDispatch hts hconc) (_hAppResolvedDispatch hts hconc)
      (_hAppUnresolvedDispatch hts hconc)
  obtain ⟨layoutMap, hlayout⟩ := toBytecode_layoutMap_ok hbc
  have hflat_cc := hflat_tc layoutMap hlayout
  -- Recover preIdx via `nameMap_value_via_remap` (same pattern as
  -- `compile_ok_funIdx_valid` above).
  have hname' : ct.nameMap[name]? = some fi := hname
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name] at hname'
  match hpre : preNameMap[name]? with
  | none => rw [hpre] at hname'; simp at hname'
  | some preIdx =>
    rw [hpre, Option.map_some] at hname'
    have hfi : fi = remap preIdx := (Option.some.injEq _ _).mp hname'.symm
    have hpre_lt : preIdx < bytecodeRaw.functions.size :=
      preNameMap_in_range hbc name preIdx hpre
    obtain ⟨body, lms, hcomp, hlayout_raw_eq⟩ :=
      toBytecode_function_layout (cd := concDecls) hlayout hbc hNameAgrees name concF preIdx
        hconcGet hpre hpre_lt
    have hinputSize := Concrete.Function.compile_inputSize hcomp
    have hremap_lt : remap preIdx < bytecodeDedup.functions.size :=
      deduplicate_remap_in_range hdedup preIdx hpre_lt
    have hdedup_layout :
        bytecodeRaw.functions[preIdx].layout =
          bytecodeDedup.functions[remap preIdx].layout :=
      deduplicate_preserves_layout hdedup preIdx hpre_lt hremap_lt
    have hsize_eq : ct.bytecode.functions.size = bytecodeDedup.functions.size := by
      rw [hbc_eq]; simp [Array.size_mapIdx]
    have hfi_dedup : fi < bytecodeDedup.functions.size := hsize_eq ▸ h
    have h_mapIdx_lt : fi < (bytecodeDedup.functions.mapIdx
        (fun i (f : Bytecode.Function) =>
          { f with constrained := bytecodeDedup.needsCircuit[i]! })).size := by
      rw [Array.size_mapIdx]; exact hfi_dedup
    have hct_fi_layout :
        ct.bytecode.functions[fi].layout = bytecodeDedup.functions[fi].layout := by
      have hct_fi :
          ct.bytecode.functions[fi]'h
            = (bytecodeDedup.functions.mapIdx
                (fun i (f : Bytecode.Function) =>
                  { f with constrained := bytecodeDedup.needsCircuit[i]! }))[fi]'h_mapIdx_lt :=
        getElem_congr_coll (by rw [hbc_eq])
      rw [congrArg Bytecode.Function.layout hct_fi]
      exact needsCircuit_preserves_layout bytecodeDedup.functions
        bytecodeDedup.needsCircuit fi hfi_dedup
    have hlayout_dedup_eq :
        (bytecodeDedup.functions[fi]'hfi_dedup).layout
          = (bytecodeDedup.functions[remap preIdx]'hremap_lt).layout :=
      congrArg Bytecode.Function.layout (getElem_congr_idx hfi)
    rw [hct_fi_layout, hlayout_dedup_eq, ← hdedup_layout, hlayout_raw_eq, hinputSize,
        ← hflat_cc, ← hsum_ts]

/-- **Wire B closure.** Entry-restricted variant of the deleted FullyMono
predecessor `compile_ok_implies_struct_compatible`. Composes the four
StructCompatible conjuncts: three close directly, the fourth delegates to
the entry-bridge stub `compile_ok_input_layout_matches_entry`. -/
theorem compile_ok_implies_struct_compatible_of_entry
    {t : Source.Toplevel} {ct : CompiledToplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct)
    (hwf : WellFormed t)
    (hentry : StructCompatibleHasEntryFn decls) :
    StructCompatible decls ct.bytecode (fun g => ct.nameMap[g]?) := by
  -- Six per-arm flat-size obligations propagated from
  -- `typFlatSize_eq_typSize_under_match_wf` (sorry #11). Each is
  -- discharged here with a single granular sorry tagged
  -- `BLOCKED-typFlatSize-arm-*` until the bound-saturation lemma
  -- (BLOCKED-typFlatSize-bound-saturation) lands and the Layout-chain
  -- ref-dispatch premises are constructed at this site. Documented in
  -- PLAN.md "Sorry #11 cascade impact".
  refine
    { total_on_reachable := compile_ok_total_on_reachable hdecls hct
      funIdx_valid := compile_ok_funIdx_valid hct
      input_layout_matches := ?_
      call_graph_closed := compile_ok_call_graph_closed hct }
  -- Sig amendment 2026-05-04 (Defect 1): premises now take `concDecls`,
  -- `typedDecls`, `hts`, `hconc`, and `concDecls.layoutMap = .ok layoutMap`
  -- (binding the actual layoutMap, not universally quantifying over it).
  -- The stub `sorry`s here remain bundled into this single
  -- `compile_ok_implies_struct_compatible_of_entry` declaration's sorry
  -- envelope (PLAN.md sorry #11*).
  exact compile_ok_input_layout_matches_entry hdecls hct hwf hentry
    (_hTupleArm := fun _ _ _ _ _ _ _ => sorry)
    (_hArrayArm := fun _ _ _ _ _ _ => sorry)
    (_hRefDispatch := fun _ _ _ _ _ => sorry)
    (_hAppEmptyDispatch := fun _ _ _ _ _ => sorry)
    (_hAppResolvedDispatch := fun _ _ _ _ _ _ _ => sorry)
    (_hAppUnresolvedDispatch := fun _ _ _ _ _ _ => sorry)

end Aiur

end -- public section
