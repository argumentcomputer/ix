module
public import Ix.Aiur.Proofs.Lib
public import Ix.Aiur.Semantics.Compatible
public import Ix.Aiur.Compiler
public import Ix.Aiur.Proofs.LowerShared
public import Ix.Aiur.Proofs.LowerCalleesFromLayout
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.CompilerProgress

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

/-- `mapIdx` with a `constrained`-only record update preserves `size` and
every `body`. Trivial from `Array.size_mapIdx` + `Array.getElem_mapIdx`. -/
theorem needsCircuit_preserves_body
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

/-- Shape of `ct.bytecode.functions`: the dedup output with a `constrained`
field patched in by `needsCircuit`. Direct definitional unpacking of
`Source.Toplevel.compile`.

Signature takes the full four-stage witness chain so the proof can chain
them through `compile`'s pipeline definition. -/
theorem compile_ct_functions_shape
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

/-- Sub-lemma: reachability is tautological under the restated definition
(every name with `nameMap name = some fi` is, by definition, "reachable"). -/
theorem compile_ok_total_on_reachable
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (_hdecls : t.mkDecls = .ok decls)
    (_hct : t.compile = .ok ct) :
    ∀ (name : Global), reachableFromEntries decls (fun g => ct.nameMap[g]?) name →
      ∃ fi, ct.nameMap[name]? = some fi := by
  intro name h
  simp only [reachableFromEntries] at h
  exact Option.isSome_iff_exists.mp h

/-- Sub-lemma: every `FunIdx` in `nameMap` is in range of `bc.functions`.
Composed from `preNameMap_in_range` (LowerShared), `deduplicate_remap_in_range`
(DedupSound), and `nameMap_value_via_remap` (Compiler.lean). -/
theorem compile_ok_funIdx_valid
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

/-! ### Sub-lemmas for `compile_ok_input_layout_matches`. -/

/-- `mapIdx (fun i f => { f with constrained := needs[i]! })` preserves
`layout` pointwise — only `constrained` changes. Companion of
`needsCircuit_preserves_body`. -/
theorem needsCircuit_preserves_layout
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
function. Signature adds `hNameAgrees` (needed to identify `(xname, .function f)`
pair with `f.name = xname`); callers thread `concretize_nameAgrees` in. -/
theorem toBytecode_function_layout
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

/-- Joint layout invariant of `Toplevel.deduplicate`'s canonicalization loop.
Provable because dedup's skeleton key uses the full `FunctionLayout`
(see `Compiler/Dedup.lean:211`): same-class functions agree on every layout
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
  -- Lift class-equality from `deduplicate_classes_of` to `partitionRefine` form.
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

/-- `Toplevel.deduplicate` preserves per-function `layout`. Closed modulo
`deduplicate_layout_loop_invariant` (which may be false — see finding). -/
theorem deduplicate_preserves_layout
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

/-- Concretize + toBytecode lift a source-function entry to a concrete-function
entry with matching pre-name-map index and flat-size-to-typSize identity.
Closed via the three extractor lemmas above.

Sig updated (2026-04-24): `htf_mono` callback replaced with `hmono : FullyMonomorphic t`
so the strengthened `concretize_extract_function_at_name` can discharge. -/
theorem concretize_extract_concrete_function
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls} {bytecodeRaw : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hbc : concDecls.toBytecode = .ok (bytecodeRaw, preNameMap))
    (hNameAgrees : ∀ (key : Global) (g : Concrete.Function),
      (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name)
    (_hct : t.compile = .ok ct)
    {name : Global} {fi : Bytecode.FunIdx} {f : Source.Function}
    (_hname : ct.nameMap[name]? = some fi)
    (hsrc : decls.getByKey name = some (.function f)) :
    ∃ (preIdx : Bytecode.FunIdx) (concName : Global) (concF : Concrete.Function),
      preNameMap[concName]? = some preIdx ∧
      concDecls.getByKey concName = some (.function concF) ∧
      ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
        (f.inputs.map Prod.snd).foldl
            (fun acc t => acc + typFlatSize decls {} t) 0 =
          (concF.inputs.map Prod.snd).foldl
            (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  obtain ⟨tf, htyped, hsum_ts⟩ :=
    checkAndSimplify_extract_typed_function hdecls hts hsrc
  obtain ⟨concName, concF, _, hconcGet, hflat_tc⟩ :=
    concretize_extract_function_at_name (decls := decls) hmono hdecls hts hconc htyped
  obtain ⟨preIdx, hpreName, _hpreLt⟩ :=
    toBytecode_extract_preIdx hbc hNameAgrees hconcGet
  refine ⟨preIdx, concName, concF, hpreName, hconcGet, ?_⟩
  intro layoutMap hlayout
  rw [hsum_ts]
  exact hflat_tc layoutMap hlayout

/-- Sub-lemma: flattened input size agrees between source decl and bytecode
layout. Composition delegates to the 6 sub-lemmas above.

Requires `FullyMonomorphic t` — threaded through to
`concretize_extract_function_at_name` via `checkAndSimplify_preserves_params`. -/
theorem compile_ok_input_layout_matches
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct) (hmono : FullyMonomorphic t) :
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
  obtain ⟨concName, concF, hcn_eq, hconcGet, hflat_tc⟩ :=
    concretize_extract_function_at_name (decls := decls) hmono hdecls hts hconc htyped
  rw [hcn_eq] at hconcGet
  obtain ⟨layoutMap, hlayout⟩ := toBytecode_layoutMap_ok hbc
  have hflat_cc := hflat_tc layoutMap hlayout
  obtain ⟨preIdx, hpreName, hpre_lt⟩ :=
    toBytecode_extract_preIdx hbc hNameAgrees hconcGet
  obtain ⟨body, lms, hcomp, hlayout_raw_eq⟩ :=
    toBytecode_function_layout (cd := concDecls) hlayout hbc hNameAgrees name concF preIdx
      hconcGet hpreName hpre_lt
  have hinputSize := Concrete.Function.compile_inputSize hcomp
  have hname' : ct.nameMap[name]? = some fi := hname
  rw [hname_eq, nameMap_value_via_remap preNameMap remap name, hpreName,
      Option.map_some] at hname'
  have hfi : fi = remap preIdx := (Option.some.injEq _ _).mp hname'.symm
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

/-- Sub-lemma: the bytecode call graph is closed. Composed from
`toBytecode_callees_in_range` (LowerShared), `deduplicate_preserves_callee_range`
(DedupSound), and `needsCircuit_preserves_body` + `compile_ct_functions_shape`
(Compiler.lean). -/
theorem compile_ok_call_graph_closed
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

/-- If `compile` succeeds, its output is structurally compatible.
Composed from the four sub-lemmas above. Requires `FullyMonomorphic t` for
the `input_layout_matches` conjunct (threaded through
`concretize_extract_function_at_name`'s monomorphism requirement). -/
theorem compile_ok_implies_struct_compatible
    {t : Source.Toplevel} {ct : CompiledToplevel}
    {decls : Source.Decls} (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct) (hmono : FullyMonomorphic t) :
    StructCompatible decls ct.bytecode
      (fun g => ct.nameMap[g]?) :=
  { total_on_reachable := compile_ok_total_on_reachable hdecls hct
    funIdx_valid := compile_ok_funIdx_valid hct
    input_layout_matches := compile_ok_input_layout_matches hdecls hct hmono
    call_graph_closed := compile_ok_call_graph_closed hct }

end Aiur

end
