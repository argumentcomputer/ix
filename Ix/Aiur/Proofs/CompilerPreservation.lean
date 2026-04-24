module
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.SimplifySound
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Proofs.StructCompatible
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.Relation

/-!
Top-level preservation.

Compose `Toplevel.compile_preservation` from Dedup, Lower, Concretize, and
Simplify soundness by transitivity of `InterpResultEq`, threading fuel /
`StructCompatible` / typing assumptions through the composition.

This is the preservation half of the top-level `compile_correct` theorem.
-/

public section

namespace Aiur

open Source

/-- Function-name → `FunIdx` lookup lifted to a `Global → Option Nat`. Used
both in `ValueEq` (to resolve `.fn` values to their call indices) and in the
statement of `compile_preservation`. -/
@[inline] def CompiledToplevel.globalFuncIdx (ct : CompiledToplevel) :
    Global → Option Nat :=
  fun g => ct.nameMap[g]?

/-!
### Signature-integration history (resolved)

Earlier rounds surfaced three signature-level mismatches between per-pass
preservation claims and what the composition needs. All have been resolved:

- **Concretize value-level equivalence**: `Typed.Decls.concretize_preservation`
  now returns `flattenValue`-equality + `IOBuffer.equiv` (not just IOBuffer).
- **Lower funcIdx remap**: `Toplevel.compile_preservation` takes FnFree
  hypotheses (`hargsFnFree`, `hconcRetFnFree`); `ValueEq.transport_remap` +
  `InterpResultEq.transport_remap_of_src_fnFree` live in `LowerShared.lean`.
- **Dedup constrained-flag irrelevance**: `Bytecode.Eval.runFunction_constrained_irrelevant`
  lives in `DedupSound.lean`.
-/

/-! ## Local aux. -/

/-- Key-set preservation through checkAndSimplify. Unfolds `checkAndSimplify`
into `wellFormedDecls` + typecheck fold + `simplifyDecls`, then chains three
key-set equivalences via `indexMap_foldlM_insertKey_default_iff`. -/
private theorem checkAndSimplify_keys
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (_hdecls : t.mkDecls = .ok decls) (_hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g, decls.getByKey g ≠ none ↔ typedDecls.getByKey g ≠ none := by
  intro g
  rw [IndexMap.getByKey_ne_none_iff_containsKey, IndexMap.getByKey_ne_none_iff_containsKey]
  unfold Source.Toplevel.checkAndSimplify at _hts
  simp only [_hdecls, bind, Except.bind] at _hts
  rcases hwell : wellFormedDecls decls with _ | u
  · rw [hwell] at _hts; simp at _hts
  rw [hwell] at _hts
  simp only [pure, Except.pure] at _hts
  split at _hts
  · simp at _hts
  rename_i _ td htc_gen
  unfold simplifyDecls at _hts
  simp only [bind, Except.bind, pure, Except.pure] at _hts
  have hsp_gen := _hts
  have hfold_ck : td.containsKey g ↔
      ∃ p ∈ decls.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff decls _ ?_ g td htc_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | constructor d c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType d =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | function f =>
      simp only [hd] at hr
      rcases hf : ((checkFunction f) (getFunctionContext f decls)).run' {} with err | tf
      · rw [hf] at hr; simp at hr
      · rw [hf] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  have hsimp_ck : typedDecls.containsKey g ↔
      ∃ p ∈ td.pairs.toList, (p.1 == g) = true := by
    refine IndexMap.indexMap_foldlM_insertKey_default_iff td _ ?_ g typedDecls hsp_gen
    intro acc x r hr g'
    cases hd : x.snd with
    | function f =>
      simp only [hd] at hr
      rcases hb : simplifyTypedTerm decls f.body with err | v
      · rw [hb] at hr; simp at hr
      · rw [hb] at hr
        simp only [Except.ok.injEq] at hr
        subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | dataType dt =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
    | constructor dt c =>
      simp only [hd, Except.ok.injEq] at hr
      subst hr; exact IndexMap.containsKey_insert_iff_or acc x.fst g' _
  rw [IndexMap.containsKey_iff_exists_pair decls g, ← hfold_ck,
      IndexMap.containsKey_iff_exists_pair td g, ← hsimp_ck]

/-! ### Step1_3Body — helpers for `step1_3_fully_mono_is_identity`.

Ported from `Step1_3BodyScratch` (2026-04-24). Axiom `typedDecls_ctor_dt_params_empty`
is the sole remaining sorry — mechanical ~60 LoC mirror of `SrcDtParamsMonoP`
for `.constructor` entries in `CheckSound.lean`. -/

namespace Step1_3Body

open Source

/-! ## Source-side invariant: every `.constructor dt c` has `dt.params = []`.

Mirror of `SrcDtParamsMonoP` for `.constructor` entries. -/

private def SrcCtorDtParamsMonoP (d : Source.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.constructor dt c) → dt.params = []

private theorem SrcCtorDtParamsMonoP_default :
    SrcCtorDtParamsMonoP (default : Source.Decls) := by
  intro k dt c hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem SrcCtorDtParamsMonoP_insert_function
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (f : Source.Function) :
    SrcCtorDtParamsMonoP (d.insert name (.function f)) := by
  intro k dt c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt c hget

private theorem SrcCtorDtParamsMonoP_insert_dataType
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (dt : DataType) :
    SrcCtorDtParamsMonoP (d.insert name (.dataType dt)) := by
  intro k dt' c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c hget

private theorem SrcCtorDtParamsMonoP_insert_constructor
    {d : Source.Decls} (hP : SrcCtorDtParamsMonoP d) (name : Global)
    (dt : DataType) (c : Constructor) (hmono : dt.params = []) :
    SrcCtorDtParamsMonoP (d.insert name (.constructor dt c)) := by
  intro k dt' c' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
    obtain ⟨heq, _⟩ := hget
    rw [← heq]
    exact hmono
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c' hget

private theorem SrcCtorDtParamsMonoP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Source.Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcCtorDtParamsMonoP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SrcCtorDtParamsMonoP acc'.2 := by
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  simp only [Except.ok.injEq] at hstep
  subst hstep
  simp only
  exact SrcCtorDtParamsMonoP_insert_function hP _ _

private theorem SrcCtorDtParamsMonoP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) (hmono' : dataType'.params = []) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SrcCtorDtParamsMonoP init.2 →
      ctors.foldlM
        (fun (acc : Std.HashSet Global × Source.Decls) ctor =>
          let ctorName := dataTypeName.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError (Std.HashSet Global × Source.Decls))
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SrcCtorDtParamsMonoP result.2 := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hP hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    cases hfold; exact hP
  | cons c rest ih =>
    intro init result hP hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hc
    split at hc
    · exact absurd hc (by intro h; cases h)
    · simp only [Except.ok.injEq] at hc
      subst hc
      apply ih _ result _ hfold
      exact SrcCtorDtParamsMonoP_insert_constructor hP _ _ _ hmono'

private theorem SrcCtorDtParamsMonoP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SrcCtorDtParamsMonoP acc.2) (hmono : dataType.params = [])
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SrcCtorDtParamsMonoP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hparams' : ({ dataType with constructors } : DataType).params = [] := hmono
  have hP_mid : SrcCtorDtParamsMonoP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SrcCtorDtParamsMonoP_insert_dataType hP dataType.name _
  exact SrcCtorDtParamsMonoP_ctor_fold dataType.name { dataType with constructors }
    hparams' constructors _ acc' hP_mid hstep

private theorem SrcCtorDtParamsMonoP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (hmono : FullyMonomorphic toplevel)
    (h : toplevel.mkDecls = .ok decls) :
    SrcCtorDtParamsMonoP decls := by
  unfold Source.Toplevel.mkDecls at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i aliasNames _halias
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i _finalAliasMapPair _hrun
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterFns hfns
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i afterDts hdts
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hP_afterFns : SrcCtorDtParamsMonoP afterFns.2 := by
    rw [show toplevel.functions.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default) =
          toplevel.functions.toList.foldlM
            (mkDecls_functionStep
              (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
            (aliasNames, default)
        from Array.foldlM_toList.symm] at hfns
    apply List.foldlM_except_invariant toplevel.functions.toList _ _ _ _ hfns
    · show SrcCtorDtParamsMonoP (aliasNames, (default : Source.Decls)).2
      exact SrcCtorDtParamsMonoP_default
    · intro a x a' _hmem hstep hP
      exact SrcCtorDtParamsMonoP_functionStep hP hstep
  rw [show toplevel.dataTypes.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns =
        toplevel.dataTypes.toList.foldlM
          (mkDecls_dataTypeStep
            (fun typ => (expandTypeM ∅ toplevel.typeAliases typ).run' _finalAliasMapPair.2))
          afterFns
      from Array.foldlM_toList.symm] at hdts
  apply List.foldlM_except_invariant toplevel.dataTypes.toList _ _ _ _ hdts
  · exact hP_afterFns
  · intro a x a' hmem hstep hP
    have hxmono : x.params = [] :=
      hmono.2 x (Array.mem_toList_iff.mp hmem)
    exact SrcCtorDtParamsMonoP_dataTypeStep hP hxmono hstep

private def TdCtorDtParamsMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k dt c, td.getByKey k = some (.constructor dt c) →
    d.getByKey k = some (.constructor dt c)

private theorem TdCtorDtParamsMatchP_default (d : Source.Decls) :
    TdCtorDtParamsMatchP d (default : Typed.Decls) := by
  intro k dt c hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem TdCtorDtParamsMatchP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TdCtorDtParamsMatchP decls typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TdCtorDtParamsMatchP_default decls
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_src : decls.getByKey name = some decl :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨heq1, heq2⟩ := hget
        subst heq1; subst heq2
        exact hname_src
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c' hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' _hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget

private theorem TdCtorDtParamsMatchP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TdCtorDtParamsMatchP decls typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TdCtorDtParamsMatchP decls typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TdCtorDtParamsMatchP_default decls
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    have hname_td : typedDecls.getByKey name = some d :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt' c hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' c hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hcmatch : decls.getByKey name = some (.constructor dt c) :=
        hP name dt c hname_td
      intro k dt' c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨heq1, heq2⟩ := hget
        subst heq1; subst heq2
        exact hcmatch
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' c' hget

private theorem TdCtorDtParamsMatchP_checkAndSimplify
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    TdCtorDtParamsMatchP decls typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [hdecls, bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hMid := TdCtorDtParamsMatchP_of_checkFold hfold
  exact TdCtorDtParamsMatchP_of_simplifyDecls hMid hts

/-- Under `FullyMono`, every typed `.constructor dt c` entry has
`dt.params = []`. Ported from `CtorDtParamsScratch` 2026-04-24. -/
private theorem typedDecls_ctor_dt_params_empty_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∀ g dt c, typedDecls.getByKey g = some (.constructor dt c) → dt.params = [] := by
  intro g dt c htyped
  have hP := TdCtorDtParamsMatchP_checkAndSimplify hdecls hts
  have hsrc : decls.getByKey g = some (.constructor dt c) := hP g dt c htyped
  have hmonoP := SrcCtorDtParamsMonoP_mkDecls hmono hdecls
  exact hmonoP g dt c hsrc

private theorem list_foldl_containsKey_preserves
    {γ : Type}
    (step : Typed.Decls → γ → Typed.Decls)
    (hmono : ∀ acc a c, acc.containsKey a → (step acc c).containsKey a) :
    ∀ (L : List γ) (init : Typed.Decls) a,
      init.containsKey a → (L.foldl step init).containsKey a
  | [], _, _, h => h
  | hd :: tl, init, a, h => by
    simp only [List.foldl_cons]
    exact list_foldl_containsKey_preserves step hmono tl (step init hd) a
      (hmono init a hd h)

private theorem concretizeBuild_containsAll_of_fullyMonomorphic
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (g : Global) (hcontains : typedDecls.containsKey g) :
    (concretizeBuild typedDecls mono newFunctions newDataTypes).containsKey g := by
  rw [IndexMap.containsKey_iff_exists_pair] at hcontains
  obtain ⟨⟨g', d⟩, hmem, hgeq⟩ := hcontains
  have hgeq' : g' = g := LawfulBEq.eq_of_beq hgeq
  rw [← hgeq']
  have hFnParams := typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hDtParams := typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hCtorDtParams :=
    typedDecls_ctor_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      let (key, dd) := p
      match dd with
      | .function f =>
        if f.params.isEmpty then
          acc.insert key (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm typedDecls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert key (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert key (.constructor newDt newCtor)
        else acc
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm typedDecls emptySubst mono f.body })
  have hsrcMono : ∀ acc a p,
      acc.containsKey a → (srcStep acc p).containsKey a := by
    intro acc a ⟨k, dd⟩ h
    show (srcStep acc (k, dd)).containsKey a
    simp only [srcStep]
    cases dd with
    | function f =>
      by_cases hp : f.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
    | dataType dt =>
      by_cases hp : dt.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
    | constructor dt c =>
      by_cases hp : dt.params.isEmpty = true
      · simp only [hp, if_true]
        exact IndexMap.containsKey_insert_preserves _ _ _ _ h
      · simp only [hp, if_false, Bool.false_eq_true]; exact h
  have hdtMono : ∀ acc a dt,
      acc.containsKey a → (dtStep acc dt).containsKey a := by
    intro acc a dt h
    show (dtStep acc dt).containsKey a
    simp only [dtStep]
    exact list_foldl_containsKey_preserves _
      (fun acc' a' c' h' => IndexMap.containsKey_insert_preserves _ _ _ _ h')
      _ _ a (IndexMap.containsKey_insert_preserves _ _ _ _ h)
  have hfnMono : ∀ acc a f,
      acc.containsKey a → (fnStep acc f).containsKey a := by
    intro acc a f h
    exact IndexMap.containsKey_insert_preserves _ _ _ _ h
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem hmem
  let L : List (Global × Typed.Declaration) := typedDecls.pairs.toList
  have hsplit : ∃ pre post, L = pre ++ (g', d) :: post := by
    refine ⟨L.take i, L.drop (i + 1), ?_⟩
    have hi' : i < L.length := hi
    calc L = L.take i ++ L.drop i := (List.take_append_drop i L).symm
      _ = L.take i ++ (L[i] :: L.drop (i + 1)) := by rw [List.drop_eq_getElem_cons hi']
      _ = L.take i ++ (g', d) :: L.drop (i + 1) := by rw [hi_eq]
  obtain ⟨pre, post, hsplit_eq⟩ := hsplit
  have hfrom_eq :
      L.foldl srcStep default =
        post.foldl srcStep (srcStep (pre.foldl srcStep default) (g', d)) := by
    rw [hsplit_eq]
    rw [List.foldl_append, List.foldl_cons]
  have hget : typedDecls.getByKey g' = some d :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  have hstepInserts : ∀ acc : Typed.Decls, (srcStep acc (g', d)).containsKey g' := by
    intro acc
    show (srcStep acc (g', d)).containsKey g'
    simp only [srcStep]
    cases d with
    | function f =>
      have hparams : f.params = [] := hFnParams g' f hget
      have hpe : f.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
    | dataType dt =>
      have hparams : dt.params = [] := hDtParams g' dt hget
      have hpe : dt.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
    | constructor dt c =>
      have hparams : dt.params = [] := hCtorDtParams g' dt c hget
      have hpe : dt.params.isEmpty = true := by rw [hparams]; rfl
      simp only [hpe, if_true]
      exact IndexMap.containsKey_insert_self _ _ _
  have hfromSource_g :
      (L.foldl srcStep default).containsKey g' := by
    rw [hfrom_eq]
    exact list_foldl_containsKey_preserves srcStep hsrcMono post _ g'
      (hstepInserts _)
  have hconc_eq :
      concretizeBuild typedDecls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep
          (newDataTypes.toList.foldl dtStep (L.foldl srcStep default)) := by
    show concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep (newDataTypes.toList.foldl dtStep
        (typedDecls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq]
  exact list_foldl_containsKey_preserves fnStep hfnMono _ _ g'
    (list_foldl_containsKey_preserves dtStep hdtMono _ _ g' hfromSource_g)

private theorem exists_mkDecls_of_checkAndSimplify
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    ∃ decls, t.mkDecls = .ok decls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  cases h : t.mkDecls with
  | error e => rw [h] at hts; simp [bind, Except.bind] at hts
  | ok decls => exact ⟨decls, rfl⟩

end Step1_3Body

/-! ### `concretize_keys_of_mono` — decomposed.

Two sub-lemmas:
1. `concretize_steps_1_3_keys`: Steps 1–3 of `concretize` under `FullyMonomorphic`
   produce a `monoDecls : Typed.Decls` whose keys match `typedDecls`.
2. `concretize_step_4_keys_of_fold`: Step 4 (an insert-only `foldlM`) preserves
   keys from `monoDecls` to `concDecls`.

The composition still has one inline sorry: extracting the Step 4 fold equation
from `_hconc`. Full closure requires refactoring `concretize`'s imperative
Steps 1–3 (`let mut`/`while`/`for`) into pure functional form. -/

/-- Under `FullyMonomorphic`, Steps 1-3 of `Typed.Decls.concretize` are an
identity (up to an inert `rewriteTyp`/`rewriteTypedTerm` pass with an empty
mono-map), so `monoDecls` has the same keys as `typedDecls` and the Step-4
`foldlM` via `step4Lower` produces the given `concDecls`.

BLOCKED ON structured decomposition:

(S1) `FullyMonomorphic`-params-preservation through `checkAndSimplify`:
    every function/dataType/constructor-carried-dt in `typedDecls` has empty
    `params`. Traces through `mkDecls_functionStep` (preserves `params`
    field), `checkFunction` (copies `function.params` into `Typed.Function`),
    `simplifyDecls` (only rewrites `.body`). Three nested folds; each is an
    insert-only `foldlM` whose step preserves a "all `.function` have empty
    params / all `.dataType` have empty params" invariant. ~300 LoC across
    (S1a), (S1b), (S1c) once the params-preservation invariant is stated as
    a List-level `foldlM`-invariant.

(S2) `concretizeBuild` forward key-inclusion: every key of `typedDecls` is in
    `concretizeBuild typedDecls drained.mono drained.newFunctions
    drained.newDataTypes`. Under (S1), `fromSource` fold's `else` branches are
    never taken, so every source pair inserts at its key. Need a generic
    `Array.foldl`/`List.foldl` key-insertion-closure lemma. ~150 LoC.

(S3) `concretizeBuild` backward key-inclusion: every output key is either a
    `typedDecls` key or the name of an entry in `drained.newFunctions` /
    `drained.newDataTypes`. `concretize_build_excludes_polymorphic` (CLOSED
    in `ConcretizeSound.lean`) handles the main decomposition.

(S4) `drained.newFunctions` / `drained.newDataTypes` names are `typedDecls`
    keys: under `FullyMonomorphic`, every worklist entry `(g, args)` has
    `args = #[]` (because well-formed typed terms have no nonempty `.app
    g args` under mono-only decls). Combined with `concretizeName_empty_args`
    (CLOSED: `concretizeName g #[] = g`) and `MonoHasDecl`-style
    reachability (CLOSED: `concretize_drain_mono_has_decl`), each new-array
    entry's name equals a worklist-seed name, which is a `typedDecls` key
    (seeds come from `decls.pairs`). ~300 LoC, dominated by the
    `collectInTyp`/`collectInTypedTerm`-only-emits-empty-args lemma.

(S5) Constructor-key case in backward-inclusion: for
    `dt.name.pushNamespace c.nameHead = g` with `dt ∈ drained.newDataTypes`
    and `c ∈ dt.constructors`, `g` is a `typedDecls` key because
    `mkDecls_dataTypeStep` inserts every ctor at
    `dt.name.pushNamespace ctor.nameHead` — plus (S4) ensures `dt.name` maps
    to a `typedDecls` datatype whose constructors have matching nameHeads.
    ~100 LoC.

Total effort: ~1000 LoC across (S1)-(S5). Main-theorem composition
(below comment) is ~50 LoC once all sub-lemmas are discharged:

```
  unfold Typed.Decls.concretize at _hconc
  simp only [bind, Except.bind] at _hconc
  split at _hconc
  · contradiction
  rename_i drained hdrain
  refine ⟨concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes,
          ?_, _hconc⟩
  intro g
  constructor
  · intro hcontains  -- forward via (S2)
    exact S2_containsAll _hmono _hts g hcontains
  · intro hcontains  -- backward via (S3) + (S4) + (S5)
    rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hcontains
    cases hgd : (concretizeBuild typedDecls drained.mono drained.newFunctions
                   drained.newDataTypes).getByKey g with ...
```

(Body ported from `Step1_3BodyScratch` 2026-04-24: closes via
FullyMono-threaded `containsKey` induction + backward case-split with
`NewDtBridge` / `NewFnBridge` + `ctor_pushed_name` dispatch.) -/


private theorem step1_3_fully_mono_is_identity
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls),
      (∀ g, typedDecls.containsKey g ↔ monoDecls.containsKey g) ∧
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls := by
  obtain ⟨decls, hdecls⟩ := Step1_3Body.exists_mkDecls_of_checkAndSimplify hts
  have hconc_orig : typedDecls.concretize = .ok concDecls := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  rename_i drained hdrain
  refine ⟨concretizeBuild typedDecls drained.mono drained.newFunctions
            drained.newDataTypes, ?_, hconc⟩
  intro g
  constructor
  · intro hc
    exact Step1_3Body.concretizeBuild_containsAll_of_fullyMonomorphic
      hmono hdecls hts _ _ _ g hc
  · intro hc
    rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hc
    cases hget : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).getByKey g with
    | none => exact absurd hget hc
    | some d =>
      rcases concretize_build_excludes_polymorphic _ _ _ _ _ _ hget with
        ⟨srcD, hsrc, _⟩ | ⟨f, hfmem, hfname⟩ | ⟨dt, hdtmem, hcond⟩
      · rw [← IndexMap.getByKey_ne_none_iff_containsKey]
        rw [hsrc]; exact Option.some_ne_none _
      · obtain ⟨g', orig, horig, hfneq⟩ :=
          newFnBridge_derive hmono hdecls hts hdrain f hfmem
        have hg_eq : g = g' := by rw [← hfname, hfneq]
        rw [hg_eq]
        rw [← IndexMap.getByKey_ne_none_iff_containsKey]
        rw [horig]; exact Option.some_ne_none _
      · rcases hcond with hdtname | ⟨c, hcmem, hceq⟩
        · obtain ⟨g', orig, horig, hdtname_eq, _⟩ :=
            newDtBridge_derive hmono hdecls hts hdrain dt hdtmem
          have hg_eq : g = g' := by rw [← hdtname, hdtname_eq]
          rw [hg_eq]
          rw [← IndexMap.getByKey_ne_none_iff_containsKey]
          rw [horig]; exact Option.some_ne_none _
        · -- (c-ctor): g = dt.name.pushNamespace c.nameHead
          obtain ⟨g', orig, horig, hdtname_eq, hctors_map⟩ :=
            newDtBridge_derive hmono hdecls hts hdrain dt hdtmem
          have hc_head_mem :
              c.nameHead ∈ orig.constructors.map (·.nameHead) := by
            rw [← hctors_map]; exact List.mem_map_of_mem hcmem
          obtain ⟨c_orig, hc_orig_mem, hc_heads_eq⟩ := List.mem_map.mp hc_head_mem
          have hDt : Typed.Decls.DtNameIsKey typedDecls :=
            checkAndSimplify_preserves_dtNameIsKey hts
          have horig_mem :
              (g', Typed.Declaration.dataType orig) ∈ typedDecls.pairs.toList :=
            IndexMap.mem_pairs_of_getByKey typedDecls g' _ horig
          have horig_name : g' = orig.name := hDt g' orig horig_mem
          have hCtorPresent : Typed.Decls.CtorPresent typedDecls :=
            checkAndSimplify_preserves_ctorPresent hts
          obtain ⟨cc, hcc_mem⟩ := hCtorPresent g' orig c_orig horig_mem hc_orig_mem
          have hcc_get := IndexMap.getByKey_of_mem_pairs typedDecls _ _ hcc_mem
          have hkey_eq : g = orig.name.pushNamespace c_orig.nameHead := by
            rw [← hceq, hdtname_eq, horig_name, hc_heads_eq]
          rw [hkey_eq]
          rw [← IndexMap.getByKey_ne_none_iff_containsKey]
          rw [hcc_get]; exact Option.some_ne_none _

/-- Under `FullyMonomorphic`, Step 1–3 of `Typed.Decls.concretize` produce a
`monoDecls : Typed.Decls` whose key set matches `typedDecls`, and whose Step 4
`foldlM` produces the given `concDecls`. Composed from
`step1_3_fully_mono_is_identity` + `step4Lower_inserts`. -/
private theorem concretize_steps_1_4_extract
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls)
      (lower : Concrete.Decls → Global × Typed.Declaration →
               Except ConcretizeError Concrete.Decls),
      (∀ g, typedDecls.containsKey g ↔ monoDecls.containsKey g) ∧
      (∀ acc x r, lower acc x = .ok r →
        ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true) ∧
      monoDecls.foldlM (init := default) lower = .ok concDecls := by
  obtain ⟨monoDecls, hkeys, hfold⟩ := step1_3_fully_mono_is_identity hmono hts hconc
  exact ⟨monoDecls, step4Lower, hkeys, step4Lower_inserts, hfold⟩

/- `concretize_step_4_keys_of_fold` moved to `ConcretizeSound.lean`
(generic over `lower` step; doesn't depend on CompilerPreservation context). -/

/-- Key-set preservation through concretize under FullyMonomorphic. -/
private theorem concretize_keys_of_mono
    {t : Source.Toplevel} {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t) (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls) :
    ∀ g, typedDecls.getByKey g ≠ none ↔ concDecls.getByKey g ≠ none := by
  intro g
  rw [IndexMap.getByKey_ne_none_iff_containsKey, IndexMap.getByKey_ne_none_iff_containsKey]
  obtain ⟨monoDecls, lower, hmonoKeys, hlower_insert, hfold⟩ :=
    concretize_steps_1_4_extract _hmono _hts _hconc
  exact Iff.trans (hmonoKeys g) (concretize_step_4_keys_of_fold lower hlower_insert hfold g)

private theorem namespace_preservation
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls) (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) (hmono : FullyMonomorphic t) :
    ∀ g, decls.getByKey g ≠ none ↔ concDecls.getByKey g ≠ none := by
  intro g
  exact Iff.trans (checkAndSimplify_keys hdecls hts g) (concretize_keys_of_mono hmono hts hconc g)

private theorem CompiledToplevel.getFuncIdx_eq (ct : CompiledToplevel) (name : Lean.Name) :
    ct.getFuncIdx name = ct.nameMap[Global.mk name]? := rfl

private theorem CompiledToplevel.globalFuncIdx_eq (ct : CompiledToplevel) (g : Global) :
    ct.globalFuncIdx g = ct.nameMap[g]? := rfl

/-- **Preservation half** of `compile_correct`. For every well-formed source
program `t`, if `compile` succeeds producing `ct.bytecode`, then for every
entry function with its flat-encoded arguments, the bytecode observation
agrees with the source observation under `InterpResultEq`. -/
theorem Toplevel.compile_preservation
    (t : Source.Toplevel) (ct : CompiledToplevel) (decls : Source.Decls)
    (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct)
    (hmono : FullyMonomorphic t) :
    ∀ (name : Lean.Name) (funIdx : Bytecode.FunIdx)
      (_hname : ct.getFuncIdx name = some funIdx)
      -- `name` must appear in the source decls too (scopes the claim to
      -- first-order monomorphic functions present in the source).
      (_hsrc : decls.getByKey (Global.mk name) ≠ none)
      (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ)
      -- Arguments contain no first-class function values (caller property of
      -- the call site; entry functions don't accept `.fn`-typed inputs).
      (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
      -- Concrete evaluator returns FnFree (type-soundness consequence; see
      -- `Concrete.Eval.runFunction_preserves_FnFree` in `ConcretizeSound`).
      (_hconcRetFnFree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.FnFree v)
      -- Structural invariant: `.function` pairs in `concDecls` store their
      -- key as `f.name`. Holds for concretize-output decls (Step 4 of
      -- `Typed.Decls.concretize` uses the iteration key which equals `f.name`
      -- in well-formed input).
      (_hcdNameAgrees : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (key : Global) (f : Concrete.Function),
          (key, Concrete.Declaration.function f) ∈ concDecls.pairs.toList → key = f.name),
      InterpResultEq decls ct.globalFuncIdx retTyp
        (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) := by
  intros name funIdx hname hsrc args io₀ fuel retTyp hargsFnFree hconcRetFnFree
         hcdNameAgrees
  have _hstruct := compile_ok_implies_struct_compatible hdecls hct hmono
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap,
          hts, hconc, hbc⟩ := Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hBD : bytecodeDedup = bytecodeRaw.deduplicate.1 := rfl
  have hRM : remap = bytecodeRaw.deduplicate.2 := rfl
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  have hct_bc : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  have hct_nm : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by
    rw [← hct_eq]
  have hgfi : ∀ g, ct.globalFuncIdx g = (preNameMap[g]?).map remap := by
    intro g
    rw [CompiledToplevel.globalFuncIdx_eq, hct_nm, nameMap_value_via_remap preNameMap remap g]
  have hname' : ct.nameMap[Global.mk name]? = some funIdx := by
    rw [← CompiledToplevel.getFuncIdx_eq]; exact hname
  rw [hct_nm, nameMap_value_via_remap] at hname'
  match hpre : preNameMap[Global.mk name]? with
  | none =>
    rw [hpre] at hname'; simp at hname'
  | some preIdx =>
    rw [hpre, Option.map_some] at hname'
    have hfi_eq : funIdx = remap preIdx := (Option.some.injEq _ _).mp hname'.symm
    have h_d :
        Bytecode.Eval.runFunction ct.bytecode funIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel =
          Bytecode.Eval.runFunction bytecodeDedup funIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel := by
      rw [hct_bc]
      exact (Bytecode.Eval.runFunction_constrained_irrelevant bytecodeDedup
              bytecodeDedup.needsCircuit funIdx
              (Flatten.args decls ct.globalFuncIdx args) io₀ fuel).symm
    -- `deduplicate_preservation` is now one-directional `.ok`-transport (was an
    -- equation before the arity-mismatch-payload weakening). Requires
    -- `WellFormedCallees bytecodeRaw` and the partitionRefine fixpoint on it;
    -- these are structural facts about compile-produced bytecode but are not
    -- yet exported as lemmas. For now we sorry-plumb them here — the actual
    -- `.ok`-transport step only fires when the source evaluates to `.ok`, and
    -- the raw-bytecode side matches (via `h_b` / `InterpResultEq`-asymmetry).
    have h_wf_raw : WellFormedCallees bytecodeRaw :=
      toBytecode_produces_WellFormedCallees hbc
    have h_fix_raw :
        (let skeletons := bytecodeRaw.functions.map fun f =>
            (Bytecode.skeletonBlock f.body, f.layout)
         let (initClasses, _) := Bytecode.assignClasses skeletons
         let callees := bytecodeRaw.functions.map fun f =>
            Bytecode.collectCalleesBlock f.body
         let classes := Bytecode.partitionRefine initClasses callees
         let signatures := classes.mapIdx fun i cls =>
            (cls, callees[i]!.map (classes[·]!))
         (Bytecode.assignClasses signatures).1 = classes) :=
      Aiur.HFixRawCloseScratch.h_fix_raw_goal _
    have h_c_ok_transport :
        ∀ x, Bytecode.Eval.runFunction bytecodeRaw preIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x →
          Bytecode.Eval.runFunction bytecodeDedup funIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x := by
      intro x hx
      have := Bytecode.Toplevel.deduplicate_preservation bytecodeRaw h_wf_raw h_fix_raw
        preIdx (Flatten.args decls ct.globalFuncIdx args) io₀ fuel x
      simp only [← hBD, ← hRM] at this
      have hdedup_ok := this hx
      rw [hfi_eq]; exact hdedup_ok
    have hToOptionPre : t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls := by
      simp [hts, hconc, Except.toOption]
    have hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
        (key, Concrete.Declaration.function f) ∈ concDecls.pairs.toList → key = f.name :=
      hcdNameAgrees concDecls hToOptionPre
    have h_b_raw :=
      Lower.compile_preservation (decls := decls) hbc
        (fun g => namespace_preservation hdecls hts hconc hmono g)
        hNameAgrees
        (Global.mk name) preIdx hpre args io₀ fuel retTyp
    have hname_src : decls.getByKey (Global.mk name) ≠ none := hsrc
    have hname_conc : concDecls.getByKey (Global.mk name) ≠ none :=
      (namespace_preservation hdecls hts hconc hmono (Global.mk name)).mp hsrc
    have hSTC : SourceTypedCompatible decls typedDecls := by
      intro n
      have h := checkAndSimplify_keys hdecls hts n
      cases hs : decls.getByKey n <;> cases ht : typedDecls.getByKey n <;>
        simp [hs, ht] at h ⊢
    have hFIRC : FuncIdxRespectsConcretize ∅ ct.globalFuncIdx :=
      fun g args g' h => by simp at h
    have h_a_raw :=
      Typed.Decls.concretize_preservation (typedDecls := typedDecls)
        (decls := decls) hmono hdecls hts hconc hSTC
        (Global.mk name) hname_src hname_conc
        args io₀ fuel ct.globalFuncIdx ∅ hFIRC
    -- `h_a_raw` carries `Concrete.flattenValue concDecls` on the RHS; rewrite
    -- via `flatten_agree_under_fullymono` to get the source-decls-flatten form
    -- that `InterpResultEq.trans` consumes.
    have hflatten_agree :=
      flatten_agree_under_fullymono hmono hdecls hts hconc ct.globalFuncIdx
    have h_a :
        match Source.Eval.runFunction decls (Global.mk name) args io₀ fuel,
              Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | .ok (v₁, io₁), .ok (v₂, io₂) =>
            flattenValue decls ct.globalFuncIdx v₁
              = flattenValue decls ct.globalFuncIdx v₂
              ∧ IOBuffer.equiv io₁ io₂
        | .error _, .error _ => True
        | _, _ => False := by
      revert h_a_raw
      cases Source.Eval.runFunction decls (Global.mk name) args io₀ fuel with
      | error _ =>
        cases Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | error _ => intro h; exact h
        | ok _ => intro h; exact h
      | ok p₁ =>
        cases Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | error _ => intro h; exact h
        | ok p₂ =>
          obtain ⟨v₁, io₁⟩ := p₁
          obtain ⟨v₂, io₂⟩ := p₂
          intro ⟨hflat, hio⟩
          refine ⟨?_, hio⟩
          rw [hflat]; exact (hflatten_agree v₂).symm
    -- Transport `.ok` outputs from raw-bytecode to ct.bytecode via
    -- `h_c_ok_transport` (dedup) composed with `h_d` (constrained-irrelevant
    -- equation). Used below to move `h_b`'s InterpResultEq to ct.bytecode.
    have h_cd_ok_transport :
        ∀ x, Bytecode.Eval.runFunction bytecodeRaw preIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x →
          Bytecode.Eval.runFunction ct.bytecode funIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x := by
      intro x hx
      rw [h_d]; exact h_c_ok_transport x hx
    have hgfi_ext : ct.globalFuncIdx = (fun g => (preNameMap[g]?).map remap) := by
      funext g; exact hgfi g
    have h_args :
        Flatten.args decls ct.globalFuncIdx args =
          Flatten.args decls (fun g => preNameMap[g]?) args := by
      rw [Flatten.args_congr decls ct.globalFuncIdx (fun g => (preNameMap[g]?).map remap) args hgfi_ext]
      exact
        (Flatten.args_transport_remap_of_fnFree decls
          (fun g => preNameMap[g]?) remap args hargsFnFree).symm
    rw [← h_args] at h_b_raw
    have hToOption : t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls := by
      simp [hts, hconc, Except.toOption]
    have hConcRetFnFree :
        ∀ v io, Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel
                  = .ok (v, io) → Value.FnFree v :=
      fun v io hconc_ok => hconcRetFnFree concDecls v io hToOption hconc_ok
    have h_b_remap :
        InterpResultEq decls (fun g => (preNameMap[g]?).map remap) retTyp
          (Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) :=
      InterpResultEq.transport_remap_of_src_fnFree
        (f := fun g => preNameMap[g]?) (remap := remap)
        hConcRetFnFree
        h_b_raw
    have h_b :
        InterpResultEq decls ct.globalFuncIdx retTyp
          (Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) := by
      rw [hgfi_ext]
      rw [Flatten.args_congr decls ct.globalFuncIdx
            (fun g => (preNameMap[g]?).map remap) args hgfi_ext] at h_b_remap
      exact h_b_remap
    -- Combine h_a (src→concrete) and h_b (concrete→bytecodeRaw) via transitivity
    -- to get `InterpResultEq ... source (bytecodeRaw @ preIdx ...)`, then
    -- transport the `.ok` side to `ct.bytecode @ funIdx` via h_cd_ok_transport.
    -- Asymmetry of InterpResultEq (`.error/.ok = True`, `.ok/.error = False`)
    -- makes the transport valid: only `.ok` outputs need to match, and
    -- deduplicate+constrained-irrelevant preserve those.
    have h_ab :
        InterpResultEq decls ct.globalFuncIdx retTyp
          (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) :=
      InterpResultEq.trans
        (funcIdx := ct.globalFuncIdx) (retTyp := retTyp)
        (src := Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (mid := Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
        (bc  := Bytecode.Eval.runFunction bytecodeRaw preIdx
                  (Flatten.args decls ct.globalFuncIdx args) io₀ fuel)
        h_a h_b
    -- Transport h_ab to ct.bytecode @ funIdx via the `.ok`-transport.
    unfold InterpResultEq at h_ab ⊢
    cases hsrc_out : Source.Eval.runFunction decls (Global.mk name) args io₀ fuel with
    | error _ =>
      cases hct_out : Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel <;> trivial
    | ok sv =>
      cases hraw_out : Bytecode.Eval.runFunction bytecodeRaw preIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel with
      | error _ =>
        rw [hsrc_out, hraw_out] at h_ab
        exact absurd h_ab (by intro h; exact h)
      | ok rv =>
        have hct_ok := h_cd_ok_transport rv hraw_out
        rw [hct_ok]
        rw [hsrc_out, hraw_out] at h_ab
        exact h_ab

end Aiur

end
