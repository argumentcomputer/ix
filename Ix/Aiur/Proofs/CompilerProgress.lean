module
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.TypedInvariants
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.SizeBound
public import Ix.Aiur.Proofs.ConcretizeSound.RefClosed
public import Ix.Aiur.Proofs.SimplifySound
public import Ix.Aiur.Proofs.Lib

/-!
`compile_progress`.

Per-pass progress lemmas composed into a top-level progress claim. Most are
byproducts of the preservation proofs; `mkDecls` and `checkAndSimplify` are
trivial because their success is already hypothesized by `WellFormed`.
-/

public section

namespace Aiur

open Source

/-- NameAgrees predicate on `Typed.Decls`: every `.function tf` pair is stored
under key `tf.name`. -/
@[reducible, expose]
def TypedDeclsNameAgrees (tds : Typed.Decls) : Prop :=
  ∀ (key : Global) (tf : Typed.Function),
    (key, Typed.Declaration.function tf) ∈ tds.pairs.toList → key = tf.name

/-- Source-level acyclicity from `WellFormed`. Direct consequence of the
`directDatatypeDAGAcyclic` field, which is now stated post-`checkAndSimplify`
(see `WellFormed.lean` docstring — alias expansion in `mkDecls` forces the
obligation to live on the typed decls rather than raw source). -/
theorem wellFormed_implies_noDirectDatatypeCycles
    {t : Source.Toplevel} (hwf : WellFormed t)
    {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    Typed.Decls.NoDirectDatatypeCycles typedDecls :=
  hwf.directDatatypeDAGAcyclic typedDecls hts

/-- Source-side analog of `TypedDeclsNameAgrees`, in `getByKey` form. -/
private def SourceDeclsNameAgreesP (d : Source.Decls) : Prop :=
  ∀ k f, d.getByKey k = some (.function f) → k = f.name

/-- Typed-side analog in `getByKey` form. -/
private def TypedDeclsNameAgreesP (d : Typed.Decls) : Prop :=
  ∀ k tf, d.getByKey k = some (.function tf) → k = tf.name

private theorem SourceDeclsNameAgreesP_default :
    SourceDeclsNameAgreesP (default : Source.Decls) := by
  intro k f hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem TypedDeclsNameAgreesP_default :
    TypedDeclsNameAgreesP (default : Typed.Decls) := by
  intro k tf hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

/-- Bridge: `TypedDeclsNameAgreesP` ⇒ `TypedDeclsNameAgrees`. -/
private theorem TypedDeclsNameAgreesP_to_pairs {d : Typed.Decls}
    (hP : TypedDeclsNameAgreesP d) : TypedDeclsNameAgrees d := by
  intro key tf hmem
  exact hP key tf (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)

private theorem SourceDeclsNameAgreesP_insert_dataType
    {d : Source.Decls} (hP : SourceDeclsNameAgreesP d) (name : Global) (dt : DataType) :
    SourceDeclsNameAgreesP (d.insert name (.dataType dt)) := by
  intro k f hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

private theorem SourceDeclsNameAgreesP_insert_constructor
    {d : Source.Decls} (hP : SourceDeclsNameAgreesP d) (name : Global)
    (dt : DataType) (c : Constructor) :
    SourceDeclsNameAgreesP (d.insert name (.constructor dt c)) := by
  intro k f hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

/-- `mkDecls_functionStep` preserves `SourceDeclsNameAgreesP`. -/
private theorem SourceDeclsNameAgreesP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceDeclsNameAgreesP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SourceDeclsNameAgreesP acc'.2 := by
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
  intro k f hget
  by_cases hkn : (function.name == k) = true
  · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    simp only at hget
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.function.injEq] at hget
    rw [← hget]
  · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    simp only at hget
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k f hget

/-- Inner ctor fold of `mkDecls_dataTypeStep` preserves `SourceDeclsNameAgreesP`. -/
private theorem SourceDeclsNameAgreesP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SourceDeclsNameAgreesP init.2 →
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
      SourceDeclsNameAgreesP result.2 := by
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
      exact SourceDeclsNameAgreesP_insert_constructor hP _ _ _

/-- `mkDecls_dataTypeStep` preserves `SourceDeclsNameAgreesP`. -/
private theorem SourceDeclsNameAgreesP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceDeclsNameAgreesP acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SourceDeclsNameAgreesP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hP_mid : SourceDeclsNameAgreesP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SourceDeclsNameAgreesP_insert_dataType hP dataType.name _
  exact SourceDeclsNameAgreesP_ctor_fold dataType.name { dataType with constructors }
    constructors _ acc' hP_mid hstep

/-- `SourceDeclsNameAgreesP` holds on the output of `mkDecls`. -/
private theorem SourceDeclsNameAgreesP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    SourceDeclsNameAgreesP decls := by
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
  have hP_afterFns : SourceDeclsNameAgreesP afterFns.2 := by
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
    · show SourceDeclsNameAgreesP (aliasNames, (default : Source.Decls)).2
      exact SourceDeclsNameAgreesP_default
    · intro a x a' _hmem hstep hP
      exact SourceDeclsNameAgreesP_functionStep hP hstep
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
  · intro a x a' _hmem hstep hP
    exact SourceDeclsNameAgreesP_dataTypeStep hP hstep

/-- `checkFunction`'s inner form preserves `.name`. Every success path returns
`⟨function.name, ...⟩`. -/
private theorem checkFunction_inner_preserves_name
    (function : Function) (ctx : CheckContext) (s : CheckState)
    {f' : Typed.Function} {s' : CheckState}
    (h : checkFunction function ctx s = .ok (f', s')) :
    f'.name = function.name := by
  unfold checkFunction at h
  simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
             StateT.pure, Except.pure] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i inferOut _hinfer
  split at h
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hfeq, _⟩ := h
    rw [← hfeq]
  · simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
               StateT.pure, Except.pure] at h
    split at h
    · exact absurd h (by intro h'; cases h')
    rename_i _ _
    split at h
    · rename_i _
      simp only [bind, ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure,
                 StateT.pure, Except.pure] at h
      split at h
      · exact absurd h (by intro h'; cases h')
      rename_i _ _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hfeq, _⟩ := h
      rw [← hfeq]
    · rename_i _
      exact absurd h (by intro h'; cases h')

/-- `.run'`-form of `checkFunction` preserves `.name`. -/
private theorem checkFunction_run'_preserves_name
    (function : Function) (ctx : CheckContext)
    {f' : Typed.Function}
    (h : ((checkFunction function) ctx).run' {} = .ok f') :
    f'.name = function.name := by
  unfold StateT.run' at h
  simp only [Functor.map, Except.map] at h
  split at h
  · exact absurd h (by intro h'; cases h')
  rename_i pair hpair
  simp only [Except.ok.injEq] at h
  obtain ⟨f_res, s_res⟩ := pair
  simp only at h
  subst h
  exact checkFunction_inner_preserves_name function ctx _ hpair

/-- `checkAndSimplify`'s first fold (typecheck pass) lifts `SourceDeclsNameAgreesP`
to `TypedDeclsNameAgreesP`. -/
private theorem TypedDeclsNameAgreesP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hSrc : SourceDeclsNameAgreesP decls)
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TypedDeclsNameAgreesP typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TypedDeclsNameAgreesP_default
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hf'name : f'.name = f.name :=
        checkFunction_run'_preserves_name f (getFunctionContext f decls) hf'
      have hnameEq : name = f.name :=
        hSrc name f (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        have htfname : tf.name = f'.name := by rw [← hget]
        rw [htfname, hf'name, ← hnameEq]
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

/-- `simplifyDecls` preserves `TypedDeclsNameAgreesP`. -/
private theorem TypedDeclsNameAgreesP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TypedDeclsNameAgreesP typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TypedDeclsNameAgreesP typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TypedDeclsNameAgreesP_default
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hnameEq : name = f.name :=
        hP name f (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        have htfname : tf.name = f.name := by rw [← hget]
        rw [htfname, ← hnameEq]
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k tf hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k tf hget

/-- `checkAndSimplify` output satisfies `TypedDeclsNameAgrees` unconditionally.
Three-layer lifting: `mkDecls` output satisfies source-side name-agreement
→ typecheck fold preserves it (`checkFunction` preserves `.name`) →
`simplifyDecls` preserves it (body rewrite doesn't touch `.name`). -/
theorem checkAndSimplify_preserves_nameAgrees
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    TypedDeclsNameAgrees typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i srcDecls hmk
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hSrc := SourceDeclsNameAgreesP_mkDecls hmk
  have hMid := TypedDeclsNameAgreesP_of_checkFold hSrc hfold
  have hFinal := TypedDeclsNameAgreesP_of_simplifyDecls hMid hts
  exact TypedDeclsNameAgreesP_to_pairs hFinal

/-- `TypedDeclsNameAgrees` holds of `concretizeBuild`'s output: the three
nested insert-folds only add `.function` entries of the form `(k, .function tf)`
with `k = tf.name`.

* `fromSource`: `(key, .function f) ∈ typedDecls` gives `key = f.name` by
  `htdna`, and the rewritten function has `.name` unchanged.
* `withNewDts`: inserts only `.dataType` / `.constructor` entries.
* `newFunctions`: inserts each `f` under `f.name`. -/
theorem concretizeBuild_nameAgrees
    {typedDecls : Typed.Decls}
    (htdna : TypedDeclsNameAgrees typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    TypedDeclsNameAgrees
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  let P : Typed.Decls → Prop := fun m =>
    ∀ k tf, m.getByKey k = some (.function tf) → k = tf.name
  have hPdefault : P (default : Typed.Decls) := by
    intro k tf hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  have htdna' : P typedDecls := by
    intro k tf hget
    unfold IndexMap.getByKey at hget
    cases hi : typedDecls.indices[k]? with
    | none => rw [hi] at hget; simp [bind, Option.bind] at hget
    | some idx =>
      rw [hi] at hget
      simp only [bind, Option.bind] at hget
      have hv := typedDecls.validIndices k hi
      have hlt : idx < typedDecls.pairs.size := hv.1
      have hget? : typedDecls.pairs[idx]? = some (typedDecls.pairs[idx]'hlt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
      rw [hget?] at hget
      simp only [Option.map_some] at hget
      have hsnd : (typedDecls.pairs[idx]'hlt).2 = .function tf := Option.some.inj hget
      have hfst_beq : (typedDecls.pairs[idx]'hlt).1 == k := hv.2
      have hfst : (typedDecls.pairs[idx]'hlt).1 = k := LawfulBEq.eq_of_beq hfst_beq
      have hmem : (typedDecls.pairs[idx]'hlt) ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hmem' : (k, Typed.Declaration.function tf) ∈ typedDecls.pairs.toList := by
        have := hmem
        rw [← hfst, ← hsnd]
        exact this
      exact htdna k tf hmem'
  let emptySubst : Global → Option Typ := fun _ => none
  have hPfromSource :
      P (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
              let newOutput := rewriteTyp emptySubst mono f.output
              let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
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
            else acc)
        default) := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPdefault
    · intro i acc hP k tf hget
      have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p at hget hp_mem
      obtain ⟨key, d⟩ := p
      simp only at hget
      cases d with
      | function f =>
        by_cases hparams : f.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
            have hname : tf.name = f.name := by rw [← hget]
            rw [hname]
            exact htdna key f hp_mem
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k tf hget
        · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k tf hget
      | dataType dt =>
        by_cases hparams : dt.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k tf hget
        · have hparams_false : dt.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k tf hget
      | constructor dt c =>
        by_cases hparams : dt.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k tf hget
        · have hparams_false : dt.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k tf hget
  have hPwithNewDts_gen : ∀ (init : Typed.Decls), P init →
      P (newDataTypes.foldl
        (fun acc dt =>
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          let acc' := acc.insert dt.name (.dataType newDt)
          rewrittenCtors.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc')
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (dt : DataType) (init : Typed.Decls), P init →
          P ((dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }).foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              (init.insert dt.name (.dataType
                { dt with constructors :=
                    dt.constructors.map fun c =>
                      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } }))) := by
        intro dt init hPinit
        have hCtorFold : ∀ (ctors : List Constructor) (init' : Typed.Decls),
            P init' →
            P (ctors.foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              init') := by
          intro ctors
          induction ctors with
          | nil => intro init' hP'; exact hP'
          | cons c rest ih =>
            intro init' hP'
            simp only [List.foldl_cons]
            apply ih
            intro k tf hget
            by_cases hkn : (dt.name.pushNamespace c.nameHead == k) = true
            · have hkEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
              subst hkEq
              rw [IndexMap.getByKey_insert_self] at hget
              cases hget
            · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
                Bool.not_eq_true _ |>.mp hkn
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
              exact hP' k tf hget
        apply hCtorFold
        intro k tf hget
        by_cases hkn : (dt.name == k) = true
        · have hkEq : dt.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPinit k tf hget
      exact hgen (newDataTypes[i.val]'i.isLt) acc hP
  have hPfinal_gen : ∀ (init : Typed.Decls), P init →
      P (newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (f : Typed.Function), P acc →
          P (acc.insert f.name (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm typedDecls emptySubst mono f.body })) := by
        intro f hPacc k tf hget
        by_cases hkn : (f.name == k) = true
        · have hkEq : f.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
          have hname : tf.name = f.name := by rw [← hget]
          rw [hname]
        · have hne : (f.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k tf hget
      exact hgen (newFunctions[i.val]'i.isLt) hP
  unfold TypedDeclsNameAgrees
  intro key tf hmem
  have hget : (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey key
      = some (Typed.Declaration.function tf) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  have hEq : concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        (newDataTypes.foldl
          (fun acc dt =>
            let rewrittenCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            let acc' := acc.insert dt.name (.dataType newDt)
            rewrittenCtors.foldl
              (fun acc'' c =>
                let cName := dt.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt c))
              acc')
          (typedDecls.pairs.foldl
            (fun acc p =>
              let (key, d) := p
              match d with
              | .function f =>
                if f.params.isEmpty then
                  let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
                  let newOutput := rewriteTyp emptySubst mono f.output
                  let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
                  acc.insert key (.function
                    { f with inputs := newInputs, output := newOutput, body := newBody })
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
                else acc)
            default)) := by
    unfold concretizeBuild
    rfl
  rw [hEq] at hget
  exact hPfinal_gen _ (hPwithNewDts_gen _ hPfromSource) key tf hget

/-- `.function`-name-agrees invariant: concretize preserves name-agreement.
Derived from `concretizeBuild_nameAgrees` + `step4Lower` insert behaviour, via
the `List.foldlM_except_invariant` bridge through `monoDecls.pairs.toList`. -/
theorem concretize_nameAgrees
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (htdna : TypedDeclsNameAgrees typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ concDecls.pairs.toList →
      key = f.name := by
  have hstep4 : ∃ (monoDecls : Typed.Decls),
      TypedDeclsNameAgrees monoDecls ∧
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls := by
    unfold Typed.Decls.concretize at hconc
    simp only [bind, Except.bind] at hconc
    split at hconc
    · contradiction
    · rename_i drained _hdrain
      refine ⟨concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes,
              ?_, hconc⟩
      exact concretizeBuild_nameAgrees htdna _ _ _
  obtain ⟨monoDecls, hmonoNA, hfold⟩ := hstep4
  have hlist :
      _root_.List.foldlM step4Lower (default : Concrete.Decls) monoDecls.pairs.toList =
        .ok concDecls := by
    have := IndexMap.indexMap_foldlM_eq_list_foldlM
      (State := Concrete.Decls) (Err := ConcretizeError) monoDecls step4Lower default
    rw [this] at hfold; exact hfold
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ k g, acc.getByKey k = some (.function g) → k = g.name
  have hP0 : P (default : Concrete.Decls) := by
    intro k g hget
    exfalso
    have : (default : Concrete.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[k]?).bind _ = none
      have : (default : Concrete.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [this] at hget; cases hget
  have hStep : ∀ (acc : Concrete.Decls) (x : Global × Typed.Declaration)
      (acc' : Concrete.Decls),
      x ∈ monoDecls.pairs.toList → step4Lower acc x = .ok acc' → P acc → P acc' := by
    intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    unfold step4Lower at hstep
    simp only at hstep
    cases d with
    | function tf =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k g hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
        have hgname : g.name = tf.name := by rw [← hget]
        rw [hgname]
        exact hmonoNA name tf hxmem
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k g hget
    | dataType dt =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k g hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k g hget
    | constructor dt c =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k g hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k g hget
  have hPfinal : P concDecls :=
    List.foldlM_except_invariant monoDecls.pairs.toList default concDecls hP0 hStep hlist
  intro key f hmem
  have hget : concDecls.getByKey key = some (.function f) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  exact hPfinal key f hget

-- `Typed.Decls.DtNameIsKey`, `Typed.Decls.CtorIsKey`, `Typed.Decls.CtorPresent`
-- moved to `Ix/Aiur/Semantics/TypedInvariants.lean`.

/-- Concrete-side version of `CtorPresent`. Parallel to `Typed.Decls.CtorPresent`. -/
@[reducible, expose]
def Concrete.Decls.CtorPresent (cd : Concrete.Decls) : Prop :=
  ∀ (dtkey : Global) (dt : Concrete.DataType) (c : Concrete.Constructor),
    (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
    c ∈ dt.constructors →
    ∃ cc,
      (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList

/-! ### getByKey-form variants threaded through folds. -/

private def SourceDtNameIsKeyP (d : Source.Decls) : Prop :=
  ∀ k dt, d.getByKey k = some (.dataType dt) → k = dt.name

private def TypedDtNameIsKeyP (d : Typed.Decls) : Prop :=
  ∀ k dt, d.getByKey k = some (.dataType dt) → k = dt.name

private def SourceCtorIsKeyP (d : Source.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.constructor dt c) →
    k = dt.name.pushNamespace c.nameHead

private def TypedCtorIsKeyP (d : Typed.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.constructor dt c) →
    k = dt.name.pushNamespace c.nameHead

/-- CtorPresent in `getByKey` form: for every `.dataType dt` at any key, each
constructor `c ∈ dt.constructors` has some `.constructor dt cc` entry at the
pushed key. The stored data type equals the enclosing `dt`; only `cc` is
existentially quantified. Uses `getByKey` for the existence target so
fold-invariants can rewrite via `getByKey_insert_*` lemmas. -/
private def SourceCtorPresentP (d : Source.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
    ∃ cc, d.getByKey (dt.name.pushNamespace c.nameHead) =
      some (.constructor dt cc)

private def TypedCtorPresentP (d : Typed.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
    ∃ cc, d.getByKey (dt.name.pushNamespace c.nameHead) =
      some (.constructor dt cc)

private def ConcreteCtorPresentP (d : Concrete.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
    ∃ cc, d.getByKey (dt.name.pushNamespace c.nameHead) =
      some (.constructor dt cc)


/-! ### Defaults -/

private theorem SourceDtNameIsKeyP_default :
    SourceDtNameIsKeyP (default : Source.Decls) := by
  intro k dt hget
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem TypedDtNameIsKeyP_default :
    TypedDtNameIsKeyP (default : Typed.Decls) := by
  intro k dt hget
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem SourceCtorIsKeyP_default :
    SourceCtorIsKeyP (default : Source.Decls) := by
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

private theorem TypedCtorIsKeyP_default :
    TypedCtorIsKeyP (default : Typed.Decls) := by
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

private theorem SourceCtorPresentP_default :
    SourceCtorPresentP (default : Source.Decls) := by
  intro k dt c hget _hc
  exfalso
  have hne : (default : Source.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Source.Decls).indices[k]?).bind _ = none
    have : (default : Source.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem TypedDtNameIsKeyP_to_pairs {d : Typed.Decls}
    (hP : TypedDtNameIsKeyP d) : Typed.Decls.DtNameIsKey d := by
  intro key dt hmem
  exact hP key dt (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)

private theorem TypedCtorIsKeyP_to_pairs {d : Typed.Decls}
    (hP : TypedCtorIsKeyP d) : Typed.Decls.CtorIsKey d := by
  intro key dt c hmem
  exact hP key dt c (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)

/-- Bridge from getByKey-form to pairs-form for `CtorPresent`. Uses
`IndexMap.mem_pairs_of_getByKey` (requires `LawfulBEq`). -/
private theorem TypedCtorPresentP_to_pairs {d : Typed.Decls}
    (hP : TypedCtorPresentP d) : Typed.Decls.CtorPresent d := by
  intro dtkey dt c hmem hc
  have hget : d.getByKey dtkey = some (.dataType dt) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  obtain ⟨cc, hcget⟩ := hP dtkey dt c hget hc
  exact ⟨cc, IndexMap.mem_pairs_of_getByKey _ _ _ hcget⟩


/-! ### mkDecls layer: Source-side insert lemmas. -/

private theorem SourceDtNameIsKeyP_insert_function
    {d : Source.Decls} (hP : SourceDtNameIsKeyP d) (name : Global) (f : Function) :
    SourceDtNameIsKeyP (d.insert name (.function f)) := by
  intro k dt hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt hget

private theorem SourceDtNameIsKeyP_insert_dataType_self
    {d : Source.Decls} (hP : SourceDtNameIsKeyP d) (dt : DataType) :
    SourceDtNameIsKeyP (d.insert dt.name (.dataType dt)) := by
  intro k dt' hget
  by_cases hkn : (dt.name == k) = true
  · have hkEq : dt.name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hget
    rw [← hget]
  · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SourceDtNameIsKeyP_insert_constructor
    {d : Source.Decls} (hP : SourceDtNameIsKeyP d) (name : Global)
    (dt : DataType) (c : Constructor) :
    SourceDtNameIsKeyP (d.insert name (.constructor dt c)) := by
  intro k dt' hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' hget

private theorem SourceCtorIsKeyP_insert_function
    {d : Source.Decls} (hP : SourceCtorIsKeyP d) (name : Global) (f : Function) :
    SourceCtorIsKeyP (d.insert name (.function f)) := by
  intro k dt c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt c hget

private theorem SourceCtorIsKeyP_insert_dataType
    {d : Source.Decls} (hP : SourceCtorIsKeyP d) (name : Global) (dt : DataType) :
    SourceCtorIsKeyP (d.insert name (.dataType dt)) := by
  intro k dt' c hget
  by_cases hkn : (name == k) = true
  · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c hget

/-- Insert a ctor at its keyed location preserves CtorIsKey. -/
private theorem SourceCtorIsKeyP_insert_constructor_at_key
    {d : Source.Decls} (hP : SourceCtorIsKeyP d)
    (dt : DataType) (c : Constructor) :
    SourceCtorIsKeyP
      (d.insert (dt.name.pushNamespace c.nameHead) (.constructor dt c)) := by
  intro k dt' c' hget
  by_cases hkn : (dt.name.pushNamespace c.nameHead == k) = true
  · have hkEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hget
    obtain ⟨hdtEq, hcEq⟩ := hget
    rw [← hdtEq, ← hcEq]
  · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
      Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k dt' c' hget

/-! ### mkDecls_functionStep preservation -/

private theorem SourceDtNameIsKeyP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceDtNameIsKeyP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SourceDtNameIsKeyP acc'.2 := by
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
  exact SourceDtNameIsKeyP_insert_function hP _ _

private theorem SourceCtorIsKeyP_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {function : Function}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceCtorIsKeyP acc.2)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SourceCtorIsKeyP acc'.2 := by
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
  exact SourceCtorIsKeyP_insert_function hP _ _

/-! ### Inner ctor fold preservation (DtNameIsKey): trivial, inserts ctors. -/

private theorem SourceDtNameIsKeyP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SourceDtNameIsKeyP init.2 →
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
      SourceDtNameIsKeyP result.2 := by
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
      exact SourceDtNameIsKeyP_insert_constructor hP _ _ _

/-- mkDecls_dataTypeStep preserves DtNameIsKey. -/
private theorem SourceDtNameIsKeyP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceDtNameIsKeyP acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SourceDtNameIsKeyP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  -- Insert `.dataType { dataType with constructors }` under `dataType.name`.
  -- Note: `{ dataType with constructors }.name = dataType.name`.
  have hP_mid : SourceDtNameIsKeyP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) := by
    have h := SourceDtNameIsKeyP_insert_dataType_self (dt := { dataType with constructors }) hP
    -- h has key = ({ dataType with constructors }).name = dataType.name
    exact h
  exact SourceDtNameIsKeyP_ctor_fold dataType.name { dataType with constructors }
    constructors _ acc' hP_mid hstep

/-! ### Inner ctor fold for CtorIsKey: inserts each under `dt.name ++ c.nameHead`. -/

private theorem SourceCtorIsKeyP_ctor_fold
    (dataTypeName : Global) (dataType' : DataType)
    (hname : dataType'.name = dataTypeName) :
    ∀ (ctors : List Constructor) (init : Std.HashSet Global × Source.Decls)
      (result : Std.HashSet Global × Source.Decls),
      SourceCtorIsKeyP init.2 →
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
      SourceCtorIsKeyP result.2 := by
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
      -- Insert at `dataTypeName.pushNamespace c.nameHead`. We need CtorIsKey
      -- with `dt.name.pushNamespace c.nameHead = dataTypeName.pushNamespace c.nameHead`
      -- since `dataType'.name = dataTypeName`.
      have hk_eq : dataType'.name.pushNamespace c.nameHead =
          dataTypeName.pushNamespace c.nameHead := by rw [hname]
      -- Use insert_at_key: need the key to be `dataType'.name.pushNamespace c.nameHead`.
      have hrewrite : init.2.insert (dataTypeName.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c) =
          init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c) := by
        rw [hk_eq]
      show SourceCtorIsKeyP
        (init.1.insert (dataTypeName.pushNamespace c.nameHead),
          init.2.insert (dataTypeName.pushNamespace c.nameHead)
            (Source.Declaration.constructor dataType' c)).2
      rw [hrewrite]
      exact SourceCtorIsKeyP_insert_constructor_at_key hP dataType' c

private theorem SourceCtorIsKeyP_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc : Std.HashSet Global × Source.Decls} {dataType : DataType}
    {acc' : Std.HashSet Global × Source.Decls}
    (hP : SourceCtorIsKeyP acc.2)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SourceCtorIsKeyP acc'.2 := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hP_mid : SourceCtorIsKeyP (acc.2.insert dataType.name
      (.dataType { dataType with constructors })) :=
    SourceCtorIsKeyP_insert_dataType hP dataType.name _
  -- `{ dataType with constructors }.name = dataType.name`.
  exact SourceCtorIsKeyP_ctor_fold dataType.name { dataType with constructors }
    rfl constructors _ acc' hP_mid hstep

/-! ### DtNameIsKey/CtorIsKey on mkDecls output -/

private theorem SourceDtNameIsKeyP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    SourceDtNameIsKeyP decls := by
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
  have hP_afterFns : SourceDtNameIsKeyP afterFns.2 := by
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
    · exact SourceDtNameIsKeyP_default
    · intro a x a' _hmem hstep hP
      exact SourceDtNameIsKeyP_functionStep hP hstep
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
  · intro a x a' _hmem hstep hP
    exact SourceDtNameIsKeyP_dataTypeStep hP hstep

private theorem SourceCtorIsKeyP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    SourceCtorIsKeyP decls := by
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
  have hP_afterFns : SourceCtorIsKeyP afterFns.2 := by
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
    · exact SourceCtorIsKeyP_default
    · intro a x a' _hmem hstep hP
      exact SourceCtorIsKeyP_functionStep hP hstep
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
  · intro a x a' _hmem hstep hP
    exact SourceCtorIsKeyP_dataTypeStep hP hstep

/-! ### Source-side CtorPresent via mkDecls

The key insight: `mkDecls_dataTypeStep` inserts a `.dataType dt'` followed by
all `.constructor dt' c` entries for `c ∈ dt'.constructors` (at the pushed
keys). Functions-first ordering + duplicate-check in `allNames` prevents
subsequent inserts from overwriting these `.constructor` entries. -/

/-- The state shape used during `mkDecls` folds: (allNames, decls). -/
private abbrev MkDeclsAcc := Std.HashSet Global × Source.Decls

/-- Source-side strong invariant threaded through `mkDecls` folds.
Couples the pure CtorPresent invariant with a key-tracking clause:
every decls key is in `allNames`. This is the property that lets us
know subsequent inserts at "fresh" keys (those not in `allNames`)
cannot overwrite existing `.constructor` entries. -/
private def SourceCtorPresentAux (acc : MkDeclsAcc) : Prop :=
  SourceCtorPresentP acc.2 ∧
  (∀ k v, acc.2.getByKey k = some v → acc.1.contains k = true)



/-- `mkDecls_functionStep` preserves `SourceCtorPresentAux`. Inserting a
`.function` at a key not yet in `allNames` can't overwrite any `.dataType`
or `.constructor` entry (those are tracked in `allNames`), so the invariant
follows from pointwise analysis. -/
private theorem SourceCtorPresentAux_functionStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : MkDeclsAcc} {function : Function}
    (hAux : SourceCtorPresentAux acc)
    (hstep : mkDecls_functionStep expandTyp acc function = .ok acc') :
    SourceCtorPresentAux acc' := by
  obtain ⟨hP, hKeys⟩ := hAux
  unfold mkDecls_functionStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i hnotIn
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i inputs' _hinputs
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i output' _houtput
  simp only [Except.ok.injEq] at hstep
  subst hstep
  have hnotInEq : acc.1.contains function.name = false := by
    cases hfc : acc.1.contains function.name with
    | false => rfl
    | true => rw [hfc] at hnotIn; exact absurd hnotIn (by simp)
  refine ⟨?_, ?_⟩
  · -- SourceCtorPresentP preservation
    intro k dt c hget hc
    simp only at hget
    by_cases hkn : (function.name == k) = true
    · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      obtain ⟨cc, hcget⟩ := hP k dt c hget hc
      -- The ctor is at pushed key. If the pushed key == function.name, it
      -- would mean function.name is already in `allNames` (via hKeys on hcget).
      -- But hnotInEq says otherwise. Thus no collision.
      have hcKey := hKeys _ _ hcget
      have hpushne : (function.name == dt.name.pushNamespace c.nameHead) = false := by
        cases hfc : (function.name == dt.name.pushNamespace c.nameHead) with
        | false => rfl
        | true =>
          have hfeq : function.name = dt.name.pushNamespace c.nameHead :=
            LawfulBEq.eq_of_beq hfc
          rw [hfeq] at hnotInEq
          rw [hnotInEq] at hcKey
          cases hcKey
      refine ⟨cc, ?_⟩
      simp only
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hpushne]
      exact hcget
  · -- allNames tracks keys
    intro k v hget
    simp only at hget
    by_cases hkn : (function.name == k) = true
    · have hkEq : function.name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [Std.HashSet.contains_insert]
      simp
    · have hne : (function.name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      rw [Std.HashSet.contains_insert]
      have := hKeys k v hget
      rw [this]; simp



/-- Weaker intermediate invariant for `mkDecls_dataTypeStep`. Allows the
in-progress `.dataType dt'` to have only already-processed ctors' entries. -/
private def CtorProgressInv (dt' : DataType) (processed : List Constructor)
    (acc : MkDeclsAcc) : Prop :=
  (∀ k d, acc.2.getByKey k = some (.dataType d) →
      (d = dt' → ∀ c ∈ processed,
        ∃ cc, acc.2.getByKey (d.name.pushNamespace c.nameHead) =
          some (.constructor d cc)) ∧
      (d ≠ dt' → ∀ c ∈ d.constructors,
        ∃ cc, acc.2.getByKey (d.name.pushNamespace c.nameHead) =
          some (.constructor d cc))) ∧
  acc.2.getByKey dt'.name = some (.dataType dt') ∧
  (∀ k v, acc.2.getByKey k = some v → acc.1.contains k = true)

/-- `mkDecls_dataTypeStep` preserves `SourceCtorPresentAux` and establishes the
CtorPresent obligation for the new dataType's constructors. -/
private theorem SourceCtorPresentAux_dataTypeStep
    {expandTyp : Typ → Except CheckError Typ}
    {acc acc' : MkDeclsAcc} {dataType : DataType}
    (hAux : SourceCtorPresentAux acc)
    (hstep : mkDecls_dataTypeStep expandTyp acc dataType = .ok acc') :
    SourceCtorPresentAux acc' := by
  unfold mkDecls_dataTypeStep at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i hDtNotIn
  split at hstep
  · exact absurd hstep (by intro h; cases h)
  rename_i constructors _hctors
  have hNotInEq : acc.1.contains dataType.name = false := by
    cases hh : acc.1.contains dataType.name with
    | false => rfl
    | true => rw [hh] at hDtNotIn; exact absurd hDtNotIn (by simp)
  have key_helper : ∀ (dt' : DataType) (processed remaining : List Constructor)
      (init final : MkDeclsAcc),
      processed ++ remaining = dt'.constructors →
      CtorProgressInv dt' processed init →
      remaining.foldlM
        (fun (acc : MkDeclsAcc) ctor =>
          let ctorName := dt'.name.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError MkDeclsAcc)
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dt' ctor)))
        init = .ok final →
      CtorProgressInv dt' dt'.constructors final := by
    intro dt' processed remaining
    induction remaining generalizing processed with
    | nil =>
      intro init final hsplit hInv hfold
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
      subst hfold
      have : processed = dt'.constructors := by rw [← hsplit]; simp
      rw [this] at hInv; exact hInv
    | cons cur rest ih =>
      intro init final hsplit hInv hfold
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      · exact absurd hfold (by intro h; cases h)
      rename_i acc_next hstep_inner
      split at hstep_inner
      · exact absurd hstep_inner (by intro h; cases h)
      rename_i hCtorNotIn
      simp only [Except.ok.injEq] at hstep_inner
      subst hstep_inner
      have hsplit' : processed ++ [cur] ++ rest = dt'.constructors := by
        simp only [← hsplit]; simp
      have hInv' : CtorProgressInv dt' (processed ++ [cur])
          (init.1.insert (dt'.name.pushNamespace cur.nameHead),
           init.2.insert (dt'.name.pushNamespace cur.nameHead)
             (.constructor dt' cur)) := by
        obtain ⟨hDtClause, hDtSelf, hKeys⟩ := hInv
        refine ⟨?_, ?_, ?_⟩
        · intro k d hget
          simp only at hget
          by_cases hkn : (dt'.name.pushNamespace cur.nameHead == k) = true
          · have hkEq : dt'.name.pushNamespace cur.nameHead = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (dt'.name.pushNamespace cur.nameHead == k) = false :=
              Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            obtain ⟨h_self, h_other⟩ := hDtClause k d hget
            refine ⟨?_, ?_⟩
            · intro hdEq
              intro c' hc'
              rcases List.mem_append.mp hc' with hc'_processed | hc'_singleton
              · obtain ⟨cc, hccget⟩ := h_self hdEq c' hc'_processed
                by_cases hkn' : (dt'.name.pushNamespace cur.nameHead ==
                                  d.name.pushNamespace c'.nameHead) = true
                · refine ⟨cur, ?_⟩
                  have hkEq' := LawfulBEq.eq_of_beq hkn'
                  rw [← hkEq', ← hdEq]
                  exact IndexMap.getByKey_insert_self _ _ _
                · have hne' : (dt'.name.pushNamespace cur.nameHead ==
                                d.name.pushNamespace c'.nameHead) = false :=
                    Bool.not_eq_true _ |>.mp hkn'
                  refine ⟨cc, ?_⟩
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hne']
                  exact hccget
              · have hceq : c' = cur := List.mem_singleton.mp hc'_singleton
                refine ⟨cur, ?_⟩
                rw [hceq]
                have hdn : d.name = dt'.name := by rw [hdEq]
                rw [hdn, ← hdEq]
                exact IndexMap.getByKey_insert_self _ _ _
            · intro hdNe c' hc'
              obtain ⟨cc, hccget⟩ := h_other hdNe c' hc'
              by_cases hkn' : (dt'.name.pushNamespace cur.nameHead ==
                                d.name.pushNamespace c'.nameHead) = true
              · -- Collision: pushed(cur) = d.name.pushNamespace c'.nameHead. The
                -- witness `hccget` was in init's decls, so init.1 contains that
                -- pushed key, but `hCtorNotIn` says the newly-inserted pushed key
                -- (= pushed(cur)) is not in init.1. Contradiction.
                exfalso
                have hkEq' := LawfulBEq.eq_of_beq hkn'
                have hccIn : init.1.contains (d.name.pushNamespace c'.nameHead) = true :=
                  hKeys _ _ hccget
                rw [← hkEq'] at hccIn
                rw [hccIn] at hCtorNotIn
                exact absurd hCtorNotIn (by simp)
              · have hne' : (dt'.name.pushNamespace cur.nameHead ==
                              d.name.pushNamespace c'.nameHead) = false :=
                  Bool.not_eq_true _ |>.mp hkn'
                refine ⟨cc, ?_⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne']
                exact hccget
        · have hne : (dt'.name.pushNamespace cur.nameHead == dt'.name) = false := by
            cases hh : (dt'.name.pushNamespace cur.nameHead == dt'.name) with
            | false => rfl
            | true =>
              exfalso
              have heq := LawfulBEq.eq_of_beq hh
              have hDtInInit : init.1.contains dt'.name = true := hKeys _ _ hDtSelf
              rw [← heq] at hDtInInit
              rw [hDtInInit] at hCtorNotIn
              exact absurd hCtorNotIn (by simp)
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hDtSelf
        · intro k v hget
          simp only at hget
          by_cases hkn : (dt'.name.pushNamespace cur.nameHead == k) = true
          · have hkEq : dt'.name.pushNamespace cur.nameHead = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [Std.HashSet.contains_insert]; simp
          · have hne : (dt'.name.pushNamespace cur.nameHead == k) = false :=
              Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            rw [Std.HashSet.contains_insert]
            have := hKeys k v hget; rw [this]; simp
      exact ih (processed ++ [cur]) _ _ hsplit' hInv' hfold
  obtain ⟨hAuxP, hAuxK⟩ := hAux
  have hDtMidGet : (acc.2.insert dataType.name
        (Source.Declaration.dataType { dataType with constructors })).getByKey dataType.name =
      some (.dataType { dataType with constructors }) :=
    IndexMap.getByKey_insert_self _ _ _
  have hInvMid : CtorProgressInv ({ dataType with constructors }) []
      (acc.1.insert dataType.name,
       acc.2.insert dataType.name (.dataType { dataType with constructors })) := by
    refine ⟨?_, hDtMidGet, ?_⟩
    · intro k d hget
      simp only at hget
      refine ⟨?_, ?_⟩
      · intro _ c hc; cases hc
      by_cases hkn : (dataType.name == k) = true
      · have hkEq : dataType.name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Source.Declaration.dataType.injEq] at hget
        intro hdNe
        exfalso
        exact hdNe hget.symm
      · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        intro hdNe c hc
        obtain ⟨cc, hccget⟩ := hAuxP k d c hget hc
        by_cases hkn2 : (dataType.name == d.name.pushNamespace c.nameHead) = true
        · exfalso
          have heq := LawfulBEq.eq_of_beq hkn2
          have hccIn : acc.1.contains (d.name.pushNamespace c.nameHead) = true :=
            hAuxK _ _ hccget
          rw [← heq] at hccIn
          rw [hccIn] at hNotInEq; cases hNotInEq
        · have hne2 : (dataType.name == d.name.pushNamespace c.nameHead) = false :=
            Bool.not_eq_true _ |>.mp hkn2
          refine ⟨cc, ?_⟩
          simp only
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
          exact hccget
    · intro k v hget
      simp only at hget
      by_cases hkn : (dataType.name == k) = true
      · have hkEq : dataType.name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [Std.HashSet.contains_insert]; simp
      · have hne : (dataType.name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        rw [Std.HashSet.contains_insert]
        have := hAuxK k v hget; rw [this]; simp
  have hFinalInv : CtorProgressInv ({ dataType with constructors })
      ({ dataType with constructors }).constructors acc' :=
    key_helper _ [] _ _ _ (by simp) hInvMid hstep
  obtain ⟨hDtClause', hDtSelf', hKeys'⟩ := hFinalInv
  refine ⟨?_, hKeys'⟩
  intro k d c hget hc
  obtain ⟨h_self, h_other⟩ := hDtClause' k d hget
  by_cases hdEq : d = ({ dataType with constructors } : DataType)
  · apply h_self hdEq
    have hdc : d.constructors = ({ dataType with constructors } : DataType).constructors := by rw [hdEq]
    rw [hdc] at hc
    exact hc
  · exact h_other hdEq c hc

/-- `SourceCtorPresentP` holds on the output of `mkDecls`. -/
private theorem SourceCtorPresentP_mkDecls
    {toplevel : Source.Toplevel} {decls : Source.Decls}
    (h : toplevel.mkDecls = .ok decls) :
    SourceCtorPresentP decls := by
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
  -- Seed aux invariant from `aliasNames`: aliases-only haven't inserted anything
  -- into decls yet (the second component is `default`). So both conjuncts hold.
  have hAux0 : SourceCtorPresentAux (aliasNames, (default : Source.Decls)) := by
    refine ⟨SourceCtorPresentP_default, ?_⟩
    intro k v hget
    exfalso
    have hne : (default : Source.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Source.Decls).indices[k]?).bind _ = none
      have : (default : Source.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  have hAux_afterFns : SourceCtorPresentAux afterFns := by
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
    · exact hAux0
    · intro a x a' _hmem hstep hAux
      exact SourceCtorPresentAux_functionStep hAux hstep
  have hAux_final : SourceCtorPresentAux afterDts := by
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
    · exact hAux_afterFns
    · intro a x a' _hmem hstep hAux
      exact SourceCtorPresentAux_dataTypeStep hAux hstep
  exact hAux_final.1

/-! ### Typecheck-fold preservation: DtNameIsKey, CtorIsKey -/

private theorem TypedDtNameIsKeyP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hSrc : SourceDtNameIsKeyP decls)
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TypedDtNameIsKeyP typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TypedDtNameIsKeyP_default
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      -- Source said `(name, .dataType d) ∈ decls.pairs.toList` via hxmem,
      -- and `hSrc` gives us name = d.name.
      have hnameEq : name = d.name :=
        hSrc name d (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        rw [← hget]; exact hnameEq
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget

private theorem TypedCtorIsKeyP_of_checkFold
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hSrc : SourceCtorIsKeyP decls)
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls) :
    TypedCtorIsKeyP typedDecls := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
  · exact TypedCtorIsKeyP_default
  · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
    simp only at hstep
    cases decl with
    | constructor d c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hnameEq : name = d.name.pushNamespace c.nameHead :=
        hSrc name d c (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k dt c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨hd, hcc⟩ := hget
        rw [← hd, ← hcc]; exact hnameEq
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c' hget
    | dataType d =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c' hget
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i f' hf'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c' hget

/-! ### simplifyDecls preservation: DtNameIsKey, CtorIsKey -/

private theorem TypedDtNameIsKeyP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TypedDtNameIsKeyP typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TypedDtNameIsKeyP typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TypedDtNameIsKeyP_default
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
    cases d with
    | function f =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · exact absurd hstep (by intro h'; cases h')
      rename_i body' _hbody'
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | dataType dt =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hnameEq : name = dt.name :=
        hP name dt (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k dt' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        rw [← hget]; exact hnameEq
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' hget
    | constructor dt c =>
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      intro k dt' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' hget

private theorem TypedCtorIsKeyP_of_simplifyDecls
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TypedCtorIsKeyP typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TypedCtorIsKeyP typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
  · exact TypedCtorIsKeyP_default
  · intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    simp only at hstep
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
      have hnameEq : name = dt.name.pushNamespace c.nameHead :=
        hP name dt c (IndexMap.getByKey_of_mem_pairs _ _ _ hxmem)
      intro k dt' c' hget
      by_cases hkn : (name == k) = true
      · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
        obtain ⟨hd, hcc⟩ := hget
        rw [← hd, ← hcc]; exact hnameEq
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt' c' hget

/-! ### Typecheck + simplify preservation of CtorPresent.

Both passes iterate over pairs and insert transformed decls at the SAME key.
A subtle point: `simplifyDecls` folds over `typedDecls.pairs` BUT each step
inserts into a fresh `default` accumulator. So the final decls' pairs are a
permutation (in the same order) of the input's pairs, with functions'
bodies updated — dataTypes and constructors pass through verbatim.

We prove CtorPresent by exhibiting, for each `.dataType` pair in the input,
all `.constructor` pairs at the pushed keys still present in the output.
Since the transformation preserves pair structure (same keys), and the
input's CtorPresent is already pair-level, the output's CtorPresent follows. -/

/-- Key observation for typecheck-fold: the fold output has the SAME keys as
input, with functions replaced by typechecked versions and dataType/constructor
pass-through. Bundled as: `output.getByKey k = some ...` implies input had
a `.dataType`/`.constructor`/`.function` at k with the same payload
(modulo typecheck transformation for functions).

A weaker, usable form: if `output.getByKey k = some (.dataType dt)`, then
`input.getByKey k = some (.dataType dt)`. Similarly for `.constructor`.

We prove this via a fold-invariant "acc preserves all .dataType/.constructor
entries from input up to position i". -/
private theorem checkFold_preserves_ctorPresent
    {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hfold : decls.foldlM (init := (default : Typed.Decls))
      (fun acc (name, decl) => match decl with
        | .constructor d c => pure $ acc.insert name (.constructor d c : Typed.Declaration)
        | .dataType d => pure $ acc.insert name (.dataType d : Typed.Declaration)
        | .function f => do
          let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
          pure $ acc.insert name (.function f : Typed.Declaration)) = .ok typedDecls)
    (hSrc : SourceCtorPresentP decls) :
    TypedCtorPresentP typedDecls := by
  have hDtTransport : ∀ k dt, typedDecls.getByKey k = some (.dataType dt) →
      decls.getByKey k = some (.dataType dt) := by
    rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
    let P : Typed.Decls → Prop := fun acc =>
      ∀ k dt, acc.getByKey k = some (.dataType dt) →
        decls.getByKey k = some (.dataType dt)
    have hP0 : P (default : Typed.Decls) := by
      intro k dt hget
      exfalso
      have : (default : Typed.Decls).getByKey k = none := by
        unfold IndexMap.getByKey
        show ((default : Typed.Decls).indices[k]?).bind _ = none
        have : (default : Typed.Decls).indices[k]? = none := by
          show ((default : Std.HashMap Global Nat))[k]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      rw [this] at hget; cases hget
    apply List.foldlM_except_invariant decls.pairs.toList _ _ _ _ hfold
    · exact hP0
    · intro acc ⟨name, decl⟩ acc' hxmem hstep hPacc
      simp only at hstep
      have hname_src : decls.getByKey name = some decl :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
      cases decl with
      | constructor d c =>
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
      | dataType d =>
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          subst hget
          exact hname_src
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
      | function f =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i f' _hf'
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
  have hCtorTransport : ∀ k dt c, decls.getByKey k = some (.constructor dt c) →
      typedDecls.getByKey k = some (.constructor dt c) := by
    rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
    intro k dt c hdeclsget
    have hmem : (k, Source.Declaration.constructor dt c) ∈ decls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hdeclsget
    have key_helper : ∀ (processed remaining : List (Global × Source.Declaration))
        (init finalacc : Typed.Decls),
        processed ++ remaining = decls.pairs.toList →
        (∀ k dt c, (k, Source.Declaration.constructor dt c) ∈ processed →
          init.getByKey k = some (.constructor dt c)) →
        remaining.foldlM
          (fun acc (p : Global × Source.Declaration) => match p.2 with
            | .constructor d c => pure $ acc.insert p.1 (.constructor d c : Typed.Declaration)
            | .dataType d => pure $ acc.insert p.1 (.dataType d : Typed.Declaration)
            | .function f => do
              let f ← ((checkFunction f) (getFunctionContext f decls)).run' {}
              pure $ acc.insert p.1 (.function f : Typed.Declaration)) init = .ok finalacc →
        ∀ k dt c, (k, Source.Declaration.constructor dt c) ∈ decls.pairs.toList →
          finalacc.getByKey k = some (.constructor dt c) := by
      intro processed remaining
      induction remaining generalizing processed with
      | nil =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
        subst hfold
        have : processed = decls.pairs.toList := by
          rw [← hsplit]; simp
        rw [this] at hPinit
        exact hPinit k dt c hmemFinal
      | cons x xs ih =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_cons, bind, Except.bind] at hfold
        split at hfold
        · exact absurd hfold (by intro h; cases h)
        rename_i acc' hstep
        obtain ⟨xname, xdecl⟩ := x
        simp only at hstep
        have hsplit' : (processed ++ [(xname, xdecl)]) ++ xs = decls.pairs.toList := by
          simp [← hsplit]
        have hPacc' : ∀ k' dt' c',
            (k', Source.Declaration.constructor dt' c') ∈ processed ++ [(xname, xdecl)] →
            acc'.getByKey k' = some (.constructor dt' c') := by
          intro k' dt' c' hmem'
          rcases List.mem_append.mp hmem' with hmemL | hmemR
          · have hacc_k' := hPinit k' dt' c' hmemL
            cases xdecl with
            | constructor xd xc =>
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                have hx_in_decls : (xname, Source.Declaration.constructor xd xc) ∈
                    decls.pairs.toList := by
                  have hh : (xname, Source.Declaration.constructor xd xc) ∈
                      processed ++ ((xname, Source.Declaration.constructor xd xc) :: xs) := by
                    apply List.mem_append_right
                    exact List.Mem.head _
                  rw [hsplit] at hh; exact hh
                have hk'_in_decls : (xname, Source.Declaration.constructor dt' c') ∈
                    decls.pairs.toList := by
                  have hh : (xname, Source.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Source.Declaration.constructor xd xc) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at hh; exact hh
                have h1 : decls.getByKey xname = some (.constructor xd xc) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ hx_in_decls
                have h2 : decls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ hk'_in_decls
                rw [h1] at h2
                simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at h2
                obtain ⟨hxdEq, hxcEq⟩ := h2
                subst hxdEq; subst hxcEq
                rw [IndexMap.getByKey_insert_self]
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | dataType xd =>
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Source.Declaration.dataType xd) ∈ decls.pairs.toList := by
                  have : (xname, Source.Declaration.dataType xd) ∈
                      processed ++ ((xname, Source.Declaration.dataType xd) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Source.Declaration.constructor dt' c') ∈ decls.pairs.toList := by
                  have : (xname, Source.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Source.Declaration.dataType xd) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : decls.getByKey xname = some (.dataType xd) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : decls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | function xf =>
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xf' _hxf'
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Source.Declaration.function xf) ∈ decls.pairs.toList := by
                  have : (xname, Source.Declaration.function xf) ∈
                      processed ++ ((xname, Source.Declaration.function xf) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Source.Declaration.constructor dt' c') ∈ decls.pairs.toList := by
                  have : (xname, Source.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Source.Declaration.function xf) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : decls.getByKey xname = some (.function xf) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : decls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
          · rcases List.mem_singleton.mp hmemR with hxeq
            rcases Prod.mk.injEq _ _ _ _ |>.mp hxeq with ⟨hname_eq, hdecl_eq⟩
            subst hname_eq; subst hdecl_eq
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            subst hstep
            exact IndexMap.getByKey_insert_self _ _ _
        exact ih (processed ++ [(xname, xdecl)]) acc' finalacc hsplit' hPacc' hfold k dt c hmemFinal
    exact key_helper [] decls.pairs.toList default typedDecls (by simp)
      (by intro _ _ _ h; cases h) hfold k dt c hmem
  intro k dt c hget hc
  have hdeclsGet : decls.getByKey k = some (.dataType dt) := hDtTransport k dt hget
  obtain ⟨cc, hccGet⟩ := hSrc k dt c hdeclsGet hc
  exact ⟨cc, hCtorTransport _ _ _ hccGet⟩

/-- simplifyDecls preserves CtorPresent similarly — .dataType and .constructor
pass verbatim, .function only updates body. -/
private theorem simplifyDecls_preserves_ctorPresent
    {decls : Source.Decls} {typedDecls typedDecls' : Typed.Decls}
    (hP : TypedCtorPresentP typedDecls)
    (hsimp : simplifyDecls decls typedDecls = .ok typedDecls') :
    TypedCtorPresentP typedDecls' := by
  unfold simplifyDecls at hsimp
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hsimp
  have hDtTransport : ∀ k dt, typedDecls'.getByKey k = some (.dataType dt) →
      typedDecls.getByKey k = some (.dataType dt) := by
    let P : Typed.Decls → Prop := fun acc =>
      ∀ k dt, acc.getByKey k = some (.dataType dt) →
        typedDecls.getByKey k = some (.dataType dt)
    have hP0 : P (default : Typed.Decls) := by
      intro k dt hget
      exfalso
      have : (default : Typed.Decls).getByKey k = none := by
        unfold IndexMap.getByKey
        show ((default : Typed.Decls).indices[k]?).bind _ = none
        have : (default : Typed.Decls).indices[k]? = none := by
          show ((default : Std.HashMap Global Nat))[k]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      rw [this] at hget; cases hget
    apply List.foldlM_except_invariant typedDecls.pairs.toList _ _ _ _ hsimp
    · exact hP0
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
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
      | dataType dt' =>
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          subst hget
          exact hname_td
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
      | constructor dt' c =>
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep
        intro k dt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
  have hCtorTransport : ∀ k dt c, typedDecls.getByKey k = some (.constructor dt c) →
      typedDecls'.getByKey k = some (.constructor dt c) := by
    intro k dt c htdget
    have hmem : (k, Typed.Declaration.constructor dt c) ∈ typedDecls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ htdget
    have key_helper : ∀ (processed remaining : List (Global × Typed.Declaration))
        (init finalacc : Typed.Decls),
        processed ++ remaining = typedDecls.pairs.toList →
        (∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ processed →
          init.getByKey k = some (.constructor dt c)) →
        remaining.foldlM
          (fun acc (p : Global × Typed.Declaration) => match p.2 with
            | .function f => do
              let body' ← simplifyTypedTerm decls f.body
              pure (acc.insert p.1 (.function { f with body := body' }))
            | .dataType dt => pure (acc.insert p.1 (.dataType dt))
            | .constructor dt c => pure (acc.insert p.1 (.constructor dt c))) init = .ok finalacc →
        ∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ typedDecls.pairs.toList →
          finalacc.getByKey k = some (.constructor dt c) := by
      intro processed remaining
      induction remaining generalizing processed with
      | nil =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
        subst hfold
        have : processed = typedDecls.pairs.toList := by
          rw [← hsplit]; simp
        rw [this] at hPinit
        exact hPinit k dt c hmemFinal
      | cons x xs ih =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_cons, bind, Except.bind] at hfold
        split at hfold
        · exact absurd hfold (by intro h; cases h)
        rename_i acc' hstep
        obtain ⟨xname, xdecl⟩ := x
        simp only at hstep
        have hsplit' : (processed ++ [(xname, xdecl)]) ++ xs = typedDecls.pairs.toList := by
          simp [← hsplit]
        have hPacc' : ∀ k' dt' c',
            (k', Typed.Declaration.constructor dt' c') ∈ processed ++ [(xname, xdecl)] →
            acc'.getByKey k' = some (.constructor dt' c') := by
          intro k' dt' c' hmem'
          rcases List.mem_append.mp hmem' with hmemL | hmemR
          · have hacc_k' := hPinit k' dt' c' hmemL
            cases xdecl with
            | constructor xd xc =>
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                have hx_in : (xname, Typed.Declaration.constructor xd xc) ∈
                    typedDecls.pairs.toList := by
                  have hh : (xname, Typed.Declaration.constructor xd xc) ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at hh; exact hh
                have hk'_in : (xname, Typed.Declaration.constructor dt' c') ∈
                    typedDecls.pairs.toList := by
                  have hh : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at hh; exact hh
                have h1 : typedDecls.getByKey xname = some (.constructor xd xc) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ hx_in
                have h2 : typedDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ hk'_in
                rw [h1] at h2
                simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at h2
                obtain ⟨hxdEq, hxcEq⟩ := h2
                subst hxdEq; subst hxcEq
                rw [IndexMap.getByKey_insert_self]
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | dataType xd =>
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.dataType xd) ∈ typedDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.dataType xd) ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ typedDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : typedDecls.getByKey xname = some (.dataType xd) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : typedDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | function xf =>
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xbody' _hxbody'
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.function xf) ∈ typedDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.function xf) ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ typedDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : typedDecls.getByKey xname = some (.function xf) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : typedDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
          · rcases List.mem_singleton.mp hmemR with hxeq
            rcases Prod.mk.injEq _ _ _ _ |>.mp hxeq with ⟨hname_eq, hdecl_eq⟩
            subst hname_eq; subst hdecl_eq
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            subst hstep
            exact IndexMap.getByKey_insert_self _ _ _
        exact ih (processed ++ [(xname, xdecl)]) acc' finalacc hsplit' hPacc' hfold k dt c hmemFinal
    exact key_helper [] typedDecls.pairs.toList default typedDecls' (by simp)
      (by intro _ _ _ h; cases h) hsimp k dt c hmem
  intro k dt c hget hc
  have htdGet : typedDecls.getByKey k = some (.dataType dt) := hDtTransport k dt hget
  obtain ⟨cc, hccGet⟩ := hP k dt c htdGet hc
  exact ⟨cc, hCtorTransport _ _ _ hccGet⟩

/-! ### checkAndSimplify_preserves for DtNameIsKey and CtorIsKey. -/

theorem checkAndSimplify_preserves_dtNameIsKey
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    Typed.Decls.DtNameIsKey typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i srcDecls hmk
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hSrc := SourceDtNameIsKeyP_mkDecls hmk
  have hMid := TypedDtNameIsKeyP_of_checkFold hSrc hfold
  have hFinal := TypedDtNameIsKeyP_of_simplifyDecls hMid hts
  exact TypedDtNameIsKeyP_to_pairs hFinal

theorem checkAndSimplify_preserves_ctorIsKey
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    Typed.Decls.CtorIsKey typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i srcDecls hmk
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hSrc := SourceCtorIsKeyP_mkDecls hmk
  have hMid := TypedCtorIsKeyP_of_checkFold hSrc hfold
  have hFinal := TypedCtorIsKeyP_of_simplifyDecls hMid hts
  exact TypedCtorIsKeyP_to_pairs hFinal

theorem checkAndSimplify_preserves_ctorPresent
    {t : Source.Toplevel} {typedDecls : Typed.Decls}
    (hts : t.checkAndSimplify = .ok typedDecls) :
    Typed.Decls.CtorPresent typedDecls := by
  unfold Source.Toplevel.checkAndSimplify at hts
  simp only [bind, Except.bind] at hts
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i srcDecls hmk
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i _u _hwf
  split at hts
  · exact absurd hts (by intro h'; cases h')
  rename_i midTyped hfold
  have hSrc := SourceCtorPresentP_mkDecls hmk
  have hMid := checkFold_preserves_ctorPresent hfold hSrc
  have hFinal := simplifyDecls_preserves_ctorPresent hMid hts
  exact TypedCtorPresentP_to_pairs hFinal


/-! ### concretizeBuild / concretize: DtNameIsKey -/

/-- Pair-form of `Typed.Decls.DtNameIsKey` for use in fold invariants. -/
private def TypedDecls_DtNameIsKey_pairs (d : Typed.Decls) : Prop :=
  ∀ key dt, (key, Typed.Declaration.dataType dt) ∈ d.pairs.toList → key = dt.name



/-- `concretizeBuild` preserves `DtNameIsKey`. Parallel to `concretizeBuild_nameAgrees`. -/
theorem concretizeBuild_dtNameIsKey
    {typedDecls : Typed.Decls}
    (htdDt : Typed.Decls.DtNameIsKey typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    Typed.Decls.DtNameIsKey
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  let P : Typed.Decls → Prop := fun m =>
    ∀ k dt, m.getByKey k = some (.dataType dt) → k = dt.name
  have hPdefault : P (default : Typed.Decls) := by
    intro k dt hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  -- Transfer pair-form `htdDt` to getByKey-form `htdDt'`.
  have htdDt' : P typedDecls := by
    intro k dt hget
    unfold IndexMap.getByKey at hget
    cases hi : typedDecls.indices[k]? with
    | none => rw [hi] at hget; simp [bind, Option.bind] at hget
    | some idx =>
      rw [hi] at hget
      simp only [bind, Option.bind] at hget
      have hv := typedDecls.validIndices k hi
      have hlt : idx < typedDecls.pairs.size := hv.1
      have hget? : typedDecls.pairs[idx]? = some (typedDecls.pairs[idx]'hlt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
      rw [hget?] at hget
      simp only [Option.map_some] at hget
      have hsnd : (typedDecls.pairs[idx]'hlt).2 = .dataType dt := Option.some.inj hget
      have hfst_beq : (typedDecls.pairs[idx]'hlt).1 == k := hv.2
      have hfst : (typedDecls.pairs[idx]'hlt).1 = k := LawfulBEq.eq_of_beq hfst_beq
      have hmem : (typedDecls.pairs[idx]'hlt) ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hmem' : (k, Typed.Declaration.dataType dt) ∈ typedDecls.pairs.toList := by
        have := hmem; rw [← hfst, ← hsnd]; exact this
      exact htdDt k dt hmem'
  let emptySubst : Global → Option Typ := fun _ => none
  -- fromSource fold: inserts .dataType entries keyed by source key, with rewritten dt having same name.
  have hPfromSource :
      P (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
              let newOutput := rewriteTyp emptySubst mono f.output
              let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
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
            else acc)
        default) := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPdefault
    · intro i acc hP k dt hget
      have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p at hget hp_mem
      obtain ⟨key, d⟩ := p
      simp only at hget
      cases d with
      | function f =>
        by_cases hparams : f.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt hget
        · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt hget
      | dataType dtSrc =>
        by_cases hparams : dtSrc.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
            -- hget says dt = { dtSrc with constructors := newCtors }
            -- so dt.name = dtSrc.name
            -- From htdDt: key = dtSrc.name (using (key, .dataType dtSrc) ∈ pairs)
            have hname : dt.name = dtSrc.name := by
              rw [← hget]
            rw [hname]
            exact htdDt key dtSrc hp_mem
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt hget
        · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt hget
      | constructor dtSrc c =>
        by_cases hparams : dtSrc.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt hget
        · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt hget
  -- withNewDts: inserts (dt.name, .dataType newDt) with newDt.name = dt.name, and ctors
  -- keyed elsewhere.
  have hPwithNewDts_gen : ∀ (init : Typed.Decls), P init →
      P (newDataTypes.foldl
        (fun acc dt =>
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          let acc' := acc.insert dt.name (.dataType newDt)
          rewrittenCtors.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc')
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (dt : DataType) (init : Typed.Decls), P init →
          P ((dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }).foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              (init.insert dt.name (.dataType
                { dt with constructors :=
                    dt.constructors.map fun c =>
                      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } }))) := by
        intro dt init hPinit
        have hCtorFold : ∀ (ctors : List Constructor) (init' : Typed.Decls),
            P init' →
            P (ctors.foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              init') := by
          intro ctors
          induction ctors with
          | nil => intro init' hP'; exact hP'
          | cons c rest ih =>
            intro init' hP'
            simp only [List.foldl_cons]
            apply ih
            intro k dt' hget
            by_cases hkn : (dt.name.pushNamespace c.nameHead == k) = true
            · have hkEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
              subst hkEq
              rw [IndexMap.getByKey_insert_self] at hget
              cases hget
            · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
                Bool.not_eq_true _ |>.mp hkn
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
              exact hP' k dt' hget
        apply hCtorFold
        intro k dt' hget
        by_cases hkn : (dt.name == k) = true
        · have hkEq : dt.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          -- hget: dt' = { dt with constructors := ... }; so dt'.name = dt.name.
          rw [← hget]
        · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPinit k dt' hget
      exact hgen (newDataTypes[i.val]'i.isLt) acc hP
  -- newFunctions: only inserts .function entries.
  have hPfinal_gen : ∀ (init : Typed.Decls), P init →
      P (newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (f : Typed.Function), P acc →
          P (acc.insert f.name (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm typedDecls emptySubst mono f.body })) := by
        intro f hPacc k dt hget
        by_cases hkn : (f.name == k) = true
        · have hkEq : f.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (f.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt hget
      exact hgen (newFunctions[i.val]'i.isLt) hP
  -- Final composition: `concretizeBuild = newFunctions.foldl _ (newDataTypes.foldl _ fromSource)`.
  intro key dt hmem
  have hget : (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey key
      = some (Typed.Declaration.dataType dt) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  have hEq : concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        (newDataTypes.foldl
          (fun acc dt =>
            let rewrittenCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            let acc' := acc.insert dt.name (.dataType newDt)
            rewrittenCtors.foldl
              (fun acc'' c =>
                let cName := dt.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt c))
              acc')
          (typedDecls.pairs.foldl
            (fun acc p =>
              let (key, d) := p
              match d with
              | .function f =>
                if f.params.isEmpty then
                  let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
                  let newOutput := rewriteTyp emptySubst mono f.output
                  let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
                  acc.insert key (.function
                    { f with inputs := newInputs, output := newOutput, body := newBody })
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
                else acc)
            default)) := by
    unfold concretizeBuild
    rfl
  rw [hEq] at hget
  exact hPfinal_gen _ (hPwithNewDts_gen _ hPfromSource) key dt hget

/-- `concretize` output satisfies `DtNameIsKey`, given the typed input does. -/
theorem concretize_produces_dtNameIsKey
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (htdDt : Typed.Decls.DtNameIsKey tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.DtNameIsKey cd := by
  have hstep4 : ∃ (monoDecls : Typed.Decls),
      Typed.Decls.DtNameIsKey monoDecls ∧
      monoDecls.foldlM (init := default) step4Lower = .ok cd := by
    unfold Typed.Decls.concretize at hconc
    simp only [bind, Except.bind] at hconc
    split at hconc
    · contradiction
    · rename_i drained _hdrain
      refine ⟨concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes,
              ?_, hconc⟩
      exact concretizeBuild_dtNameIsKey htdDt _ _ _
  obtain ⟨monoDecls, hmonoDt, hfold⟩ := hstep4
  -- Transfer to getByKey form: need `∀ k dt, monoDecls.getByKey k = some (.dataType dt) → k = dt.name`.
  have hmonoDt' : ∀ k dt, monoDecls.getByKey k = some (.dataType dt) → k = dt.name := by
    intro k dt hget
    unfold IndexMap.getByKey at hget
    cases hi : monoDecls.indices[k]? with
    | none => rw [hi] at hget; simp [bind, Option.bind] at hget
    | some idx =>
      rw [hi] at hget
      simp only [bind, Option.bind] at hget
      have hv := monoDecls.validIndices k hi
      have hlt : idx < monoDecls.pairs.size := hv.1
      have hget? : monoDecls.pairs[idx]? = some (monoDecls.pairs[idx]'hlt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
      rw [hget?] at hget
      simp only [Option.map_some] at hget
      have hsnd : (monoDecls.pairs[idx]'hlt).2 = .dataType dt := Option.some.inj hget
      have hfst_beq : (monoDecls.pairs[idx]'hlt).1 == k := hv.2
      have hfst : (monoDecls.pairs[idx]'hlt).1 = k := LawfulBEq.eq_of_beq hfst_beq
      have hmem : (monoDecls.pairs[idx]'hlt) ∈ monoDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hmem' : (k, Typed.Declaration.dataType dt) ∈ monoDecls.pairs.toList := by
        have := hmem; rw [← hfst, ← hsnd]; exact this
      exact hmonoDt k dt hmem'
  have hlist :
      _root_.List.foldlM step4Lower (default : Concrete.Decls) monoDecls.pairs.toList =
        .ok cd := by
    have := IndexMap.indexMap_foldlM_eq_list_foldlM
      (State := Concrete.Decls) (Err := ConcretizeError) monoDecls step4Lower default
    rw [this] at hfold; exact hfold
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ k dt, acc.getByKey k = some (.dataType dt) → k = dt.name
  have hP0 : P (default : Concrete.Decls) := by
    intro k dt hget
    exfalso
    have : (default : Concrete.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[k]?).bind _ = none
      have : (default : Concrete.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [this] at hget; cases hget
  have hStep : ∀ (acc : Concrete.Decls) (x : Global × Typed.Declaration)
      (acc' : Concrete.Decls),
      x ∈ monoDecls.pairs.toList → step4Lower acc x = .ok acc' → P acc → P acc' := by
    intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    unfold step4Lower at hstep
    simp only at hstep
    cases d with
    | function tf =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | dataType dtSrc =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      rename_i ctors _hctors
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Concrete.Declaration.dataType.injEq] at hget
        -- dt = { name := dtSrc.name, constructors := ctors }; so dt.name = dtSrc.name.
        have hname : dt.name = dtSrc.name := by rw [← hget]
        rw [hname]
        -- Need: name = dtSrc.name; from monoDecls getByKey via hmonoDt'.
        apply hmonoDt' name dtSrc
        exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
    | constructor dtSrc c =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      rename_i ctors _hctors
      split at hstep
      · contradiction
      rename_i argTypes _hargs
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt hget
  have hPfinal : P cd :=
    List.foldlM_except_invariant monoDecls.pairs.toList default cd hP0 hStep hlist
  intro key dt hget
  exact hPfinal key dt hget

/-- `concretizeBuild` preserves `CtorIsKey`. -/
theorem concretizeBuild_ctorIsKey
    {typedDecls : Typed.Decls}
    (htdCtor : Typed.Decls.CtorIsKey typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    ∀ k dt c,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey k =
        some (.constructor dt c) → k = dt.name.pushNamespace c.nameHead := by
  let P : Typed.Decls → Prop := fun m =>
    ∀ k dt c, m.getByKey k = some (.constructor dt c) → k = dt.name.pushNamespace c.nameHead
  have hPdefault : P (default : Typed.Decls) := by
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
  have htdCtor' : P typedDecls := by
    intro k dt c hget
    unfold IndexMap.getByKey at hget
    cases hi : typedDecls.indices[k]? with
    | none => rw [hi] at hget; simp [bind, Option.bind] at hget
    | some idx =>
      rw [hi] at hget
      simp only [bind, Option.bind] at hget
      have hv := typedDecls.validIndices k hi
      have hlt : idx < typedDecls.pairs.size := hv.1
      have hget? : typedDecls.pairs[idx]? = some (typedDecls.pairs[idx]'hlt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
      rw [hget?] at hget
      simp only [Option.map_some] at hget
      have hsnd : (typedDecls.pairs[idx]'hlt).2 = .constructor dt c := Option.some.inj hget
      have hfst_beq : (typedDecls.pairs[idx]'hlt).1 == k := hv.2
      have hfst : (typedDecls.pairs[idx]'hlt).1 = k := LawfulBEq.eq_of_beq hfst_beq
      have hmem : (typedDecls.pairs[idx]'hlt) ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hmem' : (k, Typed.Declaration.constructor dt c) ∈ typedDecls.pairs.toList := by
        have := hmem; rw [← hfst, ← hsnd]; exact this
      exact htdCtor k dt c hmem'
  let emptySubst : Global → Option Typ := fun _ => none
  have hPfromSource :
      P (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
              let newOutput := rewriteTyp emptySubst mono f.output
              let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
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
            else acc)
        default) := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPdefault
    · intro i acc hP k dt c hget
      have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p at hget hp_mem
      obtain ⟨key, d⟩ := p
      simp only at hget
      cases d with
      | function f =>
        by_cases hparams : f.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt c hget
        · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt c hget
      | dataType dtSrc =>
        by_cases hparams : dtSrc.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            cases hget
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt c hget
        · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt c hget
      | constructor dtSrc cSrc =>
        by_cases hparams : dtSrc.params.isEmpty = true
        · simp only [hparams, if_true] at hget
          by_cases hkn : (key == k) = true
          · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
            subst hkEq
            rw [IndexMap.getByKey_insert_self] at hget
            simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
            obtain ⟨hdt, hc⟩ := hget
            -- hdt: dt = { dtSrc with ... }, so dt.name = dtSrc.name
            -- hc:  c  = { cSrc with ... },   so c.nameHead = cSrc.nameHead
            have hname : dt.name = dtSrc.name := by rw [← hdt]
            have hhead : c.nameHead = cSrc.nameHead := by rw [← hc]
            rw [hname, hhead]
            exact htdCtor key dtSrc cSrc hp_mem
          · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
            exact hP k dt c hget
        · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
          simp only [hparams_false] at hget
          exact hP k dt c hget
  have hPwithNewDts_gen : ∀ (init : Typed.Decls), P init →
      P (newDataTypes.foldl
        (fun acc dt =>
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          let acc' := acc.insert dt.name (.dataType newDt)
          rewrittenCtors.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc')
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (dt : DataType) (init : Typed.Decls), P init →
          P ((dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }).foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              (init.insert dt.name (.dataType
                { dt with constructors :=
                    dt.constructors.map fun c =>
                      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } }))) := by
        intro dt init hPinit
        have hCtorFold : ∀ (ctors : List Constructor) (init' : Typed.Decls),
            P init' →
            P (ctors.foldl
              (fun acc'' c =>
                acc''.insert (dt.name.pushNamespace c.nameHead) (.constructor
                  { dt with constructors :=
                      dt.constructors.map fun c' =>
                        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
                  c))
              init') := by
          intro ctors
          induction ctors with
          | nil => intro init' hP'; exact hP'
          | cons c rest ih =>
            intro init' hP'
            simp only [List.foldl_cons]
            apply ih
            intro k dt' c' hget
            by_cases hkn : (dt.name.pushNamespace c.nameHead == k) = true
            · have hkEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
              subst hkEq
              rw [IndexMap.getByKey_insert_self] at hget
              simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
              obtain ⟨hdt, hc⟩ := hget
              -- hdt: dt' = { dt with constructors := ... }; so dt'.name = dt.name
              -- hc:  c'  = c;                                so c'.nameHead = c.nameHead
              have hname : dt'.name = dt.name := by rw [← hdt]
              have hhead : c'.nameHead = c.nameHead := by rw [← hc]
              rw [hname, hhead]
            · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
                Bool.not_eq_true _ |>.mp hkn
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
              exact hP' k dt' c' hget
        apply hCtorFold
        intro k dt' c' hget
        by_cases hkn : (dt.name == k) = true
        · have hkEq : dt.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPinit k dt' c' hget
      exact hgen (newDataTypes[i.val]'i.isLt) acc hP
  have hPfinal_gen : ∀ (init : Typed.Decls), P init →
      P (newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        init) := by
    intro init hPinit
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
    · exact hPinit
    · intro i acc hP
      have hgen : ∀ (f : Typed.Function), P acc →
          P (acc.insert f.name (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm typedDecls emptySubst mono f.body })) := by
        intro f hPacc k dt c hget
        by_cases hkn : (f.name == k) = true
        · have hkEq : f.name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (f.name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPacc k dt c hget
      exact hgen (newFunctions[i.val]'i.isLt) hP
  intro k dt c hget
  have hEq : concretizeBuild typedDecls mono newFunctions newDataTypes =
      newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        (newDataTypes.foldl
          (fun acc dt =>
            let rewrittenCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            let acc' := acc.insert dt.name (.dataType newDt)
            rewrittenCtors.foldl
              (fun acc'' c =>
                let cName := dt.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt c))
              acc')
          (typedDecls.pairs.foldl
            (fun acc p =>
              let (key, d) := p
              match d with
              | .function f =>
                if f.params.isEmpty then
                  let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
                  let newOutput := rewriteTyp emptySubst mono f.output
                  let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
                  acc.insert key (.function
                    { f with inputs := newInputs, output := newOutput, body := newBody })
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
                else acc)
            default)) := by
    unfold concretizeBuild
    rfl
  rw [hEq] at hget
  exact hPfinal_gen _ (hPwithNewDts_gen _ hPfromSource) k dt c hget

theorem concretize_produces_ctorIsKey
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (htdCtor : Typed.Decls.CtorIsKey tds)
    (hconc : tds.concretize = .ok cd) :
    ∀ (key : Global) (cdt : Concrete.DataType) (cc : Concrete.Constructor),
      (key, Concrete.Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead := by
  have hstep4 : ∃ (monoDecls : Typed.Decls),
      (∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
        k = dt.name.pushNamespace c.nameHead) ∧
      monoDecls.foldlM (init := default) step4Lower = .ok cd := by
    unfold Typed.Decls.concretize at hconc
    simp only [bind, Except.bind] at hconc
    split at hconc
    · contradiction
    · rename_i drained _hdrain
      refine ⟨concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes,
              ?_, hconc⟩
      exact concretizeBuild_ctorIsKey htdCtor _ _ _
  obtain ⟨monoDecls, hmonoCtor', hfold⟩ := hstep4
  have hlist :
      _root_.List.foldlM step4Lower (default : Concrete.Decls) monoDecls.pairs.toList =
        .ok cd := by
    have := IndexMap.indexMap_foldlM_eq_list_foldlM
      (State := Concrete.Decls) (Err := ConcretizeError) monoDecls step4Lower default
    rw [this] at hfold; exact hfold
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ k dt c, acc.getByKey k = some (.constructor dt c) →
      k = dt.name.pushNamespace c.nameHead
  have hP0 : P (default : Concrete.Decls) := by
    intro k dt c hget
    exfalso
    have : (default : Concrete.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[k]?).bind _ = none
      have : (default : Concrete.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [this] at hget; cases hget
  have hStep : ∀ (acc : Concrete.Decls) (x : Global × Typed.Declaration)
      (acc' : Concrete.Decls),
      x ∈ monoDecls.pairs.toList → step4Lower acc x = .ok acc' → P acc → P acc' := by
    intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    unfold step4Lower at hstep
    simp only at hstep
    cases d with
    | function tf =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      split at hstep
      · contradiction
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | dataType dtSrc =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      rename_i ctors _hctors
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
    | constructor dtSrc cSrc =>
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · contradiction
      rename_i ctors _hctors
      split at hstep
      · contradiction
      rename_i argTypes _hargs
      simp only [Except.ok.injEq] at hstep
      subst hstep
      intro k dt c hget
      by_cases hkn : (name == k) = true
      · have hknEq : name = k := LawfulBEq.eq_of_beq hkn
        subst hknEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Concrete.Declaration.constructor.injEq] at hget
        obtain ⟨hdt, hc⟩ := hget
        -- hdt: dt = { name := dtSrc.name, constructors := ctors }, so dt.name = dtSrc.name.
        -- hc:  c  = { nameHead := cSrc.nameHead, argTypes := argTypes }, so c.nameHead = cSrc.nameHead.
        have hname : dt.name = dtSrc.name := by rw [← hdt]
        have hhead : c.nameHead = cSrc.nameHead := by rw [← hc]
        rw [hname, hhead]
        -- Need: name = dtSrc.name.pushNamespace cSrc.nameHead; from monoDecls via hmonoCtor'.
        apply hmonoCtor' name dtSrc cSrc
        exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
      · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc k dt c hget
  have hPfinal : P cd :=
    List.foldlM_except_invariant monoDecls.pairs.toList default cd hP0 hStep hlist
  intro key cdt cc hmem
  have hget : cd.getByKey key = some (.constructor cdt cc) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  exact hPfinal key cdt cc hget


/-! ### concretize CtorPresent.

Two parts:
1. `concretizeBuild_ctorPresent`: the build phase preserves/establishes CtorPresent.
   - `fromSource` fold: for each `.dataType dt` in input, inserts rewritten `.dataType newDt`
     at same key; for each `.constructor dt c` in input (at pushed key), inserts rewritten
     `.constructor newDt' c'` at same key. Input CtorPresent yields output CtorPresent.
   - `withNewDts` fold: for each fresh `dt ∈ newDataTypes`, inserts `.dataType newDt` at
     `dt.name` and immediately inserts all `.constructor newDt c` at pushed keys.
     Self-satisfies CtorPresent for new dts.
   - `newFunctions` fold: only inserts `.function` entries, can't affect any existing
     `.dataType` / `.constructor` entries (by DtNameIsKey + CtorIsKey key analysis).
2. `step4Lower_preserves_ctorPresent`: the Typed → Concrete lowering is 1:1 on pair
   structure (each Typed pair produces exactly one Concrete pair at the same key, with
   `.dataType` → `.dataType`, `.constructor` → `.constructor` modulo `typToConcrete`
   type rewriting). So input CtorPresent transports to output. -/

-- `NewDtBridge` / `NewFnBridge` moved to `Semantics/DrainInvariants.lean`.

namespace CtorPresentBody

/-! ### `concretizeBuild_ctorPresent` body, ported from
`Ix/Aiur/Proofs/CtorPresentBodyCloseScratch.lean` (2026-04-24).

Three-fold composition matching `concretizeBuild`:

* `fromSource` fold: iterates `typedDecls.pairs.foldl`, inserting each
  rewritten entry at its source key. For each `.dataType dtSrc` insert
  `.dataType {dtSrc with constructors := rewrittenCtors}`; for each
  `.constructor dtSrc cSrc` insert `.constructor {dtSrc with ctors :=
  rewrittenCtors} {cSrc with argTypes := ...}`. Keys preserved verbatim.

* `withNewDts` fold: for each new `dt`, inserts `.dataType rewrittenDt`
  at `dt.name` and `.constructor rewrittenDt c` at each pushed key.

* `newFunctions` fold: inserts `.function newF` at `f.name` keys only.

Split into five concrete-hypothesis lemmas (4 sorried axiomatic steps +
`newFunctions_preserves_ctorPresent` closed inline).
-/

/-! ### Helpers ported from `CtorPresentBodyWorkScratch.lean`. -/

/-- Rewrite a single constructor's arg types via `mono`. -/
private abbrev rewriteC (mono : MonoMap) (c : Constructor) : Constructor :=
  { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }

/-- Rewrite a data type via `mono`: rewrite every constructor. -/
private abbrev rewriteDt (mono : MonoMap) (dt : DataType) : DataType :=
  { dt with constructors := dt.constructors.map (rewriteC mono) }





/-- The per-step function used in the `fromSource` fold. -/
private def fromSourceStep (typedDecls : Typed.Decls) (mono : MonoMap)
    (acc : Typed.Decls) (p : Global × Typed.Declaration) : Typed.Decls :=
  let emptySubst : Global → Option Typ := fun _ => none
  let (key, d) := p
  match d with
  | .function f =>
    if f.params.isEmpty then
      let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
      let newOutput := rewriteTyp emptySubst mono f.output
      let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
      acc.insert key (.function
        { f with inputs := newInputs, output := newOutput, body := newBody })
    else acc
  | .dataType dt =>
    if dt.params.isEmpty then
      acc.insert key (.dataType (rewriteDt mono dt))
    else acc
  | .constructor dt c =>
    if dt.params.isEmpty then
      acc.insert key (.constructor (rewriteDt mono dt) (rewriteC mono c))
    else acc

/-- `fromSource` as the foldl of `fromSourceStep`. -/
private def fromSource (typedDecls : Typed.Decls) (mono : MonoMap) : Typed.Decls :=
  typedDecls.pairs.foldl (fromSourceStep typedDecls mono) default









/-- Compute post-Phase-2 acc structure. -/
private def phase2Acc (typedDecls : Typed.Decls) (mono : MonoMap)
    (newDataTypes : Array DataType) : Typed.Decls :=
  let emptySubst : Global → Option Typ := fun _ => none
  newDataTypes.foldl
    (fun acc dt =>
      let rewrittenCtors := dt.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
      let newDt : DataType := { dt with constructors := rewrittenCtors }
      let acc' := acc.insert dt.name (.dataType newDt)
      rewrittenCtors.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc')
    (fromSource typedDecls mono)



















end CtorPresentBody

































/-! ### `concretize_produces_ctorPresent_entry` — closure decomposition.

The PLAN-locked closure path mirrors A.2's foundation
(`concretizeBuild_preserves_function_kind_at_entry_fwd`), with the same
3-fold trace through `concretizeBuild` (srcStep / dtStep / fnStep) plus a
final `step4Lower` lift. The dataType-companion invariant is preserved by
each fold step:

* **srcStep** — when the typed source has `.dataType td_dt` at `g` with
  `td_dt.params = []`, ALL of `td_dt`'s ctors are also iterated in the
  same `typedDecls.pairs.foldl`, since `Typed.Decls.CtorPresent tds`
  guarantees their typed-side presence (and `Typed.Decls.CtorIsKey tds`
  pins their keys). Each `.constructor td_dt c` insert produces a
  `.constructor newDt' c'` at `td_dt.name.pushNamespace c.nameHead`.
* **dtStep** — when `dt' ∈ drained.newDataTypes` with `dt'.name = g`,
  the inner ctor-fold inserts `.constructor newDt' c` at every
  `g.pushNamespace c.nameHead` for `c ∈ dt'.constructors`.
* **fnStep** — preserves all dataType / ctor entries unconditionally.
* **step4Lower** — lowers `.dataType md_dt` ↦ `.dataType cdt` and
  `.constructor md_dt md_c` ↦ `.constructor cdt cc` with the SAME `cdt`
  shape (deterministic `typToConcrete emptyMono`), so the typed/mono-side
  ctor-companion invariant transports verbatim to concrete. -/

namespace CtorPresentEntry

/-- Mono-side ctor-companion invariant: every `.dataType md_dt` entry in
`monoDecls` (= `concretizeBuild` output) carries every `c ∈ md_dt.constructors`
as a `.constructor md_dt _` entry at `md_dt.name.pushNamespace c.nameHead`. -/
private def MonoDtCtorCompanion (monoDecls : Typed.Decls) : Prop :=
  ∀ (g : Global) (md_dt : DataType),
    monoDecls.getByKey g = some (.dataType md_dt) →
    ∀ c ∈ md_dt.constructors, ∃ md_c,
      monoDecls.getByKey (md_dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c)

end CtorPresentEntry

/-- **Wire B bridge.** Entry-restricted variant of
`concretize_produces_ctorPresent`. Drops the `FullyMonomorphic t` hypothesis
in favour of `WellFormed t`; the entry-mono propagation ensures the
ctor-present chain still closes through the drained-mono subset.

CLOSURE: extracts `drained` + `monoDecls` from `hconc`, then composes
two structural sub-claims (BLOCKED inside the body):

(1) `MonoDtCtorCompanion monoDecls` — every `.dataType md_dt` in
    `monoDecls` has every `c ∈ md_dt.constructors` as a `.constructor
    md_dt _` entry at `md_dt.name.pushNamespace c.nameHead`. Established
    via 3-fold trace through `concretizeBuild`:
    * **srcStep** — typed-side `CtorPresent + CtorIsKey` ensure each
      typed `.dataType td_dt` pair has companion `.constructor td_dt _`
      pairs at `td_dt.name.pushNamespace c.nameHead`. srcStep inserts
      both into mono with same `newDt'` reference (deterministic
      `rewriteTyp` over `td_dt.constructors`).
    * **dtStep** — for `dt' ∈ drained.newDataTypes`, the inner ctor-fold
      inserts `.constructor newDt' c` at every pushed key with `newDt'`
      matching the `.dataType newDt'` outer insert.
    * **fnStep** — preserves ctor/dt entries (only inserts `.function`).

(2) `step4Lower` fold transport: from `MonoDtCtorCompanion monoDecls` +
    fold success, derive `Concrete.Decls.CtorPresent cd`. Per-`(dtkey,
    .dataType cdt) ∈ cd.pairs`:
    * `step4Lower_backward_dataType_kind_at_key` lifts to mono `.dataType
      md_dt` at same key.
    * `step4Lower_dataType_explicit` provides length/nameHead
      correspondence: each `c ∈ cdt.constructors` ↔ `c_md ∈
      md_dt.constructors` at same index with `c.nameHead = c_md.nameHead`.
    * `MonoDtCtorCompanion` gives mono `.constructor md_dt md_c` at
      `md_dt.name.pushNamespace c_md.nameHead`.
    * `step4Lower_fold_ctor_bridge_inline` lifts to cd `.constructor cdt'
      cc` at same key. The keys align via `cdt.name = md_dt.name` (from
      `step4Lower_dataType_step_explicit`'s construction `cdt = { name :=
      md_dt.name, ... }`) and `c.nameHead = c_md.nameHead`.
    * `cdt' = cdt` follows from `step4Lower`'s deterministic `mapM` over
      the SAME `md_dt.constructors` (both arms compute identical
      `lowered_ctors`).

Both sub-claims are blocked structural-induction arguments documented
inline. The single `sorry` covers their composition; net change keeps the
sorry count at the previous total. Decomposing into separate helpers
would fragment closure-path tracking without reducing total work. -/
private theorem concretize_produces_ctorPresent_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok tds)
    (hP : Typed.Decls.CtorPresent tds)
    (hDt : Typed.Decls.DtNameIsKey tds)
    (hCtor : Typed.Decls.CtorIsKey tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.CtorPresent cd :=
  -- Direct delegation to the entry-restricted ctor-present propagation lemma
  -- in ConcretizeSound (the WIRE-B bridge). Closure path documented inside.
  -- Derive `Concrete.Decls.DtNameIsKey cd` via `concretize_produces_dtNameIsKey`
  -- and pass through (used internally to close D2d).
  concretize_produces_ctorPresent_under_entry hP hDt hCtor hunique
    (concretize_produces_dtNameIsKey hDt hconc) hconc

/-! ### Decomposition of `Lower.compile_progress_entry`. -/

/-- Sub-claim: `Concrete.Decls.SizeBoundOk cd` under entry-restricted
hypotheses (no `FullyMonomorphic t`).

`BLOCKED-sizeBoundOk-entry`. Closure path documented in
`Scratch.lean`'s `concretize_produces_sizeBoundOk` (orphan, FullyMono-shaped):
composes `concretize_produces_refClosed_entry` (A.1, CLOSED 2026-05-02) +
`concretize_preserves_direct_dag` (orphan, F=1, depends on
`DirectDagBody.spine_transfer` BLOCKED at ~500-700 LoC of `concretizeBuild`
backward-trace + `templateOf_of_source_ref` lemma) +
`sizeBound_ok_of_rank` (orphan, F=0, ~140 LoC) + `concretize_produces_dtNameIsKey`
(F=0, in scope as `concretize_produces_dtNameIsKey _htdDt _hconc`).

Migrating the orphan stack upstream (Scratch.lean:6957-7218) once
`spine_transfer` is closed yields the entry variant by:
- replacing `concretize_produces_refClosed hmono ...` with
  `Toplevel.concretize_produces_refClosed_entry _hwf hdecls _hts _hconc`,
- removing the `hmono : FullyMonomorphic t` parameter (the only consumer
  of FullyMono is `concretize_produces_refClosed`, which has its
  entry-bridge available via A.1). -/
private theorem sizeBoundOk_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (_hdtkey : Concrete.Decls.DtNameIsKey cd)
    (_htdDt : Typed.Decls.DtNameIsKey tds)
    (_htdCtorPresent : Typed.Decls.CtorPresent tds) :
    Concrete.Decls.SizeBoundOk cd := by
  sorry

/-- Sub-claim: per-function `Concrete.Function.compile` succeeds on every
`.function` pair of an entry-restricted `cd`.

`BLOCKED-Function-compile-entry`. Closure path mirrors orphan
`Function_compile_progress` (Scratch.lean:1153, FullyMono-shaped, sorry'd
in turn). The orphan composes:
- Step 1 (`Function.compile`'s `layoutMap[f.name]?` lookup): discharges via
  `inputs_foldlM_ok`-shape lemma showing `lm` contains a `.function`
  layout entry at every `.function` key (~80 LoC, mechanical from
  `layoutMap`'s structural construction in `LayoutMap.layoutMap`).
- Step 2 (`f.inputs.foldlM ... typSize lm typ`): closes via
  `inputs_foldlM_ok` (Scratch.lean:1382, F=0 modulo
  `Aiur.typSize_ok_of_refClosed_lm` in `LowerShared.lean`, both available).
- Step 3 (`f.body.compile f.output lm bindings |>.run state`): F=1; depends
  on `body_compile_ok` (Scratch.lean:1322, BLOCKED on
  `toIndex_progress_core_extended` IsCoreExtended-witness extraction +
  block-level dispatch + tail-form `Ctrl.compile_progress`).

The entry-bridge variant differs from `Function_compile_progress` only by:
- replacing `hmono : FullyMonomorphic t` with `_hwf : WellFormed t` +
  `_hdecls : t.mkDecls = .ok decls`,
- consuming `Toplevel.concretize_produces_refClosed_entry` (A.1, CLOSED)
  in place of `concretize_produces_refClosed` (orphan FullyMono variant).

Migration prerequisite: lift the Step 3 closure (`body_compile_ok` →
`toIndex_preservation_core_extended` access arms) before this entry bridge
becomes mechanical. -/
private theorem function_compile_progress_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (lm : LayoutMap)
    (_hlm : cd.layoutMap = .ok lm)
    (_hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (_hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (_hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Concrete.Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (_hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (_htdDt : Typed.Decls.DtNameIsKey tds)
    (_htdCtorPresent : Typed.Decls.CtorPresent tds)
    (_name : Global) (_f : Concrete.Function)
    (_hname : cd.getByKey _name = some (.function _f)) :
    ∃ body lms, Concrete.Function.compile lm _f = .ok (body, lms) := by
  sorry

/-- **Wire B bridge.** Entry-restricted variant of `Lower.compile_progress`.
Drops the `FullyMonomorphic t` hypothesis; the lemma now consumes a
`WellFormed t` witness instead.

Body composes through (in order):
1. `Toplevel.concretize_produces_refClosed_entry` (A.1, CLOSED) — derives
   `Concrete.Decls.RefClosed cd` from `WellFormed t` + the stage witnesses.
2. `concretize_produces_dtNameIsKey` — derives `Concrete.Decls.DtNameIsKey cd`
   from the typed-side witness.
3. `sizeBoundOk_entry` (BLOCKED-sizeBoundOk-entry) — derives
   `Concrete.Decls.SizeBoundOk cd`. Required by `layoutMap_ok_of_refClosed`.
4. `layoutMap_ok_of_refClosed` (Layout.lean, F=0) — derives a layout map
   `lm` with `cd.layoutMap = .ok lm`.
5. `function_compile_progress_entry` (BLOCKED-Function-compile-entry) — per
   `.function` pair, derives `Concrete.Function.compile lm f = .ok ...`.
6. `toBytecode_fold_progress` (LowerShared.lean, F=0; migrated 2026-04-30
   from Scratch.lean orphan) — folds (5) over all pairs to close
   `cd.toBytecode = .ok ...`. -/
private theorem Lower.compile_progress_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (_hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (_hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (_hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Concrete.Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (_hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Concrete.Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (_htdDt : Typed.Decls.DtNameIsKey tds)
    (_htdCtorPresent : Typed.Decls.CtorPresent tds) :
    ∃ result, cd.toBytecode = .ok result := by
  -- (2) DtNameIsKey on `cd` (F=0).
  have hDtNameIsKey_cd : Concrete.Decls.DtNameIsKey cd :=
    concretize_produces_dtNameIsKey _htdDt _hconc
  -- (3) SizeBoundOk cd (BLOCKED-sizeBoundOk-entry; see helper docstring).
  have hSizeBoundOk : Concrete.Decls.SizeBoundOk cd :=
    sizeBoundOk_entry _hwf _hts _hconc _hacyclic _hunique hDtNameIsKey_cd _htdDt _htdCtorPresent
  -- (1) RefClosed cd via A.1.
  obtain ⟨decls, hdecls⟩ := _hwf.mkDecls_ok
  have hRefClosed : Concrete.Decls.RefClosed cd :=
    Toplevel.concretize_produces_refClosed_entry _hwf hdecls _hts _hconc
  -- (4) Layout map.
  obtain ⟨lm, hlm⟩ := layoutMap_ok_of_refClosed cd hRefClosed hSizeBoundOk
  -- (5) Per-function `Function.compile` progress (BLOCKED-Function-compile-entry).
  have hfn : ∀ name f, cd.getByKey name = some (.function f) →
      ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms) := by
    intro name f hname
    exact function_compile_progress_entry _hwf _hts _hconc _hunique lm hlm
      _hNameAgrees _hDtNameIsKey _hCtorIsKey _hCtorPresent _htdDt _htdCtorPresent
      name f hname
  -- (6) Glue via `toBytecode_fold_progress`.
  exact toBytecode_fold_progress lm hlm hfn

/-- **Progress half — entry-restricted variant.**

Same conclusion as `Toplevel.compile_progress`, but does NOT take a global
`FullyMonomorphic t` hypothesis. Provable in principle via per-entry
monomorphism propagated through `concretize`'s drained-mono table:
`Source.Function.notPolyEntry` forces every entry's params to be empty,
and `concretize`'s drain monomorphizes the transitive call graph from
entries. This means `concretize`'s output `cd` has every-function-mono on
the reachable subset.

WIRE B (2026-04-28): body now REALLY composes through the entry-bridge
variants `concretize_produces_ctorPresent_entry` and
`Lower.compile_progress_entry`. The remaining open obligations are those two
stubs (each documents its closure path). -/
theorem Toplevel.compile_progress_entry
    (t : Source.Toplevel) (hwf : WellFormed t) :
    ∃ ct decls, t.mkDecls = .ok decls ∧ t.compile = .ok ct := by
  have hwf' := hwf
  obtain ⟨⟨decls, hdecls⟩, _, hmonoTerm, _, _, hNoColl, _⟩ := hwf
  obtain ⟨typedDecls, hts, concDecls, hconc⟩ := hmonoTerm
  have hacyclic := wellFormed_implies_noDirectDatatypeCycles hwf' hts
  have hunique : Typed.Decls.ConcretizeUniqueNames typedDecls := hNoColl typedDecls hts
  have htdna := checkAndSimplify_preserves_nameAgrees hts
  have hNameAgrees := concretize_nameAgrees htdna hconc
  have htdDt := checkAndSimplify_preserves_dtNameIsKey hts
  have hDtIsKey_byKey := concretize_produces_dtNameIsKey htdDt hconc
  have hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Concrete.Declaration.dataType dt) ∈ concDecls.pairs.toList → key = dt.name := by
    intro key dt hmem
    rw [Array.mem_toList_iff] at hmem
    obtain ⟨i, hi, hpi⟩ := Array.mem_iff_getElem.mp hmem
    have hpi_fst : (concDecls.pairs[i]'hi).1 = key := by rw [hpi]
    have hpiIdx := concDecls.pairsIndexed i hi
    rw [hpi_fst] at hpiIdx
    have hget : concDecls.getByKey key = some (.dataType dt) := by
      unfold IndexMap.getByKey
      rw [hpiIdx]
      simp only [bind, Option.bind]
      have hget? : concDecls.pairs[i]? = some (concDecls.pairs[i]'hi) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hi, rfl⟩
      rw [hget?]
      simp [hpi]
    exact hDtIsKey_byKey key dt hget
  have htdCtor := checkAndSimplify_preserves_ctorIsKey hts
  have hCtorIsKey := concretize_produces_ctorIsKey htdCtor hconc
  have htdCtorPresent := checkAndSimplify_preserves_ctorPresent hts
  have hCtorPresent : Concrete.Decls.CtorPresent concDecls :=
    concretize_produces_ctorPresent_entry hwf' hdecls hts
      htdCtorPresent htdDt htdCtor hunique hconc
  obtain ⟨⟨bytecodeRaw, preNameMap⟩, hbc⟩ :=
    Lower.compile_progress_entry hwf' hts hconc hacyclic hunique
      hNameAgrees hDtNameIsKey hCtorIsKey hCtorPresent htdDt htdCtorPresent
  obtain ⟨ct, hct⟩ := Source.Toplevel.compile_ok_of_stages hts hconc hbc
  exact ⟨ct, decls, hdecls, hct⟩

end Aiur

end -- public section
