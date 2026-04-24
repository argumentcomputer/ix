module
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.TypedInvariants
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.ConcretizeSound
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

private theorem TypedCtorPresentP_default :
    TypedCtorPresentP (default : Typed.Decls) := by
  intro k dt c hget _hc
  exfalso
  have hne : (default : Typed.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[k]?).bind _ = none
    have : (default : Typed.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget

private theorem ConcreteCtorPresentP_default :
    ConcreteCtorPresentP (default : Concrete.Decls) := by
  intro k dt c hget _hc
  exfalso
  have hne : (default : Concrete.Decls).getByKey k = none := by
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[k]?).bind _ = none
    have : (default : Concrete.Decls).indices[k]? = none := by
      show ((default : Std.HashMap Global Nat))[k]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [hne] at hget; cases hget



/-! ### Bridges back to pairs-form -/

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

private theorem SourceCtorPresentAux_default :
    SourceCtorPresentAux (({}, default) : MkDeclsAcc) := by
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

/-- The inner ctor fold in `mkDecls_dataTypeStep`. Inserts each ctor at
its pushed key. Preserves `SourceCtorPresentAux` and adds the new keys. -/
private theorem SourceCtorPresentAux_ctor_fold
    (dataType' : DataType) (fullCtors : List Constructor)
    (hFullCtors : fullCtors = dataType'.constructors) :
    ∀ (ctors : List Constructor) (init result : MkDeclsAcc),
      SourceCtorPresentAux init →
      init.2.getByKey dataType'.name = some (.dataType dataType') →
      (∀ c ∈ ctors, c ∈ fullCtors) →
      (∀ c ∈ fullCtors, c ∉ ctors →
        ∃ cc, init.2.getByKey (dataType'.name.pushNamespace c.nameHead) =
          some (.constructor dataType' cc)) →
      ctors.foldlM
        (fun (acc : MkDeclsAcc) ctor =>
          let ctorName := dataType'.name.pushNamespace ctor.nameHead
          if acc.1.contains ctorName then
            (Except.error (CheckError.duplicatedDefinition ctorName) :
              Except CheckError MkDeclsAcc)
          else
            Except.ok (acc.1.insert ctorName,
                       acc.2.insert ctorName (.constructor dataType' ctor)))
        init = .ok result →
      SourceCtorPresentAux result ∧
      result.2.getByKey dataType'.name = some (.dataType dataType') ∧
      (∀ c ∈ fullCtors,
        ∃ cc, result.2.getByKey (dataType'.name.pushNamespace c.nameHead) =
          some (.constructor dataType' cc)) := by
  intro ctors
  induction ctors with
  | nil =>
    intro init result hAux hDt _hSubset hPre hfold
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    refine ⟨hAux, hDt, ?_⟩
    intro c hc
    exact hPre c hc (by intro h; cases h)
  | cons c rest ih =>
    intro init result hAux hDt hSubset hPre hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · exact absurd hfold (by intro h; cases h)
    rename_i acc' hstep
    split at hstep
    · exact absurd hstep (by intro h; cases h)
    rename_i hNotIn
    simp only [Except.ok.injEq] at hstep
    subst hstep
    have hcFull : c ∈ fullCtors := hSubset c (List.Mem.head _)
    have hAuxNew : SourceCtorPresentAux
        (init.1.insert (dataType'.name.pushNamespace c.nameHead),
         init.2.insert (dataType'.name.pushNamespace c.nameHead)
           (.constructor dataType' c)) := by
      refine ⟨?_, ?_⟩
      · intro k dt cc' hget hcc'
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead == k) = true
        · have hkEq : dataType'.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dataType'.name.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          obtain ⟨cc, hccget⟩ := hAux.1 k dt cc' hget hcc'
          by_cases hkn2 : (dataType'.name.pushNamespace c.nameHead ==
                            dt.name.pushNamespace cc'.nameHead) = true
          · -- Collision impossible: if pushed keys match, the witness
            -- `hccget` was in init, so `init.1` contains that pushed key,
            -- but `hNotIn` says the new pushed key is not in `init.1`.
            exfalso
            have hkEq2 : dataType'.name.pushNamespace c.nameHead =
                          dt.name.pushNamespace cc'.nameHead :=
              LawfulBEq.eq_of_beq hkn2
            have hccKey : init.1.contains (dt.name.pushNamespace cc'.nameHead) = true :=
              hAux.2 _ _ hccget
            rw [← hkEq2] at hccKey
            rw [hccKey] at hNotIn
            exact absurd hNotIn (by simp)
          · have hne2 : (dataType'.name.pushNamespace c.nameHead ==
                          dt.name.pushNamespace cc'.nameHead) = false :=
              Bool.not_eq_true _ |>.mp hkn2
            refine ⟨cc, ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
            exact hccget
      · intro k v hget
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead == k) = true
        · have hkEq : dataType'.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [Std.HashSet.contains_insert]; simp
        · have hne : (dataType'.name.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          rw [Std.HashSet.contains_insert]
          have := hAux.2 k v hget; rw [this]; simp
    have hDtNew : (init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c)).getByKey dataType'.name =
        some (Source.Declaration.dataType dataType') := by
      have hkNe : (dataType'.name.pushNamespace c.nameHead == dataType'.name) = false := by
        cases hh : (dataType'.name.pushNamespace c.nameHead == dataType'.name) with
        | false => rfl
        | true =>
          exfalso
          have heq := LawfulBEq.eq_of_beq hh
          have hInInit : init.1.contains dataType'.name = true := hAux.2 _ _ hDt
          have : init.1.contains (dataType'.name.pushNamespace c.nameHead) = true := by
            rw [heq]; exact hInInit
          rw [this] at hNotIn
          exact absurd hNotIn (by simp)
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hkNe]
      exact hDt
    have hSubsetNew : ∀ c' ∈ rest, c' ∈ fullCtors := by
      intro c' hc'mem
      exact hSubset c' (List.Mem.tail _ hc'mem)
    have hPreNew : ∀ c' ∈ fullCtors, c' ∉ rest →
        ∃ cc, (init.2.insert (dataType'.name.pushNamespace c.nameHead)
          (Source.Declaration.constructor dataType' c)).getByKey
              (dataType'.name.pushNamespace c'.nameHead) =
            some (.constructor dataType' cc) := by
      intro c' hc'full hc'notrest
      by_cases hcc' : c' = c
      · refine ⟨c, ?_⟩
        rw [hcc']
        exact IndexMap.getByKey_insert_self _ _ _
      · have hc'notall : c' ∉ (c :: rest) := by
          intro hmem
          rcases List.mem_cons.mp hmem with heq | htail
          · exact hcc' heq
          · exact hc'notrest htail
        obtain ⟨cc, hccget⟩ := hPre c' hc'full hc'notall
        by_cases hkn : (dataType'.name.pushNamespace c.nameHead ==
                         dataType'.name.pushNamespace c'.nameHead) = true
        · refine ⟨c, ?_⟩
          have hkEq := LawfulBEq.eq_of_beq hkn
          rw [← hkEq]
          exact IndexMap.getByKey_insert_self _ _ _
        · have hne : (dataType'.name.pushNamespace c.nameHead ==
                        dataType'.name.pushNamespace c'.nameHead) = false :=
            Bool.not_eq_true _ |>.mp hkn
          refine ⟨cc, ?_⟩
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hccget
    exact ih _ _ hAuxNew hDtNew hSubsetNew hPreNew hfold

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

private theorem TypedDecls_DtNameIsKey_pairs_of_gen
    {d : Typed.Decls}
    (hP : ∀ k dt, d.getByKey k = some (.dataType dt) → k = dt.name) :
    TypedDecls_DtNameIsKey_pairs d := by
  intro key dt hmem
  exact hP key dt (IndexMap.getByKey_of_mem_pairs _ _ _ hmem)

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

private theorem rewriteC_nameHead (mono : MonoMap) (c : Constructor) :
    (rewriteC mono c).nameHead = c.nameHead := rfl

private theorem rewriteDt_name (mono : MonoMap) (dt : DataType) :
    (rewriteDt mono dt).name = dt.name := rfl

private theorem rewriteDt_constructors (mono : MonoMap) (dt : DataType) :
    (rewriteDt mono dt).constructors =
      dt.constructors.map (rewriteC mono) := rfl

/-- `Global.pushNamespace` is injective in its string argument (for any fixed
prefix). -/
private theorem pushNamespace_right_inj {g : Global} {s t : String}
    (h : g.pushNamespace s = g.pushNamespace t) : s = t := by
  have h' : g.toName.mkStr s = g.toName.mkStr t := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g.toName s = Lean.Name.str g.toName t := h'
  injection h''

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

/-- dt-trace: every `.dataType dt_new` at `k` in fromSource originated from a
source `.dataType dtSrc` at `k` with empty params, and `dt_new = rewriteDt dtSrc`. -/
private theorem fromSource_dt_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dt_new : DataType)
    (hget : (fromSource typedDecls mono).getByKey k = some (.dataType dt_new)) :
    ∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
      dtSrc.params.isEmpty = true ∧ dt_new = rewriteDt mono dtSrc := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_new, acc.getByKey k = some (.dataType dt_new) →
      ∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧ dt_new = rewriteDt mono dtSrc
  suffices h : P (fromSource typedDecls mono) from h k dt_new hget
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_new hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  · intro i acc hP k dt_new hget
    have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    unfold fromSourceStep at hget
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
          exact hP k dt_new hget
      · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget
    | dataType dtSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          refine ⟨dtSrc, hp_mem, hparams, ?_⟩
          rw [← hget]
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget
    | constructor dtSrc cSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new hget

/-- ctor-trace: every `.constructor dt_new c_new` at `k` in fromSource
originated from a source `.constructor dtSrc cSrc` at `k` with empty
params, and `dt_new = rewriteDt dtSrc`, `c_new = rewriteC cSrc`. -/
private theorem fromSource_ctor_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dt_new : DataType) (c_new : Constructor)
    (hget : (fromSource typedDecls mono).getByKey k =
      some (.constructor dt_new c_new)) :
    ∃ dtSrc cSrc,
      (k, Typed.Declaration.constructor dtSrc cSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧
        dt_new = rewriteDt mono dtSrc ∧ c_new = rewriteC mono cSrc := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_new c_new, acc.getByKey k = some (.constructor dt_new c_new) →
      ∃ dtSrc cSrc,
        (k, Typed.Declaration.constructor dtSrc cSrc) ∈ typedDecls.pairs.toList ∧
          dtSrc.params.isEmpty = true ∧
          dt_new = rewriteDt mono dtSrc ∧ c_new = rewriteC mono cSrc
  suffices h : P (fromSource typedDecls mono) from h k dt_new c_new hget
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_new c_new hget
    exfalso
    have hne : (default : Typed.Decls).getByKey k = none := by
      unfold IndexMap.getByKey
      show ((default : Typed.Decls).indices[k]?).bind _ = none
      have : (default : Typed.Decls).indices[k]? = none := by
        show ((default : Std.HashMap Global Nat))[k]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  · intro i acc hP k dt_new c_new hget
    have hp_mem : typedDecls.pairs[i.val]'i.isLt ∈ typedDecls.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    unfold fromSourceStep at hget
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
          exact hP k dt_new c_new hget
      · have hparams_false : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget
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
          exact hP k dt_new c_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget
    | constructor dtSrc cSrc =>
      by_cases hparams : dtSrc.params.isEmpty = true
      · simp only [hparams, if_true] at hget
        by_cases hkn : (key == k) = true
        · have hkEq : key = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at hget
          refine ⟨dtSrc, cSrc, hp_mem, hparams, ?_, ?_⟩
          · rw [← hget.1]
          · rw [← hget.2]
        · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP k dt_new c_new hget
      · have hparams_false : dtSrc.params.isEmpty = false := Bool.not_eq_true _ |>.mp hparams
        simp only [hparams_false] at hget
        exact hP k dt_new c_new hget

/-- Forward lemma: every source `.constructor dtSrc cSrc` with empty params
has its rewrite present in `fromSource` at the same key. -/
private theorem fromSource_ctor_forward (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dtSrc : DataType) (cSrc : Constructor)
    (hmem : (k, Typed.Declaration.constructor dtSrc cSrc) ∈
      typedDecls.pairs.toList)
    (hparams : dtSrc.params.isEmpty = true) :
    (fromSource typedDecls mono).getByKey k =
      some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := by
  have hex : (fromSource typedDecls mono).getByKey k =
      some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := by
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
    rw [Array.length_toList] at hidx_lt
    have hpair_idx : typedDecls.pairs[idx]'hidx_lt =
        (k, Typed.Declaration.constructor dtSrc cSrc) := by
      rw [← hidx_eq, Array.getElem_toList]
    let Q : Nat → Typed.Decls → Prop := fun i acc =>
      idx < i → acc.getByKey k =
        some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc))
    suffices h : Q typedDecls.pairs.size (fromSource typedDecls mono) by
      apply h
      exact hidx_lt
    apply Array.foldl_induction
      (motive := fun (i : Nat) (acc : Typed.Decls) => Q i acc)
    · intro hlt
      exact absurd hlt (Nat.not_lt_zero _)
    · intro i acc hQ hlt
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt_i | heq
      · have hacc : acc.getByKey k =
            some (.constructor (rewriteDt mono dtSrc) (rewriteC mono cSrc)) := hQ hlt_i
        unfold fromSourceStep
        generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p
        obtain ⟨key', d'⟩ := p
        simp only
        have hkey_ne : key' ≠ k := by
          intro hEq
          subst hEq
          have h1 : typedDecls.indices[(typedDecls.pairs[i.val]'i.isLt).1]? = some i.val :=
            typedDecls.pairsIndexed i.val i.isLt
          have h2 : typedDecls.indices[(typedDecls.pairs[idx]'hidx_lt).1]? = some idx :=
            typedDecls.pairsIndexed idx hidx_lt
          rw [hpsh] at h1
          rw [hpair_idx] at h2
          simp only at h1 h2
          rw [h1] at h2
          exact absurd (Option.some.inj h2).symm (Nat.ne_of_lt hlt_i)
        have hne : (key' == k) = false := by
          by_cases h : (key' == k) = true
          · exact absurd (LawfulBEq.eq_of_beq h) hkey_ne
          · exact Bool.not_eq_true _ |>.mp h
        cases d' with
        | function f =>
          by_cases hf : f.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
        | dataType dt' =>
          by_cases hf : dt'.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
        | constructor dt' c' =>
          by_cases hf : dt'.params.isEmpty = true
          · simp only [hf, if_true]
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
            exact hacc
          · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
            simp only [hff]
            exact hacc
      · subst heq
        have hpair_idx' : typedDecls.pairs[i] =
            (k, Typed.Declaration.constructor dtSrc cSrc) := hpair_idx
        show (fromSourceStep typedDecls mono acc (typedDecls.pairs[i])).getByKey k = _
        rw [hpair_idx']
        unfold fromSourceStep
        simp only [hparams, if_true]
        exact IndexMap.getByKey_insert_self _ k _
  exact hex

/-- Forward dt lemma: every source `.dataType dtSrc` with empty params has
its rewrite at the same key in `fromSource`. -/
private theorem fromSource_dt_forward (typedDecls : Typed.Decls) (mono : MonoMap)
    (k : Global) (dtSrc : DataType)
    (hmem : (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList)
    (hparams : dtSrc.params.isEmpty = true) :
    (fromSource typedDecls mono).getByKey k =
      some (.dataType (rewriteDt mono dtSrc)) := by
  obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
  rw [Array.length_toList] at hidx_lt
  have hpair_idx : typedDecls.pairs[idx]'hidx_lt =
      (k, Typed.Declaration.dataType dtSrc) := by
    rw [← hidx_eq, Array.getElem_toList]
  let Q : Nat → Typed.Decls → Prop := fun i acc =>
    idx < i → acc.getByKey k = some (.dataType (rewriteDt mono dtSrc))
  suffices h : Q typedDecls.pairs.size (fromSource typedDecls mono) by
    apply h; exact hidx_lt
  apply Array.foldl_induction
    (motive := fun (i : Nat) (acc : Typed.Decls) => Q i acc)
  · intro hlt
    exact absurd hlt (Nat.not_lt_zero _)
  · intro i acc hQ hlt
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt_i | heq
    · have hacc : acc.getByKey k = some (.dataType (rewriteDt mono dtSrc)) := hQ hlt_i
      unfold fromSourceStep
      generalize hpsh : typedDecls.pairs[i.val]'i.isLt = p
      obtain ⟨key', d'⟩ := p
      simp only
      have hkey_ne : key' ≠ k := by
        intro hEq
        subst hEq
        have h1 : typedDecls.indices[(typedDecls.pairs[i.val]'i.isLt).1]? = some i.val :=
          typedDecls.pairsIndexed i.val i.isLt
        have h2 : typedDecls.indices[(typedDecls.pairs[idx]'hidx_lt).1]? = some idx :=
          typedDecls.pairsIndexed idx hidx_lt
        rw [hpsh] at h1
        rw [hpair_idx] at h2
        simp only at h1 h2
        rw [h1] at h2
        exact absurd (Option.some.inj h2).symm (Nat.ne_of_lt hlt_i)
      have hne : (key' == k) = false := by
        by_cases h : (key' == k) = true
        · exact absurd (LawfulBEq.eq_of_beq h) hkey_ne
        · exact Bool.not_eq_true _ |>.mp h
      cases d' with
      | function f =>
        by_cases hf : f.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
      | dataType dt' =>
        by_cases hf : dt'.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
      | constructor dt' c' =>
        by_cases hf : dt'.params.isEmpty = true
        · simp only [hf, if_true]
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
          exact hacc
        · have hff : dt'.params.isEmpty = false := Bool.not_eq_true _ |>.mp hf
          simp only [hff]; exact hacc
    · subst heq
      have hpair_idx' : typedDecls.pairs[i] =
          (k, Typed.Declaration.dataType dtSrc) := hpair_idx
      show (fromSourceStep typedDecls mono acc (typedDecls.pairs[i])).getByKey k = _
      rw [hpair_idx']
      unfold fromSourceStep
      simp only [hparams, if_true]
      exact IndexMap.getByKey_insert_self _ k _

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

/-- Phase-2 trace: a `.dataType dt_mid` at `k` in `phase2Acc` either came from
fromSource (traces back via `fromSource_dt_trace`) or from `newDataTypes`. -/
private theorem phase2Acc_dt_trace (typedDecls : Typed.Decls) (mono : MonoMap)
    (newDataTypes : Array DataType)
    (k : Global) (dt_mid : DataType)
    (hget : (phase2Acc typedDecls mono newDataTypes).getByKey k =
      some (.dataType dt_mid)) :
    (∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
        dtSrc.params.isEmpty = true ∧ dt_mid = rewriteDt mono dtSrc) ∨
    (∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧
        dt_mid = rewriteDt mono dt_orig) := by
  let P : Typed.Decls → Prop := fun acc =>
    ∀ k dt_mid, acc.getByKey k = some (.dataType dt_mid) →
      (∃ dtSrc, (k, Typed.Declaration.dataType dtSrc) ∈ typedDecls.pairs.toList ∧
          dtSrc.params.isEmpty = true ∧ dt_mid = rewriteDt mono dtSrc) ∨
      (∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧
          dt_mid = rewriteDt mono dt_orig)
  suffices h : P (phase2Acc typedDecls mono newDataTypes) from h k dt_mid hget
  unfold phase2Acc
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => P acc)
  · intro k dt_mid hget
    exact Or.inl (fromSource_dt_trace typedDecls mono k dt_mid hget)
  · intro i acc hP k dt_mid hget
    have hdt_mem : newDataTypes[i.val]'i.isLt ∈ newDataTypes := Array.getElem_mem _
    have hCtorFold : ∀ (ctors : List Constructor) (newDt : DataType)
        (dt_name : Global) (init : Typed.Decls),
        P init →
        P (ctors.foldl
          (fun acc'' c =>
            acc''.insert (dt_name.pushNamespace c.nameHead)
              (.constructor newDt c))
          init) := by
      intro ctors newDt dt_name
      induction ctors with
      | nil => intro init hP'; exact hP'
      | cons hd tl ih =>
        intro init hPinit
        simp only [List.foldl_cons]
        apply ih
        intro k dt_mid hget
        by_cases hkn : (dt_name.pushNamespace hd.nameHead == k) = true
        · have hkEq : dt_name.pushNamespace hd.nameHead = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (dt_name.pushNamespace hd.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hPinit k dt_mid hget
    have hPouter : P (acc.insert (newDataTypes[i.val]'i.isLt).name
        (.dataType (rewriteDt mono (newDataTypes[i.val]'i.isLt)))) := by
      intro k' dt_mid' hget'
      by_cases hkn : ((newDataTypes[i.val]'i.isLt).name == k') = true
      · have hkEq : (newDataTypes[i.val]'i.isLt).name = k' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget'
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget'
        refine Or.inr ⟨newDataTypes[i.val]'i.isLt, hdt_mem, rfl, ?_⟩
        rw [← hget']
      · have hne : ((newDataTypes[i.val]'i.isLt).name == k') = false :=
          Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget'
        exact hP k' dt_mid' hget'
    exact hCtorFold _ _ _ _ hPouter k dt_mid hget

/-- Helper: membership in `dt.constructors.map (f)` — for every `c ∈ mapped`,
there's a `c'` in `dt.constructors` with `c = f c'`. -/
private theorem mem_map_ctors_iff {α β : Type} (L : List α) (f : α → β) (b : β) :
    b ∈ L.map f ↔ ∃ a ∈ L, f a = b := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, ih]
    constructor
    · rintro (heq | ⟨a, hmem, hfa⟩)
      · exact ⟨hd, Or.inl rfl, heq.symm⟩
      · exact ⟨a, Or.inr hmem, hfa⟩
    · rintro ⟨a, (heq | hmem), hfa⟩
      · subst heq; exact Or.inl hfa.symm
      · exact Or.inr ⟨a, hmem, hfa⟩

/-! ### Phase-1 axiom (pass-through).

Discharge path: processed/remaining split on `typedDecls.pairs.toList`,
parallel to `concretizeBuild_ctorIsKey` in this file. Key fact: every
source entry rewrites to an entry at the same key with structurally-matching
`dt` payload.
-/

private theorem fromSource_preserves_ctorPresent
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := typedDecls.pairs.foldl
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
      default
    TypedCtorPresentP fromSource := by
  intro emptySubst fS
  -- The inline `fS` is definitionally equal to `fromSource typedDecls mono`.
  show TypedCtorPresentP (fromSource typedDecls mono)
  intro k dt_new c hget hc
  -- Trace `dt_new` back to a source dt.
  obtain ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ :=
    fromSource_dt_trace typedDecls mono k dt_new hget
  have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
  have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
  have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
  rw [rewriteDt_constructors] at hc_new
  rw [List.mem_map] at hc_new
  obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
  have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
  obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
  have hcc_mem : (dtSrc.name.pushNamespace c'.nameHead,
      Typed.Declaration.constructor dtSrc cc) ∈ typedDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hcc_get
  have hfwd := fromSource_ctor_forward typedDecls mono
    (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_mem hparams
  refine ⟨rewriteC mono cc, ?_⟩
  rw [hdt_eq, rewriteDt_name, hhead]
  exact hfwd

/-! ### Phase-2 lemma: `withNewDts` preserves CtorPresent.

For each `dt ∈ newDataTypes`:
* inserts `.dataType rewrittenDt` at `dt.name`
* for each `c ∈ rewrittenDt.constructors`, inserts `.constructor rewrittenDt c`
  at `dt.name.pushNamespace c.nameHead`.

The inner ctor-fold inserts all witnesses for the dt-name key's dt. The
outer fold threads through. Discharge via `phase2_freshness_discharge` below.
-/

/-- `Global.pushNamespace` injective in the prefix argument (other side). -/
private theorem pushNamespace_left_inj {g₁ g₂ : Global} {s : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace s) : g₁ = g₂ := by
  have h' : g₁.toName.mkStr s = g₂.toName.mkStr s := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g₁.toName s = Lean.Name.str g₂.toName s := h'
  have : g₁.toName = g₂.toName := by injection h''
  cases g₁; cases g₂; simp_all

/-- If pushed keys are equal, both prefix globals and the suffix strings match. -/
private theorem pushNamespace_inj_both {g₁ g₂ : Global} {s t : String}
    (h : g₁.pushNamespace s = g₂.pushNamespace t) : g₁ = g₂ ∧ s = t := by
  have h' : g₁.toName.mkStr s = g₂.toName.mkStr t := by
    have := h
    unfold Global.pushNamespace at this
    exact Global.mk.inj this
  have h'' : Lean.Name.str g₁.toName s = Lean.Name.str g₂.toName t := h'
  refine ⟨?_, ?_⟩
  · have hn : g₁.toName = g₂.toName := by injection h''
    cases g₁; cases g₂; simp_all
  · injection h''

/-- `Name.str n s ≠ n`: a name is never equal to its own string-extension.
Proof by structural induction on n. -/
private theorem Name_str_ne_self : ∀ (n : Lean.Name) (s : String),
    Lean.Name.str n s ≠ n
  | .anonymous, _, h => by cases h
  | .str n' s', s, h => by
    -- h : str (str n' s') s = str n' s'
    injection h with hn hs
    -- hn : str n' s' = n'.   hs : s = s'.
    exact Name_str_ne_self n' s' hn
  | .num _ _, _, h => by cases h

/-- `pushNamespace` is never a prefix of itself: `g ≠ g.pushNamespace s`. -/
private theorem ne_pushNamespace_self (g : Global) (s : String) :
    g ≠ g.pushNamespace s := by
  intro h
  have h' : g.toName = g.toName.mkStr s := Global.mk.inj h
  have h'' : Lean.Name.str g.toName s = g.toName := h'.symm
  exact Name_str_ne_self g.toName s h''

/-- Rest-fold preserves an entry at `dt_name.pushNamespace ch` when `ch` isn't in
`rest.map (·.nameHead)`. -/
private theorem restFold_preserves_unvisited
    (dt_name : Global) (newDt : DataType) (rest : List Constructor)
    (ch : String) (hch_nin : ch ∉ rest.map (·.nameHead))
    (acc : Typed.Decls) (c₀ : Constructor)
    (hc₀ : acc.getByKey (dt_name.pushNamespace ch) = some (.constructor newDt c₀)) :
    (rest.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc).getByKey (dt_name.pushNamespace ch) = some (.constructor newDt c₀) := by
  induction rest generalizing acc with
  | nil => simp [hc₀]
  | cons c' rest' ih =>
    simp only [List.foldl_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at hch_nin
    have ⟨hne_head, hch_nin_rest⟩ := hch_nin
    apply ih hch_nin_rest
    have hne : (dt_name.pushNamespace c'.nameHead == dt_name.pushNamespace ch) = false := by
      cases hbeq : (dt_name.pushNamespace c'.nameHead == dt_name.pushNamespace ch) with
      | false => rfl
      | true =>
        have heq := LawfulBEq.eq_of_beq hbeq
        have hs_eq := (pushNamespace_inj_both heq).2
        exact absurd hs_eq.symm hne_head
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    exact hc₀

/-- Inner ctor-fold helper.

Given `acc₀` satisfying:
- Partial CtorPresent: all `.dataType d'' at k''` entries with `d''.name ≠ dt_name` already
  have their witnesses (the newDt entry at `dt_name` does NOT need witnesses yet).
- DtNameIsKey.
- newDt is pinned at `dt_name`.

Freshness: `dt_name.pushNamespace ch` (for `ch ∈ ctors.map (·.nameHead)`) distinct from
witness keys of all OTHER dts in acc₀.

After folding inserts of `.constructor newDt c` at `dt_name.pushNamespace c.nameHead`, we get:
- (a') every `ch ∈ ctors.map (·.nameHead)` has a ctor-entry at `dt_name.pushNamespace ch`.
- (b) non-newDt dt's witnesses still present.
- (c) DtNameIsKey preserved.
- (d) newDt still at `dt_name`.
- (e) Data-type trace: every `.dataType` entry in result was in `acc₀`.
-/
private theorem innerCtorFold_preserves
    (dt_name : Global) (newDt : DataType)
    (ctors : List Constructor)
    (acc₀ : Typed.Decls)
    (hAcc₀_partial : ∀ k'' d'' c'',
      acc₀.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
      d''.name ≠ dt_name →
      ∃ cc, acc₀.getByKey (d''.name.pushNamespace c''.nameHead) =
        some (.constructor d'' cc))
    (hAcc₀Dt : TypedDtNameIsKeyP acc₀)
    (hAcc₀_newDt : acc₀.getByKey dt_name = some (.dataType newDt))
    (hfreshPush : ∀ k d'' c'' ch,
      acc₀.getByKey k = some (.dataType d'') → c'' ∈ d''.constructors →
      ch ∈ ctors.map (·.nameHead) →
      d''.name ≠ dt_name → d''.name.pushNamespace c''.nameHead ≠
        dt_name.pushNamespace ch) :
    (∀ ch ∈ ctors.map (·.nameHead), ∃ cc,
      (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey (dt_name.pushNamespace ch) =
        some (.constructor newDt cc)) ∧
    (∀ k'' d'' c'',
      (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
      d''.name ≠ dt_name →
      ∃ cc, (ctors.foldl
        (fun acc'' c =>
          acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
        acc₀).getByKey (d''.name.pushNamespace c''.nameHead) =
        some (.constructor d'' cc)) ∧
    TypedDtNameIsKeyP (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀) ∧
    (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀).getByKey dt_name = some (.dataType newDt) ∧
    (∀ k d'', (ctors.foldl
      (fun acc'' c =>
        acc''.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c))
      acc₀).getByKey k = some (.dataType d'') →
      acc₀.getByKey k = some (.dataType d'')) := by
  induction ctors generalizing acc₀ with
  | nil =>
    refine ⟨?_, hAcc₀_partial, hAcc₀Dt, hAcc₀_newDt, fun _ _ hget => hget⟩
    intro ch hch
    simp only [List.map_nil] at hch
    cases hch
  | cons c rest ih =>
    simp only [List.foldl_cons]
    let acc₁ : Typed.Decls :=
      acc₀.insert (dt_name.pushNamespace c.nameHead) (.constructor newDt c)
    have hne_dt_name : (dt_name.pushNamespace c.nameHead == dt_name) = false := by
      cases hbeq : (dt_name.pushNamespace c.nameHead == dt_name) with
      | false => rfl
      | true =>
        exact absurd (LawfulBEq.eq_of_beq hbeq).symm (ne_pushNamespace_self dt_name c.nameHead)
    -- newDt still at dt_name in acc₁.
    have hAcc₁_newDt : acc₁.getByKey dt_name = some (.dataType newDt) := by
      simp only [acc₁]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_dt_name]
      exact hAcc₀_newDt
    -- DtNameIsKey on acc₁.
    have hAcc₁Dt : TypedDtNameIsKeyP acc₁ := by
      intro k d'' hget
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hAcc₀Dt k d'' hget
    -- Partial CtorPresent on acc₁ (non-newDt witnesses).
    have hAcc₁_partial : ∀ k'' d'' c'',
        acc₁.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
        d''.name ≠ dt_name →
        ∃ cc, acc₁.getByKey (d''.name.pushNamespace c''.nameHead) =
          some (.constructor d'' cc) := by
      intro k'' d'' c'' hget hc'' hd_ne
      have hcName : dt_name.pushNamespace c.nameHead ≠ k'' := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne_k : (dt_name.pushNamespace c.nameHead == k'') = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k'') with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_k] at hget
      obtain ⟨cc, hcc⟩ := hAcc₀_partial k'' d'' c'' hget hc'' hd_ne
      have hch_mem : c.nameHead ∈ (c :: rest).map (·.nameHead) := List.mem_cons_self
      have hwit_ne := hfreshPush k'' d'' c'' c.nameHead hget hc'' hch_mem hd_ne
      have hne_wit : (dt_name.pushNamespace c.nameHead ==
          d''.name.pushNamespace c''.nameHead) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead ==
            d''.name.pushNamespace c''.nameHead) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq).symm hwit_ne
      refine ⟨cc, ?_⟩
      simp only [acc₁]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_wit]
      exact hcc
    -- Freshness on rest for acc₁.
    have hfreshPush₁ : ∀ k d'' c'' ch,
        acc₁.getByKey k = some (.dataType d'') → c'' ∈ d''.constructors →
        ch ∈ rest.map (·.nameHead) →
        d''.name ≠ dt_name →
        d''.name.pushNamespace c''.nameHead ≠ dt_name.pushNamespace ch := by
      intro k d'' c'' ch hget hc'' hch hd_ne
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at hget
        rw [← hkeq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      have hch' : ch ∈ (c :: rest).map (·.nameHead) := by
        simp only [List.map_cons, List.mem_cons]; exact Or.inr hch
      exact hfreshPush k d'' c'' ch hget hc'' hch' hd_ne
    -- Apply IH.
    have hfinal := ih acc₁ hAcc₁_partial hAcc₁Dt hAcc₁_newDt hfreshPush₁
    -- Massage to get result-level (a').
    refine ⟨?_, hfinal.2.1, hfinal.2.2.1, hfinal.2.2.2.1, ?_⟩
    · -- (a'): for ch ∈ (c :: rest).map (·.nameHead), witness in result.
      intro ch hch
      simp only [List.map_cons, List.mem_cons] at hch
      rcases hch with heq | hin
      · -- ch = c.nameHead: witness is the entry inserted at acc₁, which survives
        -- rest's inserts only if c.nameHead ∉ rest.map (·.nameHead). Otherwise it's
        -- overwritten by later insert (still a valid witness .constructor newDt _).
        subst heq
        -- Split: is c.nameHead in rest.map (·.nameHead)?
        by_cases hin_rest : c.nameHead ∈ rest.map (·.nameHead)
        · -- Yes: rest's later insert at the same pushed key provides a witness.
          -- That witness is `.constructor newDt c_later` for some c_later in rest.
          -- Use hfinal.1 applied to hin_rest.
          exact hfinal.1 c.nameHead hin_rest
        · -- No: acc₁'s witness is preserved by rest-fold.
          -- Prove via a side lemma: rest-fold preserves entries at keys NOT in its pushed set.
          refine ⟨c, ?_⟩
          -- Goal: rest-fold's result has `.constructor newDt c` at `dt_name.pushNamespace c.nameHead`.
          -- We know acc₁.getByKey (dt_name.pushNamespace c.nameHead) = some (.constructor newDt c)
          -- and rest-fold only inserts at `dt_name.pushNamespace c'.nameHead` for c' ∈ rest.
          -- Those keys differ from c.nameHead's pushed key (by pushNamespace_inj_both).
          have hacc₁_ce : acc₁.getByKey (dt_name.pushNamespace c.nameHead) =
              some (.constructor newDt c) := by
            simp only [acc₁]; rw [IndexMap.getByKey_insert_self]
          -- Use a local lemma proved by induction on rest.
          exact restFold_preserves_unvisited dt_name newDt rest c.nameHead hin_rest acc₁ c hacc₁_ce
      · -- ch ∈ rest.map (·.nameHead): use hfinal.1.
        exact hfinal.1 ch hin
    · -- (e): trace through the rest-fold and then the c-insert.
      intro k d'' hget
      have h_acc₁ := hfinal.2.2.2.2 k d'' hget
      have hcName : dt_name.pushNamespace c.nameHead ≠ k := by
        intro hkeq
        simp only [acc₁] at h_acc₁
        rw [← hkeq] at h_acc₁
        rw [IndexMap.getByKey_insert_self] at h_acc₁
        cases h_acc₁
      have hne : (dt_name.pushNamespace c.nameHead == k) = false := by
        cases hbeq : (dt_name.pushNamespace c.nameHead == k) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hcName
      simp only [acc₁] at h_acc₁
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at h_acc₁
      exact h_acc₁

private theorem withNewDts_preserves_ctorPresent
    (init : Typed.Decls) (mono : MonoMap) (newDataTypes : Array DataType)
    (hInit : TypedCtorPresentP init)
    (hInitDt : TypedDtNameIsKeyP init)
    (hFresh : ∀ dt ∈ newDataTypes, ∀ k dt' c,
      init.getByKey k = some (.dataType dt') → c ∈ dt'.constructors →
      -- The new dt's name is distinct from existing ctor witness keys.
      dt.name ≠ dt'.name.pushNamespace c.nameHead)
    (hMutualFresh : ∀ dt ∈ newDataTypes, ∀ dt' ∈ newDataTypes,
      ∀ ch ∈ dt'.constructors.map (·.nameHead),
      dt.name ≠ dt'.name.pushNamespace ch) :
    let emptySubst : Global → Option Typ := fun _ => none
    TypedCtorPresentP (newDataTypes.foldl
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
  intro emptySubst
  -- Invariant Q: CtorPresent + DtNameIsKey + every .dataType entry either
  -- traces to `init` (same key+payload) or to some `dt_orig ∈ newDataTypes`
  -- with payload `rewriteDt mono dt_orig` at key `dt_orig.name`.
  let Q : Typed.Decls → Prop := fun acc =>
    TypedCtorPresentP acc ∧ TypedDtNameIsKeyP acc ∧
    ∀ k d, acc.getByKey k = some (.dataType d) →
      init.getByKey k = some (.dataType d) ∨
      ∃ dt_orig ∈ newDataTypes, k = dt_orig.name ∧ d = rewriteDt mono dt_orig
  suffices h : Q (newDataTypes.foldl
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
      init) from h.1
  apply Array.foldl_induction (motive := fun (_ : Nat) (acc : Typed.Decls) => Q acc)
  · exact ⟨hInit, hInitDt, fun k d hget => Or.inl hget⟩
  · intro i acc hQ
    -- Setup.
    generalize hdt_eq : newDataTypes[i.val]'i.isLt = dt_i
    have hdt_mem : dt_i ∈ newDataTypes := by rw [← hdt_eq]; exact Array.getElem_mem _
    let rewrittenCtors := dt_i.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt_i with constructors := rewrittenCtors }
    have hnewDt_name : newDt.name = dt_i.name := rfl
    have hrewrittenHeads : rewrittenCtors.map (·.nameHead) =
        dt_i.constructors.map (·.nameHead) := by
      simp only [rewrittenCtors, List.map_map]
      apply List.map_congr_left
      intros; rfl
    -- Outer insert: acc₀ := acc.insert dt_i.name (.dataType newDt).
    let acc₀ : Typed.Decls := acc.insert dt_i.name (.dataType newDt)
    have hacc₀_newDt : acc₀.getByKey dt_i.name = some (.dataType newDt) := by
      simp only [acc₀]; rw [IndexMap.getByKey_insert_self]
    -- Partial CtorPresent on acc₀ (skip newDt at dt_i.name).
    -- For any .dataType d' at k' in acc₀ with d'.name ≠ dt_i.name: witness exists in acc₀.
    have hAcc₀_partial : ∀ k' d' c',
        acc₀.getByKey k' = some (.dataType d') → c' ∈ d'.constructors →
        d'.name ≠ dt_i.name →
        ∃ cc, acc₀.getByKey (d'.name.pushNamespace c'.nameHead) =
          some (.constructor d' cc) := by
      intro k' d' c' hget hc' hd_ne
      -- If k' = dt_i.name, would have d' = newDt with d'.name = dt_i.name, contradicting hd_ne.
      have hk_ne : (dt_i.name == k') = false := by
        cases hbeq : (dt_i.name == k') with
        | false => rfl
        | true =>
          have hkeq := LawfulBEq.eq_of_beq hbeq
          rw [← hkeq] at hget
          simp only [acc₀] at hget
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
          exact absurd (hget.symm ▸ hnewDt_name) hd_ne
      simp only [acc₀] at hget
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hk_ne] at hget
      obtain ⟨cc, hccget⟩ := hQ.1 k' d' c' hget hc'
      -- Witness key ≠ dt_i.name (via freshness).
      have hwit_ne : dt_i.name ≠ d'.name.pushNamespace c'.nameHead := by
        intro h'
        rcases hQ.2.2 k' d' hget with horig_init | ⟨dt_orig, hdt_orig_mem, hk_eq, hd_eq⟩
        · exact hFresh dt_i hdt_mem k' d' c' horig_init hc' h'
        · have hd_name : d'.name = dt_orig.name := by rw [hd_eq, rewriteDt_name]
          have hc_mem_orig : c'.nameHead ∈ dt_orig.constructors.map (·.nameHead) := by
            rw [hd_eq, rewriteDt_constructors] at hc'
            -- hc' : c' ∈ dt_orig.constructors.map (rewriteC mono)
            simp only [List.mem_map] at hc'
            obtain ⟨co, hco_mem, hco_eq⟩ := hc'
            simp only [List.mem_map]
            exact ⟨co, hco_mem, by rw [← hco_eq]⟩
          have := hMutualFresh dt_i hdt_mem dt_orig hdt_orig_mem c'.nameHead hc_mem_orig
          rw [← hd_name] at this
          exact absurd h' this
      have hne_wit : (dt_i.name == d'.name.pushNamespace c'.nameHead) = false := by
        cases hbeq : (dt_i.name == d'.name.pushNamespace c'.nameHead) with
        | false => rfl
        | true =>
          exact absurd (LawfulBEq.eq_of_beq hbeq) hwit_ne
      refine ⟨cc, ?_⟩
      simp only [acc₀]
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_wit]
      exact hccget
    -- DtNameIsKey on acc₀.
    have hAcc₀Dt : TypedDtNameIsKeyP acc₀ := by
      intro k' d' hget
      by_cases hk : (dt_i.name == k') = true
      · have hkeq := LawfulBEq.eq_of_beq hk
        rw [← hkeq] at hget
        simp only [acc₀] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hget
        rw [← hkeq, ← hget]
      · have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk
        simp only [acc₀] at hget
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hQ.2.1 k' d' hget
    -- Freshness for inner fold.
    have hfreshPush : ∀ k'' d'' c'' ch,
        acc₀.getByKey k'' = some (.dataType d'') → c'' ∈ d''.constructors →
        ch ∈ rewrittenCtors.map (·.nameHead) →
        d''.name ≠ dt_i.name → d''.name.pushNamespace c''.nameHead ≠
          dt_i.name.pushNamespace ch := by
      intro k'' d'' c'' ch _ _ _ hd_ne heq_push
      exact hd_ne (pushNamespace_inj_both heq_push).1
    -- Call innerCtorFold_preserves.
    have hinner := innerCtorFold_preserves dt_i.name newDt rewrittenCtors
      acc₀ hAcc₀_partial hAcc₀Dt hacc₀_newDt hfreshPush
    -- Goal: Q of full step.
    refine ⟨?_, ?_, ?_⟩
    · -- TypedCtorPresentP
      intro k' d' c' hget hc'
      by_cases hk_eq : (dt_i.name == k') = true
      · -- k' = dt_i.name: d' = newDt, witness via hinner.1 on c'.nameHead.
        have hkeq := LawfulBEq.eq_of_beq hk_eq
        have hacc₀_k := hinner.2.2.2.2 k' d' hget
        rw [← hkeq] at hacc₀_k
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_self] at hacc₀_k
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hacc₀_k
        -- d' = newDt.
        subst hacc₀_k
        -- c' ∈ newDt.constructors = rewrittenCtors. Need c'.nameHead in rewrittenCtors.map (·.nameHead).
        have hch_mem : c'.nameHead ∈ rewrittenCtors.map (·.nameHead) :=
          List.mem_map_of_mem hc'
        obtain ⟨cc, hcc⟩ := hinner.1 c'.nameHead hch_mem
        refine ⟨cc, ?_⟩
        -- Unfold acc₀ in hcc. Goal has newDt.name (= dt_i.name, rfl).
        simp only [acc₀] at hcc
        exact hcc
      · -- k' ≠ dt_i.name: d' traces via hinner.2.1 (non-newDt witnesses preserved).
        have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk_eq
        have hd_key := hinner.2.2.1 k' d' hget
        -- d'.name ≠ dt_i.name?
        have hd_ne : d'.name ≠ dt_i.name := by
          intro heq_name
          rw [heq_name] at hd_key
          rw [hd_key] at hne
          simp at hne
        exact hinner.2.1 k' d' c' hget hc' hd_ne
    · -- TypedDtNameIsKeyP
      exact hinner.2.2.1
    · -- Trace: init or newDataTypes.
      intro k' d' hget
      have hacc₀_k := hinner.2.2.2.2 k' d' hget
      by_cases hk : (dt_i.name == k') = true
      · have hkeq := LawfulBEq.eq_of_beq hk
        rw [← hkeq] at hacc₀_k
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_self] at hacc₀_k
        simp only [Option.some.injEq, Typed.Declaration.dataType.injEq] at hacc₀_k
        refine Or.inr ⟨dt_i, hdt_mem, ?_, ?_⟩
        · exact hkeq.symm
        · exact hacc₀_k.symm
      · have hne : (dt_i.name == k') = false := Bool.not_eq_true _ |>.mp hk
        simp only [acc₀] at hacc₀_k
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hacc₀_k
        exact hQ.2.2 k' d' hacc₀_k

/-- Phase-2 freshness discharge: from `hFreshDt` + structure of fromSource,
derive the freshness hypothesis needed by `withNewDts_preserves_ctorPresent`.

After Phase 1 (`fromSource`), a `.dataType dt_new` at key `k` corresponds
to a source `.dataType dt_orig` at `k`, where `dt_new = {dt_orig with
ctors := rewrittenCtors}`. So `dt_new.name = dt_orig.name` and
`dt_new.constructors.map (·.nameHead) = dt_orig.constructors.map
(·.nameHead)` (actual rewriting preserves nameHead).

The freshness obligation at Phase 2 becomes: `dt.name ≠ dt_new.name.pushNamespace
c'.nameHead` for `c' ∈ dt_new.constructors`. Since `dt_new.name = dt_orig.name`
and `c'.nameHead = c_src.nameHead` for some `c_src ∈ dt_orig.constructors`
(via the rewriting map), and source has `.constructor dt_orig c_src_wit`
at `dt_orig.name.pushNamespace c_src.nameHead` (by hP), the freshness
follows from `hFreshDt` (which rules out `dt.name = dt_orig.name.pushNamespace
c_src.nameHead`). -/
private theorem phase2_freshness_discharge
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (newDataTypes : Array DataType)
    (hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := typedDecls.pairs.foldl
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
      default
    ∀ dt ∈ newDataTypes, ∀ k dt' c,
      fromSource.getByKey k = some (.dataType dt') → c ∈ dt'.constructors →
      dt.name ≠ dt'.name.pushNamespace c.nameHead := by
  intro emptySubst fS
  show ∀ dt ∈ newDataTypes, ∀ k dt' c,
    (fromSource typedDecls mono).getByKey k = some (.dataType dt') →
    c ∈ dt'.constructors →
    dt.name ≠ dt'.name.pushNamespace c.nameHead
  intro dt hdt_mem k dt_new c hget hc
  obtain ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ :=
    fromSource_dt_trace typedDecls mono k dt_new hget
  have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
  have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
  have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
  rw [rewriteDt_constructors] at hc_new
  rw [List.mem_map] at hc_new
  obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
  have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
  obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
  have hfresh_src := hFreshDt dt hdt_mem
    (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
  have hcc_is_key := hCtor (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
  have hcc_head : cc.nameHead = c'.nameHead := by
    have := pushNamespace_right_inj hcc_is_key
    exact this.symm
  have hname_new : dt_new.name = dtSrc.name := by rw [hdt_eq]
  rw [hname_new, hhead, ← hcc_head]
  exact hfresh_src

/-! ### Phase-3 lemma: `newFunctions` fold preserves CtorPresent. -/

/-- Inserting `.function newF` at `fName` preserves CtorPresent when
`fName` doesn't collide with any existing dt key or pushed ctor key. -/
private theorem insert_fn_preserves_ctorPresent
    (acc : Typed.Decls) (fName : Global) (newF : Typed.Function)
    (hAcc : TypedCtorPresentP acc)
    (hFresh : ∀ k dt c, acc.getByKey k = some (.dataType dt) →
      c ∈ dt.constructors →
      fName ≠ k ∧ fName ≠ dt.name.pushNamespace c.nameHead) :
    TypedCtorPresentP
      (acc.insert fName (.function newF)) := by
  intro k dt c hget hc
  by_cases hkn : (fName == k) = true
  · have hkEq : fName = k := LawfulBEq.eq_of_beq hkn
    subst hkEq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
  · have hne : (fName == k) = false := Bool.not_eq_true _ |>.mp hkn
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    obtain ⟨cc, hccget⟩ := hAcc k dt c hget hc
    have ⟨_hne1, hne2_prop⟩ := hFresh k dt c hget hc
    have hne2 : (fName == dt.name.pushNamespace c.nameHead) = false := by
      by_cases h' : (fName == dt.name.pushNamespace c.nameHead) = true
      · exact absurd (LawfulBEq.eq_of_beq h') hne2_prop
      · exact Bool.not_eq_true _ |>.mp h'
    refine ⟨cc, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne2]
    exact hccget

/-- Phase-3 preservation: the full `newFunctions` fold preserves
CtorPresent given a freshness hypothesis at each step. -/
private theorem newFunctions_preserves_ctorPresent
    (init : Typed.Decls) (mono : MonoMap) (typedDecls : Typed.Decls)
    (newFunctions : Array Typed.Function)
    (hInit : TypedCtorPresentP init)
    (hFresh : ∀ f ∈ newFunctions, ∀ k dt c,
      init.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
      f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead) :
    let emptySubst : Global → Option Typ := fun _ => none
    TypedCtorPresentP (newFunctions.foldl
      (fun acc f =>
        let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
        let newOutput := rewriteTyp emptySubst mono f.output
        let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
        let newF : Typed.Function :=
          { f with inputs := newInputs, output := newOutput, body := newBody }
        acc.insert f.name (.function newF))
      init) := by
  -- Strengthened invariant: acc satisfies CtorPresent AND every (k, .dataType dt)
  -- in acc is already present in init. This lets us apply `hFresh` (which is
  -- stated relative to `init`) at each step.
  let emptySubst : Global → Option Typ := fun _ => none
  let step : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
    let newOutput := rewriteTyp emptySubst mono f.output
    let newBody := rewriteTypedTerm typedDecls emptySubst mono f.body
    let newF : Typed.Function :=
      { f with inputs := newInputs, output := newOutput, body := newBody }
    acc.insert f.name (.function newF)
  let Q : Typed.Decls → Prop := fun acc =>
    TypedCtorPresentP acc ∧
    ∀ k dt, acc.getByKey k = some (.dataType dt) →
      init.getByKey k = some (.dataType dt)
  suffices h : Q (newFunctions.foldl step init) from h.1
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => Q acc)
  · exact ⟨hInit, fun _ _ h => h⟩
  · intro i acc hQ
    have hfmem : newFunctions[i.val]'i.isLt ∈ newFunctions := Array.getElem_mem _
    have hFreshAt : ∀ k dt c,
        acc.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
        (newFunctions[i.val]'i.isLt).name ≠ k ∧
        (newFunctions[i.val]'i.isLt).name ≠ dt.name.pushNamespace c.nameHead := by
      intro k dt c hget hc
      have hget_init : init.getByKey k = some (.dataType dt) := hQ.2 k dt hget
      exact hFresh (newFunctions[i.val]'i.isLt) hfmem k dt c hget_init hc
    refine ⟨?_, ?_⟩
    · -- CtorPresent preserved via `insert_fn_preserves_ctorPresent`.
      exact insert_fn_preserves_ctorPresent acc
        (newFunctions[i.val]'i.isLt).name _ hQ.1 hFreshAt
    · -- dataType-in-init preserved: insert only adds a .function entry.
      intro k dt hget
      simp only [step] at hget
      by_cases hkn : (newFunctions[i].name == k) = true
      · have hkEq : newFunctions[i].name = k := LawfulBEq.eq_of_beq hkn
        rw [← hkEq] at hget
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (newFunctions[i].name == k) = false :=
          Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hQ.2 k dt hget

/-! ### Phase-3 freshness discharge: from `hFreshFn` + `NewFnBridge` +
`NewDtBridge` + `hFreshDt`, derive the per-step freshness condition
needed by `newFunctions_preserves_ctorPresent`.

For `.dataType dt` at `k` in the post-Phase-2 acc:
* Origin A: `dt` came from Phase 1 (source `.dataType`). Then `k = dt.name`
  by `hDt`. Need `f.name ≠ dt.name` and `f.name ≠ dt.name.pushNamespace c.nameHead`.
  - `f.name ≠ dt.name.pushNamespace c.nameHead`: via `hFreshFn` + `hP`+`hCtor`
    on source (source `.constructor dt c'` at `dt.name.pushNamespace c'.nameHead`;
    `f.name ≠` this key).
  - `f.name ≠ dt.name = k`: source IndexMap-key uniqueness + `NewFnBridge`
    (f origin is source `.function`; can't equal source `.dataType` key).
* Origin B: `dt` came from Phase 2 (`newDataTypes`). Then `dt.name = g` for
  some source dt `g`. Need:
  - `f.name ≠ dt.name = g`: `NewFnBridge` says `f.name = g'` for source fn `g'`;
    source key uniqueness gives `g' ≠ g`.
  - `f.name ≠ dt.name.pushNamespace c.nameHead`: `c.nameHead ∈ orig.constructors.map
    (·.nameHead)` (via `NewDtBridge`); source has `.constructor orig cc` at
    `g.pushNamespace c.nameHead` (via `hP` + `hCtor`). Apply `hFreshFn`.
-/

private theorem phase3_freshness_discharge
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    (hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    let emptySubst : Global → Option Typ := fun _ => none
    let postPhase2 : Typed.Decls := newDataTypes.foldl
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
        default)
    ∀ f ∈ newFunctions, ∀ k dt c,
      postPhase2.getByKey k = some (.dataType dt) → c ∈ dt.constructors →
      f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead := by
  intro emptySubst postPhase2
  show ∀ f ∈ newFunctions, ∀ k dt c,
    (phase2Acc typedDecls mono newDataTypes).getByKey k = some (.dataType dt) →
    c ∈ dt.constructors →
    f.name ≠ k ∧ f.name ≠ dt.name.pushNamespace c.nameHead
  intro f hf_mem k dt_mid c hget hc
  rcases phase2Acc_dt_trace typedDecls mono newDataTypes k dt_mid hget with
    ⟨dtSrc, hmem_dt, hparams, hdt_eq⟩ | ⟨dt_orig, hdt_orig_mem, hk_eq, hdt_eq⟩
  · -- Origin A: Phase-1 source.
    have hget_src : typedDecls.getByKey k = some (.dataType dtSrc) :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hmem_dt
    have hk_name : k = dtSrc.name := hDt k dtSrc hget_src
    have hc_new : c ∈ (rewriteDt mono dtSrc).constructors := by rw [← hdt_eq]; exact hc
    rw [rewriteDt_constructors] at hc_new
    rw [List.mem_map] at hc_new
    obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
    have hhead : c.nameHead = c'.nameHead := by rw [← hc'_eq]
    obtain ⟨cc, hcc_get⟩ := hP k dtSrc c' hget_src hc'_mem
    have hcc_is_key := hCtor (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
    have hcc_head : cc.nameHead = c'.nameHead := by
      have := pushNamespace_right_inj hcc_is_key
      exact this.symm
    obtain ⟨g', orig_f, hget_g', hf_name⟩ := hNewFnBridge f hf_mem
    refine ⟨?_, ?_⟩
    · rw [hf_name]
      intro hgk
      have : typedDecls.getByKey g' = some (.dataType dtSrc) := by rw [hgk]; exact hget_src
      rw [hget_g'] at this
      cases this
    · rw [hdt_eq, rewriteDt_name, hhead]
      have := hFreshFn f hf_mem (dtSrc.name.pushNamespace c'.nameHead) dtSrc cc hcc_get
      rw [← hcc_head]
      exact this
  · -- Origin B: Phase-2 new dt.
    obtain ⟨g, orig, hget_g_src, hname_eq, hhead_eq⟩ := hNewDtBridge dt_orig hdt_orig_mem
    have hc_new : c ∈ (rewriteDt mono dt_orig).constructors := by rw [← hdt_eq]; exact hc
    rw [rewriteDt_constructors] at hc_new
    rw [List.mem_map] at hc_new
    obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_new
    have hhead_c : c.nameHead = c'.nameHead := by rw [← hc'_eq]
    have hc'_head_in : c'.nameHead ∈ orig.constructors.map (·.nameHead) := by
      rw [← hhead_eq]
      rw [List.mem_map]
      exact ⟨c', hc'_mem, rfl⟩
    rw [List.mem_map] at hc'_head_in
    obtain ⟨c_orig, hc_orig_mem, hc_orig_head⟩ := hc'_head_in
    obtain ⟨cc, hcc_get⟩ := hP g orig c_orig hget_g_src hc_orig_mem
    have hcc_is_key := hCtor (orig.name.pushNamespace c_orig.nameHead) orig cc hcc_get
    have hcc_head : cc.nameHead = c_orig.nameHead := by
      have := pushNamespace_right_inj hcc_is_key
      exact this.symm
    have hg_name : g = orig.name := hDt g orig hget_g_src
    obtain ⟨g', orig_f, hget_g'_src, hf_name⟩ := hNewFnBridge f hf_mem
    refine ⟨?_, ?_⟩
    · rw [hk_eq, hname_eq, hf_name]
      intro hgeq
      have : typedDecls.getByKey g' = some (.dataType orig) := by rw [hgeq]; exact hget_g_src
      rw [hget_g'_src] at this
      cases this
    · rw [hdt_eq, rewriteDt_name, hname_eq, hhead_c]
      rw [← hc_orig_head]
      have hfresh := hFreshFn f hf_mem (orig.name.pushNamespace c_orig.nameHead) orig cc hcc_get
      rw [← hg_name] at hfresh
      rw [← hcc_head]
      exact hfresh

/-! ### Final body theorem.

Closes the body of `concretizeBuild_ctorPresent` (below) using the four
phase lemmas + direct `IndexMap.insert` analysis in
`insert_fn_preserves_ctorPresent`.
-/

/-- Body of `concretizeBuild_ctorPresent`. Strengthened signature:
FullyMono + hdecls + hts hidden in bridges. Pass through to phase lemmas. -/
private theorem concretizeBuild_ctorPresent_body
    {typedDecls : Typed.Decls}
    (hP : TypedCtorPresentP typedDecls)
    (hDt : TypedDtNameIsKeyP typedDecls)
    (hCtor : TypedCtorIsKeyP typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead)
    (hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    (_hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (_hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    TypedCtorPresentP
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  let emptySubst : Global → Option Typ := fun _ => none
  -- Phase 1: `fromSource`.
  have hP1 := fromSource_preserves_ctorPresent typedDecls mono hP hDt hCtor
  -- Phase 2: `withNewDts`.
  have hFresh2 := phase2_freshness_discharge typedDecls mono hP hDt hCtor
    newDataTypes hFreshDt
  -- `hInitDt` derivation: fromSource preserves DtNameIsKey.
  have hInitDt : TypedDtNameIsKeyP (fromSource typedDecls mono) := by
    intro k dt hget
    obtain ⟨dtSrc, _, _, hdt_eq⟩ := fromSource_dt_trace typedDecls mono k dt hget
    rw [hdt_eq, rewriteDt_name]
    exact hDt k dtSrc (IndexMap.getByKey_of_mem_pairs _ _ _ (by assumption))
  -- `hMutualFresh` derivation: uses NewDtBridge + source key uniqueness.
  have hMutualFresh : ∀ dt ∈ newDataTypes, ∀ dt' ∈ newDataTypes,
      ∀ ch ∈ dt'.constructors.map (·.nameHead),
      dt.name ≠ dt'.name.pushNamespace ch := by
    intro dt hdt_mem dt' hdt'_mem ch hch
    -- dt = corresponds to source g_dt; dt' = source g_dt' with same ctor heads.
    obtain ⟨g_dt, orig_dt, hget_dt, hname_dt, _⟩ := _hNewDtBridge dt hdt_mem
    obtain ⟨g_dt', orig_dt', hget_dt', hname_dt', hheads_dt'⟩ :=
      _hNewDtBridge dt' hdt'_mem
    -- ch is a nameHead in dt'.constructors, so also in orig_dt'.constructors (via hheads_dt').
    rw [hheads_dt'] at hch
    -- There's a c_orig ∈ orig_dt'.constructors with c_orig.nameHead = ch.
    rw [List.mem_map] at hch
    obtain ⟨c_orig, hc_orig_mem, hc_orig_head⟩ := hch
    -- source has .constructor orig_dt' cc at orig_dt'.name.pushNamespace c_orig.nameHead.
    obtain ⟨cc, hcc_get⟩ := hP g_dt' orig_dt' c_orig hget_dt' hc_orig_mem
    have hg_dt'_name : g_dt' = orig_dt'.name := hDt g_dt' orig_dt' hget_dt'
    -- Goal: dt.name ≠ dt'.name.pushNamespace ch.
    -- hname_dt' : dt'.name = g_dt'. hc_orig_head : c_orig.nameHead = ch. hg_dt'_name : g_dt' = orig_dt'.name.
    intro hkeq
    -- hkeq : dt.name = dt'.name.pushNamespace ch
    -- Transform to: g_dt = orig_dt'.name.pushNamespace c_orig.nameHead (source key of .constructor).
    rw [hname_dt'] at hkeq  -- dt.name = g_dt'.pushNamespace ch
    rw [← hc_orig_head] at hkeq  -- dt.name = g_dt'.pushNamespace c_orig.nameHead
    rw [hname_dt] at hkeq  -- g_dt = g_dt'.pushNamespace c_orig.nameHead
    -- Substitute in hget_dt to get typedDecls at the ctor-key.
    rw [hkeq] at hget_dt
    -- hget_dt : typedDecls.getByKey (g_dt'.pushNamespace c_orig.nameHead) = some (.dataType orig_dt)
    -- Rewrite hcc_get's key: orig_dt'.name.pushNamespace c_orig.nameHead = g_dt'.pushNamespace c_orig.nameHead.
    rw [← hg_dt'_name] at hcc_get
    -- hcc_get : typedDecls.getByKey (g_dt'.pushNamespace c_orig.nameHead) = some (.constructor orig_dt' cc)
    rw [hcc_get] at hget_dt
    cases hget_dt
  have hP2 := withNewDts_preserves_ctorPresent _ mono newDataTypes hP1 hInitDt hFresh2 hMutualFresh
  -- Phase 3: `newFunctions`.
  -- Rewrite `concretizeBuild` as the composed folds.
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
  rw [hEq]
  -- Phase 3 preservation via `newFunctions_preserves_ctorPresent`.
  -- The freshness hypothesis is discharged by `phase3_freshness_discharge`.
  have hFreshPost := phase3_freshness_discharge typedDecls mono hP hDt hCtor
    newFunctions newDataTypes hFreshFn _hNewDtBridge _hNewFnBridge
  exact newFunctions_preserves_ctorPresent _ mono typedDecls newFunctions hP2 hFreshPost

end CtorPresentBody

private theorem concretizeBuild_ctorPresent
    {typedDecls : Typed.Decls}
    (hP : TypedCtorPresentP typedDecls)
    (_hDt : TypedDtNameIsKeyP typedDecls)
    (_hCtor : TypedCtorIsKeyP typedDecls)
    (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    -- Freshness: new datatypes don't shadow an existing ctor witness' key.
    (_hFreshDt : ∀ dt ∈ newDataTypes,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead)
    -- Freshness: new functions don't shadow an existing ctor witness' key.
    (_hFreshFn : ∀ f ∈ newFunctions,
      ∀ k dt' c, typedDecls.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead)
    -- FullyMono-implied structural correspondence of drained `newDataTypes`/
    -- `newFunctions` to source decls.
    (_hNewDtBridge : NewDtBridge typedDecls newDataTypes)
    (_hNewFnBridge : NewFnBridge typedDecls newFunctions) :
    TypedCtorPresentP
      (concretizeBuild typedDecls mono newFunctions newDataTypes) :=
  CtorPresentBody.concretizeBuild_ctorPresent_body hP _hDt _hCtor mono
    newFunctions newDataTypes _hFreshDt _hFreshFn _hNewDtBridge _hNewFnBridge

/-- `step4Lower` preserves `CtorPresent` as a fold-invariant: each step either
inserts a `.function` (no ctor/dt effect), a `.dataType` (establishes its own
ctors via the input's CtorPresent hypothesis and downstream fold), or a
`.constructor` (pass-through keyed at same key). -/
private theorem step4Lower_preserves_ctorPresent
    {monoDecls : Typed.Decls} {cd : Concrete.Decls}
    (hP : TypedCtorPresentP monoDecls)
    (_hDt : ∀ k dt, monoDecls.getByKey k = some (.dataType dt) → k = dt.name)
    (_hCtor : ∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
      k = dt.name.pushNamespace c.nameHead)
    (hfold : monoDecls.foldlM (init := (default : Concrete.Decls)) step4Lower = .ok cd) :
    ConcreteCtorPresentP cd := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hDtBack : ∀ k concDt, cd.getByKey k = some (.dataType concDt) →
      ∃ (dt : DataType) (ctors : List Concrete.Constructor),
        monoDecls.getByKey k = some (.dataType dt) ∧
        dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors ∧
        concDt = { name := dt.name, constructors := ctors } := by
    let Q : Concrete.Decls → Prop := fun acc =>
      ∀ k concDt, acc.getByKey k = some (.dataType concDt) →
        ∃ (dt : DataType) (ctors : List Concrete.Constructor),
          monoDecls.getByKey k = some (.dataType dt) ∧
          dt.constructors.mapM (fun c' => do
            let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
            pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors ∧
          concDt = { name := dt.name, constructors := ctors }
    have hQ0 : Q (default : Concrete.Decls) := by
      intro k concDt hget
      exfalso
      have : (default : Concrete.Decls).getByKey k = none := by
        unfold IndexMap.getByKey
        show ((default : Concrete.Decls).indices[k]?).bind _ = none
        have : (default : Concrete.Decls).indices[k]? = none := by
          show ((default : Std.HashMap Global Nat))[k]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      rw [this] at hget; cases hget
    apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
    · exact hQ0
    · intro acc ⟨name, d⟩ acc' hxmem hstep hQacc
      unfold step4Lower at hstep
      simp only at hstep
      have hname_src : monoDecls.getByKey name = some d :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
      cases d with
      | function f =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
      | dataType dt =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i ctors hctors
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          simp only [Option.some.injEq, Concrete.Declaration.dataType.injEq] at hget
          refine ⟨dt, ctors, hname_src, ?_, hget.symm⟩
          exact hctors
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
      | constructor dt c =>
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i ctors _hctors
        split at hstep
        · exact absurd hstep (by intro h'; cases h')
        rename_i argTypes _hargs
        simp only [Except.ok.injEq] at hstep
        subst hstep
        intro k concDt hget
        by_cases hkn : (name == k) = true
        · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
          subst hkEq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
        · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hQacc k concDt hget
  have hCtorForward : ∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
      ∃ concDt concC ctors', cd.getByKey k = some (.constructor concDt concC) ∧
        concC.nameHead = c.nameHead ∧
        dt.constructors.mapM (fun c' => do
          let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
          pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
        concDt = { name := dt.name, constructors := ctors' } := by
    intro k dt c hmonoget
    have hmem : (k, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hmonoget
    have key_helper : ∀ (processed remaining : List (Global × Typed.Declaration))
        (init finalacc : Concrete.Decls),
        processed ++ remaining = monoDecls.pairs.toList →
        (∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ processed →
          ∃ concDt concC ctors', init.getByKey k = some (.constructor concDt concC) ∧
            concC.nameHead = c.nameHead ∧
            dt.constructors.mapM (fun c' => do
              let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
              pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
            concDt = { name := dt.name, constructors := ctors' }) →
        remaining.foldlM step4Lower init = .ok finalacc →
        ∀ k dt c, (k, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList →
          ∃ concDt concC ctors', finalacc.getByKey k = some (.constructor concDt concC) ∧
            concC.nameHead = c.nameHead ∧
            dt.constructors.mapM (fun c' => do
              let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
              pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
            concDt = { name := dt.name, constructors := ctors' } := by
      intro processed remaining
      induction remaining generalizing processed with
      | nil =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
        subst hfold
        have : processed = monoDecls.pairs.toList := by rw [← hsplit]; simp
        rw [this] at hPinit
        exact hPinit k dt c hmemFinal
      | cons x xs ih =>
        intro init finalacc hsplit hPinit hfold k dt c hmemFinal
        simp only [List.foldlM_cons, bind, Except.bind] at hfold
        split at hfold
        · exact absurd hfold (by intro h; cases h)
        rename_i acc' hstep
        obtain ⟨xname, xdecl⟩ := x
        have hsplit' : (processed ++ [(xname, xdecl)]) ++ xs = monoDecls.pairs.toList := by
          simp [← hsplit]
        have hPacc' : ∀ k' dt' c',
            (k', Typed.Declaration.constructor dt' c') ∈ processed ++ [(xname, xdecl)] →
            ∃ concDt concC ctors', acc'.getByKey k' = some (.constructor concDt concC) ∧
              concC.nameHead = c'.nameHead ∧
              dt'.constructors.mapM (fun c'' => do
                let argTypes ← c''.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
                pure ({ nameHead := c''.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' ∧
              concDt = { name := dt'.name, constructors := ctors' } := by
          intro k' dt' c' hmem'
          rcases List.mem_append.mp hmem' with hmemL | hmemR
          · obtain ⟨cDt0, cC0, ctors0, hacc_k', hheadEq, hctors0Map, hcDt0Eq⟩ :=
              hPinit k' dt' c' hmemL
            cases xdecl with
            | constructor xd xc =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xctors _hxctors
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xargs _hxargs
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                have h_x_mem : (xname, Typed.Declaration.constructor xd xc) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor xd xc) ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.constructor xd xc) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.constructor xd xc) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2
                simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at h2
                obtain ⟨hxdEq, hxcEq⟩ := h2
                subst hxdEq; subst hxcEq
                refine ⟨{ name := xd.name, constructors := xctors },
                        ⟨xc.nameHead, xargs⟩, xctors, ?_, rfl, _hxctors, rfl⟩
                rw [IndexMap.getByKey_insert_self]
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | dataType xd =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              rename_i xctors _hxctors
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.dataType xd) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.dataType xd) ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.dataType xd) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.dataType xd) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
            | function xf =>
              unfold step4Lower at hstep
              simp only [bind, Except.bind, pure, Except.pure] at hstep
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              split at hstep
              · exact absurd hstep (by intro h'; cases h')
              simp only [Except.ok.injEq] at hstep
              subst hstep
              by_cases hkn : (xname == k') = true
              · have hkEq : xname = k' := LawfulBEq.eq_of_beq hkn
                subst hkEq
                exfalso
                have h_x_mem : (xname, Typed.Declaration.function xf) ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.function xf) ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) := by
                    apply List.mem_append_right; exact List.Mem.head _
                  rw [hsplit] at this; exact this
                have h_k'_mem : (xname, Typed.Declaration.constructor dt' c') ∈ monoDecls.pairs.toList := by
                  have : (xname, Typed.Declaration.constructor dt' c') ∈
                      processed ++ ((xname, Typed.Declaration.function xf) :: xs) :=
                    List.mem_append_left _ hmemL
                  rw [hsplit] at this; exact this
                have h1 : monoDecls.getByKey xname = some (.function xf) :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_x_mem
                have h2 : monoDecls.getByKey xname = some (.constructor dt' c') :=
                  IndexMap.getByKey_of_mem_pairs _ _ _ h_k'_mem
                rw [h1] at h2; cases h2
              · have hne : (xname == k') = false := Bool.not_eq_true _ |>.mp hkn
                refine ⟨cDt0, cC0, ctors0, ?_, hheadEq, hctors0Map, hcDt0Eq⟩
                rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
                exact hacc_k'
          · rcases List.mem_singleton.mp hmemR with hxeq
            rcases Prod.mk.injEq _ _ _ _ |>.mp hxeq with ⟨hname_eq, hdecl_eq⟩
            subst hname_eq; subst hdecl_eq
            unfold step4Lower at hstep
            simp only [bind, Except.bind, pure, Except.pure] at hstep
            split at hstep
            · exact absurd hstep (by intro h'; cases h')
            rename_i xctors _hxctors
            split at hstep
            · exact absurd hstep (by intro h'; cases h')
            rename_i xargs _hxargs
            simp only [Except.ok.injEq] at hstep
            subst hstep
            refine ⟨{ name := dt'.name, constructors := xctors },
                    ⟨c'.nameHead, xargs⟩, xctors, ?_, rfl, _hxctors, rfl⟩
            rw [IndexMap.getByKey_insert_self]
        exact ih (processed ++ [(xname, xdecl)]) acc' finalacc hsplit' hPacc' hfold k dt c hmemFinal
    exact key_helper [] monoDecls.pairs.toList default cd (by simp)
      (by intro _ _ _ h; cases h) hfold k dt c hmem
  intro k concDt c hget hc
  obtain ⟨dt, ctors, hmonoGet, hctorsMap, hconcDtEq⟩ := hDtBack k concDt hget
  subst hconcDtEq
  simp only at hc
  have hc_in_ctors : c ∈ ctors := hc
  have hExistsOrig : ∀ (orig : List Constructor) (ctors' : List Concrete.Constructor),
      orig.mapM (fun c' => do
        let argTypes ← c'.argTypes.mapM (typToConcrete ({} : Std.HashMap (Global × Array Typ) Global))
        pure ({ nameHead := c'.nameHead, argTypes } : Concrete.Constructor)) = .ok ctors' →
      ∀ (cc : Concrete.Constructor), cc ∈ ctors' →
      ∃ c_orig ∈ orig, cc.nameHead = c_orig.nameHead := by
    intro orig
    induction orig with
    | nil =>
      intro ctors' hmap cc hcc
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      cases hcc
    | cons head rest ih =>
      intro ctors' hmap cc hcc
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hmap
      split at hmap
      · exact absurd hmap (by intro h; cases h)
      rename_i headArgs hheadArgs
      split at hmap
      · exact absurd hmap (by intro h; cases h)
      rename_i restCtors hrestCtors
      simp only [Except.ok.injEq] at hmap
      subst hmap
      split at hheadArgs
      · exact absurd hheadArgs (by intro h; cases h)
      rename_i v _hv
      simp only [Except.ok.injEq] at hheadArgs
      subst hheadArgs
      rcases List.mem_cons.mp hcc with heq | htail
      · refine ⟨head, List.Mem.head _, ?_⟩
        rw [heq]
      · obtain ⟨c_orig, hc_orig_mem, hhead_eq⟩ := ih restCtors hrestCtors cc htail
        exact ⟨c_orig, List.Mem.tail _ hc_orig_mem, hhead_eq⟩
  obtain ⟨c_orig, hc_orig_mem, hhead_eq⟩ :=
    hExistsOrig dt.constructors ctors hctorsMap c hc_in_ctors
  obtain ⟨cc_orig, hccOrigGet⟩ := hP k dt c_orig hmonoGet hc_orig_mem
  obtain ⟨concDt', concC', ctors_fwd, hcdGet, _hconcHead, hctorsFwdMap, hconcDtEq⟩ :=
    hCtorForward _ _ _ hccOrigGet
  -- `dt.constructors.mapM ... = .ok ctors` (hctorsMap) AND
  -- `dt.constructors.mapM ... = .ok ctors_fwd` (hctorsFwdMap), so `ctors = ctors_fwd`.
  have hctorsEq : ctors = ctors_fwd := by
    rw [hctorsMap] at hctorsFwdMap
    exact Except.ok.inj hctorsFwdMap
  refine ⟨concC', ?_⟩
  have hpushEq : ({ name := dt.name, constructors := ctors } : Concrete.DataType).name.pushNamespace c.nameHead
                  = dt.name.pushNamespace c_orig.nameHead := by
    show dt.name.pushNamespace c.nameHead = dt.name.pushNamespace c_orig.nameHead
    rw [hhead_eq]
  rw [hpushEq, hctorsEq, ← hconcDtEq]
  exact hcdGet

/-- Bridge: get `TypedCtorPresentP` from `Typed.Decls.CtorPresent`. -/
private theorem TypedCtorPresentP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.CtorPresent d) : TypedCtorPresentP d := by
  intro k dt c hget hc
  have hmem : (k, Typed.Declaration.dataType dt) ∈ d.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  obtain ⟨cc, hcmem⟩ := hP k dt c hmem hc
  exact ⟨cc, IndexMap.getByKey_of_mem_pairs _ _ _ hcmem⟩

/-- Bridge: `TypedDtNameIsKey` (pairs form) ⇒ getByKey form. -/
private theorem TypedDtNameIsKeyP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.DtNameIsKey d) : TypedDtNameIsKeyP d := by
  intro k dt hget
  exact hP k dt (IndexMap.mem_pairs_of_getByKey _ _ _ hget)

private theorem TypedCtorIsKeyP_of_pairs {d : Typed.Decls}
    (hP : Typed.Decls.CtorIsKey d) : TypedCtorIsKeyP d := by
  intro k dt c hget
  exact hP k dt c (IndexMap.mem_pairs_of_getByKey _ _ _ hget)

/-! ### `hFresh_bridge` infrastructure

Ported from `HFreshBridgeScratch.lean`. Derives newDataTypes/newFunctions
names disjoint from pushed-ctor-keys in typedDecls via `DrainState.NewNameShape`. -/

/-- `concretizeDrainEntry` preserves `NewNameShape`. -/
private theorem concretizeDrainEntry_preserves_NewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.NewNameShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · obtain ⟨g, args, f_orig, hname, hget⟩ := hinv.1 f' hin
            exact ⟨g, args, f_orig, hname, hget⟩
          · subst heq
            refine ⟨entry.1, entry.2, f, ?_, ?_⟩
            · show concretizeName entry.1 entry.2 = concretizeName entry.1 entry.2; rfl
            · exact hf_get
        · intro dt hdt
          exact hinv.2 dt hdt
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, ?_, ?_⟩
            · show concretizeName entry.1 entry.2 = concretizeName entry.1 entry.2; rfl
            · exact hdt_get
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

/-- Folding `concretizeDrainEntry` over a list preserves `NewNameShape`. -/
private theorem concretizeDrainEntry_list_foldlM_preserves_NewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.NewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.NewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.NewNameShape decls :=
        concretizeDrainEntry_preserves_NewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

/-- `concretizeDrainIter` preserves `NewNameShape`. -/
private theorem concretizeDrainIter_preserves_NewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.NewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

/-- `concretizeDrain` preserves `NewNameShape`. -/
private theorem concretize_drain_preserves_NewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.NewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.NewNameShape decls := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.NewNameShape decls :=
          concretizeDrainIter_preserves_NewNameShape hinv hstate'
        exact ih state' hinv' hdrain

/-- Every `drained.newFunctions` name is `concretizeName g args` for some drained
`(g, args)` whose source origin is a `.function` entry in `tds`. -/
private theorem drain_newFunctions_name_shape
    {tds : Typed.Decls} {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ f ∈ drained.newFunctions,
      ∃ (g : Global) (args : Array Typ) (f_orig : Typed.Function),
        f.name = concretizeName g args ∧
        tds.getByKey g = some (.function f_orig) := by
  have hinit : DrainState.NewNameShape tds _ :=
    DrainState.NewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_NewNameShape _ _ hinit hdrain
  exact hfinal.1

/-- Same for `newDataTypes`. -/
private theorem drain_newDataTypes_name_shape
    {tds : Typed.Decls} {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ dt ∈ drained.newDataTypes,
      ∃ (g : Global) (args : Array Typ) (dt_orig : DataType),
        dt.name = concretizeName g args ∧
        tds.getByKey g = some (.dataType dt_orig) := by
  have hinit : DrainState.NewNameShape tds _ :=
    DrainState.NewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_NewNameShape _ _ hinit hdrain
  exact hfinal.2

/-- Helper: List.foldl with step = `IndexMap.insert` at `Typed.Function.name`
— every `f ∈ L` has its name in the resulting map. -/
private theorem list_foldl_insert_fn_containsKey
    (step : Typed.Decls → Typed.Function → Typed.Decls)
    (hstep_self : ∀ acc f, (step acc f).containsKey f.name)
    (hstep_mono : ∀ acc a f, acc.containsKey a → (step acc f).containsKey a) :
    ∀ (L : List Typed.Function) (init : Typed.Decls) f,
      f ∈ L → (L.foldl step init).containsKey f.name
  | [], _, _, h => by cases h
  | hd :: tl, init, f, hfmem => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hfmem with heq | hrest
    · subst heq
      have hinit' : (step init f).containsKey f.name := hstep_self init f
      have hpres : ∀ (L' : List Typed.Function) (acc : Typed.Decls),
          acc.containsKey f.name → (L'.foldl step acc).containsKey f.name := by
        intro L'
        induction L' with
        | nil => intros acc h; simpa using h
        | cons hd' tl' ih' =>
          intro acc hac
          simp only [List.foldl_cons]
          exact ih' (step acc hd') (hstep_mono _ _ _ hac)
      exact hpres tl (step init f) hinit'
    · exact list_foldl_insert_fn_containsKey step hstep_self hstep_mono tl (step init hd) f hrest

/-- Helper for Arrays. -/
private theorem array_foldl_insert_fn_containsKey
    (step : Typed.Decls → Typed.Function → Typed.Decls)
    (hstep_self : ∀ acc f, (step acc f).containsKey f.name)
    (hstep_mono : ∀ acc a f, acc.containsKey a → (step acc f).containsKey a)
    (xs : Array Typed.Function) (init : Typed.Decls) :
    ∀ f ∈ xs, (xs.foldl step init).containsKey f.name := by
  intro f hfmem
  rw [← Array.foldl_toList]
  have hfmem_list : f ∈ xs.toList := Array.mem_toList_iff.mpr hfmem
  exact list_foldl_insert_fn_containsKey step hstep_self hstep_mono xs.toList init f hfmem_list

/-- Generic `List.foldl` preserves `containsKey` for any already-contained key
when the step is IndexMap.insert-only. -/
private theorem list_foldl_containsKey_mono
    {γ : Type}
    (step : Typed.Decls → γ → Typed.Decls)
    (hmono : ∀ a acc c, acc.containsKey a → (step acc c).containsKey a) :
    ∀ (L : List γ) (init : Typed.Decls) a,
      init.containsKey a → (L.foldl step init).containsKey a
  | [], _, _, h => h
  | hd :: tl, init, a, hac => by
    simp only [List.foldl_cons]
    exact list_foldl_containsKey_mono step hmono tl (step init hd) a
      (hmono a init hd hac)

/-- Every `drained.newFunctions` name is in `cd`. -/
private theorem drain_newFn_in_cd
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ f ∈ drained.newFunctions, ∃ d, cd.getByKey f.name = some d := by
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · contradiction
  rename_i drained' hdrain'
  have hdrained_eq : drained = drained' := by
    have heq : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := ∅, mono := ∅,
          newFunctions := #[], newDataTypes := #[] } = .ok drained := hdrain
    rw [heq] at hdrain'
    exact Except.ok.inj hdrain'
  rw [← hdrained_eq] at hconc'
  let monoDecls : Typed.Decls := concretizeBuild tds drained.mono
    drained.newFunctions drained.newDataTypes
  have hstep4 : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc'
  intro f hfmem
  have hfn_in_mono : monoDecls.containsKey f.name := by
    show (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).containsKey f.name
    unfold concretizeBuild
    apply array_foldl_insert_fn_containsKey _ _ _ drained.newFunctions _ f hfmem
    · intro acc f'
      exact IndexMap.containsKey_insert_self _ _ _
    · intro acc a f' hac
      exact IndexMap.containsKey_insert_preserves _ _ _ _ hac
  have hfn_in_cd : cd.containsKey f.name := by
    have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hstep4
    exact (hkeys f.name).mp hfn_in_mono
  rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hfn_in_cd
  cases hget : cd.getByKey f.name with
  | none => exact absurd hget hfn_in_cd
  | some d => exact ⟨d, rfl⟩

/-- Every `drained.newDataTypes` name is in `cd`. -/
private theorem drain_newDt_in_cd
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    ∀ dt ∈ drained.newDataTypes, ∃ d, cd.getByKey dt.name = some d := by
  have hconc' := hconc
  unfold Typed.Decls.concretize at hconc'
  simp only [bind, Except.bind] at hconc'
  split at hconc'
  · contradiction
  rename_i drained' hdrain'
  have hdrained_eq : drained = drained' := by
    have heq : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := ∅, mono := ∅,
          newFunctions := #[], newDataTypes := #[] } = .ok drained := hdrain
    rw [heq] at hdrain'
    exact Except.ok.inj hdrain'
  rw [← hdrained_eq] at hconc'
  let monoDecls : Typed.Decls := concretizeBuild tds drained.mono
    drained.newFunctions drained.newDataTypes
  have hstep4 : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc'
  intro dt hdt_mem
  have array_foldl_mono : ∀ {γ : Type}
      (step : Typed.Decls → γ → Typed.Decls)
      (_ : ∀ acc a c, acc.containsKey a → (step acc c).containsKey a)
      (xs : Array γ) (init : Typed.Decls) (a : Global),
      init.containsKey a → (xs.foldl step init).containsKey a := by
    intro γ step hmono xs init a hac
    rw [← Array.foldl_toList]
    exact list_foldl_containsKey_mono step (fun a' acc c h' => hmono acc a' c h')
      xs.toList init a hac
  have hdt_in_mono : monoDecls.containsKey dt.name := by
    show (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).containsKey dt.name
    unfold concretizeBuild
    simp only
    apply array_foldl_mono _
      (fun acc a f hac => IndexMap.containsKey_insert_preserves _ _ _ _ hac)
    have hdt_list : dt ∈ drained.newDataTypes.toList := Array.mem_toList_iff.mpr hdt_mem
    let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt' =>
      let rewrittenCtors := dt'.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
      let newDt : DataType := { dt' with constructors := rewrittenCtors }
      let acc' := acc.insert dt'.name (.dataType newDt)
      rewrittenCtors.foldl
        (fun acc'' c =>
          let cName := dt'.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc'
    have dtStep_mono : ∀ (init : Typed.Decls) (dt' : DataType) (a : Global),
        init.containsKey a → (dtStep init dt').containsKey a := by
      intro init dt' a hac
      simp only [dtStep]
      apply list_foldl_containsKey_mono (γ := Constructor) _
        (fun _a _acc _c hac' => IndexMap.containsKey_insert_preserves _ _ _ _ hac')
      exact IndexMap.containsKey_insert_preserves _ _ _ _ hac
    have dtStep_self : ∀ (init : Typed.Decls) (dt' : DataType),
        (dtStep init dt').containsKey dt'.name := by
      intro init dt'
      simp only [dtStep]
      apply list_foldl_containsKey_mono (γ := Constructor) _
        (fun _a _acc _c hac' => IndexMap.containsKey_insert_preserves _ _ _ _ hac')
      exact IndexMap.containsKey_insert_self _ _ _
    rw [← Array.foldl_toList]
    revert hdt_list
    generalize (tds.pairs.foldl _ (default : Typed.Decls)) = src0
    generalize drained.newDataTypes.toList = L
    induction L generalizing src0 with
    | nil => intro h; cases h
    | cons hd tl ih =>
      intro hmem
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst heq
        have h_mid : (_ : Typed.Decls).containsKey dt.name := dtStep_self src0 dt
        exact list_foldl_containsKey_mono _ (fun a acc c hac => dtStep_mono acc c a hac)
          tl _ _ h_mid
      · exact ih _ hrest
  have hdt_in_cd : cd.containsKey dt.name := by
    have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hstep4
    exact (hkeys dt.name).mp hdt_in_mono
  rw [← IndexMap.getByKey_ne_none_iff_containsKey] at hdt_in_cd
  cases hget : cd.getByKey dt.name with
  | none => exact absurd hget hdt_in_cd
  | some d => exact ⟨d, rfl⟩

/-- The `hFresh` bridge. -/
private theorem hFresh_bridge
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hCtor : Typed.Decls.CtorIsKey tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    (∀ dt ∈ drained.newDataTypes,
      ∀ k dt' c, tds.getByKey k = some (.constructor dt' c) →
        dt.name ≠ dt'.name.pushNamespace c.nameHead) ∧
    (∀ f ∈ drained.newFunctions,
      ∀ k dt' c, tds.getByKey k = some (.constructor dt' c) →
        f.name ≠ dt'.name.pushNamespace c.nameHead) := by
  refine ⟨?_, ?_⟩
  · intro dt hdt_mem k dt' c hk_ctor hname_eq
    obtain ⟨g, args, dt_orig, hdt_name, hg_dt⟩ :=
      drain_newDataTypes_name_shape hdrain dt hdt_mem
    have hk_eq : k = dt'.name.pushNamespace c.nameHead := hCtor k dt' c
      (IndexMap.mem_pairs_of_getByKey _ _ _ hk_ctor)
    have hcn_eq_k : concretizeName g args = k := by
      rw [hk_eq, ← hdt_name]; exact hname_eq
    obtain ⟨d_at_dt, hd_at_dt⟩ := drain_newDt_in_cd hconc hdrain dt hdt_mem
    have hcn_empty : concretizeName k #[] = k := concretizeName_empty_args k
    have hcn_both : concretizeName g args = concretizeName k #[] := by
      rw [hcn_empty]; exact hcn_eq_k
    have hexists : ∃ d, cd.getByKey (concretizeName g args) = some d := by
      refine ⟨d_at_dt, ?_⟩
      rw [hdt_name] at hd_at_dt; exact hd_at_dt
    have := hunique hconc g k args #[] hcn_both hexists
    obtain ⟨hg_eq, _⟩ := this
    rw [hg_eq] at hg_dt
    rw [hg_dt] at hk_ctor
    cases hk_ctor
  · intro f hf_mem k dt' c hk_ctor hname_eq
    obtain ⟨g, args, f_orig, hf_name, hg_fn⟩ :=
      drain_newFunctions_name_shape hdrain f hf_mem
    have hk_eq : k = dt'.name.pushNamespace c.nameHead := hCtor k dt' c
      (IndexMap.mem_pairs_of_getByKey _ _ _ hk_ctor)
    have hcn_eq_k : concretizeName g args = k := by
      rw [hk_eq, ← hf_name]; exact hname_eq
    obtain ⟨d_at_f, hd_at_f⟩ := drain_newFn_in_cd hconc hdrain f hf_mem
    have hcn_empty : concretizeName k #[] = k := concretizeName_empty_args k
    have hcn_both : concretizeName g args = concretizeName k #[] := by
      rw [hcn_empty]; exact hcn_eq_k
    have hexists : ∃ d, cd.getByKey (concretizeName g args) = some d := by
      refine ⟨d_at_f, ?_⟩
      rw [hf_name] at hd_at_f; exact hd_at_f
    have := hunique hconc g k args #[] hcn_both hexists
    obtain ⟨hg_eq, _⟩ := this
    rw [hg_eq] at hg_fn
    rw [hg_fn] at hk_ctor
    cases hk_ctor

/-! ### Bridge derivations for `NewDtBridge` / `NewFnBridge`.

Ported from `NewBridgesScratch.lean` (2026-04-24). Derives the FullyMono-
implied structural correspondence of `drained.newDataTypes` /
`drained.newFunctions` to source `.dataType` / `.function` entries in
`tds`, via a strengthened drain invariant `StrongNewNameShape`.
-/

-- `DrainState.StrongNewNameShape` + `.init` moved to
-- `Ix/Aiur/Semantics/DrainInvariants.lean`.

private theorem concretizeDrainEntry_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · exact hinv.1 f' hin
          · subst heq
            exact ⟨entry.1, entry.2, f, rfl, hf_get, hsz.symm⟩
        · intro dt hdt
          exact hinv.2 dt hdt
      · simp [hsz] at hstep
    · rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, rfl, hdt_get, hsz.symm, ?_⟩
            rw [List.map_map]
            apply List.map_congr_left
            intro c _
            rfl
      · simp [hsz] at hstep
    · exact absurd hstep (by intro h; cases h)

private theorem concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.StrongNewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.StrongNewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.StrongNewNameShape decls :=
        concretizeDrainEntry_preserves_StrongNewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

private theorem concretizeDrainIter_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.StrongNewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_StrongNewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.StrongNewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.StrongNewNameShape decls := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.StrongNewNameShape decls :=
          concretizeDrainIter_preserves_StrongNewNameShape hinv hstate'
        exact ih state' hinv' hdrain

theorem newDtBridge_derive
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    NewDtBridge tds drained.newDataTypes := by
  intro dt hdt_mem
  have hinit : DrainState.StrongNewNameShape tds _ :=
    DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  obtain ⟨g, args, dt_orig, hname, hget, hargs_sz, hctors⟩ := hfinal.2 dt hdt_mem
  have hdt_orig_params :=
    typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts g dt_orig hget
  have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
  have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
  have hname_eq : dt.name = g := by
    rw [hname, hargs_empty]; exact concretizeName_empty_args g
  exact ⟨g, dt_orig, hget, hname_eq, hctors⟩

theorem newFnBridge_derive
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    NewFnBridge tds drained.newFunctions := by
  intro f hf_mem
  have hinit : DrainState.StrongNewNameShape tds _ :=
    DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
  have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  obtain ⟨g, args, f_orig, hname, hget, hargs_sz⟩ := hfinal.1 f hf_mem
  have hf_orig_params :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts g f_orig hget
  have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
  have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
  have hname_eq : f.name = g := by
    rw [hname, hargs_empty]; exact concretizeName_empty_args g
  exact ⟨g, f_orig, hget, hname_eq⟩

theorem concretize_produces_ctorPresent
    {t : Source.Toplevel} {tds : Typed.Decls} {decls : Source.Decls}
    {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hP : Typed.Decls.CtorPresent tds)
    (hDt : Typed.Decls.DtNameIsKey tds)
    (hCtor : Typed.Decls.CtorIsKey tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.CtorPresent cd := by
  -- Bridge pair-form to getByKey-form for the internal proof.
  have hP_byKey := TypedCtorPresentP_of_pairs hP
  have hDt_byKey := TypedDtNameIsKeyP_of_pairs hDt
  have hCtor_byKey := TypedCtorIsKeyP_of_pairs hCtor
  have hconc_orig : tds.concretize = .ok cd := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  rename_i drained _hdrain
  let monoDecls : Typed.Decls :=
    concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes
  -- Freshness: `drained.newDataTypes` / `drained.newFunctions` come from the
  -- drain's monomorphic-expansion; their names are `concretizeName g args`
  -- which under `hunique` cannot collide with source-present ctor keys.
  have hFresh := hFresh_bridge hCtor hunique hconc_orig _hdrain
  have hNewDt : NewDtBridge tds drained.newDataTypes :=
    newDtBridge_derive hmono hdecls hts _hdrain
  have hNewFn : NewFnBridge tds drained.newFunctions :=
    newFnBridge_derive hmono hdecls hts _hdrain
  have hP_mono : TypedCtorPresentP monoDecls :=
    concretizeBuild_ctorPresent hP_byKey hDt_byKey hCtor_byKey _ _ _
      hFresh.1 hFresh.2 hNewDt hNewFn
  -- DtNameIsKey in getByKey form on monoDecls.
  have hDt_mono : ∀ k dt, monoDecls.getByKey k = some (.dataType dt) → k = dt.name := by
    intro k dt hget
    have := concretizeBuild_dtNameIsKey hDt drained.mono drained.newFunctions drained.newDataTypes
    exact this k dt (IndexMap.mem_pairs_of_getByKey _ _ _ hget)
  have hCtor_mono : ∀ k dt c, monoDecls.getByKey k = some (.constructor dt c) →
      k = dt.name.pushNamespace c.nameHead := by
    intro k dt c hget
    exact concretizeBuild_ctorIsKey hCtor drained.mono drained.newFunctions drained.newDataTypes
      k dt c hget
  -- Lift step4Lower_preserves_ctorPresent output (ConcreteCtorPresentP) to pairs-form.
  have hconcP : ConcreteCtorPresentP cd :=
    step4Lower_preserves_ctorPresent hP_mono hDt_mono hCtor_mono hconc
  intro dtkey dt c hmem hc
  have hget : cd.getByKey dtkey = some (.dataType dt) :=
    IndexMap.getByKey_of_mem_pairs _ _ _ hmem
  obtain ⟨cc, hcget⟩ := hconcP dtkey dt c hget hc
  exact ⟨cc, IndexMap.mem_pairs_of_getByKey _ _ _ hcget⟩


/-- **Progress half** of `compile_correct`.

Every `WellFormed` source program produces a compilation output.

Takes `hFullyMono : FullyMonomorphic t` as a separate hypothesis (no longer
in `WellFormed` — see `WellFormed.lean` docstring). Internal monomorphism
machinery has not been generalized to per-entry yet; this is the
caller's obligation. -/
theorem Toplevel.compile_progress
    (t : Source.Toplevel) (hwf : WellFormed t) (hFullyMono : FullyMonomorphic t) :
    ∃ ct decls, t.mkDecls = .ok decls ∧ t.compile = .ok ct := by
  have hwf' := hwf
  obtain ⟨⟨decls, hdecls⟩, _, hmonoTerm, _, _, hNoColl, _⟩ := hwf
  obtain ⟨typedDecls, hts, concDecls, hconc⟩ := hmonoTerm
  have hacyclic := wellFormed_implies_noDirectDatatypeCycles hwf' hts
  have hunique : Typed.Decls.ConcretizeUniqueNames typedDecls := hNoColl typedDecls hts
  have htdna := checkAndSimplify_preserves_nameAgrees hts
  have hNameAgrees := concretize_nameAgrees htdna hconc
  -- hDtNameIsKey from `concretize_produces_dtNameIsKey` (getByKey form) bridged
  -- to pairs.toList form via `IndexMap.mem_iff_exists_pair_beq` + key-uniqueness.
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
  -- Source chain: checkAndSimplify_preserves_ctorPresent produces
  -- Typed.Decls.CtorPresent typedDecls. Bridge to getByKey form, then
  -- concretize_produces_ctorPresent yields ConcreteCtorPresentP concDecls.
  -- Finally bridge back to pairs.toList form for the Lower.compile_progress consumer.
  have htdCtorPresent := checkAndSimplify_preserves_ctorPresent hts
  have hCtorPresent : Concrete.Decls.CtorPresent concDecls :=
    concretize_produces_ctorPresent hFullyMono hdecls hts
      htdCtorPresent htdDt htdCtor hunique hconc
  obtain ⟨⟨bytecodeRaw, preNameMap⟩, hbc⟩ :=
    Lower.compile_progress hFullyMono hts hconc hacyclic hunique
      hNameAgrees hDtNameIsKey hCtorIsKey hCtorPresent htdDt htdCtorPresent
  obtain ⟨ct, hct⟩ := Source.Toplevel.compile_ok_of_stages hts hconc hbc
  exact ⟨ct, decls, hdecls, hct⟩

end Aiur

end
