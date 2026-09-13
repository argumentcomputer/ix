/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Std.AxiomAudit
import Ix.Theory.Named.Verify.Environment.IndexedVecOuterReplay

/-!
# Complete semantic replay of the IndexedVec normalization candidate

This module connects the exact executable family/`nil`/`cons` candidate
produced by `buildNormalizationCandidate` to its Theory generation
certificate and the E1 kernel-environment replay. Every retained candidate
node is interpreted in its exact pre-family or post-family verifier context;
the final transaction therefore consumes the certificate projected from the
same producer-selected package rather than an independently supplied
well-formedness proof.
-/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta
open Ix.Theory.Named.InductiveFixtures
open IndexedVecConsReplay

theorem indexedVecSemanticNatHasPrimitives : VEnv.HasPrimitives natFinalEnv := by
  have absent (n : Name) (hlookup : natFinalEnv.constants n = none) :
      ¬ natFinalEnv.contains n := by
    rintro ⟨ci, hci⟩
    rw [hlookup] at hci
    contradiction
  refine {
    bool := fun h => (absent ``Bool rfl h).elim
    boolFalse := fun h => by
      change none = some _ at h
      contradiction
    boolTrue := fun h => by
      change none = some _ at h
      contradiction
    nat := fun _ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    natZero := fun h => by
      change some natType.ctors[0].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natSucc := fun h => by
      change some natType.ctors[1].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natAdd := fun h => (absent ``Nat.add rfl h).elim
    natSub := fun h => (absent ``Nat.sub rfl h).elim
    natMul := fun h => (absent ``Nat.mul rfl h).elim
    natPow := fun h => (absent ``Nat.pow rfl h).elim
    natGcd := fun h => (absent ``Nat.gcd rfl h).elim
    natMod := fun h => (absent ``Nat.mod rfl h).elim
    natDiv := fun h => (absent ``Nat.div rfl h).elim
    natBEq := fun h => (absent ``Nat.beq rfl h).elim
    natBLE := fun h => (absent ``Nat.ble rfl h).elim
    natLAnd := fun h => (absent ``Nat.land rfl h).elim
    natLOr := fun h => (absent ``Nat.lor rfl h).elim
    natXor := fun h => (absent ``Nat.xor rfl h).elim
    natShiftLeft := fun h => (absent ``Nat.shiftLeft rfl h).elim
    natShiftRight := fun h => (absent ``Nat.shiftRight rfl h).elim
    charOfNat := fun h => by
      change none = some _ at h
      contradiction
    stringOfList := fun h => by
      change none = some _ at h
      contradiction }

theorem indexedVecSemanticNatSafePrimitives :
    indexedVecKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change natMap.find?' n = some ci at hfind
  rw [natMap_wf.find?'_eq_find?, natMap,
    natCtorMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp at hfind
    subst ci
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [natCtorMap, natZeroMap_wf.find?_insert] at hfind
    split at hfind
    · rename_i heq
      simp at heq
      subst n
      simp at hfind
      subst ci
      exact ⟨rfl, rfl⟩
    · rw [natZeroMap, natTypeMap_wf.find?_insert] at hfind
      split at hfind
      · rename_i heq
        simp at heq
        subst n
        simp at hfind
        subst ci
        exact ⟨rfl, rfl⟩
      · rw [natTypeMap,
          SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
          at hfind
        split at hfind
        · rename_i heq
          simp at heq
          subst n
          simp at hfind
          subst ci
          exact ⟨rfl, rfl⟩
        · simp [SMap.find?] at hfind

theorem indexedVecKernelEnv_noProjectionReady (name : Name) :
    indexedVecKernelEnv.isProjectionReadyStructure name = false := by
  simp only [indexedVecKernelEnv,
    Kernel.Environment.isProjectionReadyStructure,
    Kernel.Environment.ofConstants]
  simp only [natMap_wf.find?'_eq_find?]
  simp only [natMap, natCtorMap_wf.find?_insert]
  simp only [natCtorMap, natZeroMap_wf.find?_insert]
  simp only [natZeroMap, natTypeMap_wf.find?_insert]
  simp only [natTypeMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hRec : ``Nat.rec = name
  · subst name
    simp [natRecInfo]
  · by_cases hSucc : ``Nat.succ = name
    · subst name
      simp [hRec, natSuccInfo]
    · by_cases hZero : ``Nat.zero = name
      · subst name
        simp [hRec, hSucc, natZeroInfo]
      · by_cases hNat : ``Nat = name
        · subst name
          simp [hRec, hSucc, hZero, natInfo]
        · simp [hRec, hSucc, hZero, hNat, SMap.find?]

theorem indexedVecKernelEnv_noStructureEta (name : Name) :
    indexedVecKernelEnv.isNonRecStructure name = false := by
  simp only [indexedVecKernelEnv, Kernel.Environment.isNonRecStructure,
    Kernel.Environment.ofConstants, Kernel.Environment.find?]
  simp only [natMap_wf.find?'_eq_find?]
  simp only [natMap, natCtorMap_wf.find?_insert]
  simp only [natCtorMap, natZeroMap_wf.find?_insert]
  simp only [natZeroMap, natTypeMap_wf.find?_insert]
  simp only [natTypeMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hRec : ``Nat.rec = name
  · subst name
    simp [natRecInfo]
  · by_cases hSucc : ``Nat.succ = name
    · subst name
      simp [hRec, natSuccInfo]
    · by_cases hZero : ``Nat.zero = name
      · subst name
        simp [hRec, hSucc, natZeroInfo]
      · by_cases hNat : ``Nat = name
        · subst name
          simp [hRec, hSucc, hZero, natInfo]
        · simp [hRec, hSucc, hZero, hNat, SMap.find?]

theorem indexedVecTypeEnv_noProjectionReady (name : Name) :
    ctorContext.env.isProjectionReadyStructure name = false := by
  simp only [ctorContext, ctorEnv,
    Kernel.Environment.isProjectionReadyStructure,
    Kernel.Environment.ofConstants]
  simp only [indexedVecTypeMap_wf.find?'_eq_find?]
  simp only [indexedVecTypeMap, natMap_wf.find?_insert]
  simp only [natMap, natCtorMap_wf.find?_insert]
  simp only [natCtorMap, natZeroMap_wf.find?_insert]
  simp only [natZeroMap, natTypeMap_wf.find?_insert]
  simp only [natTypeMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hVec : ``IndexedVec = name
  · subst name
    simp [indexedVecInfo]
  · by_cases hRec : ``Nat.rec = name
    · subst name
      simp [hVec, natRecInfo]
    · by_cases hSucc : ``Nat.succ = name
      · subst name
        simp [hVec, hRec, natSuccInfo]
      · by_cases hZero : ``Nat.zero = name
        · subst name
          simp [hVec, hRec, hSucc, natZeroInfo]
        · by_cases hNat : ``Nat = name
          · subst name
            simp [hVec, hRec, hSucc, hZero, natInfo]
          · simp [hVec, hRec, hSucc, hZero, hNat, SMap.find?]

theorem indexedVecTypeEnv_noStructureEta (name : Name) :
    ctorContext.env.isNonRecStructure name = false := by
  simp only [ctorContext, ctorEnv, Kernel.Environment.isNonRecStructure,
    Kernel.Environment.ofConstants, Kernel.Environment.find?]
  simp only [indexedVecTypeMap_wf.find?'_eq_find?]
  simp only [indexedVecTypeMap, natMap_wf.find?_insert]
  simp only [natMap, natCtorMap_wf.find?_insert]
  simp only [natCtorMap, natZeroMap_wf.find?_insert]
  simp only [natZeroMap, natTypeMap_wf.find?_insert]
  simp only [natTypeMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hVec : ``IndexedVec = name
  · subst name
    simp [indexedVecInfo]
  · by_cases hRec : ``Nat.rec = name
    · subst name
      simp [hVec, natRecInfo]
    · by_cases hSucc : ``Nat.succ = name
      · subst name
        simp [hVec, hRec, natSuccInfo]
      · by_cases hZero : ``Nat.zero = name
        · subst name
          simp [hVec, hRec, hSucc, natZeroInfo]
        · by_cases hNat : ``Nat = name
          · subst name
            simp [hVec, hRec, hSucc, hZero, natInfo]
          · simp [hVec, hRec, hSucc, hZero, hNat, SMap.find?]

private theorem addConst_constants {env env' : VEnv} {name : Name}
    {ci : VConstant} (hadd : env.addConst name ci = some env') (query : Name) :
    env'.constants query =
      if name = query then some ci else env.constants query := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  rfl

private theorem structureView_nparams_eq_zero_of_nat
    {env : VEnv} {view : VStructureView} (hview : view.WF env)
    (hname : ``Nat = view.name)
    (hNat : env.constants ``Nat = some natType.toVConstant) :
    view.nparams = 0 := by
  have hfamily := hview.family
  rw [← hname, hNat] at hfamily
  have hsourceType : view.generation.block.sourceType.type = natType.type :=
    congrArg VConstant.type (Option.some.inj hfamily).symm
  have hshape := view.generation.shape_eq
  simp only [VInductDecl.NormalizedChecked.generationShape, Bool.and_eq_true,
    beq_iff_eq] at hshape
  have hrawParamsLength := hshape.1.1.1.1.1
  have hNatType : natType.type = .sort (.succ .zero) := rfl
  rw [VInductDecl.NormalizedChecked.rawParams, hsourceType,
    hNatType] at hrawParamsLength
  cases hnp : view.source.nparams with
  | zero => simpa using hnp
  | succ _ =>
    rw [hnp] at hrawParamsLength
    simp [VExpr.telN] at hrawParamsLength

private theorem natFinalEnv_structureView_nparams_eq_zero
    {view : VStructureView} (hview : view.WF natFinalEnv) :
    view.nparams = 0 := by
  have hrec := hview.recursor
  change natRecEnv.constants view.recursorName =
    some view.generation.recursor at hrec
  rw [addConst_constants
      (show natCtorEnv.addConst ``Nat.rec
        (VInductDecl.recConst 0 ``Nat 0 natType) = some natRecEnv from rfl),
    addConst_constants
      (show natZeroEnv.addConst natType.ctors[1].name
        natType.ctors[1].toVConstant = some natCtorEnv from rfl),
    addConst_constants
      (show natTypeEnv.addConst natType.ctors[0].name
        natType.ctors[0].toVConstant = some natZeroEnv from rfl),
    addConst_constants
      (show VEnv.empty.addConst natType.name natType.toVConstant =
        some natTypeEnv from rfl)] at hrec
  have hNatName : natType.name = ``Nat := rfl
  have hZeroName : natType.ctors[0].name = ``Nat.zero := rfl
  have hSuccName : natType.ctors[1].name = ``Nat.succ := rfl
  rw [hNatName, hZeroName, hSuccName] at hrec
  simp [VEnv.empty, VStructureView.recursorName] at hrec
  exact structureView_nparams_eq_zero_of_nat hview hrec.1
    nat_type_env_lookup

private theorem indexedVecTypeEnv_structureView_nparams_eq_zero
    {view : VStructureView} (hview : view.WF indexedVecTypeEnv) :
    view.nparams = 0 := by
  have hrec := hview.recursor
  rw [addConst_constants
      (show natFinalEnv.addConst indexedVecType.name
        indexedVecType.toVConstant = some indexedVecTypeEnv from rfl)] at hrec
  change (if indexedVecType.name = view.recursorName then
      some indexedVecType.toVConstant else
      natRecEnv.constants view.recursorName) =
    some view.generation.recursor at hrec
  rw [addConst_constants
      (show natCtorEnv.addConst ``Nat.rec
        (VInductDecl.recConst 0 ``Nat 0 natType) = some natRecEnv from rfl),
    addConst_constants
      (show natZeroEnv.addConst natType.ctors[1].name
        natType.ctors[1].toVConstant = some natCtorEnv from rfl),
    addConst_constants
      (show natTypeEnv.addConst natType.ctors[0].name
        natType.ctors[0].toVConstant = some natZeroEnv from rfl),
    addConst_constants
      (show VEnv.empty.addConst natType.name natType.toVConstant =
        some natTypeEnv from rfl)] at hrec
  have hVecName : indexedVecType.name = ``IndexedVec := rfl
  have hNatName : natType.name = ``Nat := rfl
  have hZeroName : natType.ctors[0].name = ``Nat.zero := rfl
  have hSuccName : natType.ctors[1].name = ``Nat.succ := rfl
  rw [hVecName, hNatName, hZeroName, hSuccName] at hrec
  simp [VEnv.empty, VStructureView.recursorName] at hrec
  exact structureView_nparams_eq_zero_of_nat hview hrec.1 rfl

private theorem natMap_constructor_numParams
    {view : VStructureView} {info : ConstructorVal}
    (hzero : view.nparams = 0)
    (hfind : natMap.find? view.constructorName = some (.ctorInfo info)) :
    info.numParams = view.nparams := by
  rw [natMap, natCtorMap_wf.find?_insert] at hfind
  split at hfind
  · cases hfind
  · rw [natCtorMap, natZeroMap_wf.find?_insert] at hfind
    split at hfind
    · simp [natSuccInfo] at hfind
      cases hfind
      exact hzero.symm
    · rw [natZeroMap, natTypeMap_wf.find?_insert] at hfind
      split at hfind
      · simp [natZeroInfo] at hfind
        cases hfind
        exact hzero.symm
      · rw [natTypeMap,
          SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
          at hfind
        split at hfind
        · cases hfind
        · simp [SMap.find?] at hfind

def indexedVecSemanticNatVEnvs : VEnvs where
  venv _ := natFinalEnv

theorem indexedVecSemanticNatVEnvsWF : indexedVecSemanticNatVEnvs.WF indexedVecKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ natMap false natFinalEnv
    exact nat_trEnv'
  hasPrimitives := indexedVecSemanticNatHasPrimitives
  safePrimitives := indexedVecSemanticNatSafePrimitives
  mono := fun _ => .rfl
  projectionReady := {
    infer := by
      intro name _info _hfind hready
      rw [indexedVecKernelEnv_noProjectionReady] at hready
      contradiction
    constructorNumParams := by
      intro view info hview hfind
      change natMap.find?' view.constructorName =
        some (.ctorInfo info) at hfind
      rw [natMap_wf.find?'_eq_find?] at hfind
      exact natMap_constructor_numParams
        (natFinalEnv_structureView_nparams_eq_zero hview) hfind }
  structureEtaReady := StructureEtaReady.of_no_nonRecStructure
    indexedVecKernelEnv_noStructureEta

def indexedVecSemanticAddType :
    AddInductConstant .induct natMap natFinalEnv
      indexedVecType.toVConstVal indexedVecTypeMap indexedVecTypeEnv where
  info := indexedVecInfo
  kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
  tr := indexedVecInfo_tr
  map_fresh := by simpa [indexedVecType] using indexedVecType_fresh
  env_add := rfl
  map_add := rfl

theorem indexedVecSemanticFamilyPrefixNe :
    indexedVecFamilyCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedVecSemanticFamilyContextRun :
    TypeChecker.CandidateContextRun indexedVecFamilyCandidateContext :=
  TypeChecker.CandidateContextRun.root indexedVecSemanticNatVEnvsWF rfl
    indexedVecSemanticFamilyPrefixNe

theorem indexedVecSemanticFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedVecInfo.type indexedVecType.type :=
  indexedVecInfo_tr.1.2.2

def indexedVecPreFamilyStage :
    TypeChecker.CandidateSemanticStage indexedVecFamilyCandidateContext
      natFinalEnv [`u] where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

def indexedVecFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      indexedVecKernelType indexedVecFamilyCandidate.trace where
  nparams := 1
  resultLevel := .succ (.param `u)
  stats := indexedVecCandidateInductiveStats
  stats_eq := rfl
  terminal_eq := indexedVecFamilyCandidate_terminalResult
  run := indexedVec_checkInductiveTypes

def indexedVecFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecFamilyListCandidate.familyType indexedVecType
      indexedVecPreFamilyStage where
  name_eq := rfl
  uvars_eq := rfl
  type := {
    context_eq := rfl
    source_tr := indexedVecSemanticFamilySourceTr
    whnfFuel := 9999
    whnfDepth := rfl }
  validation := indexedVecFamilyValidationRun
  typeEnv := indexedVecTypeEnv
  addInduct := indexedVecSemanticAddType
  projectionReady := {
    infer := by
      intro name _info _hfind hready
      rw [indexedVecTypeEnv_noProjectionReady] at hready
      contradiction
    constructorNumParams := by
      intro view info hview hfind
      change indexedVecTypeMap.find?' view.constructorName =
        some (.ctorInfo info) at hfind
      rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
        natMap_wf.find?_insert] at hfind
      split at hfind
      · cases hfind
      · exact natMap_constructor_numParams
          (indexedVecTypeEnv_structureView_nparams_eq_zero hview) hfind }
  structureEtaReady := StructureEtaReady.of_no_nonRecStructure
    indexedVecTypeEnv_noStructureEta
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := rfl
  name_not_reflected := by decide
  name_not_primitive := by
    simp [indexedVecType, Kernel.Environment.primitives,
      NameSet.ofList]
    simp +decide [NameSet.contains]

def indexedVecSemanticCtorContextRun :
    TypeChecker.CandidateContextRun ctorContext :=
  indexedVecFamilyStage.postContextRun

theorem indexedVecSemanticNilSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecNilInfo.type
      indexedVecType.ctors[0].type :=
  indexedVecNilInfo_tr.1.2.2

theorem indexedVecSemanticConsIsType :
    indexedVecTypeEnv.IsType 1 [] indexedVecType.ctors[1].type := by
  have hwf :=
    (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
      nat_env_wf.ordered
  have hctor := hwf.rawCtor_isType (envT := indexedVecTypeEnv) rfl
    (ctor := indexedVecChecked.identityGeneration.block.ctorPairs[1])
    (by simp)
  simpa only [
    show indexedVecDecl.uvars = 1 by rfl,
    show indexedVecChecked.identityGeneration.block.ctorPairs[1].raw.type =
      indexedVecType.ctors[1].type by rfl] using hctor

theorem indexedVecSemanticConsSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecConsInfo.type
      indexedVecType.ctors[1].type := by
  have hshape : TrTypeExpr indexedVecTypeEnv [`u] []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

def indexedVecStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  staged := {
    raw := indexedVecType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := indexedVecPreFamilyStage
    family := indexedVecFamilyStage
    validation_nparams_eq := rfl
    constructorValidation :=
      AddInductive.ConstructorValidationRun.of_run
        indexedVecValidationCheckConstructors
    constructors := .cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := indexedVecSemanticNilSourceTr
        whnfFuel := 9999
        whnfDepth := rfl } } (.cons {
      name_eq := rfl
      uvars_eq := rfl
      type := {
        context_eq := rfl
        source_tr := indexedVecSemanticConsSourceTr
        whnfFuel := 9999
        whnfDepth := rfl } } .nil)
    familyTypesProduced := indexedVecFamilyTypeListProduced
    familiesProduced := indexedVecFamilyListProduced }
  universeRun := indexedVecValidationCheckConstructorUniverseSemantics

/-- Generic automatic assembly joins the arbitrary-length operational list
witnesses to the complete retained semantic hierarchy for the two-constructor
fixture.  No expected normalized view is an input to this theorem. -/
theorem indexedVecProducedSemanticHierarchy_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidateSemanticRun
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl) :=
  indexedVecStagedUniverseInput.exists

/-- The automatically assembled hierarchy retains both constructor headers in
the producer's `nil`/`cons` source order.  This inspects the semantic result,
not the separately constructed concrete replay below. -/
theorem indexedVecProducedSemanticHierarchy_constructorHeaders :
    ∃ run : VInductDecl.ProducedNormalizationCandidateSemanticRun
        indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
        indexedVecNormalizationCandidate indexedVecDecl,
      VInductDecl.sameCtorHeaders indexedVecType.ctors
        run.semantic.family.root.constructors.views = true := by
  obtain ⟨run⟩ := indexedVecProducedSemanticHierarchy_exists
  have hraw : run.semantic.raw = indexedVecType := by
    have htypes : [indexedVecType] = [run.semantic.raw] := by
      simpa [indexedVecDecl] using run.semantic.raw_types_eq
    injection htypes with h
    exact h.symm
  exact ⟨run, by
    simpa only [hraw] using
      run.semantic.family.root.constructors.sameHeaders⟩

/-! ## Post-family constructor alignment -/

private theorem indexedVecValidationSortCheckTypeM (lctx : LocalContext) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    checkLevelSuccParam, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

private def indexedVecValidationZeroState (alphaId : FVarId) :
    TypeChecker.State :=
  replayInsert (validationFirstAppState alphaId)
    (.const ``Nat.zero []) (.const ``Nat [])

private def indexedVecValidationZeroFinalState (alphaId : FVarId) :
    TypeChecker.State :=
  replayInsert (indexedVecValidationZeroState alphaId)
    (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero []))
    (.sort (.succ (.param `u)))

private theorem indexedVecValidationZeroCheckTypeM
    (lctx : LocalContext) (alphaId : FVarId)
    (halpha : lctx.find? alphaId = some (.cdecl alphaIndex alphaId
      alphaName (.sort (.succ (.param `u))) alphaBi alphaKind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType
        (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero []))) =
      .ok (.sort (.succ (.param `u))) := by
  have hfirst :
      TypeChecker.Inner.inferType' (replayFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (vecFamilyTail, validationFirstAppState alphaId) := by
    simpa [validationFirstAppState] using
      (replayInferFirstAppFVarCore 9999 lctx
        ({} : TypeChecker.State) alphaId
        (by simp)
        (by simp [replayInsert])
        (by simp [replayFirstApp]) halpha)
  have hzero :
      TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        (validationFirstAppState alphaId) =
      .ok (.const ``Nat [], indexedVecValidationZeroState alphaId) := by
    simpa [indexedVecValidationZeroState, replayInsert] using
      (inferTypeZeroCore 9999 lctx (validationFirstAppState alphaId)
        (by simp [validationFirstAppState, replayInsert,
          replayFirstApp]))
  have hresult :
      TypeChecker.Inner.inferType'
        (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero [])) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.param `u)),
        indexedVecValidationZeroFinalState alphaId) := by
    simpa [indexedVecValidationZeroFinalState] using
      (replayInferIndexedVecAppCore 9999 lctx
        ({} : TypeChecker.State) (validationFirstAppState alphaId)
        (indexedVecValidationZeroState alphaId) (.fvar alphaId)
        (.const ``Nat.zero [])
        (by simp [ctorIndexedVecApp, Expr.hasLooseBVars,
          Expr.looseBVarRange'])
        (by simp [ctorIndexedVecApp])
        hfirst hzero (by rfl))
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId) (.const ``Nat.zero [])) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [hresult]
  rfl

private def indexedVecValidationSuccState
    (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert
    (replayInsert
      (replayInsert (validationFirstAppState alphaId)
        (.const ``Nat.succ [])
        (.forallE `n (.const ``Nat []) (.const ``Nat []) .default))
      (.fvar nId) (.const ``Nat []))
    (replaySuccApp (.fvar nId)) (.const ``Nat [])

private def indexedVecValidationSuccFinalState
    (alphaId nId : FVarId) : TypeChecker.State :=
  replayInsert (indexedVecValidationSuccState alphaId nId)
    (ctorIndexedVecApp (.fvar alphaId) (replaySuccApp (.fvar nId)))
    (.sort (.succ (.param `u)))

private theorem indexedVecValidationSuccCheckTypeM
    (lctx : LocalContext) (alphaId nId : FVarId)
    (hne : alphaId ≠ nId)
    (halpha : lctx.find? alphaId = some (.cdecl alphaIndex alphaId
      alphaName (.sort (.succ (.param `u))) alphaBi alphaKind))
    (hn : lctx.find? nId = some (.cdecl nIndex nId nName
      (.const ``Nat []) nBi nKind)) :
    TypeChecker.M.run ctorEnv .safe lctx [`u] ({} : FuelConfig)
      (TypeChecker.checkType
        (ctorIndexedVecApp (.fvar alphaId)
          (replaySuccApp (.fvar nId)))) =
      .ok (.sort (.succ (.param `u))) := by
  have hfirst :
      TypeChecker.Inner.inferType' (replayFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (vecFamilyTail, validationFirstAppState alphaId) := by
    simpa [validationFirstAppState] using
      (replayInferFirstAppFVarCore 9999 lctx
        ({} : TypeChecker.State) alphaId
        (by simp)
        (by simp [replayInsert])
        (by simp [replayFirstApp]) halpha)
  have hsucc :
      TypeChecker.Inner.inferType' (replaySuccApp (.fvar nId)) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        (validationFirstAppState alphaId) =
      .ok (.const ``Nat [], indexedVecValidationSuccState alphaId nId) := by
    simpa [indexedVecValidationSuccState] using
      (replayInferSuccFVarCore 9999 lctx
        (validationFirstAppState alphaId) nId
        (by simp [validationFirstAppState, replayInsert,
          replayFirstApp])
        (by
          simp only [validationFirstAppState, replayInsert,
            Std.HashMap.getElem?_insert]
          rw [constBeqFVar]
          rw [show (replayFirstApp (.fvar alphaId) ==
              (.fvar nId : Expr)) = false by
            simp [replayFirstApp]]
          rw [show ((.fvar alphaId : Expr) == .fvar nId) = false by
            change Expr.eqv (.fvar alphaId) (.fvar nId) = false
            rw [Expr.eqv_eq]
            simp [Expr.eqv', hne]]
          rw [constBeqFVar]
          simp)
        (by simp [validationFirstAppState, replayInsert,
          replaySuccApp])
        hn)
  have hresult :
      TypeChecker.Inner.inferType'
        (ctorIndexedVecApp (.fvar alphaId)
          (replaySuccApp (.fvar nId))) false
        (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
        ({} : TypeChecker.State) =
      .ok (.sort (.succ (.param `u)),
        indexedVecValidationSuccFinalState alphaId nId) := by
    simpa [indexedVecValidationSuccFinalState] using
      (replayInferIndexedVecAppCore 9999 lctx
        ({} : TypeChecker.State) (validationFirstAppState alphaId)
        (indexedVecValidationSuccState alphaId nId) (.fvar alphaId)
        (replaySuccApp (.fvar nId))
        (by simp [ctorIndexedVecApp, replaySuccApp,
          Expr.hasLooseBVars, Expr.looseBVarRange'])
        (by simp [ctorIndexedVecApp, replaySuccApp])
        hfirst hsucc (by rfl))
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (ctorIndexedVecApp (.fvar alphaId)
        (replaySuccApp (.fvar nId))) false
      (TypeChecker.Methods.withFuel 9999) (tcContext lctx)
      ({} : TypeChecker.State)) = _
  rw [hresult]
  rfl

private theorem indexedVecValidationHeadContextFresh :
    indexedVecValidationHeadContext.lctx.find?
      indexedVecValidationHeadContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecValidationHeadContext.freshFVarId)
    indexedVecValidationHeadContextWF
  rw [h]
  simp only [indexedVecValidationHeadContext,
    indexedVecValidationNContext, indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext,
    indexedVecFamilyCandidateContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList,
    LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp +decide

private theorem indexedVecValidationAlphaFindInTail :
    indexedVecValidationTailContext.lctx.find?
        indexedVecValidationAlphaId =
      some (.cdecl 0 indexedVecValidationAlphaId
        indexedVecValidationParamName
        (.sort (.succ (.param `u))) .default .default) := by
  have hfresh := indexedVecValidationHeadContextFresh
  have hne : indexedVecValidationAlphaId ≠
      indexedVecValidationTailId := by
    change indexedVecValidationAlphaId ≠
      indexedVecValidationHeadContext.freshFVarId
    intro heq
    rw [← heq] at hfresh
    rw [indexedVecValidationAlphaFindInHead] at hfresh
    contradiction
  have h := localContextFindOld
    (lctx := indexedVecValidationHeadContext.lctx)
    (oldId := indexedVecValidationAlphaId)
    (newId := indexedVecValidationTailId)
    (newName := consTailName)
    (newType := ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 0 indexedVecValidationAlphaId
      indexedVecValidationParamName (.sort (.succ (.param `u)))
      .default .default)
    indexedVecValidationHeadContextWF
    hfresh hne
    indexedVecValidationAlphaFindInHead
  simpa [indexedVecValidationTailContext,
    indexedVecValidationTailId,
    AddInductive.Context.pushLocalDecl] using h

private theorem indexedVecValidationNFindInTail :
    indexedVecValidationTailContext.lctx.find?
        indexedVecValidationNId =
      some (.cdecl 2 indexedVecValidationNId consNName
        (.const ``Nat []) .implicit .default) := by
  have hfresh := indexedVecValidationHeadContextFresh
  have hne : indexedVecValidationNId ≠
      indexedVecValidationTailId := by
    change indexedVecValidationNId ≠
      indexedVecValidationHeadContext.freshFVarId
    intro heq
    rw [← heq] at hfresh
    rw [indexedVecValidationNFindInHead] at hfresh
    contradiction
  have h := localContextFindOld
    (lctx := indexedVecValidationHeadContext.lctx)
    (oldId := indexedVecValidationNId)
    (newId := indexedVecValidationTailId)
    (newName := consTailName)
    (newType := ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)
    (newBi := .default) (newKind := .default)
    (oldDecl := .cdecl 2 indexedVecValidationNId consNName
      (.const ``Nat []) .implicit .default)
    indexedVecValidationHeadContextWF
    hfresh hne
    indexedVecValidationNFindInHead
  simpa [indexedVecValidationTailContext,
    indexedVecValidationTailId,
    AddInductive.Context.pushLocalDecl] using h

private theorem indexedVecValidationSortCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext,
        .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  exact indexedVecValidationSortCheckTypeM
    indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationNatCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext, .const ``Nat [],
        .sort (.succ .zero)⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.const ``Nat [])) = _
  exact ctorNatCheckTypeM indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationAlphaCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationNContext, indexedVecValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationNContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType (.fvar indexedVecValidationAlphaId)) = _
  exact ctorFVarCheckTypeM indexedVecValidationNContext.lctx
    indexedVecValidationAlphaId (.sort (.succ (.param `u)))
    indexedVecValidationAlphaFindInN

private theorem indexedVecValidationTailCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationHeadContext,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationHeadContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (.fvar indexedVecValidationNId))) = _
  exact ctorIndexedVecFVarCheckTypeM
    indexedVecValidationHeadContext.lctx
    indexedVecValidationAlphaId indexedVecValidationNId
    indexedVecValidationAlphaNeN indexedVecValidationAlphaFindInHead
    indexedVecValidationNFindInHead

private theorem indexedVecValidationNilResultCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecCtorValidationContext, indexedVecValidationNilResult,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (.const ``Nat.zero []))) = _
  exact indexedVecValidationZeroCheckTypeM
    indexedVecCtorValidationContext.lctx indexedVecValidationAlphaId
    indexedVecValidationAlphaFind

private theorem indexedVecValidationConsResultCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨indexedVecValidationTailContext, indexedVecValidationConsResult,
        .sort (.succ (.param `u))⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationTailContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.checkType
      (ctorIndexedVecApp (.fvar indexedVecValidationAlphaId)
        (replaySuccApp (.fvar indexedVecValidationNId)))) = _
  exact indexedVecValidationSuccCheckTypeM
    indexedVecValidationTailContext.lctx
    indexedVecValidationAlphaId indexedVecValidationNId
    indexedVecValidationAlphaNeN
    indexedVecValidationAlphaFindInTail
    indexedVecValidationNFindInTail

private def indexedVecCheckedOfValid
    (context : AddInductive.Context) (source inferred : Expr)
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (valid : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    AddInductive.ConstructorCheckedExpr context source :=
  .ofRun fvars valid

private def indexedVecValidationSortChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      (.sort (.succ (.param `u))) :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [FVarsIn, Level.hasMVar'])
    indexedVecValidationSortCheckValid

private def indexedVecValidationNatChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      (.const ``Nat []) :=
  indexedVecCheckedOfValid _ _ _ (by simp [FVarsIn])
    indexedVecValidationNatCheckValid

private def indexedVecValidationAlphaChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationNContext
      indexedVecValidationAlpha :=
  indexedVecCheckedOfValid _ _ _ (by
    change (indexedVecValidationNContext.lctx.find?
      indexedVecValidationAlphaId).isSome = true
    rw [indexedVecValidationAlphaFindInN]
    rfl)
    indexedVecValidationAlphaCheckValid

private def indexedVecValidationTailChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [ctorIndexedVecApp, indexedVecValidationAlpha,
      indexedVecValidationNExpr, AddInductive.Context.freshExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationAlphaId).isSome = true
      rw [indexedVecValidationAlphaFindInHead]
      rfl
    · change (indexedVecValidationHeadContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [indexedVecValidationNFindInHead]
      rfl)
    indexedVecValidationTailCheckValid

private def indexedVecValidationNilResultChecked :
    AddInductive.ConstructorCheckedExpr indexedVecCtorValidationContext
      indexedVecValidationNilResult :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [indexedVecValidationNilResult, ctorIndexedVecApp,
      indexedVecValidationAlpha,
      AddInductive.Context.freshExpr, FVarsIn, Level.hasMVar']
    change (indexedVecCtorValidationContext.lctx.find?
      indexedVecValidationAlphaId).isSome = true
    rw [indexedVecValidationAlphaFind]
    rfl)
    indexedVecValidationNilResultCheckValid

private def indexedVecValidationConsResultChecked :
    AddInductive.ConstructorCheckedExpr indexedVecValidationTailContext
      indexedVecValidationConsResult :=
  indexedVecCheckedOfValid _ _ _ (by
    simp [indexedVecValidationConsResult, ctorIndexedVecApp,
      replaySuccApp, indexedVecValidationAlpha,
      indexedVecValidationNExpr, AddInductive.Context.freshExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (indexedVecValidationTailContext.lctx.find?
        indexedVecValidationAlphaId).isSome = true
      rw [indexedVecValidationAlphaFindInTail]
      rfl
    · change (indexedVecValidationTailContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [indexedVecValidationNFindInTail]
      rfl)
    indexedVecValidationConsResultCheckValid

private theorem indexedVecStagedStats_eq :
    indexedVecStagedUniverseInput.staged.family.validation.stats =
      indexedVecCandidateInductiveStats := rfl

private theorem indexedVecValidationPostContext_eq :
    { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
      env := ctorContext.env } = indexedVecCtorValidationContext := rfl

private def indexedVecTransportValidationTrace
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx fuel := by
  subst context'
  subst source'
  exact trace

private def indexedVecTransportViewAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (indexedVecTransportValidationTrace context_eq source_eq trace)
      view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  exact alignment

@[simp] private theorem indexedVecTransportValidationTrace_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (indexedVecTransportValidationTrace context_eq source_eq trace).spineLength =
      trace.spineLength := by
  subst context'
  subst source'
  rfl

private theorem indexedVecValidationNatWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecCtorValidationContext, .const ``Nat [],
        .const ``Nat []⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecCtorValidationContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf (.const ``Nat [])) = .ok (.const ``Nat [])
  exact ctorNatWhnfM indexedVecCtorValidationContext.lctx

private theorem indexedVecValidationAlphaWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecValidationNContext, indexedVecValidationAlpha,
        indexedVecValidationAlpha⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationNContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf (.fvar indexedVecValidationAlphaId)) =
      .ok (.fvar indexedVecValidationAlphaId)
  exact ctorFVarWhnfM indexedVecValidationNContext.lctx
    indexedVecValidationAlphaId indexedVecValidationAlphaFindInN

private theorem indexedVecValidationTailWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨indexedVecValidationHeadContext,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr,
        ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr⟩ := by
  change TypeChecker.M.run ctorEnv .safe
    indexedVecValidationHeadContext.lctx [`u] ({} : FuelConfig)
    (TypeChecker.whnf
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)) =
      .ok (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
  exact ctorIndexedVecWhnfM indexedVecValidationHeadContext.lctx
    indexedVecValidationAlpha indexedVecValidationNExpr

private theorem indexedVecCandidateWhnfResult_eq
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (other : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, result⟩) :
    result = source := by
  unfold AddInductive.CandidateWhnfStep.Valid at self other
  rw [self] at other
  exact (Except.ok.inj other).symm

private def indexedVecValidationNatPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 1 indexedVecCtorValidationContext
      (.const ``Nat [])) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          subst result
          exact .absent indexedVecValidationNatChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationNatWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq,
            indexedVecValidationNatHasNoIndOcc] at occurs
          contradiction

private def indexedVecValidationAlphaPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 2 indexedVecValidationNContext
      indexedVecValidationAlpha) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          subst result
          exact .absent indexedVecValidationAlphaChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [indexedVecValidationAlphaShape, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationAlphaWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq] at occurs
          change AddInductive.hasIndOcc
            indexedVecCandidateInductiveStats.indConsts
              indexedVecValidationAlpha = true at occurs
          rw [indexedVecValidationAlphaHasNoIndOcc] at occurs
          contradiction

private def indexedVecValidationTailPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false
      indexedVecKernelCons.name 3 indexedVecValidationHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          subst result
          rw [indexedVecStagedStats_eq] at occurs
          change AddInductive.hasIndOcc
            indexedVecCandidateInductiveStats.indConsts
              (ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr) = false at occurs
          rw [indexedVecValidationTailHasIndOcc] at occurs
          contradiction
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [ctorIndexedVecApp, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := indexedVecCandidateWhnfResult_eq
            indexedVecValidationTailWhnfSelf whnf
          subst result
          exact .target indexedVecValidationTailChecked

private def indexedVecValidationNatAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecCtorValidationContext (.const ``Nat [])
        (.const ``Nat []) :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecCtorValidationContext
    (.const ``Nat [])⟩

private def indexedVecValidationAlphaAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecValidationNContext indexedVecValidationAlpha
        indexedVecValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecValidationNContext
    indexedVecValidationAlpha⟩

private def indexedVecValidationTailAnnotations :
    AddInductive.CandidateIsDefEqObservation
      indexedVecValidationHeadContext
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr) :=
  ⟨AddInductive.candidateIsDefEqRefl indexedVecValidationHeadContext
    (ctorIndexedVecApp indexedVecValidationAlpha
      indexedVecValidationNExpr)⟩

/-- The validator and analyzer intentionally allocate the retained `n` field
under different fresh-FVar histories.  D2 alignment must therefore be
positional rather than identifier-based. -/
theorem indexedVecValidationCandidateFieldFVars_ne :
    indexedVecValidationNId ≠ consNId := by
  simp [indexedVecValidationNId, indexedVecCtorValidationContext,
    indexedVecValidationTerminalContextShape,
    indexedVecValidationFamilyContext,
    indexedVecValidationParamContext, indexedVecFamilyCandidateContext,
    consNId, consAlphaContext, consRootContext, ctorContext,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId,
    NameGenerator.next, NameGenerator.curr]

/-- Exact D2 owner for `IndexedVec`.  Its validator telescope is transported
only across proved context/source equalities, while every candidate view is
instantiated with the validator-owned locals at the same de Bruijn position. -/
def indexedVecStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  universeInput := indexedVecStagedUniverseInput
  alignment := by
    change AddInductive.ConstructorCandidateAlignmentTrace
      indexedVecStagedUniverseInput.staged.family.validation.stats false 0
      indexedVecCtorValidationContext
      indexedVecStagedUniverseInput.staged.constructorValidation.trace
      (.cons indexedVecNilConstructorCandidate
        (.cons indexedVecConsConstructorCandidate .nil))
    generalize htrace :
      indexedVecStagedUniverseInput.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors fresh closed rootCheck typeTrace tailTrace =>
        clear htrace
        cases hnilRoot : typeTrace with
        | parameter context fuel argIdx name domain body binderInfo param
            parameterType parameterAt parameterTypeRun parameterDefEq
            nilTypeTail =>
            rw [indexedVecStagedStats_eq,
              indexedVecValidationStatsParams] at parameterAt
            simp at parameterAt
            subst param
            change AddInductive.getType indexedVecValidationAlpha
              indexedVecCtorValidationContext = .ok parameterType at parameterTypeRun
            rw [indexedVecValidationGetTypeAlpha] at parameterTypeRun
            injection parameterTypeRun with parameterType_eq
            subst parameterType
            let nilNormalized := indexedVecTransportValidationTrace
              indexedVecValidationPostContext_eq
              indexedVecValidationNilResultShape nilTypeTail
            let nilNormalizedTrace := nilNormalized
            have nilSpine : nilTypeTail.spineLength =
                nilNormalizedTrace.spineLength := by
              exact (indexedVecTransportValidationTrace_spineLength
                indexedVecValidationPostContext_eq
                indexedVecValidationNilResultShape nilTypeTail).symm
            cases hnilNormalized : nilNormalizedTrace with
            | terminal context source fuel argIdx nilTerminal nilValid =>
                simp [hnilNormalized,
                  AddInductive.ConstructorTypeValidationTrace.spineLength] at nilSpine
                have nilNormalizedAlignment :
                    AddInductive.ConstructorViewAlignmentTrace
                      nilNormalizedTrace indexedVecValidationNilResult := by
                  rw [hnilNormalized]
                  exact .terminal indexedVecValidationNilResultChecked
                    indexedVecValidationNilResultChecked nilTerminal nilValid
                have nilTailAlignment := indexedVecTransportViewAlignment
                  indexedVecValidationPostContext_eq
                  indexedVecValidationNilResultShape
                  indexedVecValidationNilResultShape nilTypeTail
                  nilNormalizedAlignment
                have nilHeadAlignment :
                    AddInductive.ConstructorViewAlignmentTrace
                      (.parameter
                        { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                          env := ctorContext.env }
                        999 0 `α (.sort (.succ (.param `u)))
                        nilCtorBodyRaw .implicit indexedVecValidationAlpha
                        (.sort (.succ (.param `u))) parameterAt
                        parameterTypeRun parameterDefEq nilTypeTail)
                      indexedVecNilConstructorCandidate.type.view := by
                  change AddInductive.ConstructorViewAlignmentTrace
                    _ nilCandidate.view
                  rw [nilCandidate_view_eq]
                  exact .parameter indexedVecValidationSortChecked
                    indexedVecValidationSortChecked
                    indexedVecValidationSortChecked rfl
                    (by simp [indexedVecValidationAlphaFind])
                    nilTypeTail nilTailAlignment
                cases tailTrace with
                | cons seen head constructors consFresh consClosed
                    consRootCheck consTypeTrace finalTrace =>
                    cases hconsRoot : consTypeTrace with
                    | parameter context fuel argIdx name domain body binderInfo
                        param parameterType parameterAt parameterTypeRun
                        parameterDefEq consAfterParamTrace =>
                        rw [indexedVecStagedStats_eq,
                          indexedVecValidationStatsParams] at parameterAt
                        simp at parameterAt
                        subst param
                        change AddInductive.getType indexedVecValidationAlpha
                          indexedVecCtorValidationContext = .ok parameterType at parameterTypeRun
                        rw [indexedVecValidationGetTypeAlpha] at parameterTypeRun
                        injection parameterTypeRun with parameterType_eq
                        subst parameterType
                        let buildConsHeadAlignment
                            (tailAlignment :
                              AddInductive.ConstructorViewAlignmentTrace
                                consAfterParamTrace
                                (consNTypeRaw.instantiate1
                                  indexedVecValidationAlpha)) :
                            AddInductive.ConstructorViewAlignmentTrace
                              (.parameter
                                { indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext with
                                  env := ctorContext.env }
                                999 0 consAlphaName
                                (.sort (.succ (.param `u))) consNTypeRaw
                                .implicit indexedVecValidationAlpha
                                (.sort (.succ (.param `u))) parameterAt
                                parameterTypeRun parameterDefEq
                                consAfterParamTrace)
                              indexedVecConsConstructorCandidate.type.view := by
                          change AddInductive.ConstructorViewAlignmentTrace
                            _ consCandidate.view
                          rw [consCandidate_view_eq]
                          exact .parameter indexedVecValidationSortChecked
                            indexedVecValidationSortChecked
                            indexedVecValidationSortChecked rfl
                            (by simp [indexedVecValidationAlphaFind])
                            consAfterParamTrace tailAlignment
                        have consAfterParamSource_eq :
                            indexedVecConsInfo.type.bindingBody!.instantiate1
                                indexedVecValidationAlpha =
                              indexedVecValidationConsAfterParam :=
                          indexedVecValidationConsAfterParamShape
                        have consAfterParamExplicit_eq :
                            indexedVecConsInfo.type.bindingBody!.instantiate1
                                indexedVecValidationAlpha =
                              .forallE consNName (.const ``Nat [])
                                (.forallE consHeadName
                                  indexedVecValidationAlpha
                                  (.forallE consTailName
                                    (ctorIndexedVecApp
                                      indexedVecValidationAlpha (.bvar 1))
                                    (ctorIndexedVecApp
                                      indexedVecValidationAlpha
                                      (replaySuccApp (.bvar 2))) .default)
                                  .default)
                                .implicit :=
                          consAfterParamSource_eq.trans
                            indexedVecValidationConsAfterParamExplicitShape
                        let consAfterParamNormalized :=
                          indexedVecTransportValidationTrace
                            indexedVecValidationPostContext_eq
                            consAfterParamExplicit_eq consAfterParamTrace
                        let consAfterParamNormalizedTrace :=
                          consAfterParamNormalized
                        have consAfterParamSpine :
                            consAfterParamTrace.spineLength =
                              consAfterParamNormalizedTrace.spineLength := by
                          exact (indexedVecTransportValidationTrace_spineLength
                            indexedVecValidationPostContext_eq
                            consAfterParamExplicit_eq
                            consAfterParamTrace).symm
                        cases hconsAfterParamNormalized :
                            consAfterParamNormalizedTrace with
                        | parameter context fuel argIdx name domain body
                            binderInfo param parameterType parameterAt
                            parameterTypeRun parameterDefEq tail =>
                            rw [indexedVecStagedStats_eq,
                              indexedVecValidationStatsParams] at parameterAt
                            simp at parameterAt
                        | ordinary context fuel argIdx name domain body
                            binderInfo sortResult noParameter ensureType
                            universeTrace natPositivity consAfterNTrace =>
                            simp [hconsAfterParamNormalized,
                              AddInductive.ConstructorTypeValidationTrace.spineLength]
                              at consAfterParamSpine
                            have natPositivityAlignment :=
                              indexedVecValidationNatPositivityAlignment
                                natPositivity
                            have afterParamBody_eq :
                                indexedVecValidationConsAfterParam.bindingBody! =
                                  .forallE consHeadName
                                    indexedVecValidationAlpha
                                    (.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default := by
                              exact congrArg Expr.bindingBody!
                                indexedVecValidationConsAfterParamExplicitShape
                            have afterNSource_eq :
                                ((Expr.forallE consHeadName
                                    indexedVecValidationAlpha
                                    (Expr.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default).instantiate1
                                  indexedVecCtorValidationContext.freshExpr) =
                                    indexedVecValidationConsAfterN := by
                              change
                                ((Expr.forallE consHeadName
                                    indexedVecValidationAlpha
                                    (Expr.forallE consTailName
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha (.bvar 1))
                                      (ctorIndexedVecApp
                                        indexedVecValidationAlpha
                                        (replaySuccApp (.bvar 2))) .default)
                                    .default).instantiate1
                                  indexedVecValidationNExpr) =
                                    indexedVecValidationConsAfterN
                              rw [← afterParamBody_eq]
                              exact indexedVecValidationConsAfterNShape
                            have nContext_eq :
                                indexedVecCtorValidationContext.pushLocalDecl
                                    consNName .implicit
                                      (AddInductive.consumeTypeAnnotations
                                        (.const ``Nat [])) =
                                  indexedVecValidationNContext := by
                              simp [indexedVecValidationNContext]
                            let consAfterNNormalized :=
                              indexedVecTransportValidationTrace nContext_eq
                                afterNSource_eq consAfterNTrace
                            let consAfterNNormalizedTrace := consAfterNNormalized
                            have consAfterNSpine :
                                consAfterNTrace.spineLength =
                                  consAfterNNormalizedTrace.spineLength := by
                              exact
                                (indexedVecTransportValidationTrace_spineLength
                                  nContext_eq afterNSource_eq
                                  consAfterNTrace).symm
                            cases hconsAfterNNormalized :
                                consAfterNNormalizedTrace with
                            | parameter context fuel argIdx name domain body
                                binderInfo param parameterType parameterAt
                                parameterTypeRun parameterDefEq tail =>
                                rw [indexedVecStagedStats_eq,
                                  indexedVecValidationStatsParams] at parameterAt
                                simp at parameterAt
                            | ordinary context fuel argIdx name domain body
                                binderInfo sortResult noParameter ensureType
                                universeTrace alphaPositivity
                                consAfterHeadTrace =>
                                simp [hconsAfterNNormalized,
                                  AddInductive.ConstructorTypeValidationTrace.spineLength]
                                  at consAfterNSpine
                                have alphaPositivityAlignment :=
                                  indexedVecValidationAlphaPositivityAlignment
                                    alphaPositivity
                                have headContext_eq :
                                    indexedVecValidationNContext.pushLocalDecl
                                        consHeadName .default
                                          (AddInductive.consumeTypeAnnotations
                                            indexedVecValidationAlpha) =
                                      indexedVecValidationHeadContext := by
                                  rw [indexedVecValidationConsumeAlpha]
                                  rfl
                                let consAfterHeadNormalized :=
                                  indexedVecTransportValidationTrace
                                    headContext_eq
                                    indexedVecValidationConsAfterHeadShape
                                    consAfterHeadTrace
                                let consAfterHeadNormalizedTrace :=
                                  consAfterHeadNormalized
                                have consAfterHeadSpine :
                                    consAfterHeadTrace.spineLength =
                                      consAfterHeadNormalizedTrace.spineLength := by
                                  exact
                                    (indexedVecTransportValidationTrace_spineLength
                                      headContext_eq
                                      indexedVecValidationConsAfterHeadShape
                                      consAfterHeadTrace).symm
                                cases hconsAfterHeadNormalized :
                                    consAfterHeadNormalizedTrace with
                                | parameter context fuel argIdx name domain body
                                    binderInfo param parameterType parameterAt
                                    parameterTypeRun parameterDefEq tail =>
                                    rw [indexedVecStagedStats_eq,
                                      indexedVecValidationStatsParams] at parameterAt
                                    simp at parameterAt
                                | ordinary context fuel argIdx name domain body
                                    binderInfo sortResult noParameter ensureType
                                    universeTrace tailPositivity
                                    consResultTrace =>
                                    simp [hconsAfterHeadNormalized,
                                      AddInductive.ConstructorTypeValidationTrace.spineLength]
                                      at consAfterHeadSpine
                                    have tailPositivityAlignment :=
                                      indexedVecValidationTailPositivityAlignment
                                        tailPositivity
                                    have tailContext_eq :
                                        indexedVecValidationHeadContext.pushLocalDecl
                                            consTailName .default
                                              (AddInductive.consumeTypeAnnotations
                                                (ctorIndexedVecApp
                                                  indexedVecValidationAlpha
                                                  indexedVecValidationNExpr)) =
                                          indexedVecValidationTailContext := by
                                      rw [indexedVecValidationConsumeTail]
                                      rfl
                                    let consResultNormalized :=
                                      indexedVecTransportValidationTrace
                                        tailContext_eq
                                        indexedVecValidationConsResultShape
                                        consResultTrace
                                    let consResultNormalizedTrace :=
                                      consResultNormalized
                                    have consResultSpine :
                                        consResultTrace.spineLength =
                                          consResultNormalizedTrace.spineLength := by
                                      exact
                                        (indexedVecTransportValidationTrace_spineLength
                                          tailContext_eq
                                          indexedVecValidationConsResultShape
                                          consResultTrace).symm
                                    cases hconsResultNormalized :
                                        consResultNormalizedTrace with
                                    | terminal context source fuel argIdx
                                        resultTerminal resultValid =>
                                        simp [hconsResultNormalized,
                                          AddInductive.ConstructorTypeValidationTrace.spineLength]
                                          at consResultSpine
                                        have consResultNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consResultNormalizedTrace
                                              indexedVecValidationConsResult := by
                                          rw [hconsResultNormalized]
                                          exact .terminal
                                            indexedVecValidationConsResultChecked
                                            indexedVecValidationConsResultChecked
                                            resultTerminal resultValid
                                        have consResultAlignment :=
                                          indexedVecTransportViewAlignment
                                            tailContext_eq
                                            indexedVecValidationConsResultShape
                                            indexedVecValidationConsResultShape
                                            consResultTrace
                                            consResultNormalizedAlignment
                                        have consAfterHeadNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterHeadNormalizedTrace
                                              indexedVecValidationConsAfterHead := by
                                          rw [hconsAfterHeadNormalized]
                                          exact .ordinary
                                            indexedVecValidationTailChecked
                                            indexedVecValidationTailChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeTail]
                                              using
                                                indexedVecValidationTailAnnotations)
                                            (by simpa only
                                              [indexedVecValidationConsumeTail]
                                              using indexedVecValidationTailChecked)
                                            tailPositivity
                                            tailPositivityAlignment
                                            indexedVecValidationHeadContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeTail]
                                              using
                                                indexedVecValidationTailAnnotations)
                                            consResultTrace consResultAlignment
                                        have consAfterHeadAlignment :=
                                          indexedVecTransportViewAlignment
                                            headContext_eq
                                            indexedVecValidationConsAfterHeadShape
                                            indexedVecValidationConsAfterHeadShape
                                            consAfterHeadTrace
                                            consAfterHeadNormalizedAlignment
                                        have consAfterNNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterNNormalizedTrace
                                              indexedVecValidationConsAfterN := by
                                          rw [hconsAfterNNormalized]
                                          exact .ordinary
                                            indexedVecValidationAlphaChecked
                                            indexedVecValidationAlphaChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeAlpha]
                                              using
                                                indexedVecValidationAlphaAnnotations)
                                            (by simpa only
                                              [indexedVecValidationConsumeAlpha]
                                              using indexedVecValidationAlphaChecked)
                                            alphaPositivity
                                            alphaPositivityAlignment
                                            indexedVecValidationNContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeAlpha]
                                              using
                                                indexedVecValidationAlphaAnnotations)
                                            consAfterHeadTrace
                                            consAfterHeadAlignment
                                        have consAfterNAlignment :=
                                          indexedVecTransportViewAlignment
                                            nContext_eq afterNSource_eq
                                            afterNSource_eq consAfterNTrace
                                            consAfterNNormalizedAlignment
                                        have consAfterParamNormalizedAlignment :
                                            AddInductive.ConstructorViewAlignmentTrace
                                              consAfterParamNormalizedTrace
                                              (.forallE consNName
                                                (.const ``Nat [])
                                                (.forallE consHeadName
                                                  indexedVecValidationAlpha
                                                  (.forallE consTailName
                                                    (ctorIndexedVecApp
                                                      indexedVecValidationAlpha
                                                      (.bvar 1))
                                                    (ctorIndexedVecApp
                                                      indexedVecValidationAlpha
                                                      (replaySuccApp (.bvar 2)))
                                                    .default)
                                                  .default)
                                                .implicit) := by
                                          rw [hconsAfterParamNormalized]
                                          exact .ordinary
                                            indexedVecValidationNatChecked
                                            indexedVecValidationNatChecked
                                            (by simpa only
                                              [indexedVecValidationConsumeNat]
                                              using
                                                indexedVecValidationNatAnnotations)
                                            (by simpa only
                                              [indexedVecValidationConsumeNat]
                                              using indexedVecValidationNatChecked)
                                            natPositivity natPositivityAlignment
                                            indexedVecCtorValidationContextFresh
                                            (by simpa only
                                              [indexedVecValidationConsumeNat]
                                              using
                                                indexedVecValidationNatAnnotations)
                                            consAfterNTrace consAfterNAlignment
                                        have consAfterParamAlignment :=
                                          indexedVecTransportViewAlignment
                                            indexedVecValidationPostContext_eq
                                            consAfterParamExplicit_eq
                                            consAfterParamExplicit_eq
                                            consAfterParamTrace
                                            consAfterParamNormalizedAlignment
                                        have consHeadAlignment :=
                                          buildConsHeadAlignment
                                            consAfterParamAlignment
                                        change
                                          AddInductive.CandidateCheckTypeObservation
                                            indexedVecCtorValidationContext.withEmptyLocalContext
                                            indexedVecKernelNil.type at rootCheck
                                        change
                                          AddInductive.CandidateCheckTypeObservation
                                            indexedVecCtorValidationContext.withEmptyLocalContext
                                            indexedVecKernelCons.type at consRootCheck
                                        let nilRootScope :
                                            AddInductive.ConstructorCheckedExpr
                                              indexedVecCtorValidationContext.withEmptyLocalContext
                                              indexedVecKernelNil.type :=
                                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                                            closed rootCheck
                                        let consRootScope :
                                            AddInductive.ConstructorCheckedExpr
                                              indexedVecCtorValidationContext.withEmptyLocalContext
                                              indexedVecKernelCons.type :=
                                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                                            consClosed consRootCheck
                                        cases finalTrace with
                                        | nil finalSeen =>
                                            exact
                                              AddInductive.ConstructorCandidateAlignmentTrace.cons
                                                nilRootScope
                                                (by
                                                  change nilCandidate.trace.storedSpine = true
                                                  exact nilCandidate_identity.storedSpine)
                                                (by
                                                  change 1 =
                                                    nilTypeTail.spineLength + 1
                                                  omega)
                                                (by rfl) nilHeadAlignment <|
                                              AddInductive.ConstructorCandidateAlignmentTrace.cons
                                                consRootScope
                                                (by
                                                  change consCandidate.trace.storedSpine = true
                                                  exact consCandidate_identity.storedSpine)
                                                (by
                                                  change 4 =
                                                    consAfterParamTrace.spineLength + 1
                                                  omega)
                                                (by rfl) consHeadAlignment <|
                                              AddInductive.ConstructorCandidateAlignmentTrace.nil
                                                ((∅ : NameSet).insert
                                                  indexedVecKernelNil.name |>.insert
                                                    indexedVecKernelCons.name)
                                | terminal context source fuel argIdx terminal
                                    valid =>
                                    simp [indexedVecValidationConsAfterHead,
                                      Expr.isForall] at terminal
                            | terminal context source fuel argIdx terminal valid =>
                                simp [indexedVecValidationConsAfterN,
                                  Expr.isForall] at terminal
                        | terminal context source fuel argIdx terminal valid =>
                            simp [Expr.isForall] at terminal
                    | ordinary context fuel argIdx name domain body binderInfo
                        sortResult noParameter ensureType universeTrace positivity
                        tail =>
                        rw [indexedVecStagedStats_eq,
                          indexedVecValidationStatsParams] at noParameter
                        simp at noParameter
                    | terminal context source fuel argIdx terminal valid =>
                        have consType_eq : indexedVecKernelCons.type =
                            consCtorTypeRaw := by
                          simpa [indexedVecKernelCons] using consInfoTypeShape
                        rw [consType_eq] at terminal
                        simp [consCtorTypeRaw, Expr.isForall] at terminal
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity nilTypeTail =>
            rw [indexedVecStagedStats_eq,
              indexedVecValidationStatsParams] at noParameter
            simp at noParameter
        | terminal context source fuel argIdx terminal valid =>
            simp [indexedVecKernelNil, indexedVecNilInfo,
              ConstantInfo.type, ConstantInfo.toConstantVal,
              Expr.isForall] at terminal

/-- The retained `nil`/`cons` validator telescopes, exact analyzer views, field
checks, positivity target, and terminal family applications all admit the D2
post-family Theory interpretation despite their distinct fresh identifiers. -/
theorem indexedVecProducedPostFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePostFamilySemanticRun
      indexedVecStagedPostFamilyInput) :=
  indexedVecStagedPostFamilyInput.exists

/-! ## Pre-family constructor safety

The D3 replay uses the terminal family-analysis context, whose environment is
still exactly `natMap`.  Ordinary constructor fields extend that context;
recursive fields advance only the fresh-name generator so their locals cannot
be used by later fields or the result. -/

private def indexedVecPreFamilyContext : AddInductive.Context :=
  indexedVecFamilyCandidate.trace.terminalContext

private def indexedVecPreFamilyNContext : AddInductive.Context :=
  indexedVecPreFamilyContext.pushLocalDecl
    consNName .implicit (.const ``Nat [])

private def indexedVecPreFamilyHeadContext : AddInductive.Context :=
  indexedVecPreFamilyNContext.pushLocalDecl
    consHeadName .default indexedVecValidationAlpha

private def indexedVecPreFamilyResultContext : AddInductive.Context :=
  indexedVecPreFamilyHeadContext.advanceFresh

private theorem indexedVecPreFamilyContext_eq :
    indexedVecPreFamilyContext = indexedVecValidationFamilyContext := rfl

private theorem indexedVecPreFamilyNContext_eq :
    indexedVecPreFamilyNContext =
      { indexedVecValidationNContext with env := indexedVecKernelEnv } := rfl

private theorem indexedVecPreFamilyHeadContext_eq :
    indexedVecPreFamilyHeadContext =
      { indexedVecValidationHeadContext with env := indexedVecKernelEnv } := rfl

private theorem indexedVecPreFamilySortCheckValid
    (context : AddInductive.Context)
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilySortCheckTypeM context.lctx

private theorem indexedVecPreFamilyNatCheckValid
    (context : AddInductive.Context)
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .const ``Nat [], .sort (.succ .zero)⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyNatCheckTypeM context.lctx

private theorem indexedVecPreFamilyNatEnsureValid
    (context : AddInductive.Context)
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, .const ``Nat [], .sort (.succ .zero)⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyNatEnsureTypeM context.lctx

private theorem indexedVecPreFamilyTelescopeCheckValid
    (context : AddInductive.Context)
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, indexedVecPreFamilyIndexTelescope,
        .sort (mkLevelIMax' (.succ .zero)
          (.succ (.succ (.param `u))))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyIndexTelescopeCheckTypeM context.lctx

private theorem indexedVecPreFamilyFVarCheckTypeM
    (lctx : LocalContext) (id : FVarId) (type : Expr)
    (find : lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType (.fvar id)) =
        .ok type := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : TypeChecker.State)) = _
  rw [indexedVecPreFamilyInferTypeFVarCore 9999 lctx
    ({} : TypeChecker.State) id type Std.HashMap.getElem?_empty find]
  rfl

private def indexedVecPreFamilyFVarInferOnlyState
    (id : FVarId) (type : Expr) : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeI := ({} : TypeChecker.State).inferTypeI.insert
      (.fvar id) type }

private theorem indexedVecPreFamilyFVarInferOnly
    (lctx : LocalContext) (id : FVarId) (type : Expr)
    (find : lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : TypeChecker.State) =
        .ok (type, indexedVecPreFamilyFVarInferOnlyState id type) := by
  change TypeChecker.Inner.inferType' (.fvar id) true
    (TypeChecker.Methods.withFuel 9999)
    (indexedVecTypeCheckerContext lctx)
    ({} : TypeChecker.State) = _
  unfold TypeChecker.Inner.inferType'
  simp [indexedVecPreFamilyFVarInferOnlyState,
    Expr.hasLooseBVars, Expr.looseBVarRange',
    TypeChecker.Inner.inferFVar, indexedVecTypeCheckerContext,
    find, LocalDecl.type, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

private theorem indexedVecPreFamilyFVarEnsureTypeM
    (lctx : LocalContext) (id : FVarId) (level : Level)
    (find : lctx.find? id =
      some (.cdecl index id name (.sort level) bi kind)) :
    TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig) (TypeChecker.ensureType (.fvar id)) =
        .ok (.sort level) := by
  unfold TypeChecker.ensureType TypeChecker.inferType
    TypeChecker.ensureSort TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel 10000)
      { env := indexedVecKernelEnv, lctx := lctx, safety := .safe,
        lparams := [`u], fuel := ({} : FuelConfig) }
      ({} : TypeChecker.State) =
        .ok (.sort level,
          indexedVecPreFamilyFVarInferOnlyState id (.sort level)) by
    simpa [indexedVecTypeCheckerContext] using
      indexedVecPreFamilyFVarInferOnly lctx id (.sort level) find]
  rfl

private theorem indexedVecPreFamilyZeroCheckTypeM
    (lctx : LocalContext) :
    TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig) (TypeChecker.checkType (.const ``Nat.zero [])) =
        .ok (.const ``Nat []) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.const ``Nat.zero []) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : TypeChecker.State)) = _
  rw [indexedVecPreFamilyInferTypeZeroCore 9999 lctx
    ({} : TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private theorem indexedVecPreFamilySuccFVarCheckTypeM
    (lctx : LocalContext) (id : FVarId)
    (find : lctx.find? id =
      some (.cdecl index id name (.const ``Nat []) bi kind)) :
    TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (TypeChecker.checkType (replaySuccApp (.fvar id))) =
        .ok (.const ``Nat []) := by
  let succState := replayInsert ({} : TypeChecker.State)
    (.const ``Nat.succ [])
    (.forallE `n (.const ``Nat []) (.const ``Nat []) .default)
  let argumentState := replayInsert succState (.fvar id) (.const ``Nat [])
  have succRun : TypeChecker.Inner.inferType' (.const ``Nat.succ []) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx) ({} : TypeChecker.State) =
      .ok (.forallE `n (.const ``Nat []) (.const ``Nat []) .default,
        succState) := by
    simpa [succState, replayInsert] using
      (indexedVecPreFamilyInferTypeSuccCore 9999 lctx
        ({} : TypeChecker.State) Std.HashMap.getElem?_empty)
  have argumentRun : TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx) succState =
      .ok (.const ``Nat [], argumentState) := by
    apply indexedVecPreFamilyInferTypeFVarCore
    · simp [succState, replayInsert]
    · exact find
  have appRun := inferAppCoreOf 9999
    (indexedVecTypeCheckerContext lctx)
    ({} : TypeChecker.State) succState argumentState
    (.const ``Nat.succ []) (.fvar id) (.const ``Nat [])
    (.const ``Nat []) `n .default
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange'])
    (by simp) succRun argumentRun (by rfl)
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (replaySuccApp (.fvar id)) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : TypeChecker.State)) = _
  rw [show TypeChecker.Inner.inferType'
      (replaySuccApp (.fvar id)) false
      (TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : TypeChecker.State) =
        .ok (.const ``Nat [],
          { argumentState with inferTypeC :=
            (argumentState.inferTypeC.insert
              (replaySuccApp (.fvar id)) (.const ``Nat [])) }) by
    simpa [replaySuccApp, Expr.instantiate1_eq,
      Expr.instantiate1'] using appRun]
  rfl

private theorem indexedVecPreFamilyFVarCheckValid
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (find : context.lctx.find? id =
      some (.cdecl index id name type bi kind))
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .fvar id, type⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyFVarCheckTypeM context.lctx id type find

private theorem indexedVecPreFamilyFVarEnsureValid
    (context : AddInductive.Context) (id : FVarId) (level : Level)
    (find : context.lctx.find? id =
      some (.cdecl index id name (.sort level) bi kind))
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, .fvar id, .sort level⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyFVarEnsureTypeM context.lctx id level find

private theorem indexedVecPreFamilyZeroCheckValid
    (context : AddInductive.Context)
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .const ``Nat.zero [], .const ``Nat []⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilyZeroCheckTypeM context.lctx

private theorem indexedVecPreFamilySuccCheckValid
    (context : AddInductive.Context) (id : FVarId)
    (find : context.lctx.find? id =
      some (.cdecl index id name (.const ``Nat []) bi kind))
    (contextEnv : context.env = indexedVecKernelEnv)
    (contextSafety : context.safety = .safe)
    (contextLparams : context.lparams = [`u])
    (contextFuel : context.fuel = ({} : FuelConfig)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, replaySuccApp (.fvar id), .const ``Nat []⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  rw [contextEnv, contextSafety, contextLparams, contextFuel]
  exact indexedVecPreFamilySuccFVarCheckTypeM context.lctx id find

private theorem indexedVecNormalizationFamilyView_eq :
    indexedVecNormalizationCandidate.families.singleton.familyType.type.view =
      indexedVecInfo.type := by
  change indexedVecFamilyCandidate.view = indexedVecInfo.type
  exact indexedVecFamilyCandidate_view_eq

private theorem indexedVecNormalizationConstructors_eq :
    indexedVecNormalizationCandidate.families.singleton.constructors =
      .cons indexedVecNilConstructorCandidate
        (.cons indexedVecConsConstructorCandidate .nil) := rfl

private theorem indexedVecNormalizationPreFamilyContext_eq :
    indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext =
      indexedVecPreFamilyContext := rfl

private theorem indexedVecPreFamilySafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        indexedVecStagedUniverseInput.staged.family.validation.stats
        indexedVecNormalizationCandidate.families.singleton.familyType.type.view
        indexedVecNormalizationCandidate.families.singleton.constructors
        indexedVecNormalizationCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  rw [indexedVecStagedStats_eq]
  rw [indexedVecNormalizationFamilyView_eq,
    indexedVecNormalizationConstructors_eq,
    indexedVecNormalizationPreFamilyContext_eq]
  change AddInductive.checkConstructorPreFamilySafety
    indexedVecCandidateInductiveStats indexedVecInfo.type
    (.cons indexedVecNilConstructorCandidate
      (.cons indexedVecConsConstructorCandidate .nil))
    indexedVecPreFamilyContext = .ok ()
  have alphaFind : indexedVecPreFamilyContext.lctx.find?
      indexedVecValidationAlphaId =
        some (.cdecl 0 indexedVecValidationAlphaId
          indexedVecValidationParamName
          (.sort (.succ (.param `u))) .default .default) := by
    change indexedVecCtorValidationContext.lctx.find?
      indexedVecValidationAlphaId = _
    exact indexedVecValidationAlphaFind
  have alphaFindN : indexedVecPreFamilyNContext.lctx.find?
      indexedVecValidationAlphaId =
        some (.cdecl 0 indexedVecValidationAlphaId
          indexedVecValidationParamName
          (.sort (.succ (.param `u))) .default .default) := by
    change indexedVecValidationNContext.lctx.find?
      indexedVecValidationAlphaId = _
    exact indexedVecValidationAlphaFindInN
  have alphaFindHead : indexedVecPreFamilyHeadContext.lctx.find?
      indexedVecValidationAlphaId =
        some (.cdecl 0 indexedVecValidationAlphaId
          indexedVecValidationParamName
          (.sort (.succ (.param `u))) .default .default) := by
    change indexedVecValidationHeadContext.lctx.find?
      indexedVecValidationAlphaId = _
    exact indexedVecValidationAlphaFindInHead
  have nFindHead : indexedVecPreFamilyHeadContext.lctx.find?
      indexedVecValidationNId =
        some (.cdecl 2 indexedVecValidationNId consNName
          (.const ``Nat []) .implicit .default) := by
    change indexedVecValidationHeadContext.lctx.find?
      indexedVecValidationNId = _
    exact indexedVecValidationNFindInHead
  have nFindResult : indexedVecPreFamilyResultContext.lctx.find?
      indexedVecValidationNId =
        some (.cdecl 2 indexedVecValidationNId consNName
          (.const ``Nat []) .implicit .default) := by
    simpa [indexedVecPreFamilyResultContext,
      AddInductive.Context.advanceFresh] using nFindHead
  have baseFresh : indexedVecPreFamilyContext.lctx.find?
      indexedVecPreFamilyContext.freshFVarId = none := by
    change indexedVecCtorValidationContext.lctx.find?
      indexedVecCtorValidationContext.freshFVarId = none
    exact indexedVecCtorValidationContextFresh
  have nFresh : indexedVecPreFamilyNContext.lctx.find?
      indexedVecPreFamilyNContext.freshFVarId = none := by
    change indexedVecValidationNContext.lctx.find?
      indexedVecValidationNContext.freshFVarId = none
    exact indexedVecValidationNContextFresh
  have headFresh : indexedVecPreFamilyHeadContext.lctx.find?
      indexedVecPreFamilyHeadContext.freshFVarId = none := by
    change indexedVecValidationHeadContext.lctx.find?
      indexedVecValidationHeadContext.freshFVarId = none
    exact indexedVecValidationHeadContextFresh
  let baseTelescope : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyContext indexedVecPreFamilyIndexTelescope :=
    .ofRun (by
      simp [indexedVecPreFamilyIndexTelescope, FVarsIn,
        Level.hasMVar'])
      (indexedVecPreFamilyTelescopeCheckValid
        indexedVecPreFamilyContext rfl rfl rfl rfl)
  let headTelescope : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyHeadContext indexedVecPreFamilyIndexTelescope :=
    .ofRun (by
      simp [indexedVecPreFamilyIndexTelescope, FVarsIn,
        Level.hasMVar'])
      (indexedVecPreFamilyTelescopeCheckValid
        indexedVecPreFamilyHeadContext rfl rfl rfl rfl)
  let resultTelescope : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyResultContext indexedVecPreFamilyIndexTelescope :=
    .ofRun (by
      simp [indexedVecPreFamilyIndexTelescope, FVarsIn,
        Level.hasMVar'])
      (indexedVecPreFamilyTelescopeCheckValid
        indexedVecPreFamilyResultContext rfl rfl rfl rfl)
  let baseSort : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyContext (.sort (.succ (.param `u))) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (indexedVecPreFamilySortCheckValid
        indexedVecPreFamilyContext rfl rfl rfl rfl)
  let headSort : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyHeadContext (.sort (.succ (.param `u))) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (indexedVecPreFamilySortCheckValid
        indexedVecPreFamilyHeadContext rfl rfl rfl rfl)
  let resultSort : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyResultContext (.sort (.succ (.param `u))) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (indexedVecPreFamilySortCheckValid
        indexedVecPreFamilyResultContext rfl rfl rfl rfl)
  let baseNat : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyContext (.const ``Nat []) :=
    .ofRun (by simp [FVarsIn])
      (indexedVecPreFamilyNatCheckValid
        indexedVecPreFamilyContext rfl rfl rfl rfl)
  let headNat : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyHeadContext (.const ``Nat []) :=
    .ofRun (by simp [FVarsIn])
      (indexedVecPreFamilyNatCheckValid
        indexedVecPreFamilyHeadContext rfl rfl rfl rfl)
  let resultNat : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyResultContext (.const ``Nat []) :=
    .ofRun (by simp [FVarsIn])
      (indexedVecPreFamilyNatCheckValid
        indexedVecPreFamilyResultContext rfl rfl rfl rfl)
  let zeroChecked : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyContext (.const ``Nat.zero []) :=
    .ofRun (by simp [FVarsIn])
      (indexedVecPreFamilyZeroCheckValid
        indexedVecPreFamilyContext rfl rfl rfl rfl)
  let nChecked : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyHeadContext indexedVecValidationNExpr := by
    rw [indexedVecValidationNExprShape]
    exact .ofRun (by
      change (indexedVecPreFamilyHeadContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [nFindHead]
      rfl) (indexedVecPreFamilyFVarCheckValid
        indexedVecPreFamilyHeadContext indexedVecValidationNId
        (.const ``Nat []) nFindHead rfl rfl rfl rfl)
  let succChecked : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyResultContext
        (replaySuccApp indexedVecValidationNExpr) := by
    rw [indexedVecValidationNExprShape]
    exact .ofRun (by
      simp [replaySuccApp, FVarsIn]
      change (indexedVecPreFamilyResultContext.lctx.find?
        indexedVecValidationNId).isSome = true
      rw [nFindResult]
      rfl) (indexedVecPreFamilySuccCheckValid
        indexedVecPreFamilyResultContext indexedVecValidationNId
        nFindResult rfl rfl rfl rfl)
  let zeroComparison : AddInductive.CandidateIsDefEqObservation
      indexedVecPreFamilyContext (.const ``Nat []) (.const ``Nat []) :=
    ⟨candidateIsDefEqSelfValid indexedVecPreFamilyContext
      (.const ``Nat []) 9999 rfl⟩
  let nComparison : AddInductive.CandidateIsDefEqObservation
      indexedVecPreFamilyHeadContext (.const ``Nat []) (.const ``Nat []) :=
    ⟨candidateIsDefEqSelfValid indexedVecPreFamilyHeadContext
      (.const ``Nat []) 9999 rfl⟩
  let succComparison : AddInductive.CandidateIsDefEqObservation
      indexedVecPreFamilyResultContext (.const ``Nat []) (.const ``Nat []) :=
    ⟨candidateIsDefEqSelfValid indexedVecPreFamilyResultContext
      (.const ``Nat []) 9999 rfl⟩
  let nilSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      indexedVecPreFamilyContext indexedVecPreFamilyIndexTelescope
        [.const ``Nat.zero []] := by
    unfold indexedVecPreFamilyIndexTelescope
    exact .cons indexedVecPreFamilyContext
      indexedVecInfo.type.bindingBody!.bindingName!
      (.const ``Nat []) (.sort (.succ (.param `u))) .default
      (.const ``Nat.zero []) [] baseTelescope
      ⟨zeroChecked, baseNat, zeroComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            indexedVecPreFamilyContext
            (.sort (.succ (.param `u))) baseSort rfl))
  let recursiveSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      indexedVecPreFamilyHeadContext indexedVecPreFamilyIndexTelescope
        [indexedVecValidationNExpr] := by
    unfold indexedVecPreFamilyIndexTelescope
    exact .cons indexedVecPreFamilyHeadContext
      indexedVecInfo.type.bindingBody!.bindingName!
      (.const ``Nat []) (.sort (.succ (.param `u))) .default
      indexedVecValidationNExpr [] headTelescope
      ⟨nChecked, headNat, nComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            indexedVecPreFamilyHeadContext
            (.sort (.succ (.param `u))) headSort rfl))
  let resultSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      indexedVecPreFamilyResultContext indexedVecPreFamilyIndexTelescope
        [replaySuccApp indexedVecValidationNExpr] := by
    unfold indexedVecPreFamilyIndexTelescope
    exact .cons indexedVecPreFamilyResultContext
      indexedVecInfo.type.bindingBody!.bindingName!
      (.const ``Nat []) (.sort (.succ (.param `u))) .default
      (replaySuccApp indexedVecValidationNExpr) [] resultTelescope
      ⟨succChecked, resultNat, succComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            indexedVecPreFamilyResultContext
            (.sort (.succ (.param `u))) resultSort rfl))
  have nilArgs : indexedVecValidationNilResult.getAppArgs.toList.drop
      indexedVecCandidateInductiveStats.params.size =
        [.const ``Nat.zero []] := by
    simp [indexedVecValidationNilResult,
      indexedVecValidationStatsParams, ctorIndexedVecAppGetAppArgs]
  obtain ⟨nilTargetSpine, nilTargetSpineRun⟩ :
      ∃ nilTargetSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
          indexedVecPreFamilyContext indexedVecPreFamilyIndexTelescope
          (indexedVecValidationNilResult.getAppArgs.toList.drop
            indexedVecCandidateInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            indexedVecPreFamilyContext indexedVecPreFamilyIndexTelescope
            (indexedVecValidationNilResult.getAppArgs.toList.drop
              indexedVecCandidateInductiveStats.params.size) =
          .ok nilTargetSpine := by
    rw [nilArgs]
    exact ⟨nilSpine, nilSpine.build_eq⟩
  have nilIndependent : AddInductive.constructorIndependentOf
      indexedVecValidationNilResult [] = true := by
    simp [AddInductive.constructorIndependentOf]
  let nilTerminalTrace : AddInductive.ConstructorPreFamilyViewTrace
      indexedVecCandidateInductiveStats 0
      indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
      indexedVecValidationNilResult 1 [] false :=
    .terminal indexedVecPreFamilyContext indexedVecValidationNilResult
      1 [] false indexedVecValidationNilResultIsValid nilIndependent
      nilTargetSpine
  have nilTerminalRun :
      AddInductive.ConstructorPreFamilyViewTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecValidationNilResult 1 [] false 999 =
        .ok nilTerminalTrace := by
    exact AddInductive.ConstructorPreFamilyViewTrace.terminal_build_eq
      (fuel := 998) rfl indexedVecValidationNilResultIsValid nilIndependent
      nilTargetSpine
  obtain ⟨nilTailTrace, nilTailRun⟩ :
      ∃ nilTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          (nilCtorBodyRaw.instantiate1 indexedVecValidationAlpha)
          1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            (nilCtorBodyRaw.instantiate1 indexedVecValidationAlpha)
            1 [] false 999 =
          .ok nilTailTrace := by
    rw [show nilCtorBodyRaw.instantiate1 indexedVecValidationAlpha =
        indexedVecValidationNilResult by
      simpa [nilInfoTypeShape, nilCtorTypeRaw] using
        indexedVecValidationNilResultShape]
    exact ⟨nilTerminalTrace, nilTerminalRun⟩
  have parameterAtZero : indexedVecCandidateInductiveStats.params[0]? =
      some indexedVecValidationAlpha := by
    rw [indexedVecValidationStatsParams]
    rfl
  obtain ⟨nilRawViewTrace, nilRawViewRun⟩ :
      ∃ nilRawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          nilCtorTypeRaw 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            nilCtorTypeRaw 0 [] false 1000 = .ok nilRawViewTrace := by
    simp only [nilCtorTypeRaw,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [parameterAtZero] at parameterAt
      cases parameterAt
      rw [nilTailRun]
      exact ⟨_, rfl⟩
    · rename_i noParameter
      rw [parameterAtZero] at noParameter
      contradiction
  obtain ⟨nilViewTrace, nilViewRun⟩ :
      ∃ nilViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecNilInfo.type 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            indexedVecNilInfo.type 0 [] false 1000 =
          .ok nilViewTrace := by
    rw [nilInfoTypeShape]
    exact ⟨nilRawViewTrace, nilRawViewRun⟩
  obtain ⟨nilHeadTrace, nilHeadRun⟩ :
      ∃ nilHeadTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecNilConstructorCandidate.type.view 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            indexedVecNilConstructorCandidate.type.view 0 [] false 1000 =
          .ok nilHeadTrace := by
    change ∃ nilHeadTrace : AddInductive.ConstructorPreFamilyViewTrace
        indexedVecCandidateInductiveStats 0
        indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
        nilCandidate.view 0 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          nilCandidate.view 0 [] false 1000 = .ok nilHeadTrace
    rw [nilCandidate_view_eq]
    exact ⟨nilViewTrace, nilViewRun⟩
  let baseNatEnsure : AddInductive.ConstructorEnsureTypeObservation
      indexedVecPreFamilyContext (.const ``Nat []) :=
    ⟨.sort (.succ .zero), indexedVecPreFamilyNatEnsureValid
      indexedVecPreFamilyContext rfl rfl rfl rfl⟩
  let baseNatConsumed : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyContext
      (AddInductive.consumeTypeAnnotations (.const ``Nat [])) := by
    rw [indexedVecValidationConsumeNat]
    exact baseNat
  let baseNatAnnotations : AddInductive.CandidateIsDefEqObservation
      indexedVecPreFamilyContext (.const ``Nat [])
      (AddInductive.consumeTypeAnnotations (.const ``Nat [])) := by
    rw [indexedVecValidationConsumeNat]
    exact ⟨candidateIsDefEqSelfValid indexedVecPreFamilyContext
      (.const ``Nat []) 9999 rfl⟩
  let alphaChecked : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyNContext indexedVecValidationAlpha := by
    rw [indexedVecValidationAlphaShape]
    exact .ofRun (by
      change (indexedVecPreFamilyNContext.lctx.find?
        indexedVecValidationAlphaId).isSome = true
      rw [alphaFindN]
      rfl) (indexedVecPreFamilyFVarCheckValid
        indexedVecPreFamilyNContext indexedVecValidationAlphaId
        (.sort (.succ (.param `u))) alphaFindN rfl rfl rfl rfl)
  let alphaEnsure : AddInductive.ConstructorEnsureTypeObservation
      indexedVecPreFamilyNContext indexedVecValidationAlpha := by
    rw [indexedVecValidationAlphaShape]
    exact ⟨.sort (.succ (.param `u)),
      indexedVecPreFamilyFVarEnsureValid indexedVecPreFamilyNContext
        indexedVecValidationAlphaId (.succ (.param `u)) alphaFindN
        rfl rfl rfl rfl⟩
  let alphaConsumed : AddInductive.ConstructorCheckedExpr
      indexedVecPreFamilyNContext
      (AddInductive.consumeTypeAnnotations indexedVecValidationAlpha) := by
    rw [indexedVecValidationConsumeAlpha]
    exact alphaChecked
  let alphaAnnotations : AddInductive.CandidateIsDefEqObservation
      indexedVecPreFamilyNContext indexedVecValidationAlpha
      (AddInductive.consumeTypeAnnotations indexedVecValidationAlpha) := by
    rw [indexedVecValidationConsumeAlpha]
    exact ⟨candidateIsDefEqSelfValid indexedVecPreFamilyNContext
      indexedVecValidationAlpha 9999 rfl⟩
  have alphaNeRemoved : indexedVecValidationAlphaId ≠
      indexedVecPreFamilyHeadContext.freshFVarId := by
    intro equality
    have fresh := headFresh
    rw [← equality, alphaFindHead] at fresh
    contradiction
  have nNeRemoved : indexedVecValidationNId ≠
      indexedVecPreFamilyHeadContext.freshFVarId := by
    intro equality
    have fresh := headFresh
    rw [← equality, nFindHead] at fresh
    contradiction
  have recursiveArgs :
      (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr).getAppArgs.toList.drop
        indexedVecCandidateInductiveStats.params.size =
      [indexedVecValidationNExpr] := by
    simp [indexedVecValidationStatsParams, ctorIndexedVecAppGetAppArgs]
  obtain ⟨recursiveTargetSpine, recursiveTargetSpineRun⟩ :
      ∃ recursiveTargetSpine :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            indexedVecPreFamilyHeadContext
            indexedVecPreFamilyIndexTelescope
            ((ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr).getAppArgs.toList.drop
              indexedVecCandidateInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            indexedVecPreFamilyHeadContext
            indexedVecPreFamilyIndexTelescope
            ((ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr).getAppArgs.toList.drop
              indexedVecCandidateInductiveStats.params.size) =
          .ok recursiveTargetSpine := by
    rw [recursiveArgs]
    exact ⟨recursiveSpine, recursiveSpine.build_eq⟩
  have recursiveTargetValid : AddInductive.isValidIndAppIdx
      indexedVecCandidateInductiveStats
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) 0 = true :=
    indexedVecValidationAppIsValidIdx indexedVecValidationNExpr
      indexedVecValidationNHasNoIndOcc
  let recursiveFieldTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
      indexedVecPreFamilyHeadContext.fuel.inductiveFuel :=
    .target indexedVecPreFamilyHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
      recursiveTargetValid recursiveTargetSpine
  have recursiveFieldRun : AddInductive.ConstructorPreFamilyRecursiveTrace.build
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyHeadContext
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr)
      indexedVecPreFamilyHeadContext.fuel.inductiveFuel =
        .ok recursiveFieldTrace := by
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
      (fuel := 999) rfl recursiveTargetValid recursiveTargetSpine
  have recursiveIndependent : AddInductive.constructorIndependentOf
      (ctorIndexedVecApp indexedVecValidationAlpha
        indexedVecValidationNExpr) [] = true := by
    simp [AddInductive.constructorIndependentOf]
  have resultArgs : indexedVecValidationConsResult.getAppArgs.toList.drop
      indexedVecCandidateInductiveStats.params.size =
        [replaySuccApp indexedVecValidationNExpr] := by
    simp [indexedVecValidationConsResult,
      indexedVecValidationStatsParams, ctorIndexedVecAppGetAppArgs]
  obtain ⟨resultTargetSpine, resultTargetSpineRun⟩ :
      ∃ resultTargetSpine :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            indexedVecPreFamilyResultContext
            indexedVecPreFamilyIndexTelescope
            (indexedVecValidationConsResult.getAppArgs.toList.drop
              indexedVecCandidateInductiveStats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            indexedVecPreFamilyResultContext
            indexedVecPreFamilyIndexTelescope
            (indexedVecValidationConsResult.getAppArgs.toList.drop
              indexedVecCandidateInductiveStats.params.size) =
          .ok resultTargetSpine := by
    rw [resultArgs]
    exact ⟨resultSpine, resultSpine.build_eq⟩
  have resultIndependent : AddInductive.constructorIndependentOf
      indexedVecValidationConsResult
      [indexedVecPreFamilyHeadContext.freshFVarId] = true := by
    simp [AddInductive.constructorIndependentOf,
      indexedVecValidationConsResult, ctorIndexedVecApp, replaySuccApp,
      Expr.fvarsList,
      indexedVecValidationAlphaShape, indexedVecValidationNExprShape,
      alphaNeRemoved, nNeRemoved]
  let resultTerminalTrace : AddInductive.ConstructorPreFamilyViewTrace
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyResultContext indexedVecValidationConsResult 4
      [indexedVecPreFamilyHeadContext.freshFVarId] true :=
    .terminal indexedVecPreFamilyResultContext
      indexedVecValidationConsResult 4
      [indexedVecPreFamilyHeadContext.freshFVarId] true
      indexedVecValidationConsResultIsValid resultIndependent
      resultTargetSpine
  have resultTerminalRun : AddInductive.ConstructorPreFamilyViewTrace.build
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyResultContext indexedVecValidationConsResult 4
      [indexedVecPreFamilyHeadContext.freshFVarId] true 996 =
        .ok resultTerminalTrace := by
    exact AddInductive.ConstructorPreFamilyViewTrace.terminal_build_eq
      (fuel := 995) rfl indexedVecValidationConsResultIsValid
      resultIndependent resultTargetSpine
  obtain ⟨consResultTailTrace, consResultTailRun⟩ :
      ∃ consResultTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope
          indexedVecPreFamilyHeadContext.advanceFresh
          (indexedVecValidationConsAfterHead.bindingBody!.instantiate1
            indexedVecPreFamilyHeadContext.freshExpr)
          4 [indexedVecPreFamilyHeadContext.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            indexedVecPreFamilyHeadContext.advanceFresh
            (indexedVecValidationConsAfterHead.bindingBody!.instantiate1
              indexedVecPreFamilyHeadContext.freshExpr)
            4 [indexedVecPreFamilyHeadContext.freshFVarId] true 996 =
          .ok consResultTailTrace := by
    rw [show indexedVecValidationConsAfterHead.bindingBody!.instantiate1
        indexedVecPreFamilyHeadContext.freshExpr =
          indexedVecValidationConsResult by
      change indexedVecValidationConsAfterHead.bindingBody!.instantiate1
        indexedVecValidationHeadContext.freshExpr = _
      exact indexedVecValidationConsResultShape]
    exact ⟨resultTerminalTrace, resultTerminalRun⟩
  obtain ⟨explicitResultTailTrace, explicitResultTailRun⟩ :
      ∃ explicitResultTailTrace :
          AddInductive.ConstructorPreFamilyViewTrace
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            indexedVecPreFamilyHeadContext.advanceFresh
            ((ctorIndexedVecApp indexedVecValidationAlpha
              (replaySuccApp indexedVecValidationNExpr)).instantiate1
                indexedVecPreFamilyHeadContext.freshExpr)
            4 [indexedVecPreFamilyHeadContext.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            indexedVecPreFamilyHeadContext.advanceFresh
            ((ctorIndexedVecApp indexedVecValidationAlpha
              (replaySuccApp indexedVecValidationNExpr)).instantiate1
                indexedVecPreFamilyHeadContext.freshExpr)
            4 [indexedVecPreFamilyHeadContext.freshFVarId] true 996 =
          .ok explicitResultTailTrace := by
    change ∃ explicitResultTailTrace :
        AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope
          indexedVecPreFamilyHeadContext.advanceFresh
          (indexedVecValidationConsAfterHead.bindingBody!.instantiate1
            indexedVecPreFamilyHeadContext.freshExpr)
          4 [indexedVecPreFamilyHeadContext.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope
          indexedVecPreFamilyHeadContext.advanceFresh
          (indexedVecValidationConsAfterHead.bindingBody!.instantiate1
            indexedVecPreFamilyHeadContext.freshExpr)
          4 [indexedVecPreFamilyHeadContext.freshFVarId] true 996 =
        .ok explicitResultTailTrace
    exact ⟨consResultTailTrace, consResultTailRun⟩
  have noParameterThree : indexedVecCandidateInductiveStats.params[3]? =
      none := by
    rw [indexedVecValidationStatsParams]
    rfl
  obtain ⟨consAfterHeadTrace, consAfterHeadRun⟩ :
      ∃ consAfterHeadTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyHeadContext
          indexedVecValidationConsAfterHead 3 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyHeadContext
            indexedVecValidationConsAfterHead 3 [] false 997 =
          .ok consAfterHeadTrace := by
    simp only [indexedVecValidationConsAfterHead,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterThree] at parameterAt
      contradiction
    · split
      · rename_i nonrecursive
        rw [indexedVecValidationTailHasIndOcc] at nonrecursive
        contradiction
      · rw [dif_pos recursiveIndependent, recursiveFieldRun]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos headFresh]
        rw [explicitResultTailRun]
        exact ⟨_, rfl⟩
  obtain ⟨consHeadTailTrace, consHeadTailRun⟩ :
      ∃ consHeadTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyHeadContext
          (indexedVecValidationConsAfterN.bindingBody!.instantiate1
            indexedVecPreFamilyNContext.freshExpr)
          3 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyHeadContext
            (indexedVecValidationConsAfterN.bindingBody!.instantiate1
              indexedVecPreFamilyNContext.freshExpr)
            3 [] false 997 = .ok consHeadTailTrace := by
    rw [show indexedVecValidationConsAfterN.bindingBody!.instantiate1
        indexedVecPreFamilyNContext.freshExpr =
          indexedVecValidationConsAfterHead by
      change indexedVecValidationConsAfterN.bindingBody!.instantiate1
        indexedVecValidationNContext.freshExpr = _
      exact indexedVecValidationConsAfterHeadShape]
    exact ⟨consAfterHeadTrace, consAfterHeadRun⟩
  obtain ⟨explicitHeadTailTrace, explicitHeadTailRun⟩ :
      ∃ explicitHeadTailTrace :
          AddInductive.ConstructorPreFamilyViewTrace
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            (indexedVecPreFamilyNContext.pushLocalDecl consHeadName .default
              (AddInductive.consumeTypeAnnotations
                indexedVecValidationAlpha))
            ((Expr.forallE consTailName
              (ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr)
              (ctorIndexedVecApp indexedVecValidationAlpha
                (replaySuccApp indexedVecValidationNExpr))
              .default).instantiate1 indexedVecPreFamilyNContext.freshExpr)
            3 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            (indexedVecPreFamilyNContext.pushLocalDecl consHeadName .default
              (AddInductive.consumeTypeAnnotations
                indexedVecValidationAlpha))
            ((Expr.forallE consTailName
              (ctorIndexedVecApp indexedVecValidationAlpha
                indexedVecValidationNExpr)
              (ctorIndexedVecApp indexedVecValidationAlpha
                (replaySuccApp indexedVecValidationNExpr))
              .default).instantiate1 indexedVecPreFamilyNContext.freshExpr)
            3 [] false 997 = .ok explicitHeadTailTrace := by
    rw [indexedVecValidationConsumeAlpha]
    rw [show Expr.forallE consTailName
        (ctorIndexedVecApp indexedVecValidationAlpha
          indexedVecValidationNExpr)
        (ctorIndexedVecApp indexedVecValidationAlpha
          (replaySuccApp indexedVecValidationNExpr)) .default =
          indexedVecValidationConsAfterN.bindingBody! by rfl]
    exact ⟨consHeadTailTrace, consHeadTailRun⟩
  have noParameterTwo : indexedVecCandidateInductiveStats.params[2]? =
      none := by
    rw [indexedVecValidationStatsParams]
    rfl
  obtain ⟨consAfterNTrace, consAfterNRun⟩ :
      ∃ consAfterNTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyNContext
          indexedVecValidationConsAfterN 2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyNContext
            indexedVecValidationConsAfterN 2 [] false 998 =
          .ok consAfterNTrace := by
    simp only [indexedVecValidationConsAfterN,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterTwo] at parameterAt
      contradiction
    · split
      · rw [alphaChecked.check_eq, alphaEnsure.observe_eq,
          alphaConsumed.check_eq]
        rw [dif_pos (by
          simp [AddInductive.constructorIndependentOf])]
        simp only [Bind.bind, Except.bind]
        rw [alphaAnnotations.observe_eq]
        simp only []
        rw [dif_pos nFresh]
        rw [explicitHeadTailRun]
        exact ⟨_, rfl⟩
      · rename_i recursive
        rw [indexedVecValidationAlphaHasNoIndOcc] at recursive
        contradiction
  obtain ⟨consNTailTrace, consNTailRun⟩ :
      ∃ consNTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyNContext
          (indexedVecValidationConsAfterParam.bindingBody!.instantiate1
            indexedVecPreFamilyContext.freshExpr)
          2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyNContext
            (indexedVecValidationConsAfterParam.bindingBody!.instantiate1
              indexedVecPreFamilyContext.freshExpr)
            2 [] false 998 = .ok consNTailTrace := by
    rw [show indexedVecValidationConsAfterParam.bindingBody!.instantiate1
        indexedVecPreFamilyContext.freshExpr =
          indexedVecValidationConsAfterN by
      change indexedVecValidationConsAfterParam.bindingBody!.instantiate1
        indexedVecValidationNExpr = _
      exact indexedVecValidationConsAfterNShape]
    exact ⟨consAfterNTrace, consAfterNRun⟩
  obtain ⟨explicitNTailTrace, explicitNTailRun⟩ :
      ∃ explicitNTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope
          (indexedVecPreFamilyContext.pushLocalDecl consNName .implicit
            (AddInductive.consumeTypeAnnotations (.const ``Nat [])))
          ((Expr.forallE consHeadName indexedVecValidationAlpha
            (Expr.forallE consTailName
              (ctorIndexedVecApp indexedVecValidationAlpha (.bvar 1))
              (ctorIndexedVecApp indexedVecValidationAlpha
                (replaySuccApp (.bvar 2))) .default)
            .default).instantiate1 indexedVecPreFamilyContext.freshExpr)
          2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope
            (indexedVecPreFamilyContext.pushLocalDecl consNName .implicit
              (AddInductive.consumeTypeAnnotations (.const ``Nat [])))
            ((Expr.forallE consHeadName indexedVecValidationAlpha
              (Expr.forallE consTailName
                (ctorIndexedVecApp indexedVecValidationAlpha (.bvar 1))
                (ctorIndexedVecApp indexedVecValidationAlpha
                  (replaySuccApp (.bvar 2))) .default)
              .default).instantiate1 indexedVecPreFamilyContext.freshExpr)
            2 [] false 998 = .ok explicitNTailTrace := by
    rw [indexedVecValidationConsumeNat]
    rw [show Expr.forallE consHeadName indexedVecValidationAlpha
        (Expr.forallE consTailName
          (ctorIndexedVecApp indexedVecValidationAlpha (.bvar 1))
          (ctorIndexedVecApp indexedVecValidationAlpha
            (replaySuccApp (.bvar 2))) .default) .default =
          indexedVecValidationConsAfterParam.bindingBody! by
      rw [indexedVecValidationConsAfterParamExplicitShape]
      rfl]
    exact ⟨consNTailTrace, consNTailRun⟩
  have noParameterOne : indexedVecCandidateInductiveStats.params[1]? =
      none := by
    rw [indexedVecValidationStatsParams]
    rfl
  obtain ⟨consAfterParamTrace, consAfterParamRun⟩ :
      ∃ consAfterParamTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecValidationConsAfterParam 1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            indexedVecValidationConsAfterParam 1 [] false 999 =
          .ok consAfterParamTrace := by
    rw [indexedVecValidationConsAfterParamExplicitShape]
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterOne] at parameterAt
      contradiction
    · split
      · rw [baseNat.check_eq, baseNatEnsure.observe_eq,
          baseNatConsumed.check_eq]
        rw [dif_pos (by
          simp [AddInductive.constructorIndependentOf])]
        simp only [Bind.bind, Except.bind]
        rw [baseNatAnnotations.observe_eq]
        simp only []
        rw [dif_pos baseFresh]
        rw [explicitNTailRun]
        exact ⟨_, rfl⟩
      · rename_i recursive
        rw [indexedVecValidationNatHasNoIndOcc] at recursive
        contradiction
  obtain ⟨consParameterTailTrace, consParameterTailRun⟩ :
      ∃ consParameterTailTrace :
          AddInductive.ConstructorPreFamilyViewTrace
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            (consNTypeRaw.instantiate1 indexedVecValidationAlpha)
            1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            (consNTypeRaw.instantiate1 indexedVecValidationAlpha)
            1 [] false 999 = .ok consParameterTailTrace := by
    change ∃ consParameterTailTrace :
        AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecValidationConsAfterParam 1 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecValidationConsAfterParam 1 [] false 999 =
        .ok consParameterTailTrace
    exact ⟨consAfterParamTrace, consAfterParamRun⟩
  obtain ⟨consRawViewTrace, consRawViewRun⟩ :
      ∃ consRawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          consCtorTypeRaw 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            consCtorTypeRaw 0 [] false 1000 = .ok consRawViewTrace := by
    simp only [consCtorTypeRaw,
      AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [parameterAtZero] at parameterAt
      cases parameterAt
      rw [consParameterTailRun]
      exact ⟨_, rfl⟩
    · rename_i noParameter
      rw [parameterAtZero] at noParameter
      contradiction
  obtain ⟨consViewTrace, consViewRun⟩ :
      ∃ consViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecConsInfo.type 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            indexedVecConsInfo.type 0 [] false 1000 = .ok consViewTrace := by
    rw [consInfoTypeShape]
    exact ⟨consRawViewTrace, consRawViewRun⟩
  obtain ⟨consHeadTrace, consHeadRun⟩ :
      ∃ consHeadTrace : AddInductive.ConstructorPreFamilyViewTrace
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          indexedVecConsConstructorCandidate.type.view 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            indexedVecCandidateInductiveStats 0
            indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
            indexedVecConsConstructorCandidate.type.view 0 [] false 1000 =
          .ok consHeadTrace := by
    change ∃ consHeadTrace : AddInductive.ConstructorPreFamilyViewTrace
        indexedVecCandidateInductiveStats 0
        indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
        consCandidate.view 0 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          consCandidate.view 0 [] false 1000 = .ok consHeadTrace
    rw [consCandidate_view_eq]
    exact ⟨consViewTrace, consViewRun⟩
  let consListTrace : AddInductive.ConstructorPreFamilyListTrace
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyContext
      (.cons indexedVecConsConstructorCandidate .nil) :=
    .cons consHeadTrace .nil
  have consListRun : AddInductive.ConstructorPreFamilyListTrace.build
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyContext
      (.cons indexedVecConsConstructorCandidate .nil) =
        .ok consListTrace := by
    exact AddInductive.ConstructorPreFamilyListTrace.cons_build_eq
      consHeadTrace consHeadRun .nil rfl
  let constructorListTrace : AddInductive.ConstructorPreFamilyListTrace
      indexedVecCandidateInductiveStats 0 indexedVecPreFamilyIndexTelescope
      indexedVecPreFamilyContext
      (.cons indexedVecNilConstructorCandidate
        (.cons indexedVecConsConstructorCandidate .nil)) :=
    .cons nilHeadTrace consListTrace
  have constructorListRun :
      AddInductive.ConstructorPreFamilyListTrace.build
          indexedVecCandidateInductiveStats 0
          indexedVecPreFamilyIndexTelescope indexedVecPreFamilyContext
          (.cons indexedVecNilConstructorCandidate
            (.cons indexedVecConsConstructorCandidate .nil)) =
        .ok constructorListTrace := by
    exact AddInductive.ConstructorPreFamilyListTrace.cons_build_eq
      nilHeadTrace nilHeadRun consListTrace consListRun
  have parametersRun : AddInductive.instantiateFamilyParameters
      indexedVecInfo.type indexedVecCandidateInductiveStats.params.toList =
        .ok indexedVecPreFamilyIndexTelescope := by
    rw [indexedVecPreFamilyIndexTelescope_eq]
    rw [indexedVecValidationStatsParams]
    rw [indexedVecInfoTypeShape]
    simp [AddInductive.instantiateFamilyParameters, vecFamilyTail, vecIndexName,
      Expr.instantiate1_eq, Expr.instantiate1', Pure.pure, Except.pure]
  unfold AddInductive.checkConstructorPreFamilySafety
  have translationUnique :
      (AddInductive.theoryTranslationUnique indexedVecInfo.type &&
        (AddInductive.CandidateList.cons indexedVecNilConstructorCandidate
          (AddInductive.CandidateList.cons indexedVecConsConstructorCandidate
            (AddInductive.CandidateList.nil : AddInductive.CandidateList
              AddInductive.CandidateConstructor []))).viewTranslationUnique) =
        true := by
    change (AddInductive.theoryTranslationUnique indexedVecInfo.type &&
      (nilCandidateTrace.viewTranslationUnique &&
        (consCandidateTrace.viewTranslationUnique && true))) = true
    rw [nilCandidateTrace.viewTranslationUnique_eq,
      consCandidateTrace.viewTranslationUnique_eq]
    change (AddInductive.theoryTranslationUnique indexedVecInfo.type &&
      (AddInductive.theoryTranslationUnique nilCandidate.view &&
        (AddInductive.theoryTranslationUnique consCandidate.view && true))) =
          true
    rw [nilCandidate_view_eq, consCandidate_view_eq,
      indexedVecInfoTypeShape, nilInfoTypeShape, consInfoTypeShape]
    simp [AddInductive.theoryTranslationUnique, vecFamilyTail,
      nilCtorTypeRaw, nilCtorBodyRaw, consCtorTypeRaw, consNTypeRaw,
      consHeadTypeRaw, consTailTypeRaw, consTerminalRaw]
  rw [if_pos translationUnique]
  rw [parametersRun]
  simp only [Bind.bind, Except.bind]
  rw [constructorListRun]
  rfl

private def indexedVecStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    indexedVecStagedPostFamilyInput indexedVecPreFamilySafetyRun

/-- IndexedVec's ordinary fields are retained, its recursive tail is omitted,
and both constructor-result index spines admit the exact pre-family semantic
replay. -/
theorem indexedVecProducedPreFamilySemantic_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidatePreFamilySemanticRun
      indexedVecStagedPreFamilyInput) :=
  indexedVecStagedPreFamilyInput.exists

private def indexedVecReorderedViewType : VInductiveType :=
  { indexedVecType with
    ctors := [indexedVecType.ctors[1], indexedVecType.ctors[0]] }

private def indexedVecReorderedViewDecl : VInductDecl :=
  { indexedVecDecl with types := [indexedVecReorderedViewType] }

/-- Swapping the two otherwise unchanged constructor payloads fails the
computational normalization-shape gate before semantic or generation evidence
can be attached. -/
theorem indexedVecReorderedView_rejected :
    VInductDecl.normalization? indexedVecDecl
      indexedVecReorderedViewDecl = none := rfl

theorem indexedVecSemanticFamilyViewTr :
    TrExpr natFinalEnv [`u] [] indexedVecFamilyCandidate.view
      indexedVecType.type := by
  rw [indexedVecFamilyCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecType_wf
  exact ⟨_, indexedVecSemanticFamilySourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticNilViewTr :
    TrExpr indexedVecTypeEnv [`u] [] nilCandidate.view
      indexedVecType.ctors[0].type := by
  rw [nilCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecNil_wf
  exact ⟨_, indexedVecSemanticNilSourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticConsViewTr :
    TrExpr indexedVecTypeEnv [`u] [] consCandidate.view
      indexedVecType.ctors[1].type := by
  rw [consCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact ⟨_, indexedVecSemanticConsSourceTr, ⟨_, htype⟩⟩

def indexedVecSemanticFamilyRootRun :
    TypeChecker.CandidateExprRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type indexedVecType.type where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticFamilySourceTr
  view_tr := indexedVecSemanticFamilyViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticNilRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type where
  contextRun := by
    simpa [nilCandidate, nilCandidateContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticNilSourceTr
  view_tr := indexedVecSemanticNilViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticConsRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type where
  contextRun := by
    simpa [consCandidate, consRootContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticConsSourceTr
  view_tr := indexedVecSemanticConsViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type :=
  indexedVecSemanticFamilyRootRun.semanticOfIdentity
    indexedVecFamilyCandidate_identity

def indexedVecSemanticNilSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type :=
  indexedVecSemanticNilRootRun.semanticOfIdentity nilCandidate_identity

def indexedVecSemanticConsSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type :=
  indexedVecSemanticConsRootRun.semanticOfIdentity consCandidate_identity

def indexedVecSemanticNilConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticNilSemanticRootRun

def indexedVecSemanticConsConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticConsSemanticRootRun

def indexedVecSemanticNilConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] :=
  indexedVecSemanticNilConstructorSemanticRun.root

def indexedVecSemanticConsConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] :=
  indexedVecSemanticConsConstructorSemanticRun.root

def indexedVecSemanticConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors := by
  exact .cons indexedVecSemanticNilConstructorSemanticRun
    (.cons indexedVecSemanticConsConstructorSemanticRun .nil)

def indexedVecSemanticConstructorListRun :
    VInductDecl.CandidateConstructorListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors :=
  indexedVecSemanticConstructorSemanticListRun.roots

def indexedVecSemanticFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticFamilySemanticRootRun
  typeEnv := indexedVecTypeEnv
  addType := rfl
  constructors := indexedVecSemanticConstructorSemanticListRun

def indexedVecSemanticFamilyRun :
    VInductDecl.CandidateFamilyRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType :=
  indexedVecSemanticFamilySemanticRun.root

def indexedVecSemanticNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  raw := indexedVecType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := indexedVecSemanticFamilyRun

/-- Reconstructing every family and constructor payload leaves the identity
IndexedVec declaration unchanged. -/
theorem indexedVecSemantic_viewDecl_eq :
    indexedVecSemanticNormalizationCandidateRun.viewDecl =
      indexedVecDecl := rfl

/-- The candidate-derived normalization is exactly the analyzer's canonical
identity normalization, not merely propositionally interchangeable with it. -/
theorem indexedVecSemantic_normalization_eq :
    indexedVecSemanticNormalizationCandidateRun.normalization =
      indexedVecChecked.identityGeneration.block.normalization := rfl

theorem indexedVecSemanticFamilySpineRun :
    TypeChecker.CandidateExprSpineRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type
      indexedVecType.type :=
  indexedVecSemanticFamilySemanticRootRun.spine
    indexedVecFamilyCandidate_identity.storedSpine

theorem indexedVecSemanticNilSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type :=
  indexedVecSemanticNilSemanticRootRun.spine
    nilCandidate_identity.storedSpine

theorem indexedVecSemanticConsSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type :=
  indexedVecSemanticConsSemanticRootRun.spine
    consCandidate_identity.storedSpine

theorem indexedVecSemanticCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape indexedVecDecl
      indexedVecType indexedVecNormalizationCandidate = true := by
  change ((indexedVecFamilyCandidate.trace.storedSpine && true) &&
    ((nilCandidate.trace.storedSpine && true) &&
      ((consCandidate.trace.storedSpine && true) && true))) = true
  rw [indexedVecFamilyCandidate_identity.storedSpine,
    nilCandidate_identity.storedSpine,
    consCandidate_identity.storedSpine]
  rfl

/-- The consolidated constructor gate rejects truncation in either direction
before dependent semantic generation is assembled. -/
theorem indexedVecSemanticCandidate_missingRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      (.cons indexedVecNilConstructorCandidate .nil) [] = false :=
  rfl

theorem indexedVecSemanticCandidate_extraRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      .nil [indexedVecType.ctors[0]] = false :=
  rfl

def indexedVecSemanticProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext where
  candidate := indexedVecNormalizationCandidate
  produced := indexedVecNormalizationCandidateProduced
  shape := indexedVecSemanticCandidate_generationShape

/-- The strengthened outer gate retains the complete parameter/index and
ordered `nil`/`cons` generation layout in the same produced result. -/
theorem indexedVecSemanticGenerationShapeCandidate_produced :
    VInductDecl.produceGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecSemanticProducedGenerationShapeCandidate := by
  have produced :
      AddInductive.buildNormalizationCandidate indexedVecDecl.nparams
          [indexedVecKernelType] 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecNormalizationCandidate :=
    indexedVecNormalizationCandidateProduced
  simpa only [indexedVecSemanticProducedGenerationShapeCandidate] using
    VInductDecl.produceGenerationShapeCandidate_eq_ok
      (source := indexedVecDecl) (raw := indexedVecType)
      produced indexedVecSemanticCandidate_generationShape

private theorem indexedVecSemanticCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun
      natFinalEnv [`u] indexedVecNormalizationCandidate indexedVecDecl) :
    normalization.root.normalization.generation? =
      some indexedVecChecked.identityGeneration := by
  let reference : VInductDecl.NormalizationCandidateSemanticRun natFinalEnv
      [`u] indexedVecNormalizationCandidate indexedVecDecl := {
    raw := indexedVecType
    raw_types_eq := rfl
    uvars_eq := rfl
    family := indexedVecSemanticFamilySemanticRun }
  rw [indexedVecStagedPreFamilyInput.normalization_eq normalization reference]
  rfl

/-- The parameter/index and two-constructor fixture closes through the same
generic staged-owner theorem without supplying its semantic hierarchy. -/
theorem indexedVecSemanticExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      natFinalEnv [`u] indexedVecSemanticProducedGenerationShapeCandidate
      indexedVecChecked.identityGeneration) :=
  indexedVecSemanticProducedGenerationShapeCandidate
    |>.exactProducedPackage_nonempty indexedVecStagedPreFamilyInput rfl
      indexedVecChecked.identityGeneration indexedVecSemanticCandidate_analysis

private def
    indexedVecSemanticExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage natFinalEnv [`u]
      indexedVecSemanticProducedGenerationShapeCandidate
      indexedVecChecked.identityGeneration :=
  indexedVecSemanticProducedGenerationShapeCandidate.exactProducedPackage
    indexedVecStagedPreFamilyInput rfl indexedVecChecked.identityGeneration
    indexedVecSemanticCandidate_analysis

def indexedVecSemanticGenerationCandidateSemanticRun :
  VInductDecl.GenerationCandidateSemanticRun
      indexedVecSemanticExactProducedGenerationCandidatePackage.normalization
      indexedVecChecked.identityGeneration :=
  indexedVecSemanticExactProducedGenerationCandidatePackage.semantic

def indexedVecSemanticGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      indexedVecSemanticExactProducedGenerationCandidatePackage.normalization.root
      indexedVecChecked.identityGeneration :=
  indexedVecSemanticGenerationCandidateSemanticRun.run

def indexedVecSemanticGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticGenerationCandidateSemanticRun.package

def indexedVecSemanticProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticExactProducedGenerationCandidatePackage.package

def indexedVecSemanticGenerationCertificate :
    indexedVecDecl.GenerationCertificate natFinalEnv where
  generation := indexedVecChecked.identityGeneration
  wf :=
    indexedVecSemanticExactProducedGenerationCandidatePackage.semantic.run.wf

theorem indexedVecSemantic_addInductCertified :
    natFinalEnv.addInductCertified indexedVecSemanticGenerationCertificate =
      some indexedVecFinalEnv := by
  rfl

theorem indexedVecSemanticCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace natFinalEnv
      indexedVecFinalEnv indexedVecChecked.identityGeneration) :=
  VEnv.addInductCertified_trace indexedVecSemantic_addInductCertified

theorem indexedVecSemanticCertified_ordered :
    indexedVecFinalEnv.Ordered :=
  VEnv.addInductCertified_WF nat_env_wf.ordered
    indexedVecSemantic_addInductCertified

def indexedVecSemanticAddInductTraceChecked :
    AddInductTrace natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv := by
  refine indexedVecSemanticProducedGenerationCandidatePackage.package.addInductTrace
    indexedVecTypeMap indexedVecTypeEnv indexedVecCtorMap
    indexedVecCtorEnv indexedVecRecEnv ?_ ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := indexedVecInfo
      kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
      tr := indexedVecInfo_tr
      map_fresh := by
        rw [show
          indexedVecSemanticProducedGenerationCandidatePackage.package.generation.block.sourceType.name =
            ``IndexedVec by rfl]
        exact indexedVecType_fresh
      env_add := rfl
      map_add := rfl }
  · refine .cons (m₂ := indexedVecNilMap)
      (env₂ := indexedVecNilEnv) ?_ ?_
    · exact {
        info := indexedVecNilInfo
        kind_eq := by simp [indexedVecNilInfo, InductConstantKind.Matches]
        tr := indexedVecNilInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecNil_fresh
        env_add := rfl
        map_add := rfl }
    · refine .cons ?_ .nil
      exact {
        info := indexedVecConsInfo
        kind_eq := by simp [indexedVecConsInfo, InductConstantKind.Matches]
        tr := indexedVecConsInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecCons_fresh
        env_add := rfl
        map_add := rfl }
  · exact {
      info := indexedVecRecInfo
      kind_eq := by simp [indexedVecRecInfo, InductConstantKind.Matches]
      tr := indexedVecRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            indexedVecSemanticProducedGenerationCandidatePackage.package.generation).name =
              ``IndexedVec.rec by rfl]
        exact indexedVecRec_fresh
      env_add := rfl
      map_add := rfl }
  · decide

theorem indexedVecSemantic_addInduct_checked :
    AddInduct natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv :=
  ⟨indexedVecSemanticAddInductTraceChecked⟩

theorem indexedVecSemantic_trEnv'_checked :
    TrEnv' .safe indexedVecMap false indexedVecFinalEnv :=
  .induct indexedVecSemantic_addInduct_checked nat_trEnv'

theorem indexedVecSemantic_env_wf_checked : indexedVecFinalEnv.WF :=
  indexedVecSemantic_trEnv'_checked.wf

theorem indexedVecSemantic_aligned_checked :
    Aligned .safe indexedVecMap indexedVecFinalEnv :=
  indexedVecSemantic_trEnv'_checked.aligned

/-
The semantic assembly, executable producer, and final E1 replay intentionally
inherit the existing transitional verifier closure. These guards make
additions to that closure visible at the public roots of this module.
-/
#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecProducedPostFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecProducedPreFamilySemantic_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_constructorHeaders [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecReorderedView_rejected [propext]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticCandidate_missingRawShape_rejected [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticCandidate_extraRawShape_rejected [propext, Classical.choice, Quot.sound]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticGenerationShapeCandidate_produced [
  propext,
  Classical.choice,
  Quot.sound,
  Lean.Expr.eqv_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticExactProducedGenerationCandidatePackage_exists [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticGenerationCandidateSemanticRun [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemanticProducedGenerationCandidatePackage [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

#guard_named_axioms Ix.Theory.Named.InductiveReplayFixtures.indexedVecSemantic_trEnv'_checked [
  propext,
  sorryAx,
  Classical.choice,
  Ix.Theory.Named.ptrEqConstantInfo_eq,
  Quot.sound,
  Lean.Expr.abstractRange_eq,
  Lean.Expr.abstract_eq,
  Lean.Expr.eqv_eq,
  Lean.Expr.hasLooseBVar_eq,
  Lean.Expr.instantiate1_eq,
  Lean.Expr.instantiateRange_eq,
  Lean.Expr.instantiateRevRange_eq,
  Lean.Expr.instantiateRev_eq,
  Lean.Expr.instantiate_eq,
  Lean.Expr.looseBVarRange_eq,
  Lean.Expr.lowerLooseBVars_eq,
  Lean.Expr.mkAppData_eq,
  Lean.Expr.mkData_eq,
  Lean.Expr.replace_eq,
  Lean.Level.hasMVar_eq,
  Lean.Level.hasParam_eq,
  Lean.Level.instLawfulBEqLevel,
  Lean.Level.isExplicitSubsumedAux_eq,
  Lean.Level.normalize_eq,
  Lean.PersistentArray.toList'_push,
  Lean.PersistentHashMap.findAux_isSome,
  Lean.Syntax.structEq_eq,
  Std.TreeMap.all_eq_all_toList,
  Lean.PersistentHashMap.WF.find?_eq,
  Lean.PersistentHashMap.WF.toList'_insert]

end Ix.Theory.Named.InductiveReplayFixtures
