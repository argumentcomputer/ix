import Ix.Tc.Verify.Inductive.IndexedBlockValidation
import Ix.Tc.Verify.Inductive.PositivityTraceAdapter

/-!
# Production-selected IndexedVec positivity

The concrete operation fixtures replay positivity from a convenient standalone
state.  This module retains a different boundary: every trace below is
projected from the `IndexedVec.cons` validation selected by the exact
`checkInductiveBlock` execution.  In particular, none of the intermediate
states is reconstructed by running positivity a second time.
-/

namespace Ix.Tc.IndexedRecursiveFixture

/-- The production-selected constructor is the exact ingressed `cons`
declaration, not merely some telescope that happened to pass the same
metadata guards. -/
theorem indexedVecConsProductionConcreteMetadataAndCoreTrace :
    ∃ (afterMetadata afterParameters afterCore afterPositivity :
        TcState .anon),
      ConstructorMetadataValidationTrace consId familyId 1 1 1 false
          checkerMethods consConcrete.ty 3 familyNilValidationAfter
            afterMetadata ∧
        (RecM.checkParamAgreement familyConcrete.ty consConcrete.ty 1).run
            checkerMethods afterMetadata = .ok () afterParameters ∧
        ConstructorPositivityCoreTrace consConcrete.ty 1 #[familyId.addr]
          checkerMethods afterParameters afterCore ∧
        afterPositivity = { afterCore with
          lctx := afterCore.lctx.truncate afterParameters.lctx.size } := by
  obtain ⟨final, validation⟩ :=
    indexedVecConsProductionValidationTraceExact
  cases validation with
  | success metadata parameters positivity universes returnType =>
      clear universes returnType
      have metadataTrace :=
        RecM.checkCtorMetadataAgainstParent_success metadata
      cases metadataTrace with
      | success fields_eq lookup run =>
          rw [familyNilAfterConsHeaderLookupRun] at lookup
          cases lookup
          cases fields_eq
          cases positivity with
          | safe positivityRun positivityTrace =>
              clear positivityRun
              cases positivityTrace with
              | success core restored =>
                  exact ⟨_, _, _, _, .success rfl
                    familyNilAfterConsHeaderLookupRun run, parameters, core,
                      restored⟩

/-- Canonical state immediately after the production `cons` metadata gate. -/
def familyConsMetadataAfter : TcState .anon :=
  match
      (RecM.checkCtorMetadataAgainstParent consId familyId 1 1 1 false).run
        checkerMethods familyNilValidationAfter with
  | .ok _ after => after
  | .error _ failed => failed

theorem familyConsMetadataRun :
    (RecM.checkCtorMetadataAgainstParent consId familyId 1 1 1 false).run
      checkerMethods familyNilValidationAfter =
        .ok (consConcrete.ty, 3) familyConsMetadataAfter := by
  obtain ⟨afterMetadata, _, _, _, metadata, _, _, _⟩ :=
    indexedVecConsProductionConcreteMetadataAndCoreTrace
  cases metadata with
  | success fields_eq lookup run =>
      unfold familyConsMetadataAfter
      rw [run]

/-- Canonical state at the protected positivity ingress, after A1 has checked
the shared `IndexedVec` parameter against this exact constructor. -/
def familyConsParameterAgreementAfter : TcState .anon :=
  match
      (RecM.checkParamAgreement familyConcrete.ty consConcrete.ty 1).run
        checkerMethods familyConsMetadataAfter with
  | .ok _ after => after
  | .error _ failed => failed

theorem familyConsParameterAgreementRun :
    (RecM.checkParamAgreement familyConcrete.ty consConcrete.ty 1).run
      checkerMethods familyConsMetadataAfter =
        .ok () familyConsParameterAgreementAfter := by
  obtain ⟨afterMetadata, afterParameters, _, _, metadata, parameters, _, _⟩ :=
    indexedVecConsProductionConcreteMetadataAndCoreTrace
  cases metadata with
  | success fields_eq lookup run =>
      rw [familyConsMetadataRun] at run
      cases run
      unfold familyConsParameterAgreementAfter
      rw [parameters]

/-- Exact one-parameter positivity ingress selected after A1. -/
def familyConsPositivityParametersOutcome :=
  (RecM.openPositivityParameters consConcrete.ty 1 (Array.mkEmpty 1)).run
    checkerMethods familyConsParameterAgreementAfter

def familyConsFieldsSource : KExpr .anon :=
  match familyConsPositivityParametersOutcome with
  | .ok (some (fieldsSource, _)) _ => fieldsSource
  | _ => default

def familyConsParameterFVars : Array (KExpr .anon) :=
  match familyConsPositivityParametersOutcome with
  | .ok (some (_, parameterFVars)) _ => parameterFVars
  | _ => #[]

def familyConsPositivityParametersAfter : TcState .anon :=
  match familyConsPositivityParametersOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsPositivityParametersSucceededNative :
    (match familyConsPositivityParametersOutcome with
      | .ok (some _) _ => true
      | _ => false) = true := by
  native_decide

/-- The exact production ingress consumes the shared parameter; its
permissive `none` result is impossible for the certified `cons` telescope. -/
theorem familyConsPositivityParametersRun :
    (RecM.openPositivityParameters consConcrete.ty 1 (Array.mkEmpty 1)).run
      checkerMethods familyConsParameterAgreementAfter =
        .ok (some (familyConsFieldsSource, familyConsParameterFVars))
          familyConsPositivityParametersAfter := by
  have success := familyConsPositivityParametersSucceededNative
  unfold familyConsFieldsSource familyConsParameterFVars
    familyConsPositivityParametersAfter
  generalize houtcome : familyConsPositivityParametersOutcome = outcome
    at success ⊢
  cases outcome with
  | error err failed => simp at success
  | ok result after =>
      cases result with
      | none => simp at success
      | some payload =>
          rcases payload with ⟨fieldsSource, parameterFVars⟩
          simpa only [familyConsPositivityParametersOutcome] using houtcome

/-- Root group installed by the exact production parameter-prefix execution. -/
def familyConsRootPositivityGroup : PositivityGroup .anon :=
  { addrs := #[familyId.addr]
    params := familyConsParameterFVars
    concreteUs := none }

/-- Complete positivity-group stack used by the production-selected `cons`. -/
def familyConsPositivityGroups : Array (PositivityGroup .anon) :=
  #[familyConsRootPositivityGroup]

/-- Complete source-ordered field traversal projected from the real `cons`
validation.  The malformed short-telescope branch has now been eliminated by
the exact production parameter ingress above. -/
theorem indexedVecConsProductionFieldsTrace :
    ∃ final : TcState .anon,
      ConstructorPositivityFieldsTrace
        familyConsPositivityGroups
        #[familyId.addr] checkerMethods maxWhnfFuel.toNat
          familyConsFieldsSource familyConsPositivityParametersAfter final := by
  obtain ⟨afterMetadata, afterParameters, afterCore, afterPositivity,
      metadata, parameters, core, restored⟩ :=
    indexedVecConsProductionConcreteMetadataAndCoreTrace
  cases metadata with
  | success fields_eq lookup metadataRun =>
      rw [familyConsMetadataRun] at metadataRun
      cases metadataRun
      rw [familyConsParameterAgreementRun] at parameters
      cases parameters
      cases core with
      | short parameterTrace =>
          have ingress := parameterTrace.run
          rw [familyConsPositivityParametersRun] at ingress
          cases ingress
      | fields parameterTrace fields =>
          have ingress := parameterTrace.run
          rw [familyConsPositivityParametersRun] at ingress
          cases ingress
          exact ⟨_, fields⟩

/-! ## Exact production field-loop observations

The definitions below start at `familyConsPositivityParametersAfter`, the
state selected by the real family-block execution above.  They are not the
older standalone `checkerInitial` replay.  The final projection theorem will
also destruct `indexedVecConsProductionFieldsTrace` and align every named
observation by determinism, so these computations cannot be spliced into an
unrelated successful traversal.
-/

/-- Total projection used only after an accompanying exact forall-shape
theorem has ruled out the fallback. -/
def productionForallDomain : KExpr .anon → KExpr .anon
  | .all _ _ domain _ _ => domain
  | source => source

/-- Total body projection paired with `productionForallDomain`. -/
def productionForallBody : KExpr .anon → KExpr .anon
  | .all _ _ _ body _ => body
  | source => source

/-- First field-loop WHNF, reached immediately after the production parameter
prefix has opened `α`. -/
def familyConsNatTelescopeWhnfOutcome :=
  (RecM.whnf familyConsFieldsSource).run checkerMethods
    familyConsPositivityParametersAfter

def familyConsNatTelescopeWhnfResult : KExpr .anon :=
  match familyConsNatTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyConsNatDomainState : TcState .anon :=
  match familyConsNatTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyConsNatDomain : KExpr .anon :=
  productionForallDomain familyConsNatTelescopeWhnfResult

def familyConsNatBody : KExpr .anon :=
  productionForallBody familyConsNatTelescopeWhnfResult

private theorem familyConsNatTelescopeWhnfIsForallNative :
    (match familyConsNatTelescopeWhnfOutcome with
      | .ok (.all ..) _ => true
      | _ => false) = true := by
  native_decide

/-- Exact forall-shaped first field-loop WHNF selected by production. -/
theorem familyConsNatTelescopeWhnfRun :
    ∃ name bi info,
      (RecM.whnf familyConsFieldsSource).run checkerMethods
          familyConsPositivityParametersAfter =
        .ok (.all name bi familyConsNatDomain familyConsNatBody info)
          familyConsNatDomainState := by
  have shape := familyConsNatTelescopeWhnfIsForallNative
  unfold familyConsNatDomain familyConsNatBody productionForallDomain
    productionForallBody familyConsNatTelescopeWhnfResult
    familyConsNatDomainState
  generalize houtcome : familyConsNatTelescopeWhnfOutcome = outcome
    at shape ⊢
  cases outcome with
  | error err failed => simp at shape
  | ok result after =>
      cases result <;> simp_all [familyConsNatTelescopeWhnfOutcome]

private theorem familyConsNatDomainRootFreeNative :
    exprMentionsAnyAddr familyConsNatDomain #[familyId.addr] = false := by
  native_decide

/-- `Nat` cannot mention the freshly declared indexed family. -/
theorem familyConsNatDomainRootFree :
    exprMentionsAnyAddr familyConsNatDomain #[familyId.addr] = false :=
  familyConsNatDomainRootFreeNative

/-- Production opening of the first ordinary field binder. -/
def familyConsNatOpenOutcome :=
  TcM.openBinderAnon familyConsNatDomain familyConsNatBody
    familyConsNatDomainState

def familyConsAfterNat : KExpr .anon :=
  match familyConsNatOpenOutcome with
  | .ok (opened, _) _ => opened
  | .error _ _ => default

def familyConsNatFVarId : FVarId :=
  match familyConsNatOpenOutcome with
  | .ok (_, id) _ => id
  | .error _ _ => default

def familyConsAfterNatState : TcState .anon :=
  match familyConsNatOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsNatOpenSucceededNative :
    (match familyConsNatOpenOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsNatOpenRun :
    TcM.openBinderAnon familyConsNatDomain familyConsNatBody
        familyConsNatDomainState =
      .ok (familyConsAfterNat, familyConsNatFVarId)
        familyConsAfterNatState := by
  have success := familyConsNatOpenSucceededNative
  unfold familyConsAfterNat familyConsNatFVarId familyConsAfterNatState
  generalize houtcome : familyConsNatOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsNatOpenOutcome]

/-- Second field-loop WHNF, after opening the Nat index binder. -/
def familyConsHeadTelescopeWhnfOutcome :=
  (RecM.whnf familyConsAfterNat).run checkerMethods familyConsAfterNatState

def familyConsHeadTelescopeWhnfResult : KExpr .anon :=
  match familyConsHeadTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyConsHeadDomainState : TcState .anon :=
  match familyConsHeadTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyConsHeadDomain : KExpr .anon :=
  productionForallDomain familyConsHeadTelescopeWhnfResult

def familyConsHeadBody : KExpr .anon :=
  productionForallBody familyConsHeadTelescopeWhnfResult

private theorem familyConsHeadTelescopeWhnfIsForallNative :
    (match familyConsHeadTelescopeWhnfOutcome with
      | .ok (.all ..) _ => true
      | _ => false) = true := by
  native_decide

theorem familyConsHeadTelescopeWhnfRun :
    ∃ name bi info,
      (RecM.whnf familyConsAfterNat).run checkerMethods
          familyConsAfterNatState =
        .ok (.all name bi familyConsHeadDomain familyConsHeadBody info)
          familyConsHeadDomainState := by
  have shape := familyConsHeadTelescopeWhnfIsForallNative
  unfold familyConsHeadDomain familyConsHeadBody productionForallDomain
    productionForallBody familyConsHeadTelescopeWhnfResult
    familyConsHeadDomainState
  generalize houtcome : familyConsHeadTelescopeWhnfOutcome = outcome
    at shape ⊢
  cases outcome with
  | error err failed => simp at shape
  | ok result after =>
      cases result <;> simp_all [familyConsHeadTelescopeWhnfOutcome]

private theorem familyConsHeadDomainRootFreeNative :
    exprMentionsAnyAddr familyConsHeadDomain #[familyId.addr] = false := by
  native_decide

/-- The opened shared parameter is root-free. -/
theorem familyConsHeadDomainRootFree :
    exprMentionsAnyAddr familyConsHeadDomain #[familyId.addr] = false :=
  familyConsHeadDomainRootFreeNative

def familyConsHeadOpenOutcome :=
  TcM.openBinderAnon familyConsHeadDomain familyConsHeadBody
    familyConsHeadDomainState

def familyConsAfterHead : KExpr .anon :=
  match familyConsHeadOpenOutcome with
  | .ok (opened, _) _ => opened
  | .error _ _ => default

def familyConsHeadFVarId : FVarId :=
  match familyConsHeadOpenOutcome with
  | .ok (_, id) _ => id
  | .error _ _ => default

def familyConsAfterHeadState : TcState .anon :=
  match familyConsHeadOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsHeadOpenSucceededNative :
    (match familyConsHeadOpenOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsHeadOpenRun :
    TcM.openBinderAnon familyConsHeadDomain familyConsHeadBody
        familyConsHeadDomainState =
      .ok (familyConsAfterHead, familyConsHeadFVarId)
        familyConsAfterHeadState := by
  have success := familyConsHeadOpenSucceededNative
  unfold familyConsAfterHead familyConsHeadFVarId familyConsAfterHeadState
  generalize houtcome : familyConsHeadOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsHeadOpenOutcome]

/-- Third field-loop WHNF, exposing the recursive `IndexedVec α n` domain. -/
def familyConsTailTelescopeWhnfOutcome :=
  (RecM.whnf familyConsAfterHead).run checkerMethods familyConsAfterHeadState

def familyConsTailTelescopeWhnfResult : KExpr .anon :=
  match familyConsTailTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyConsTailDomainState : TcState .anon :=
  match familyConsTailTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyConsTailDomain : KExpr .anon :=
  productionForallDomain familyConsTailTelescopeWhnfResult

def familyConsTailBody : KExpr .anon :=
  productionForallBody familyConsTailTelescopeWhnfResult

private theorem familyConsTailTelescopeWhnfIsForallNative :
    (match familyConsTailTelescopeWhnfOutcome with
      | .ok (.all ..) _ => true
      | _ => false) = true := by
  native_decide

theorem familyConsTailTelescopeWhnfRun :
    ∃ name bi info,
      (RecM.whnf familyConsAfterHead).run checkerMethods
          familyConsAfterHeadState =
        .ok (.all name bi familyConsTailDomain familyConsTailBody info)
          familyConsTailDomainState := by
  have shape := familyConsTailTelescopeWhnfIsForallNative
  unfold familyConsTailDomain familyConsTailBody productionForallDomain
    productionForallBody familyConsTailTelescopeWhnfResult
    familyConsTailDomainState
  generalize houtcome : familyConsTailTelescopeWhnfOutcome = outcome
    at shape ⊢
  cases outcome with
  | error err failed => simp at shape
  | ok result after =>
      cases result <;> simp_all [familyConsTailTelescopeWhnfOutcome]

private theorem familyConsTailDomainMentionsRootNative :
    exprMentionsAnyAddr familyConsTailDomain #[familyId.addr] = true := by
  native_decide

theorem familyConsTailDomainMentionsRoot :
    exprMentionsAnyAddr familyConsTailDomain #[familyId.addr] = true :=
  familyConsTailDomainMentionsRootNative

/-- WHNF performed inside positivity on the recursive field domain. -/
def familyConsTailDomainWhnfOutcome :=
  (RecM.whnf familyConsTailDomain).run checkerMethods
    familyConsTailDomainState

def familyConsTailDomainWhnfResult : KExpr .anon :=
  match familyConsTailDomainWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyConsTailDomainWhnfAfter : TcState .anon :=
  match familyConsTailDomainWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsTailDomainWhnfSucceededNative :
    (match familyConsTailDomainWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsTailDomainWhnfRun :
    (RecM.whnf familyConsTailDomain).run checkerMethods
        familyConsTailDomainState =
      .ok familyConsTailDomainWhnfResult familyConsTailDomainWhnfAfter := by
  have success := familyConsTailDomainWhnfSucceededNative
  unfold familyConsTailDomainWhnfResult familyConsTailDomainWhnfAfter
  generalize houtcome : familyConsTailDomainWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsTailDomainWhnfOutcome]

private theorem familyConsTailDomainWhnfNotForallNative :
    (match familyConsTailDomainWhnfResult with
      | .all .. => false
      | _ => true) = true := by
  native_decide

theorem familyConsTailDomainWhnfNotForall :
    PositivityTerminalForm familyConsTailDomainWhnfResult := by
  have terminal := familyConsTailDomainWhnfNotForallNative
  generalize hresult : familyConsTailDomainWhnfResult = result at terminal ⊢
  cases result <;> simp_all [PositivityTerminalForm]

def familyConsTailWhnfSpineHead : KExpr .anon :=
  familyConsTailDomainWhnfResult.collectSpine.1

def familyConsTailWhnfSpineArgs : Array (KExpr .anon) :=
  familyConsTailDomainWhnfResult.collectSpine.2

def familyConsTailWhnfSpineId : KId .anon :=
  match familyConsTailWhnfSpineHead with
  | .const id _ _ => id
  | _ => default

def familyConsTailWhnfSpineUniverses : Array (KUniv .anon) :=
  match familyConsTailWhnfSpineHead with
  | .const _ universes _ => universes
  | _ => default

def familyConsTailWhnfSpineInfo : ExprInfo .anon :=
  match familyConsTailWhnfSpineHead with
  | .const _ _ info => info
  | head => head.info

private theorem familyConsTailWhnfSpineIsConstNative :
    (match familyConsTailWhnfSpineHead with
      | .const .. => true
      | _ => false) = true := by
  native_decide

theorem familyConsTailWhnfSpine :
    familyConsTailDomainWhnfResult.collectSpine =
      (.const familyConsTailWhnfSpineId familyConsTailWhnfSpineUniverses
        familyConsTailWhnfSpineInfo, familyConsTailWhnfSpineArgs) := by
  have shape := familyConsTailWhnfSpineIsConstNative
  generalize hspine : familyConsTailDomainWhnfResult.collectSpine = spine
    at shape ⊢
  rcases spine with ⟨head, args⟩
  cases head <;> simp_all [familyConsTailWhnfSpineHead,
    familyConsTailWhnfSpineArgs, familyConsTailWhnfSpineId,
    familyConsTailWhnfSpineUniverses, familyConsTailWhnfSpineInfo]

private theorem familyConsTailWhnfSpineActiveNative :
    familyConsRootPositivityGroup.addrs.contains
      familyConsTailWhnfSpineId.addr = true := by
  native_decide

theorem familyConsTailWhnfSpineActive :
    familyConsRootPositivityGroup.addrs.contains
      familyConsTailWhnfSpineId.addr = true :=
  familyConsTailWhnfSpineActiveNative

/-- Exact production positivity result for the recursive field domain. -/
def familyConsTailDomainOutcome :=
  (RecM.checkPositivityDomain familyConsTailDomain familyConsPositivityGroups
    #[familyId.addr]).run checkerMethods familyConsTailDomainState

def familyConsTailDomainAfter : TcState .anon :=
  match familyConsTailDomainOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsTailDomainSucceededNative :
    (match familyConsTailDomainOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsTailDomainRun :
    (RecM.checkPositivityDomain familyConsTailDomain familyConsPositivityGroups
      #[familyId.addr]).run checkerMethods familyConsTailDomainState =
        .ok () familyConsTailDomainAfter := by
  have success := familyConsTailDomainSucceededNative
  unfold familyConsTailDomainAfter
  generalize houtcome : familyConsTailDomainOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsTailDomainOutcome]

def familyConsTailOpenOutcome :=
  TcM.openBinderAnon familyConsTailDomain familyConsTailBody
    familyConsTailDomainAfter

def familyConsResultSource : KExpr .anon :=
  match familyConsTailOpenOutcome with
  | .ok (opened, _) _ => opened
  | .error _ _ => default

def familyConsTailFVarId : FVarId :=
  match familyConsTailOpenOutcome with
  | .ok (_, id) _ => id
  | .error _ _ => default

def familyConsResultState : TcState .anon :=
  match familyConsTailOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsTailOpenSucceededNative :
    (match familyConsTailOpenOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsTailOpenRun :
    TcM.openBinderAnon familyConsTailDomain familyConsTailBody
        familyConsTailDomainAfter =
      .ok (familyConsResultSource, familyConsTailFVarId)
        familyConsResultState := by
  have success := familyConsTailOpenSucceededNative
  unfold familyConsResultSource familyConsTailFVarId familyConsResultState
  generalize houtcome : familyConsTailOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsTailOpenOutcome]

/-- Field-loop terminal WHNF after exactly three ordinary fields. -/
def familyConsResultWhnfOutcome :=
  (RecM.whnf familyConsResultSource).run checkerMethods familyConsResultState

def familyConsResultWhnfResult : KExpr .anon :=
  match familyConsResultWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyConsResultWhnfAfter : TcState .anon :=
  match familyConsResultWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem familyConsResultWhnfSucceededNative :
    (match familyConsResultWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem familyConsResultWhnfRun :
    (RecM.whnf familyConsResultSource).run checkerMethods
        familyConsResultState =
      .ok familyConsResultWhnfResult familyConsResultWhnfAfter := by
  have success := familyConsResultWhnfSucceededNative
  unfold familyConsResultWhnfResult familyConsResultWhnfAfter
  generalize houtcome : familyConsResultWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [familyConsResultWhnfOutcome]

private theorem familyConsResultWhnfTerminalNative :
    (match familyConsResultWhnfResult with
      | .all .. => false
      | _ => true) = true := by
  native_decide

theorem familyConsResultWhnfTerminal :
    PositivityTerminalForm familyConsResultWhnfResult := by
  have terminal := familyConsResultWhnfTerminalNative
  generalize hresult : familyConsResultWhnfResult = result at terminal ⊢
  cases result <;> simp_all [PositivityTerminalForm]

/-- Exact three-field view of the positivity traversal selected by the real
family-block execution.  Besides the complete enclosing loop, the view exposes
the direct-only flat traces consumed by the Lean4Lean adapter. -/
structure IndexedVecConsProductionFieldProjection : Prop where
  nat : FlatPositivityDomainTrace familyConsPositivityGroups
    #[familyId.addr] checkerMethods maxWhnfFuel.toNat familyConsNatDomain
      familyConsNatDomainState familyConsNatDomainState
  head : FlatPositivityDomainTrace familyConsPositivityGroups
    #[familyId.addr] checkerMethods maxWhnfFuel.toNat familyConsHeadDomain
      familyConsHeadDomainState familyConsHeadDomainState
  tail : FlatPositivityDomainTrace familyConsPositivityGroups
    #[familyId.addr] checkerMethods maxWhnfFuel.toNat familyConsTailDomain
      familyConsTailDomainState familyConsTailDomainAfter
  complete : ConstructorPositivityFieldsTrace familyConsPositivityGroups
    #[familyId.addr] checkerMethods maxWhnfFuel.toNat familyConsFieldsSource
      familyConsPositivityParametersAfter familyConsResultWhnfAfter

/-- The whole retained production field traversal is necessarily

* root-free `Nat`,
* root-free head parameter,
* one direct recursive tail application, and
* a terminal result after exactly those three fields.

The proof destructs the trace obtained from the enclosing family checker.  The
named concrete observations are used only to discriminate and align that same
trace by determinism. -/
theorem indexedVecConsProductionFieldProjection :
    IndexedVecConsProductionFieldProjection := by
  obtain ⟨final, fields⟩ := indexedVecConsProductionFieldsTrace
  obtain ⟨natName, natBi, natInfo, natWhnf⟩ :=
    familyConsNatTelescopeWhnfRun
  cases fields with
  | terminal whnf notForall =>
      rw [natWhnf] at whnf
      cases whnf
      contradiction
  | field whnf natTrace natOpening afterNat =>
      rw [natWhnf] at whnf
      cases whnf
      cases natTrace with
      | rootFree root free =>
          rw [show familyConsPositivityGroups[0]? =
            some familyConsRootPositivityGroup by rfl] at root
          cases root
          rw [familyConsNatOpenRun] at natOpening
          cases natOpening
          have natFlat :
              FlatPositivityDomainTrace familyConsPositivityGroups
                #[familyId.addr] checkerMethods maxWhnfFuel.toNat
                  familyConsNatDomain familyConsNatDomainState
                    familyConsNatDomainState :=
            .rootFree rfl familyConsNatDomainRootFree
          obtain ⟨headName, headBi, headInfo, headWhnf⟩ :=
            familyConsHeadTelescopeWhnfRun
          cases afterNat with
          | terminal whnf notForall =>
              rw [headWhnf] at whnf
              cases whnf
              contradiction
          | field whnf headTrace headOpening afterHead =>
              rw [headWhnf] at whnf
              cases whnf
              cases headTrace with
              | rootFree root free =>
                  rw [show familyConsPositivityGroups[0]? =
                    some familyConsRootPositivityGroup by rfl] at root
                  cases root
                  rw [familyConsHeadOpenRun] at headOpening
                  cases headOpening
                  have headFlat :
                      FlatPositivityDomainTrace familyConsPositivityGroups
                        #[familyId.addr] checkerMethods maxWhnfFuel.toNat
                          familyConsHeadDomain familyConsHeadDomainState
                            familyConsHeadDomainState :=
                    .rootFree rfl familyConsHeadDomainRootFree
                  obtain ⟨tailName, tailBi, tailInfo, tailWhnf⟩ :=
                    familyConsTailTelescopeWhnfRun
                  cases afterHead with
                  | terminal whnf notForall =>
                      rw [tailWhnf] at whnf
                      cases whnf
                      contradiction
                  | field whnf tailTrace tailOpening afterTail =>
                      rw [tailWhnf] at whnf
                      cases whnf
                      cases tailTrace with
                      | rootFree root free =>
                          rw [show familyConsPositivityGroups[0]? =
                            some familyConsRootPositivityGroup by rfl] at root
                          cases root
                          have mentions :
                              exprMentionsAnyAddr familyConsTailDomain
                                familyConsRootPositivityGroup.addrs = true := by
                            simpa [familyConsRootPositivityGroup] using
                              familyConsTailDomainMentionsRoot
                          rw [mentions] at free
                          contradiction
                      | «forall» root mentioned domainWhnf domainFree opening
                          recursive restored =>
                          rw [familyConsTailDomainWhnfRun] at domainWhnf
                          injection domainWhnf with resultEq stateEq
                          have terminal := familyConsTailDomainWhnfNotForall
                          rw [resultEq] at terminal
                          exact terminal.elim
                      | application root mentioned domainWhnf notForall spine
                          application =>
                          rw [show familyConsPositivityGroups[0]? =
                            some familyConsRootPositivityGroup by rfl] at root
                          cases root
                          rw [familyConsTailDomainWhnfRun] at domainWhnf
                          cases domainWhnf
                          rw [familyConsTailWhnfSpine] at spine
                          cases spine
                          cases application with
                          | nested inactive nested =>
                              rw [familyConsTailWhnfSpineActive] at inactive
                              contradiction
                          | direct active valid =>
                              have directRun :=
                                RecM.ValidPositiveRecursiveApplication.run valid
                              have domainRun :=
                                RecM.checkPositivityDomainFuel_direct_run
                                  (fuel := maxWhnfFuel.toNat - 1)
                                  (activeAddrs := #[familyId.addr]) rfl
                                  (by simpa [familyConsRootPositivityGroup] using
                                    familyConsTailDomainMentionsRoot)
                                  familyConsTailDomainWhnfRun
                                  familyConsTailWhnfSpine active directRun
                              change
                                (RecM.checkPositivityDomain familyConsTailDomain
                                  familyConsPositivityGroups #[familyId.addr]).run
                                    checkerMethods familyConsTailDomainState =
                                  .ok () _ at domainRun
                              rw [familyConsTailDomainRun] at domainRun
                              cases domainRun
                              rw [familyConsTailOpenRun] at tailOpening
                              cases tailOpening
                              have tailFlat :
                                  FlatPositivityDomainTrace
                                    familyConsPositivityGroups #[familyId.addr]
                                      checkerMethods maxWhnfFuel.toNat
                                        familyConsTailDomain
                                          familyConsTailDomainState
                                            familyConsTailDomainAfter :=
                                .application
                                  (fuel := maxWhnfFuel.toNat - 1)
                                  (rootGroup := familyConsRootPositivityGroup)
                                  rfl
                                  (by simpa [familyConsRootPositivityGroup] using
                                    familyConsTailDomainMentionsRoot)
                                  familyConsTailDomainWhnfRun
                                  familyConsTailDomainWhnfNotForall
                                  familyConsTailWhnfSpine active valid
                              cases afterTail with
                              | field whnf domainTrace opening tail =>
                                  rw [familyConsResultWhnfRun] at whnf
                                  injection whnf with resultEq stateEq
                                  have terminal := familyConsResultWhnfTerminal
                                  rw [resultEq] at terminal
                                  exact terminal.elim
                              | terminal whnf notForall =>
                                  rw [familyConsResultWhnfRun] at whnf
                                  cases whnf
                                  exact ⟨natFlat, headFlat, tailFlat,
                                    .field natWhnf
                                      natFlat.toPositivityDomainTrace
                                      familyConsNatOpenRun
                                      (.field headWhnf
                                        headFlat.toPositivityDomainTrace
                                        familyConsHeadOpenRun
                                        (.field tailWhnf
                                          tailFlat.toPositivityDomainTrace
                                          familyConsTailOpenRun
                                          (.terminal familyConsResultWhnfRun
                                            familyConsResultWhnfTerminal)))⟩
              | «forall» root mentioned domainWhnf domainFree opening recursive
                  restored =>
                  rw [show familyConsPositivityGroups[0]? =
                    some familyConsRootPositivityGroup by rfl] at root
                  cases root
                  have free :
                      exprMentionsAnyAddr familyConsHeadDomain
                        familyConsRootPositivityGroup.addrs = false := by
                    simpa [familyConsRootPositivityGroup] using
                      familyConsHeadDomainRootFree
                  rw [free] at mentioned
                  contradiction
              | application root mentioned domainWhnf notForall spine
                  application =>
                  rw [show familyConsPositivityGroups[0]? =
                    some familyConsRootPositivityGroup by rfl] at root
                  cases root
                  have free :
                      exprMentionsAnyAddr familyConsHeadDomain
                        familyConsRootPositivityGroup.addrs = false := by
                    simpa [familyConsRootPositivityGroup] using
                      familyConsHeadDomainRootFree
                  rw [free] at mentioned
                  contradiction
      | «forall» root mentioned domainWhnf domainFree opening recursive restored =>
          rw [show familyConsPositivityGroups[0]? =
            some familyConsRootPositivityGroup by rfl] at root
          cases root
          have free :
              exprMentionsAnyAddr familyConsNatDomain
                familyConsRootPositivityGroup.addrs = false := by
            simpa [familyConsRootPositivityGroup] using
              familyConsNatDomainRootFree
          rw [free] at mentioned
          contradiction
      | application root mentioned domainWhnf notForall spine application =>
          rw [show familyConsPositivityGroups[0]? =
            some familyConsRootPositivityGroup by rfl] at root
          cases root
          have free :
              exprMentionsAnyAddr familyConsNatDomain
                familyConsRootPositivityGroup.addrs = false := by
            simpa [familyConsRootPositivityGroup] using
              familyConsNatDomainRootFree
          rw [free] at mentioned
          contradiction

/-- Exact physical metadata selection, shared-parameter check, protected
positivity core, and public scope restoration for the `cons` validation chosen
by the real family-block execution.  The metadata trace's lookup and the core's
`ctorTy` index are definitionally the same expression. -/
theorem indexedVecConsProductionMetadataAndCoreTrace :
    ∃ (ctorTy : KExpr .anon) (ctorFields : Nat)
        (initial afterMetadata afterParameters afterCore afterPositivity :
          TcState .anon),
      ConstructorMetadataValidationTrace consId familyId 1 1 1 false
          checkerMethods ctorTy ctorFields initial afterMetadata ∧
        (RecM.checkParamAgreement familyConcrete.ty ctorTy 1).run
            checkerMethods afterMetadata = .ok () afterParameters ∧
        ConstructorPositivityCoreTrace ctorTy 1 #[familyId.addr]
          checkerMethods afterParameters afterCore ∧
        afterPositivity = { afterCore with
          lctx := afterCore.lctx.truncate afterParameters.lctx.size } := by
  obtain ⟨_, _, _, validation⟩ :=
    indexedVecConsProductionValidationTrace
  cases validation with
  | success metadata parameters positivity universes returnType =>
      clear universes returnType
      have metadataTrace :=
        RecM.checkCtorMetadataAgainstParent_success metadata
      cases positivity with
      | safe run trace =>
          clear run
          cases trace with
          | success core restored =>
              exact ⟨_, _, _, _, _, _, _, metadataTrace, parameters, core,
                restored⟩

/-- The protected positivity body selected by the real family-block run.
The selected constructor type is retained as an index because the surrounding
metadata trace exposes the physical lookup but the block-level environment
preservation theorem needed to rewrite it to `consConcrete.ty` is kept as the
next explicit bridge. -/
theorem indexedVecConsProductionCoreTrace :
    ∃ (ctorTy : KExpr .anon) (initial afterCore : TcState .anon),
      ConstructorPositivityCoreTrace ctorTy 1 #[familyId.addr]
        checkerMethods initial afterCore := by
  obtain ⟨ctorTy, _, _, _, afterParameters, afterCore, _, _, _, core, _⟩ :=
    indexedVecConsProductionMetadataAndCoreTrace
  exact ⟨ctorTy, afterParameters, afterCore, core⟩

/-- Exhaustive parameter-prefix result inside the production-selected core.
This theorem deliberately retains the malformed short branch until constructor
metadata is strengthened with its physical lookup. -/
theorem indexedVecConsProductionParameterBranch :
    ∃ (ctorTy : KExpr .anon) (initial final : TcState .anon),
      (PositivityParameterTrace checkerMethods 1 ctorTy #[] initial none
          final ∨
        ∃ (fieldsSource : KExpr .anon)
            (parameterFVars : Array (KExpr .anon))
            (afterParameters : TcState .anon),
          PositivityParameterTrace checkerMethods 1 ctorTy #[] initial
            (some (fieldsSource, parameterFVars)) afterParameters ∧
          ConstructorPositivityFieldsTrace
            #[{ addrs := #[familyId.addr], params := parameterFVars,
                concreteUs := none }]
            #[familyId.addr] checkerMethods maxWhnfFuel.toNat fieldsSource
              afterParameters final) := by
  obtain ⟨ctorTy, initial, final, core⟩ :=
    indexedVecConsProductionCoreTrace
  cases core with
  | short parameters =>
      exact ⟨ctorTy, initial, final, .inl parameters⟩
  | fields parameters fields =>
      exact ⟨ctorTy, initial, final, .inr ⟨_, _, _, parameters, fields⟩⟩

end Ix.Tc.IndexedRecursiveFixture
