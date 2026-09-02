import Ix.Tc.Verify.Inductive.IndexedCandidateSyntax
import Ix.Tc.Verify.Inductive.IndexedRecursiveAcceptance

/-!
# IndexedVec candidate operations

The closed syntax relation is not enough once constructor validation opens its
telescope.  This module follows the same anonymous binder instantiation used
by `TcM.openBinderAnon`, pairs each minted Ix identifier with Lean4Lean's
corresponding validation identifier, and checks the three actual `cons` field
domains at which positivity is invoked.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean.InductiveReplayFixtures

/-- Domain projection used only after a separately checked constructor shape.
Returning the source in the impossible fallback keeps the definition total. -/
def candidateForallDomain : KExpr .anon → KExpr .anon
  | .all _ _ domain _ _ => domain
  | source => source

/-- Body projection paired with `candidateForallDomain`. -/
def candidateForallBody : KExpr .anon → KExpr .anon
  | .all _ _ _ body _ => body
  | source => source

/-- Exact parameter-prefix WHNF performed by `openPositivityParameters`. -/
def ixConsParameterWhnfOutcome :=
  (RecM.whnf consConcrete.ty).run checkerMethods checkerInitial

def ixConsParameterWhnfResult : KExpr .anon :=
  match ixConsParameterWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ixConsParameterWhnfAfter : TcState .anon :=
  match ixConsParameterWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsParameterWhnfSucceeded : Bool :=
  match ixConsParameterWhnfOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsParameterWhnfSucceededNative :
    ixConsParameterWhnfSucceeded = true := by
  native_decide

theorem ixConsParameterWhnfRun :
    (RecM.whnf consConcrete.ty).run checkerMethods checkerInitial =
      .ok ixConsParameterWhnfResult ixConsParameterWhnfAfter := by
  have success := ixConsParameterWhnfSucceededNative
  unfold ixConsParameterWhnfSucceeded at success
  unfold ixConsParameterWhnfResult ixConsParameterWhnfAfter
  generalize houtcome : ixConsParameterWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsParameterWhnfOutcome]

/-- Actual parameter opening used by production positivity, including the
fvar expression inserted into the root `PositivityGroup`. -/
def ixConsAlphaOpenOutcome :=
  TcM.openBinderAnonWithFV
    (candidateForallDomain ixConsParameterWhnfResult)
    (candidateForallBody ixConsParameterWhnfResult)
    ixConsParameterWhnfAfter

def ixConsAfterAlpha : KExpr .anon :=
  match ixConsAlphaOpenOutcome with
  | .ok (opened, _, _) _ => opened
  | .error _ _ => default

def ixValidationAlphaId : FVarId :=
  match ixConsAlphaOpenOutcome with
  | .ok (_, _, id) _ => id
  | .error _ _ => default

def ixValidationAlphaExpr : KExpr .anon :=
  match ixConsAlphaOpenOutcome with
  | .ok (_, fv, _) _ => fv
  | .error _ _ => default

def ixConsAfterAlphaState : TcState .anon :=
  match ixConsAlphaOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsAlphaOpenSucceeded : Bool :=
  match ixConsAlphaOpenOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsAlphaOpenSucceededNative :
    ixConsAlphaOpenSucceeded = true := by
  native_decide

theorem ixConsAlphaOpenRun :
    ixConsAlphaOpenOutcome =
      .ok (ixConsAfterAlpha, ixValidationAlphaExpr, ixValidationAlphaId)
        ixConsAfterAlphaState := by
  have success := ixConsAlphaOpenSucceededNative
  unfold ixConsAlphaOpenSucceeded at success
  unfold ixConsAfterAlpha ixValidationAlphaExpr ixValidationAlphaId
    ixConsAfterAlphaState
  generalize houtcome : ixConsAlphaOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all

/-- WHNF at the first source-ordered field-loop iteration. -/
def ixConsNatTelescopeWhnfOutcome :=
  (RecM.whnf ixConsAfterAlpha).run checkerMethods ixConsAfterAlphaState

def ixConsNatTelescopeWhnfResult : KExpr .anon :=
  match ixConsNatTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ixConsNatDomainState : TcState .anon :=
  match ixConsNatTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem ixConsNatTelescopeWhnfSucceededNative :
    (match ixConsNatTelescopeWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem ixConsNatTelescopeWhnfRun :
    (RecM.whnf ixConsAfterAlpha).run checkerMethods ixConsAfterAlphaState =
      .ok ixConsNatTelescopeWhnfResult ixConsNatDomainState := by
  have success := ixConsNatTelescopeWhnfSucceededNative
  unfold ixConsNatTelescopeWhnfResult ixConsNatDomainState
  generalize houtcome : ixConsNatTelescopeWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsNatTelescopeWhnfOutcome]

def ixConsNatDomain : KExpr .anon :=
  candidateForallDomain ixConsNatTelescopeWhnfResult

/-- Root positivity group built by the exact parameter-prefix execution. -/
def indexedVecRootPositivityGroup : PositivityGroup .anon :=
  { addrs := #[familyId.addr]
    params := #[ixValidationAlphaExpr]
    concreteUs := none }

def indexedVecPositivityGroups : Array (PositivityGroup .anon) :=
  #[indexedVecRootPositivityGroup]

/-- Exact first field-domain call. -/
def ixConsNatDomainOutcome :=
  (RecM.checkPositivityDomain ixConsNatDomain indexedVecPositivityGroups
    #[familyId.addr]).run checkerMethods ixConsNatDomainState

def ixConsNatDomainAfter : TcState .anon :=
  match ixConsNatDomainOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem ixConsNatDomainSucceededNative :
    (match ixConsNatDomainOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem ixConsNatDomainRun :
    (RecM.checkPositivityDomain ixConsNatDomain indexedVecPositivityGroups
      #[familyId.addr]).run checkerMethods ixConsNatDomainState =
        .ok () ixConsNatDomainAfter := by
  have success := ixConsNatDomainSucceededNative
  unfold ixConsNatDomainAfter
  generalize houtcome : ixConsNatDomainOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsNatDomainOutcome]

/-- Actual opening of the implicit Nat field binder. -/
def ixConsNOpenOutcome :=
  TcM.openBinderAnon (candidateForallDomain ixConsNatTelescopeWhnfResult)
    (candidateForallBody ixConsNatTelescopeWhnfResult) ixConsNatDomainAfter

def ixConsAfterN : KExpr .anon :=
  match ixConsNOpenOutcome with
  | .ok (opened, _) _ => opened
  | .error _ _ => default

def ixValidationNId : FVarId :=
  match ixConsNOpenOutcome with
  | .ok (_, id) _ => id
  | .error _ _ => default

def ixConsAfterNState : TcState .anon :=
  match ixConsNOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsNOpenSucceeded : Bool :=
  match ixConsNOpenOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsNOpenSucceededNative :
    ixConsNOpenSucceeded = true := by
  native_decide

theorem ixConsNOpenRun :
    ixConsNOpenOutcome =
      .ok (ixConsAfterN, ixValidationNId) ixConsAfterNState := by
  have success := ixConsNOpenSucceededNative
  unfold ixConsNOpenSucceeded at success
  unfold ixConsAfterN ixValidationNId ixConsAfterNState
  generalize houtcome : ixConsNOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def ixValidationNExpr : KExpr .anon :=
  .mkFVar ixValidationNId ()

/-- WHNF at the second source-ordered field-loop iteration. -/
def ixConsHeadTelescopeWhnfOutcome :=
  (RecM.whnf ixConsAfterN).run checkerMethods ixConsAfterNState

def ixConsHeadTelescopeWhnfResult : KExpr .anon :=
  match ixConsHeadTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ixConsHeadDomainState : TcState .anon :=
  match ixConsHeadTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem ixConsHeadTelescopeWhnfSucceededNative :
    (match ixConsHeadTelescopeWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem ixConsHeadTelescopeWhnfRun :
    (RecM.whnf ixConsAfterN).run checkerMethods ixConsAfterNState =
      .ok ixConsHeadTelescopeWhnfResult ixConsHeadDomainState := by
  have success := ixConsHeadTelescopeWhnfSucceededNative
  unfold ixConsHeadTelescopeWhnfResult ixConsHeadDomainState
  generalize houtcome : ixConsHeadTelescopeWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsHeadTelescopeWhnfOutcome]

def ixConsHeadDomain : KExpr .anon :=
  candidateForallDomain ixConsHeadTelescopeWhnfResult

/-- Exact second field-domain call. -/
def ixConsHeadDomainOutcome :=
  (RecM.checkPositivityDomain ixConsHeadDomain indexedVecPositivityGroups
    #[familyId.addr]).run checkerMethods ixConsHeadDomainState

def ixConsHeadDomainAfter : TcState .anon :=
  match ixConsHeadDomainOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem ixConsHeadDomainSucceededNative :
    (match ixConsHeadDomainOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem ixConsHeadDomainRun :
    (RecM.checkPositivityDomain ixConsHeadDomain indexedVecPositivityGroups
      #[familyId.addr]).run checkerMethods ixConsHeadDomainState =
        .ok () ixConsHeadDomainAfter := by
  have success := ixConsHeadDomainSucceededNative
  unfold ixConsHeadDomainAfter
  generalize houtcome : ixConsHeadDomainOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsHeadDomainOutcome]

/-- Actual opening of the head field binder. -/
def ixConsHeadOpenOutcome :=
  TcM.openBinderAnon (candidateForallDomain ixConsHeadTelescopeWhnfResult)
    (candidateForallBody ixConsHeadTelescopeWhnfResult) ixConsHeadDomainAfter

def ixConsAfterHead : KExpr .anon :=
  match ixConsHeadOpenOutcome with
  | .ok (opened, _) _ => opened
  | .error _ _ => default

def ixValidationHeadId : FVarId :=
  match ixConsHeadOpenOutcome with
  | .ok (_, id) _ => id
  | .error _ _ => default

def ixConsAfterHeadState : TcState .anon :=
  match ixConsHeadOpenOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def ixConsHeadOpenSucceeded : Bool :=
  match ixConsHeadOpenOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsHeadOpenSucceededNative :
    ixConsHeadOpenSucceeded = true := by
  native_decide

theorem ixConsHeadOpenRun :
    ixConsHeadOpenOutcome =
      .ok (ixConsAfterHead, ixValidationHeadId)
        ixConsAfterHeadState := by
  have success := ixConsHeadOpenSucceededNative
  unfold ixConsHeadOpenSucceeded at success
  unfold ixConsAfterHead ixValidationHeadId ixConsAfterHeadState
  generalize houtcome : ixConsHeadOpenOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def ixValidationHeadExpr : KExpr .anon :=
  .mkFVar ixValidationHeadId ()

/-- Observable allocation and scope effects of the three retained production
openings.  These facts prevent the syntax bridge from pairing arbitrary fvars
unrelated to the actual checker state. -/
structure CandidateOpeningFacts : Prop where
  alphaFresh :
    ixValidationAlphaId = ⟨checkerInitial.env.nextFVarId⟩
  nFresh :
    ixValidationNId = ⟨ixConsAfterAlphaState.env.nextFVarId⟩
  headFresh :
    ixValidationHeadId = ⟨ixConsAfterNState.env.nextFVarId⟩
  alphaCounter :
    ixConsAfterAlphaState.env.nextFVarId =
      checkerInitial.env.nextFVarId + 1
  nCounter :
    ixConsAfterNState.env.nextFVarId =
      ixConsAfterAlphaState.env.nextFVarId + 1
  headCounter :
    ixConsAfterHeadState.env.nextFVarId =
      ixConsAfterNState.env.nextFVarId + 1
  alphaScope :
    ixConsAfterAlphaState.lctx.size = checkerInitial.lctx.size + 1
  nScope :
    ixConsAfterNState.lctx.size = ixConsAfterAlphaState.lctx.size + 1
  headScope :
    ixConsAfterHeadState.lctx.size = ixConsAfterNState.lctx.size + 1

private theorem candidateOpeningFactsNative : CandidateOpeningFacts := by
  constructor <;> native_decide

theorem candidateOpeningFacts : CandidateOpeningFacts :=
  candidateOpeningFactsNative

/-- WHNF at the recursive-tail field-loop iteration. -/
def ixConsTailTelescopeWhnfOutcome :=
  (RecM.whnf ixConsAfterHead).run checkerMethods ixConsAfterHeadState

def ixConsTailTelescopeWhnfResult : KExpr .anon :=
  match ixConsTailTelescopeWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def ixConsTailDomainState : TcState .anon :=
  match ixConsTailTelescopeWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem ixConsTailTelescopeWhnfSucceededNative :
    (match ixConsTailTelescopeWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem ixConsTailTelescopeWhnfRun :
    (RecM.whnf ixConsAfterHead).run checkerMethods ixConsAfterHeadState =
      .ok ixConsTailTelescopeWhnfResult ixConsTailDomainState := by
  have success := ixConsTailTelescopeWhnfSucceededNative
  unfold ixConsTailTelescopeWhnfResult ixConsTailDomainState
  generalize houtcome : ixConsTailTelescopeWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsTailTelescopeWhnfOutcome]

def ixConsTailDomain : KExpr .anon :=
  candidateForallDomain ixConsTailTelescopeWhnfResult

/-- Finite pairing used by the executable exact-syntax checker after binders
have been opened independently by the two kernels. -/
def pairedFVarMatches
    (pairs : List (FVarId × Lean.FVarId))
    (ixId : FVarId) (leanId : Lean.FVarId) : Bool :=
  pairs.any fun pair => pair.1 == ixId && pair.2 == leanId

def alphaPair : List (FVarId × Lean.FVarId) :=
  [(ixValidationAlphaId, indexedVecConstructorAlphaId)]

def alphaNPair : List (FVarId × Lean.FVarId) :=
  [(ixValidationAlphaId, indexedVecConstructorAlphaId),
    (ixValidationNId, indexedVecConstructorNId)]

private theorem natDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches alphaPair) [`u]
      ixConsNatDomain (.const ``Nat []) = true := by
  native_decide

private theorem headDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches alphaNPair) [`u]
      ixConsHeadDomain indexedVecConstructorAlpha = true := by
  native_decide

private theorem tailDomainCandidateCheckNative :
    CandidateSyntax.check nameOf (pairedFVarMatches alphaNPair) [`u]
      ixConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) = true := by
  native_decide

theorem natDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => pairedFVarMatches alphaPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      ixConsNatDomain (.const ``Nat []) :=
  CandidateSyntax.rel_of_check natDomainCandidateCheckNative

theorem headDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => pairedFVarMatches alphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      ixConsHeadDomain indexedVecConstructorAlpha :=
  CandidateSyntax.rel_of_check headDomainCandidateCheckNative

theorem tailDomainCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => pairedFVarMatches alphaNPair ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      ixConsTailDomain
        (ctorIndexedVecApp indexedVecConstructorAlpha
          indexedVecConstructorNExpr) :=
  CandidateSyntax.rel_of_check tailDomainCandidateCheckNative

end Ix.Tc.IndexedRecursiveFixture
