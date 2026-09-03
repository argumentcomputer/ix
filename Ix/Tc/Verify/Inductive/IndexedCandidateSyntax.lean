import Ix.Tc.Verify.Inductive.CandidateSyntax
import Ix.Tc.Verify.Inductive.IndexedRecursiveFixture
import Lean4Lean.Verify.Environment.IndexedVecOuterReplay

/-!
# Exact IndexedVec candidate syntax

This module connects the actual anonymous expressions produced by Ix ingress
to the exact Lean kernel expressions consumed by Lean4Lean's constructor
validator.  The relation is deliberately syntactic: positivity occurrence
and `isValidIndApp?` inspect the candidate expression rather than its Theory
denotation.
-/

namespace Ix.Tc.IndexedRecursiveFixture

open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.InductiveReplayFixtures.IndexedVecConsReplay

/-! ## Proof-independent Lean4Lean validation fixture

The upstream replay exposes the right executable values, but its public
`indexedVecCtorValidationContext` is projected out of a proof-bearing family
trace.  Merely mentioning that projection therefore imports the replay's
reflection axioms into a downstream theorem statement.  Reconstruct the same
post-family context and constructor-local binders directly from transparent
data.  These are the values E2c relates to production Ix execution.
-/

/-- Post-family context in which the two IndexedVec constructors are checked.
It has the validated parameter/index local context and the staged environment
containing the family constant, without retaining an upstream replay proof. -/
def indexedVecConstructorContext : Lean4Lean.AddInductive.Context :=
  { indexedVecValidationFamilyContext with env := ctorEnv }

def indexedVecConstructorAlpha : Lean.Expr :=
  indexedVecValidationAlpha

def indexedVecConstructorAlphaId : Lean.FVarId :=
  indexedVecValidationAlphaId

def indexedVecConstructorNId : Lean.FVarId :=
  indexedVecConstructorContext.freshFVarId

def indexedVecConstructorNExpr : Lean.Expr :=
  indexedVecConstructorContext.freshExpr

def indexedVecConstructorNContext : Lean4Lean.AddInductive.Context :=
  indexedVecConstructorContext.pushLocalDecl
    consNName .implicit (.const ``Nat [])

def indexedVecConstructorHeadId : Lean.FVarId :=
  indexedVecConstructorNContext.freshFVarId

def indexedVecConstructorHeadContext : Lean4Lean.AddInductive.Context :=
  indexedVecConstructorNContext.pushLocalDecl
    consHeadName .default indexedVecConstructorAlpha

def indexedVecConstructorTailContext : Lean4Lean.AddInductive.Context :=
  indexedVecConstructorHeadContext.pushLocalDecl consTailName .default
    (ctorIndexedVecApp indexedVecConstructorAlpha
      indexedVecConstructorNExpr)

/-- Constructor statistics selected by the validated one-parameter,
one-index family spine.  Writing the finite record directly prevents the
statement from retaining `CandidateExprTrace.singletonCandidateInductiveStats`
through an upstream proof object. -/
def indexedVecConstructorStats : Lean4Lean.AddInductive.InductiveStats where
  lctx := indexedVecConstructorContext.lctx
  levels := [.param `u]
  resultLevel := .succ (.param `u)
  nindices := #[1]
  indConsts :=
    #[.const ``Lean4Lean.InductiveFixtures.IndexedVec [.param `u]]
  params := #[indexedVecConstructorAlpha]
  isNotZero := true

def indexedVecConstructorAfterParam : Lean.Expr :=
  consNTypeRaw.instantiate1 indexedVecConstructorAlpha

def indexedVecConstructorAfterN : Lean.Expr :=
  .forallE consHeadName indexedVecConstructorAlpha
    (.forallE consTailName
      (ctorIndexedVecApp indexedVecConstructorAlpha
        indexedVecConstructorNExpr)
      (ctorIndexedVecApp indexedVecConstructorAlpha
        (replaySuccApp indexedVecConstructorNExpr))
      .default)
    .default

def indexedVecConstructorAfterHead : Lean.Expr :=
  .forallE consTailName
    (ctorIndexedVecApp indexedVecConstructorAlpha
      indexedVecConstructorNExpr)
    (ctorIndexedVecApp indexedVecConstructorAlpha
      (replaySuccApp indexedVecConstructorNExpr))
    .default

def indexedVecConstructorResult : Lean.Expr :=
  ctorIndexedVecApp indexedVecConstructorAlpha
    (replaySuccApp indexedVecConstructorNExpr)

/-- Constructor source types are closed, so no free-variable correspondence
is needed before either positivity checker opens their telescopes. -/
def closedFVarMatches (_ : FVarId) (_ : Lean.FVarId) : Bool := false

private theorem familyCandidateCheckNative :
    CandidateSyntax.check nameOf closedFVarMatches [`u]
      familyConcrete.ty indexedVecKernelType.type = true := by
  native_decide

private theorem nilCandidateCheckNative :
    CandidateSyntax.check nameOf closedFVarMatches [`u]
      nilConcrete.ty indexedVecKernelNil.type = true := by
  native_decide

private theorem consCandidateCheckNative :
    CandidateSyntax.check nameOf closedFVarMatches [`u]
      consConcrete.ty indexedVecKernelCons.type = true := by
  native_decide

/-- The family type selected by production anonymous ingress is exactly the
Lean4Lean IndexedVec family candidate, modulo irrelevant binder metadata. -/
theorem familyCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => closedFVarMatches ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      familyConcrete.ty indexedVecKernelType.type :=
  CandidateSyntax.rel_of_check familyCandidateCheckNative

/-- The ingressed nil constructor type is the exact candidate validated by
Lean4Lean. -/
theorem nilCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => closedFVarMatches ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      nilConcrete.ty indexedVecKernelNil.type :=
  CandidateSyntax.rel_of_check nilCandidateCheckNative

/-- The ingressed cons constructor type is the exact candidate validated by
Lean4Lean, including its recursive family application and changing index. -/
theorem consCandidateSyntax :
    CandidateSyntaxRel nameOf
      (fun ixId leanId => closedFVarMatches ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [`u] ixLevel leanLevel = true)
      consConcrete.ty indexedVecKernelCons.type :=
  CandidateSyntax.rel_of_check consCandidateCheckNative

private theorem candidateBlockSyntaxNative :
    CandidateBlockRel nameOf #[familyId.addr]
      indexedVecConstructorStats.indConsts := by
  rw [show indexedVecConstructorStats.indConsts =
      #[.const ``Lean4Lean.InductiveFixtures.IndexedVec [.param `u]] by rfl]
  intro id leanName hname
  unfold nameOf at hname
  repeat' split at hname
  all_goals simp_all [Lean.Expr.constName!]
  all_goals subst_vars
  all_goals native_decide

/-- The physical singleton-family address and Lean4Lean's singleton constant
array make the same occurrence decision.  The proof analyzes the concrete
ingress name map, so it assumes neither address nor name injectivity. -/
theorem candidateBlockSyntax :
    CandidateBlockRel nameOf #[familyId.addr]
      indexedVecConstructorStats.indConsts :=
  candidateBlockSyntaxNative

end Ix.Tc.IndexedRecursiveFixture
