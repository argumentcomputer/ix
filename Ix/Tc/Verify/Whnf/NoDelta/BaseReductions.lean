import Ix.Tc.Verify.Whnf.NoDelta.Quotient

/-!
# Assemble the active no-delta base oracle

The five reducers active under `.noAccel` are now independently closed:
projection application, Nat, String, projection-wrapper definitions, and
quotients.  This slice packages their exact finite and semantic inputs and
constructs the `NoDeltaBaseOracle` consumed by the already-proved ordered
no-delta step.
-/

namespace Ix.Tc
namespace RecM

/-- Complete input package for the five active no-delta reducers.

The fields remain separated by ownership.  In particular, generated String,
projection-wrapper, and quotient nodes have their own finite plans; the
generic primitive context's final-result support cannot stand in for those
intermediate intern obligations. -/
structure NoDeltaBaseContext
    {alpha : Type} (initial : TcState .anon) (program : TcM .anon alpha)
    (requests : List WalkerRequest) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (flags : WhnfFlags) : Type where
  run : RunAssumptions initial program requests support
  theory : ∀ uvars, WhnfTheory trProj world uvars
  applicationCensus : ApplicationFinishRequestCensus requests support
  coreInputs : WhnfCoreInputSupport support
  projectionHelper :
    ProjectionHelper.WF .noAccel semantics trProj world support
  inductiveReduction :
    InductiveReductionOracle .noAccel semantics trProj world support
  primitive : ∀ mode,
    NoDeltaPrimitiveContext world support flags mode
  natWrites : NatSuccStuckWriteOracle semantics world support
  natParts : NatRecLiteralPartsPreserves .noAccel semantics trProj world
    support
  natReflection :
    NatSuccLinearReflection .noAccel semantics trProj world support
  natShape : NatCollapseRequestCensus.NatBoolResultShapeSeparation world
  stringSupport : StringReductionSupport support
  stringReflection :
    StringReductionReflection semantics trProj world support
  projectionCensus :
    ProjectionDefinitionRequestCensus requests support
  projectionReflection :
    ProjectionDefinitionReflection semantics trProj world support
  quotientCensus : QuotientReductionRequestCensus requests support
  quotientReflection :
    QuotientReductionReflection semantics trProj world support
  ingress :
    AnonLazyIngressContext .noAccel semantics trProj world support

namespace NoDeltaBaseContext

/-- Construct all five active fields in production order for either Nat
successor policy. -/
theorem oracle
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags}
    (context : NoDeltaBaseContext initial program requests semantics trProj
      world support flags)
    (mode : NatSuccMode) :
    NoDeltaBaseOracle semantics trProj world support flags mode where
  projApp :=
    tryProjAppReduceFinished_optional_wf_of_contexts
      context.run context.applicationCensus context.theory
      context.coreInputs context.projectionHelper
      context.inductiveReduction flags
  nat :=
    tryReduceNatWithSuccMode_optional_wf_of_boundaries
      context.primitive context.run context.theory context.natWrites
      context.natParts context.natReflection context.natShape mode
  string :=
    tryReduceString_optional_wf_of_reflection
      (context.primitive mode).collisionFree context.stringSupport
      context.stringReflection
  projectionDef :=
    tryReduceProjectionDefinition_optional_wf_of_contexts
      context.run context.projectionCensus
        (fun {_ _} => context.ingress.preserves)
      context.projectionReflection
  quot :=
    tryQuotReduce_optional_wf_of_contexts
      context.run context.quotientCensus (context.primitive mode).inputs
      context.quotientReflection

end NoDeltaBaseContext
end RecM
end Ix.Tc
