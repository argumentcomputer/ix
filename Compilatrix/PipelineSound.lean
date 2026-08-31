import Compilatrix.Pipeline
import Compilatrix.IxIR1.LowerMutualAddressedProgress

/-!
# Semantic interface for validator-gated compilation

`Pipeline.compileValidatedWithTrace` retains the exact scoped erasure
certificate, simultaneous-member coverage, addressed-erasure equation, and
stateful fully-addressed lowering equations.  This file projects those
witnesses into the production forward-simulation theorem.  Source sharing and
oracle correspondence remain semantic premises; target ownership and extern
behavior retain their explicit ABI contracts.
-/

namespace Compilatrix.Pipeline

open Compilatrix.Ixon (Address Constant Owned)
open Compilatrix.IxIR1
open Compilatrix.IxIR1.Lower
open Compilatrix.IxIR1.LowerSim

namespace ValidatedCompilation

/-- Exact legacy IxIR₀ context certified by the validated compiler. -/
def rawCtx {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) : IxIR0.Ctx :=
  compilation.erasure.result.rawCtx

/-- Addressed IxIR₀ context consumed by lowering, using the executable empty
legacy-oracle adapter. -/
def addressedSourceCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) : IxIR0.Ctx :=
  compilation.erasure.result.addressed.addressedCtx
    (IxIR0.Readdress.Oracle.readdress
      compilation.erasure.result.addressMap (fun _ _ => none))

/-- Raw-keyed target context immediately before the complete IxIR₁ address
pass. -/
def targetCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) : IxIR1.Ctx :=
  compilation.lowering.result.preAddressCtx compilation.lowering.raw
    targetOracle

/-- Function relation reconstructed from the exact final lowering state. -/
def functionRel
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) : Sim.FunctionRel :=
  CompilerFunctionRel compilation.addressedSourceCtx
    (IxIR0.Env.ofList compilation.erasure.result.declarations)
    compilation.lowering.finalState

/-- The concise semantic endpoint for one successful
`compileValidatedWithTrace` result.  All executable equalities and the
runtime-derived mutual-member scope are supplied by `compilation`; the
remaining premises are genuine source/oracle and backend ABI obligations. -/
theorem semanticForwardSimulation
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    {sourceFuel : Nat} {sourceValue : Ixon.Eval.Value}
    (horacles : @Sim.OracleRel compilation.memberScope
      (validatedEvalCtx constants config).inlineSharing compilation.rawCtx)
    (hctx : (validatedEvalCtx constants config).SharingWF)
    (hsource : Ixon.Eval.eval (validatedEvalCtx constants config) sourceFuel
      (validatedMainFrame mainAddress) [] validatedMainSource =
        .ok sourceValue)
    (targetOracle : Address → List RVal → Option RVal)
    (htarget : ∀ {targetAddress targetDecl},
      (targetAddress, targetDecl) ∈ compilation.lowering.raw →
      (compilation.targetCtx targetOracle).decls targetAddress =
        some targetDecl)
    (hrepresented : ExtraRepresented (compilation.targetCtx targetOracle)
      compilation.lowering.finalState)
    (hcontracts : CompilerContracts
      (IxIR0.Env.ofList compilation.erasure.result.declarations)
      (compilation.targetCtx targetOracle))
    (hexternValue : ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx (compilation.targetCtx targetOracle))
    (hexternProgress : ExternTraceProgressContract compilation.functionRel
      compilation.addressedSourceCtx (compilation.targetCtx targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.lowering.result.addressedCtx targetOracle)
      (.ref mainAddress) compilation.lowering.result.main
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (IxIR1.Readdress.Renaming.apply
        compilation.lowering.result.addressMap)
      compilation.functionRel := by
  letI : Sim.MemberScope := compilation.memberScope
  have hframe : (validatedMainFrame mainAddress).SharingWF := by
    constructor
    · rfl
    · intro index member hget
      simp [validatedMainFrame] at hget
  have hbelow : Ixon.Sharing.sharesBelow
      (validatedMainFrame mainAddress).sharing.size
      validatedMainSource = true := rfl
  have herase : EraseAddressed.run
      (EraseValidator.eraseCtxOf (validatedEvalCtx constants config))
      constants compilation.entry.target eraseFuel =
        .ok compilation.erasure.result := by
    rw [compilation.entryTarget]
    exact compilation.erasure.runEq
  have hsimulation : MutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.lowering.result.addressedCtx targetOracle)
      compilation.entry.target compilation.lowering.result.main
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (IxIR1.Readdress.Renaming.apply
        compilation.lowering.result.addressMap)
      compilation.functionRel := by
    exact
      lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_sealed
      (erased := compilation.erasure.result)
      (mainWorld := mainWorld) (compilerFuel := lowerFuel)
      (raw := compilation.lowering.raw)
      (mainCode := compilation.lowering.mainCode)
      (finalState := compilation.lowering.finalState)
      (lowered := compilation.lowering.result)
      (fun _ _ => none) compilation.members compilation.entry herase
      (IxIR0.Readdress.Oracle.Readdressable.empty
        compilation.erasure.result.addressMap)
      horacles hctx hframe hbelow hsource compilation.lowering.lowerRun
      compilation.lowering.addressedRun targetOracle htarget hrepresented
      hcontracts hexternValue hexternProgress
  intro legacyFuel legacyValue hlegacy
  apply hsimulation
  simpa only [compilation.entryTarget] using hlegacy

end ValidatedCompilation

end Compilatrix.Pipeline
