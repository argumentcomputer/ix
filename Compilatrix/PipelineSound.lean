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

/-- Alias-completed target context retained by the generic readdressing
compatibility endpoint. -/
def targetCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) : IxIR1.Ctx :=
  compilation.lowering.result.preAddressCtx compilation.lowering.raw
    targetOracle

/-- Exact raw target context immediately before complete IxIR₁ addressing.
Its oracle is pulled back through the certified total rebuild renaming, but
its declarations are literally the lowerer's returned list environment. -/
def exactTargetCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) : IxIR1.Ctx :=
  compilation.lowering.result.rebuildSourceCtx compilation.lowering.raw
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

/-- Addressed erasure selects every callable declaration row in the exact
list environment consumed by lowering. -/
theorem sourceCallableRowsSelected
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) :
    SourceCallableRowsSelected compilation.erasure.result.declarations := by
  intro address source worlds result hmember _
  have haudit := EraseAddressed.semanticAudit_of_run_eq_ok
    compilation.erasure.runEq
  have haddressed := compilation.erasure.result.addressed_audit haudit
  exact IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit
    haddressed hmember

/-- Initial complete target addressing certifies that every raw lowering row
is selected by the exact pre-address context. -/
theorem exactTargetCtx_decls_of_mem
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal)
    {address : Address} {declaration : Decl}
    (hmember : (address, declaration) ∈ compilation.lowering.raw) :
    (compilation.exactTargetCtx targetOracle).decls address =
      some declaration := by
  have hrun :=
    readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      compilation.lowering.lowerRun compilation.lowering.addressedRun
  have haudit := ReaddressAll.rebuildSemanticAudit_of_run_eq_ok hrun
  exact ReaddressAll.Result.raw_lookup_of_mem_of_rebuildSemanticAudit
    haudit hmember

/-- The validated trace determines every source callable/extern layout in the
exact raw target context. -/
theorem sourceDeclLayout
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    SourceDeclLayout
      (IxIR0.Env.ofList compilation.erasure.result.declarations)
      (compilation.exactTargetCtx targetOracle) := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  exact lowerAllAction_sourceDeclLayout
    (ctx := compilation.exactTargetCtx targetOracle) hlower
    (fun hmember =>
      compilation.exactTargetCtx_decls_of_mem targetOracle hmember)

/-- The validated trace discharges the owner-sensitive source PAP premise in
the exact raw target context. -/
theorem sourcePapSafe
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    SourcePapSafe
      (IxIR0.Env.ofList compilation.erasure.result.declarations)
      (compilation.exactTargetCtx targetOracle) := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  intro address source worlds result d hsrc hsignature hdecl hsafe
  exact lowerAllAction_sourcePapSafe
    (ctx := compilation.exactTargetCtx targetOracle)
    (address := address) (source := source) (worlds := worlds)
    (result := result) (d := d) hlower
    (fun hmember =>
      compilation.exactTargetCtx_decls_of_mem targetOracle hmember)
    hsrc hsignature hdecl hsafe

/-- Every raw function declaration in a validated trace is covered by either
its selected source callable or the final generated-declaration state. -/
theorem fnDeclCovered
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    FnDeclCovered
      (IxIR0.Env.ofList compilation.erasure.result.declarations)
      (compilation.exactTargetCtx targetOracle)
      compilation.lowering.finalState := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  apply lowerAllAction_fnDeclCovered hlower
    compilation.sourceCallableRowsSelected
  rfl

/-- The validated compiler trace constructs, rather than assumes, every
ownership contract of its exact raw target context. The second conjunct keeps
the generated-function contracts available for downstream reclamation and
cost corollaries. -/
theorem exactCompilerContracts
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    CompilerContracts
        (IxIR0.Env.ofList compilation.erasure.result.declarations)
        (compilation.exactTargetCtx targetOracle) ∧
      ExtraFnContracts (compilation.exactTargetCtx targetOracle)
        compilation.lowering.finalState := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  apply lowerAllAction_compilerContracts hlower
    (fun hmember =>
      compilation.exactTargetCtx_decls_of_mem targetOracle hmember)
    compilation.sourceCallableRowsSelected
  rfl

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
