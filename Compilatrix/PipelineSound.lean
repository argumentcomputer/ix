import Compilatrix.Pipeline
import Compilatrix.IxIR1.LowerMutualAddressedProgress
import Compilatrix.IxIR1.NoReuseAddressed
import Compilatrix.IxIR1.CostTrace

/-!
# Semantic interface for validator-gated compilation

`Pipeline.compileValidatedWithTrace` retains the exact scoped erasure
certificate, simultaneous-member coverage, addressed-erasure equation, and
stateful fully-addressed lowering equations.  This file projects those
witnesses into the production forward-simulation theorem.  Source sharing and
oracle correspondence remain semantic premises, and extern behavior retains
its explicit ABI contract. Target layout, generated representation, and every
compiler-owned ownership contract are reconstructed from the retained traces.
-/

namespace Compilatrix.Pipeline

open Compilatrix.Ixon (Address Constant Owned)
open Compilatrix.IxIR1
open Compilatrix.IxIR1.Lower
open Compilatrix.IxIR1.LowerSim
open Compilatrix.IxIR1.CostTrace

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

/-- The exact raw target context represents every generated declaration and
memoized constructor wrapper in the final lowering state. -/
theorem exactExtraRepresented
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    ExtraRepresented (compilation.exactTargetCtx targetOracle)
      compilation.lowering.finalState := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  apply lowerAllAction_extraRepresented hlower
  intro address declaration hmember
  exact compilation.exactTargetCtx_decls_of_mem targetOracle
    (lowerAllAction_extra_mem_result hlower hmember)

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
`compileValidatedWithTrace` result. All executable equalities, target layout,
ownership contracts, and the runtime-derived mutual-member scope are supplied
by `compilation`; the remaining premises are genuine source/oracle and backend
ABI obligations. The final heap relation uses the certified alias-free rebuild
map consumed by the exact raw target context. -/
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
    (hexternValue : ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle))
    (hexternProgress : ExternTraceProgressContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle)) :
    MutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.lowering.result.addressedCtx targetOracle)
      (.ref mainAddress) compilation.lowering.result.main
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (compilation.lowering.result.rebuildRename compilation.lowering.raw)
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
      (compilation.lowering.result.rebuildRename compilation.lowering.raw)
      compilation.functionRel := by
    exact
      lowerAllIndexedFullyAddressed_semanticForwardSimulation_of_certificate_with_members_exact_sealed
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
      compilation.lowering.addressedRun targetOracle
      (fun hmember =>
        compilation.exactTargetCtx_decls_of_mem targetOracle hmember)
      (compilation.exactExtraRepresented targetOracle)
      (compilation.exactCompilerContracts targetOracle).1
      hexternValue hexternProgress
  intro legacyFuel legacyValue hlegacy
  apply hsimulation
  simpa only [compilation.entryTarget] using hlegacy

/-- The validated source execution and backend ABI contracts produce an
actual successful execution of the final content-addressed target. -/
theorem targetProgress
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
    (hexternValue : ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle))
    (hexternProgress : ExternTraceProgressContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle)) :
    ∃ targetFuel store value,
      runMain (compilation.lowering.result.addressedCtx targetOracle)
        compilation.lowering.result.main targetFuel = .ok (store, value) := by
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
  exact
    lowerAllIndexedFullyAddressed_main_progress_of_addressed_certificate_with_members_exact_sealed
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
      compilation.lowering.addressedRun targetOracle
      (fun hmember =>
        compilation.exactTargetCtx_decls_of_mem targetOracle hmember)
      (compilation.exactExtraRepresented targetOracle)
      (compilation.exactCompilerContracts targetOracle).1
      hexternValue hexternProgress

/-- No execution fuel can expose a dynamic memory error in the validated
fully addressed main. One certified successful run rules out smaller-fuel
memory errors by persistence and larger-fuel errors by success monotonicity. -/
theorem memoryErrorUnreachable
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
    (hexternValue : ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle))
    (hexternProgress : ExternTraceProgressContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle)) :
    MemoryErrorUnreachable
      (compilation.lowering.result.addressedCtx targetOracle)
      compilation.lowering.result.main := by
  apply memoryErrorUnreachable_of_progress
  exact compilation.targetProgress horacles hctx hsource targetOracle
    hexternValue hexternProgress

/-- Every successful execution of the validated fully addressed artifact can
release its result and reclaim the entire fresh heap. No target-context or
ownership premise remains at the pipeline boundary. -/
theorem reclamation
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    Reclamation (compilation.lowering.result.addressedCtx targetOracle)
      compilation.lowering.result.main mainWorld := by
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  have hraw : Reclamation (compilation.exactTargetCtx targetOracle)
      compilation.lowering.mainCode mainWorld :=
    NoReuse.lowerAllAction_reclamation hlower rfl
      (compilation.exactExtraRepresented targetOracle)
      (compilation.exactCompilerContracts targetOracle).1
  intro runFuel store value hrun
  exact NoReuse.lowerAllIndexedFullyAddressed_reclamation_of_exact_raw
    compilation.lowering.lowerRun compilation.lowering.addressedRun
    targetOracle hraw hrun

/-- The fully addressed artifact satisfies the current lowerer's public
counter contract: no reuse instruction executes, and frees never exceed
allocations. Address completion preserves all four observed counters. -/
theorem costRefinement
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    CostRefinement compilation.addressedSourceCtx
      (compilation.lowering.result.addressedCtx targetOracle)
      compilation.erasure.result.main compilation.lowering.result.main
      compilation.functionRel
      (fun _ observation => NoReuse.CurrentLowererCostSpec observation) := by
  apply RunCostInvariant.costRefinement
  have hlower :
      (lowerAllAction compilation.erasure.result.declarations
        compilation.erasure.result.main mainWorld lowerFuel).run {} =
          .ok (compilation.lowering.raw, compilation.lowering.mainCode)
            compilation.lowering.finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using
      compilation.lowering.lowerRun
  have hraw : RunCostInvariant (compilation.exactTargetCtx targetOracle)
      compilation.lowering.mainCode NoReuse.CurrentLowererCostSpec :=
    NoReuse.runCostInvariant_of_noReuse_with_allocationFree
      (NoReuse.lowerAllAction_ctxNoReuse hlower rfl)
      (NoReuse.lowerAllAction_noReuse hlower).2.1
  intro targetFuel targetStore targetValue htarget
  exact
    NoReuse.lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw
      compilation.lowering.lowerRun compilation.lowering.addressedRun
      targetOracle hraw htarget

/-- A call-aware source profile gives the final artifact the existing
ownership-amortized four-counter budget. Profile availability stays explicit
because ordinary IxIR₀ evaluation is broader than the call-aware trace
fragment; target layout and ownership are derived from compilation. -/
theorem ownershipAmortizedCostRefinement
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal)
    (hexternValue : ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle))
    (hprofile : ∀ {sourceFuel sourceValue},
      IxIR0.eval compilation.addressedSourceCtx sourceFuel []
        compilation.erasure.result.main = .ok sourceValue →
      ∃ profile, IxIR0.DynamicCost.Profiled compilation.addressedSourceCtx
        compilation.erasure.result.main sourceValue profile) :
    ProfileCostRefinement compilation.addressedSourceCtx
      (compilation.lowering.result.addressedCtx targetOracle)
      compilation.erasure.result.main compilation.lowering.result.main
      compilation.functionRel
      (fun _ profile observation =>
        WithinBudget ownershipAmortizedWeights profile observation) := by
  exact lowerAllIndexedFullyAddressed_profileCostRefinement_exact_sealed
    (funRel := compilation.functionRel) rfl
    compilation.lowering.lowerRun compilation.lowering.addressedRun
    targetOracle
    (fun hmember =>
      compilation.exactTargetCtx_decls_of_mem targetOracle hmember)
    (compilation.exactExtraRepresented targetOracle)
    (compilation.exactCompilerContracts targetOracle).1 hexternValue hprofile

end ValidatedCompilation

end Compilatrix.Pipeline
