import Ix.Compiler.Pipeline
import Ix.Compiler.IxIR1.LowerMutualAddressedProgress
import Ix.Compiler.IxIR1.NoReuseAddressed
import Ix.Compiler.IxIR1.CostTrace
import Ix.Compiler.IxIR1.OptimizerReclamation

/-!
# Semantic interface for validator-gated compilation

`Pipeline.compileValidatedWithTrace` retains the exact scoped erasure
certificate, simultaneous-member coverage, addressed-erasure equation, and
stateful fully-addressed lowering equations.  This file projects those
witnesses into the production forward-simulation theorem.  Source sharing and
oracle correspondence remain semantic premises. The certified pipeline's
closed extern boundary discharges scalar-oracle value and progress contracts
vacuously. Target layout, generated representation, and every compiler-owned
ownership contract are reconstructed from the retained traces.
-/

namespace Ix.Compiler.Pipeline

open Ix.Compiler.Ixon (Address Constant Owned)
open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Lower
open Ix.Compiler.IxIR1.LowerSim
open Ix.Compiler.IxIR1.CostTrace

/-- Semantic value relation after the fail-soft O1 optimizer.  The compiler's
two address images remain explicit in the first conjunct; the optimizer then
relates the emitted IxIR₁ result by allocation history and, when rebuilding
succeeds, by its independent final address image. -/
def OptimizedMutualAddressedValueGraph
    (outcome : Optimizer.Outcome) (policy : Optimizer.Policy)
    (program : List ReaddressAll.Artifact) (summaries : HPT.SummaryEnv)
    (main : Code) (sourceRename targetRename : Address → Address)
    (funRel : Sim.FunctionRel) (store : Store)
    (legacyValue : IxIR0.Value) (targetValue : RVal) : Prop :=
  ∃ compilerOut : Store × RVal,
    MutualAddressedValueGraph sourceRename targetRename funRel
        compilerOut.1 legacyValue compilerOut.2 ∧
      outcome.RunRefines policy program summaries main compilerOut
        (store, targetValue)

/-- Forward simulation through validated lowering and the fail-soft O1
selection. -/
def OptimizedMutualAddressedSemanticForwardSimulation
    (legacyCtx : IxIR0.Ctx) (outcome : Optimizer.Outcome)
    (policy : Optimizer.Policy) (program : List ReaddressAll.Artifact)
    (summaries : HPT.SummaryEnv) (legacyMain : IxIR0.Expr)
    (main : Code) (oracle : Address → List RVal → Option RVal)
    (sourceRename targetRename : Address → Address)
    (funRel : Sim.FunctionRel) : Prop :=
  ∀ {sourceFuel sourceValue},
    IxIR0.eval legacyCtx sourceFuel [] legacyMain = .ok sourceValue →
    ∃ targetFuel targetStore targetValue,
      runMain (outcome.targetCtx program oracle) (outcome.main main)
          targetFuel = .ok (targetStore, targetValue) ∧
        OptimizedMutualAddressedValueGraph outcome policy program summaries
          main sourceRename targetRename funRel targetStore sourceValue
          targetValue

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

/-- The exact addressed source context exposed to lowering cannot resolve an
extern.  This is the context-level form of the executable validated ABI
certificate retained by `compileValidatedWithTrace`. -/
theorem addressedSourceCtx_ne_extern
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    {address : Address} {arity : Nat} :
    compilation.addressedSourceCtx.env address ≠ some (.extern arity) := by
  simpa [addressedSourceCtx, EraseAddressed.Result.declarations,
    IxIR0.Readdress.Result.addressedCtx] using
    (compilation.addressedSourceEnv_ne_extern
      (address := address) (arity := arity))

/-- Validated compilation manufactures the scalar extern value contract:
its certified source context has no extern application to discharge. -/
theorem externValueContract
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    ExternValueContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle) := by
  constructor
  intro store address arity sourceFunction sourceResult sourceArgs args result
    hlookup
  exact False.elim (compilation.addressedSourceCtx_ne_extern hlookup)

/-- Validated compilation likewise manufactures extern progress: no admitted
source trace can start at an extern declaration. -/
theorem externTraceProgressContract
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (targetOracle : Address → List RVal → Option RVal) :
    ExternTraceProgressContract compilation.functionRel
      compilation.addressedSourceCtx
      (compilation.exactTargetCtx targetOracle) := by
  constructor
  intro sourceLimit store address arity sourceFunction sourceResult sourceArgs
    args hlookup
  exact False.elim (compilation.addressedSourceCtx_ne_extern hlookup)

/-- Exact fail-soft optimizer outcome selected for this validated artifact and
its directly produced checked HPT certificate. -/
def producedOptimizationOutcome
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts) :
    Optimizer.Outcome :=
  Optimizer.runWithProducedHPT policy compilation.artifact.targetArtifacts
    compilation.artifact.main production

/-- Oracle used to establish the original compiled execution before the
selected optimizer result. -/
def producedOptimizationSourceOracle
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (oracle : Address → List RVal → Option RVal) :
    Address → List RVal → Option RVal :=
  (compilation.producedOptimizationOutcome policy production).sourceOracle
    policy compilation.artifact.targetArtifacts
    production.certificate.summaryEnv compilation.artifact.main oracle

/-- Exact artifact selected by the existing fail-soft production API. -/
def producedOptimizedArtifact
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts) :
    Artifact :=
  (compilation.artifact.optimizeWithProducedHPT policy production).1

/-- The selected artifact carries exactly the target graph projected by the
proof-facing optimizer outcome. -/
theorem producedOptimizedArtifact_targetArtifacts
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts) :
    (compilation.producedOptimizedArtifact policy production).targetArtifacts =
      (compilation.producedOptimizationOutcome policy production).artifacts
        compilation.artifact.targetArtifacts := by
  cases hrebuilt :
      (Optimizer.runWithProducedHPT policy
        compilation.artifact.targetArtifacts compilation.artifact.main
        production).rebuilt <;>
    simp [producedOptimizedArtifact, Artifact.optimizeWithProducedHPT,
      producedOptimizationOutcome, Optimizer.Outcome.artifacts, hrebuilt,
      Artifact.withRebuiltTarget]

/-- The selected artifact carries exactly the main projected by the
proof-facing optimizer outcome. -/
theorem producedOptimizedArtifact_main
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts) :
    (compilation.producedOptimizedArtifact policy production).main =
      (compilation.producedOptimizationOutcome policy production).main
        compilation.artifact.main := by
  cases hrebuilt :
      (Optimizer.runWithProducedHPT policy
        compilation.artifact.targetArtifacts compilation.artifact.main
        production).rebuilt <;>
    simp [producedOptimizedArtifact, Artifact.optimizeWithProducedHPT,
      producedOptimizationOutcome, Optimizer.Outcome.main, hrebuilt,
      Artifact.withRebuiltTarget]

/-- Runtime context of the selected artifact is the optimizer outcome's
proof-facing target context. -/
theorem producedOptimizedArtifact_targetCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (oracle : Address → List RVal → Option RVal) :
    ({ decls :=
        (compilation.producedOptimizedArtifact policy production).targetDeclEnv
       oracle } : Ctx) =
      (compilation.producedOptimizationOutcome policy production).targetCtx
        compilation.artifact.targetArtifacts oracle := by
  have hdecls := Optimizer.Outcome.targetCtx_decls
    (compilation.producedOptimizationOutcome policy production)
    compilation.artifact.targetArtifacts oracle
  rw [← compilation.producedOptimizedArtifact_targetArtifacts policy
    production] at hdecls
  have horacle :
      ((compilation.producedOptimizationOutcome policy production).targetCtx
        compilation.artifact.targetArtifacts oracle).oracle = oracle := by
    cases hrebuilt :
        (compilation.producedOptimizationOutcome policy production).rebuilt <;>
      simp [Optimizer.Outcome.targetCtx, hrebuilt,
        ReaddressAll.Result.addressedCtx,
        ReaddressAll.Result.asReaddressResult,
        Readdress.Result.addressedCtx]
  cases htarget :
      (compilation.producedOptimizationOutcome policy production).targetCtx
        compilation.artifact.targetArtifacts oracle with
  | mk targetDecls targetOracle =>
      have htargetDecls :
          targetDecls = HPT.programDeclEnv
            (compilation.producedOptimizedArtifact policy production).targetArtifacts := by
        simpa [htarget] using hdecls
      have htargetOracle : targetOracle = oracle := by
        simpa [htarget] using horacle
      subst targetDecls
      subst targetOracle
      simp [Artifact.targetDeclEnv]

/-- The emitted compiler context with the optimizer oracle pullback is
literally the source context consumed by the optimizer theorem. -/
theorem addressedTargetCtx_eq_producedOptimizationSourceCtx
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (oracle : Address → List RVal → Option RVal) :
    compilation.lowering.result.addressedCtx
        (compilation.producedOptimizationSourceOracle policy production
          oracle) =
      (compilation.producedOptimizationOutcome policy production).sourceCtx
        policy compilation.artifact.targetArtifacts
        production.certificate.summaryEnv compilation.artifact.main oracle := by
  let sourceOracle := compilation.producedOptimizationSourceOracle policy
    production oracle
  have henv := HPT.OptimizeProgram.envOfList_declarationEntries
    compilation.lowering.result.artifacts
  change
    Env.ofList
        (compilation.lowering.result.artifacts.flatMap
          ReaddressAll.Artifact.declarations) =
      HPT.programDeclEnv compilation.lowering.result.artifacts at henv
  have hdecls :
      (compilation.lowering.result.addressedCtx sourceOracle).decls =
        HPT.programDeclEnv compilation.artifact.targetArtifacts := by
    simpa only [ValidatedCompilation.artifact,
      ReaddressAll.Result.addressedCtx,
      ReaddressAll.Result.asReaddressResult,
      Readdress.Result.addressedCtx, Readdress.Result.declarations,
      List.append_nil, ReaddressAll.Result.declarations] using henv
  change
    ({ decls :=
        (compilation.lowering.result.addressedCtx sourceOracle).decls
       oracle := sourceOracle } : Ctx) =
      { decls := HPT.programDeclEnv compilation.artifact.targetArtifacts
        oracle := sourceOracle }
  rw [hdecls]

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
ownership contracts, the closed extern boundary, and the runtime-derived
mutual-member scope are supplied by `compilation`; the remaining premises are
genuine source/oracle obligations. The final heap relation uses the certified
alias-free rebuild map consumed by the exact raw target context. -/
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
    (targetOracle : Address → List RVal → Option RVal) :
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
      (compilation.externValueContract targetOracle)
      (compilation.externTraceProgressContract targetOracle)
  intro legacyFuel legacyValue hlegacy
  apply hsimulation
  simpa only [compilation.entryTarget] using hlegacy

/-- The validated semantic spine composed with a directly produced checked
O1 optimizer run.  The optimized oracle is pulled back automatically for the
pre-optimization execution. Fail-soft skips therefore select the original
simulation literally, while successful rebuilds add allocation-history and
optimizer-address witnesses. -/
theorem semanticForwardSimulationAfterProducedOptimization
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
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    OptimizedMutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.producedOptimizationOutcome policy production) policy
      compilation.artifact.targetArtifacts production.certificate.summaryEnv
      (.ref mainAddress) compilation.artifact.main optimizerOracle
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (compilation.lowering.result.rebuildRename compilation.lowering.raw)
      compilation.functionRel := by
  let outcome := compilation.producedOptimizationOutcome policy production
  let sourceOracle := compilation.producedOptimizationSourceOracle policy
    production optimizerOracle
  have hcompiler : MutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.lowering.result.addressedCtx sourceOracle)
      (.ref mainAddress) compilation.lowering.result.main
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (compilation.lowering.result.rebuildRename compilation.lowering.raw)
      compilation.functionRel := by
    exact compilation.semanticForwardSimulation
      (sourceFuel := sourceFuel) (sourceValue := sourceValue)
      horacles hctx hsource sourceOracle
  intro legacyFuel legacyValue hlegacy
  obtain ⟨compilerFuel, compilerStore, compilerValue, hcompilerRun,
      hcompilerGraph⟩ := hcompiler hlegacy
  have hsourceCtx :
      compilation.lowering.result.addressedCtx sourceOracle =
        outcome.sourceCtx policy compilation.artifact.targetArtifacts
          production.certificate.summaryEnv compilation.artifact.main
          optimizerOracle := by
    simpa [outcome, sourceOracle] using
      compilation.addressedTargetCtx_eq_producedOptimizationSourceCtx
        policy production optimizerOracle
  have hoptimizerSource :
      runMain
          (outcome.sourceCtx policy compilation.artifact.targetArtifacts
            production.certificate.summaryEnv compilation.artifact.main
            optimizerOracle)
          compilation.artifact.main compilerFuel =
        .ok (compilerStore, compilerValue) := by
    rw [← hsourceCtx]
    simpa [ValidatedCompilation.artifact] using hcompilerRun
  obtain ⟨targetOut, htargetRun, hrefines⟩ :=
    Optimizer.runMain_of_runWithProducedHPT_eq
      (policy := policy) (program := compilation.artifact.targetArtifacts)
      (main := compilation.artifact.main) (production := production)
      (outcome := outcome) rfl optimizerOracle compilerFuel hoptimizerSource
  rcases targetOut with ⟨targetStore, targetValue⟩
  refine ⟨compilerFuel, targetStore, targetValue, ?_, ?_⟩
  · simpa [outcome, producedOptimizationOutcome] using htargetRun
  · exact ⟨(compilerStore, compilerValue), hcompilerGraph, hrefines⟩

/-- Artifact-facing form of the optimized semantic theorem.  Its executable
context and main are projected directly from the artifact returned by
`optimizeWithProducedHPT`, rather than from the proof-facing optimizer
outcome. -/
theorem semanticForwardSimulationOfProducedOptimizedArtifact
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
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    ∀ {legacyFuel legacyValue},
      IxIR0.eval
          (compilation.erasure.result.addressed.preAddressCtx
            compilation.erasure.result.groups)
          legacyFuel [] (.ref mainAddress) = .ok legacyValue →
      ∃ targetFuel targetStore targetValue,
        runMain
            ({ decls :=
                (compilation.producedOptimizedArtifact policy production).targetDeclEnv
               oracle := optimizerOracle } : Ctx)
            (compilation.producedOptimizedArtifact policy production).main
            targetFuel = .ok (targetStore, targetValue) ∧
          OptimizedMutualAddressedValueGraph
            (compilation.producedOptimizationOutcome policy production)
            policy compilation.artifact.targetArtifacts
            production.certificate.summaryEnv compilation.artifact.main
            (IxIR0.MutualBlock.Renaming.apply
              compilation.erasure.result.addressMap)
            (compilation.lowering.result.rebuildRename
              compilation.lowering.raw)
            compilation.functionRel targetStore legacyValue targetValue := by
  have hsimulation : OptimizedMutualAddressedSemanticForwardSimulation
      (compilation.erasure.result.addressed.preAddressCtx
        compilation.erasure.result.groups)
      (compilation.producedOptimizationOutcome policy production) policy
      compilation.artifact.targetArtifacts production.certificate.summaryEnv
      (.ref mainAddress) compilation.artifact.main optimizerOracle
      (IxIR0.MutualBlock.Renaming.apply
        compilation.erasure.result.addressMap)
      (compilation.lowering.result.rebuildRename compilation.lowering.raw)
      compilation.functionRel :=
    compilation.semanticForwardSimulationAfterProducedOptimization
      horacles hctx hsource policy production optimizerOracle
  intro legacyFuel legacyValue hlegacy
  obtain ⟨targetFuel, targetStore, targetValue, htarget, hgraph⟩ :=
    hsimulation hlegacy
  refine ⟨targetFuel, targetStore, targetValue, ?_, hgraph⟩
  rw [compilation.producedOptimizedArtifact_targetCtx policy production
    optimizerOracle]
  rw [compilation.producedOptimizedArtifact_main policy production]
  exact htarget

/-- The validated source execution produces an actual successful execution
of the final content-addressed target. -/
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
    (targetOracle : Address → List RVal → Option RVal) :
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
      (compilation.externValueContract targetOracle)
      (compilation.externTraceProgressContract targetOracle)

/-- The artifact selected by the directly produced fail-soft optimizer has a
successful execution.  This is stated on the artifact's own declaration
environment and main, so no proof-facing optimizer projection remains in the
operational conclusion. -/
theorem targetProgressAfterProducedOptimization
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
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    ∃ targetFuel store value,
      runMain
          ({ decls :=
              (compilation.producedOptimizedArtifact policy production).targetDeclEnv
             oracle := optimizerOracle } : Ctx)
          (compilation.producedOptimizedArtifact policy production).main
          targetFuel = .ok (store, value) := by
  let outcome := compilation.producedOptimizationOutcome policy production
  let sourceOracle := compilation.producedOptimizationSourceOracle policy
    production optimizerOracle
  obtain ⟨compilerFuel, compilerStore, compilerValue, hcompilerRun⟩ :=
    compilation.targetProgress horacles hctx hsource sourceOracle
  have hsourceCtx :
      compilation.lowering.result.addressedCtx sourceOracle =
        outcome.sourceCtx policy compilation.artifact.targetArtifacts
          production.certificate.summaryEnv compilation.artifact.main
          optimizerOracle := by
    simpa [outcome, sourceOracle] using
      compilation.addressedTargetCtx_eq_producedOptimizationSourceCtx
        policy production optimizerOracle
  have hoptimizerSource :
      runMain
          (outcome.sourceCtx policy compilation.artifact.targetArtifacts
            production.certificate.summaryEnv compilation.artifact.main
            optimizerOracle)
          compilation.artifact.main compilerFuel =
        .ok (compilerStore, compilerValue) := by
    rw [← hsourceCtx]
    simpa [ValidatedCompilation.artifact] using hcompilerRun
  obtain ⟨targetOut, htargetRun, _⟩ :=
    Optimizer.runMain_of_runWithProducedHPT_eq
      (policy := policy) (program := compilation.artifact.targetArtifacts)
      (main := compilation.artifact.main) (production := production)
      (outcome := outcome) rfl optimizerOracle compilerFuel hoptimizerSource
  rcases targetOut with ⟨targetStore, targetValue⟩
  refine ⟨compilerFuel, targetStore, targetValue, ?_⟩
  rw [compilation.producedOptimizedArtifact_targetCtx policy production
    optimizerOracle]
  rw [compilation.producedOptimizedArtifact_main policy production]
  simpa [outcome, producedOptimizationOutcome] using htargetRun

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
    (targetOracle : Address → List RVal → Option RVal) :
    MemoryErrorUnreachable
      (compilation.lowering.result.addressedCtx targetOracle)
      compilation.lowering.result.main := by
  apply memoryErrorUnreachable_of_progress
  exact compilation.targetProgress horacles hctx hsource targetOracle

/-- No execution fuel can expose a dynamic memory error in the artifact
selected by the directly produced fail-soft optimizer. -/
theorem memoryErrorUnreachableAfterProducedOptimization
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
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    MemoryErrorUnreachable
      ({ decls :=
          (compilation.producedOptimizedArtifact policy production).targetDeclEnv
         oracle := optimizerOracle } : Ctx)
      (compilation.producedOptimizedArtifact policy production).main := by
  apply memoryErrorUnreachable_of_progress
  exact compilation.targetProgressAfterProducedOptimization
    horacles hctx hsource policy production optimizerOracle

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

/-- Every successful execution of the artifact selected by the directly
produced fail-soft optimizer can release its result and reclaim the entire
fresh heap.  The optimizer needs one successful source run to identify its
selected execution; the validated source premises provide that witness. -/
theorem reclamationAfterProducedOptimization
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
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    Reclamation
      ({ decls :=
          (compilation.producedOptimizedArtifact policy production).targetDeclEnv
         oracle := optimizerOracle } : Ctx)
      (compilation.producedOptimizedArtifact policy production).main
      mainWorld := by
  let outcome := compilation.producedOptimizationOutcome policy production
  let sourceOracle := compilation.producedOptimizationSourceOracle policy
    production optimizerOracle
  obtain ⟨compilerFuel, compilerStore, compilerValue, hcompilerRun⟩ :=
    compilation.targetProgress horacles hctx hsource sourceOracle
  have hsourceCtx :
      compilation.lowering.result.addressedCtx sourceOracle =
        outcome.sourceCtx policy compilation.artifact.targetArtifacts
          production.certificate.summaryEnv compilation.artifact.main
          optimizerOracle := by
    simpa [outcome, sourceOracle] using
      compilation.addressedTargetCtx_eq_producedOptimizationSourceCtx
        policy production optimizerOracle
  have hoptimizerSource :
      runMain
          (outcome.sourceCtx policy compilation.artifact.targetArtifacts
            production.certificate.summaryEnv compilation.artifact.main
            optimizerOracle)
          compilation.artifact.main compilerFuel =
        .ok (compilerStore, compilerValue) := by
    rw [← hsourceCtx]
    simpa [ValidatedCompilation.artifact] using hcompilerRun
  have hsourceReclamation :
      Reclamation
          (outcome.sourceCtx policy compilation.artifact.targetArtifacts
            production.certificate.summaryEnv compilation.artifact.main
            optimizerOracle)
          compilation.artifact.main mainWorld := by
    intro runFuel store value hrun
    have hcompilerRun' :
        runMain (compilation.lowering.result.addressedCtx sourceOracle)
            compilation.lowering.result.main runFuel = .ok (store, value) := by
      rw [hsourceCtx]
      simpa [ValidatedCompilation.artifact] using hrun
    obtain ⟨releaseFuel, released, hrelease, hlive⟩ :=
      compilation.reclamation sourceOracle hcompilerRun'
    refine ⟨releaseFuel, released, ?_, hlive⟩
    rw [LowerSim.releaseResult_ctx_eq
      (compilation.lowering.result.addressedCtx sourceOracle)
      (outcome.sourceCtx policy compilation.artifact.targetArtifacts
        production.certificate.summaryEnv compilation.artifact.main
        optimizerOracle)]
    exact hrelease
  have htarget :
      Reclamation
        (outcome.targetCtx compilation.artifact.targetArtifacts
          optimizerOracle)
        (outcome.main compilation.artifact.main) mainWorld :=
    Optimizer.reclamation_of_runWithProducedHPT_eq
      (policy := policy) (program := compilation.artifact.targetArtifacts)
      (main := compilation.artifact.main) (production := production)
      (outcome := outcome) (houtcome := rfl) (oracle := optimizerOracle)
      (world := mainWorld)
      (hprogress :=
        ⟨compilerFuel, (compilerStore, compilerValue), hoptimizerSource⟩)
      (hreclamation := hsourceReclamation)
  rw [compilation.producedOptimizedArtifact_targetCtx policy production
    optimizerOracle]
  rw [compilation.producedOptimizedArtifact_main policy production]
  intro runFuel store value hrun
  exact htarget hrun

/-- The selected optimized artifact retains the evaluator-universal
allocation/free law.  Stronger four-counter contracts are deliberately not
claimed here: successful optimizer rewrites may change allocation and free
counts while preserving the heap history used by semantic refinement. -/
theorem allocationFreeCostInvariantAfterProducedOptimization
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    (policy : Optimizer.Policy) {limits : HPT.Limits}
    (production : HPT.Production limits compilation.artifact.targetArtifacts)
    (optimizerOracle : Address → List RVal → Option RVal) :
    RunCostInvariant
      ({ decls :=
          (compilation.producedOptimizedArtifact policy production).targetDeclEnv
         oracle := optimizerOracle } : Ctx)
      (compilation.producedOptimizedArtifact policy production).main
      AllocationFreeCostSpec := by
  exact runCostInvariant_allocationFree _ _

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
    (compilation.exactCompilerContracts targetOracle).1
    (compilation.externValueContract targetOracle) hprofile

end ValidatedCompilation

end Ix.Compiler.Pipeline
