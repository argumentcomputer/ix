import Ix.Compiler.CallReuse.Pipeline
import Ix.Compiler.IxIR0.MapRecovery

/-! Optional exact map specialization feeds the ordinary ownership compiler
and common checked backend. Every failure keeps the validated literal source
artifact. The v1 reuse selection itself retains checked baseline fallback. -/

namespace Ix.Compiler.CallReuse

open Ix.Compiler.Ixon (Address Constant)

def mapInput (result : IxIR1.ReaddressAll.Result) : IxIR2.Lower.Input :=
  { declarations := result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations
    main := result.main, mainResult := .shared }

def mapSidecars {fuel : Nat} (plan : IxIR0.MapRecovery.Plan)
    (source : Pipeline.LoweredCompilation .shared fuel) :
    Except IxIR2.Pipeline.Error (IxIR2.Pipeline.BuiltCompiledSidecars source) := do
  let hpt ← (IxIR1.HPT.produce source.lowering.result.artifacts).mapError .hpt
  let constructors : List IxIR2.Pipeline.ConstructorInfo :=
    [{ identity := IxIR1.Lower.ctorIdOf plan.schema.nil 0, arity := 0 },
      { identity := IxIR1.Lower.ctorIdOf plan.schema.cons 1, arity := 2 }] ++
      plan.retainedAlias.toList.map fun pair => { identity := IxIR1.Lower.ctorIdOf pair 0, arity := 2 }
  let sidecars : IxIR2.Pipeline.Sidecars := {
    input := mapInput source.lowering.result
    parameterEntries := source.targetDecls.filterMap fun (address, declaration) => match declaration with
      | .fn definition => some (address, Array.replicate definition.arity .shared)
      | .extern _ => none
    constructors
    hptCertificate := hpt.certificate }
  return { sidecars, hpt, certificateProduced := rfl, inputProduced := rfl }

structure MapLowered {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (recovery : IxIR0.MapRecovery.Recovered declarations main) (fuel : Nat) where
  lowering : IxIR1.Lower.FullyAddressedTrace
    (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)
    (recovery.checked.plan.directMain recovery.address) .shared fuel
  certificate : Pipeline.LoweringCertificate
    (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)
    (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)
  backend : IxIR2.Pipeline.CompiledRun (Pipeline.LoweredCompilation.ofTrace lowering certificate)
  reuse : IxIR2.CallReuse.Selection IxIR2.Validate.defaultLimits
    backend.val.target.artifact.validationContext backend.val.target.artifact.program

def MapLowered.compilation {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}
    (lowered : MapLowered recovery fuel) : Pipeline.LoweredCompilation .shared fuel :=
  Pipeline.LoweredCompilation.ofTrace lowered.lowering lowered.certificate
def MapLowered.attached {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}
    (lowered : MapLowered recovery fuel) : IxIR2.Pipeline.CompiledAttachment .shared fuel := lowered.backend.val
theorem MapLowered.sourceProduced {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}
    (lowered : MapLowered recovery fuel) : lowered.attached.source = lowered.compilation := lowered.backend.property

inductive MapSkip where
  | recovery (reason : IxIR0.Recursion.Skip)
  | lowering (message : String)
  | attachment (error : IxIR2.Pipeline.Error)
  deriving Repr

def lowerMap {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (recovery : IxIR0.MapRecovery.Recovered declarations main) (fuel : Nat) (maxDepth : Nat) :
    Except MapSkip (MapLowered recovery fuel) := do
  let lowering ← (IxIR1.Lower.lowerAllIndexedFullyAddressedWithTrace
    (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)
    (recovery.checked.plan.directMain recovery.address) .shared fuel).mapError .lowering
  let certificate ← (Pipeline.checkLoweringCertificate
    (IxIR0.MapRecovery.targetDeclarations recovery.checked.plan recovery.address)
    (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)).mapError .lowering
  let compilation := Pipeline.LoweredCompilation.ofTrace lowering certificate.down
  let built ← (mapSidecars recovery.checked.plan compilation).mapError .attachment
  let backend ← (IxIR2.Pipeline.attachCompiled compilation built maxDepth).mapError .attachment
  let reuse := IxIR2.CallReuse.selectChecked IxIR2.Validate.defaultLimits
    backend.val.target.artifact.validationContext backend.val.target.artifact.program
    ⟨backend.val.target.stats, backend.val.target.accepted⟩
  return { lowering, certificate := certificate.down, backend, reuse }

inductive MapOutcome (declarations : List (Address × IxIR0.Decl)) (main : IxIR0.Expr) (fuel : Nat) where
  | literal (reason : MapSkip)
  | recovered (recovery : IxIR0.MapRecovery.Recovered declarations main) (lowered : MapLowered recovery fuel)
def MapOutcome.selected {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr} {fuel : Nat} :
    MapOutcome declarations main fuel → IxIR0.MapRecovery.Selection declarations main
  | .literal (.recovery reason) => .literal reason
  | .literal _ => .literal .rejectedTarget
  | .recovered recovery _ => .recovered recovery

structure MapCompilation (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config) (eraseFuel lowerFuel : Nat) where
  source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel
  outcome : MapOutcome source.erasure.result.raw (.ref root) lowerFuel

def compileMap (constants : List (Address × Constant)) (root : Address) (config : Pipeline.Config := {})
    (checkFuel : Nat := 1000) (eraseFuel : Nat := 1000) (validateFuel : Nat := 1000)
    (lowerFuel : Nat := 1000) (maxDepth : Nat := 1000) :
    Except Pipeline.Error (MapCompilation constants root config eraseFuel lowerFuel) := do
  let source ← Pipeline.compileValidatedWithTrace constants root config .shared checkFuel eraseFuel validateFuel lowerFuel
  let outcome := match IxIR0.MapRecovery.select source.erasure.result.raw (.ref root) with
    | .literal reason => MapOutcome.literal (.recovery reason)
    | .recovered recovery => match lowerMap recovery lowerFuel maxDepth with
      | .error reason => .literal reason
      | .ok lowered => .recovered recovery lowered
  return { source, outcome }

end Ix.Compiler.CallReuse
