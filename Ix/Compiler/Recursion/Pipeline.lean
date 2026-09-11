import Ix.Compiler.Pipeline
import Ix.Compiler.IxIR0.Recursion
import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR2.Reuse

/-!
# Validated source compilation with optional recursion recovery

The literal validated compilation remains available in every result. Recovery
consumes its exact raw erasure. A recovered recursor receives a fresh canonical
IxIR₀ key, passes ordinary ownership lowering and complete IxIR₁ addressing,
and then crosses the existing checked CFG and reuse boundaries. The constructor
sidecars here come from the small checked recovery schema.

Unrecognized inputs and optional backend failures retain the literal compiler
artifact. Source validation failures remain compilation errors.
-/

namespace Ix.Compiler.Recursion

open Ix.Compiler.Ixon (Address Constant)

def inputOf (result : IxIR1.ReaddressAll.Result) : IxIR2.Lower.Input :=
  { declarations := result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations
    main := result.main, mainResult := .shared }

def loopAddress (result : IxIR1.ReaddressAll.Result) (address : Address) : Address :=
  IxIR1.Readdress.Renaming.apply result.addressMap address

/-- The known recovery constructors and actual addressed loop feed the same
checked HPT/sidecar attachment as ordinary source compilation. -/
def buildSidecars {fuel : Nat} (plan : IxIR0.Recursion.Plan) (address : Address)
    (source : Pipeline.LoweredCompilation .shared fuel) :
    Except IxIR2.Pipeline.Error (IxIR2.Pipeline.BuiltCompiledSidecars source) := do
  let hpt ← (IxIR1.HPT.produce source.lowering.result.artifacts).mapError .hpt
  let constructors : List IxIR2.Pipeline.ConstructorInfo :=
    [{ identity := IxIR1.Lower.ctorIdOf plan.schema.nil 0, arity := 0 },
     { identity := IxIR1.Lower.ctorIdOf plan.schema.cons 1, arity := 2 }] ++
      plan.retainedAlias.toList.map fun pair =>
        { identity := IxIR1.Lower.ctorIdOf pair 0, arity := 2 }
  let sidecars : IxIR2.Pipeline.Sidecars :=
    { input := inputOf source.lowering.result
      parameterEntries := [(loopAddress source.lowering.result address, #[.shared, .shared])]
      constructors
      hptCertificate := hpt.certificate }
  return { sidecars, hpt, certificateProduced := rfl, inputProduced := rfl }

structure Lowered {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (recovery : IxIR0.Recursion.Recovered declarations main) (fuel : Nat) where
  lowering : IxIR1.Lower.FullyAddressedTrace
    (IxIR0.Recursion.targetDeclarations recovery.checked.plan recovery.address)
    (recovery.checked.plan.directMain recovery.address) .shared fuel
  certificate : Pipeline.LoweringCertificate
    (IxIR0.Recursion.targetDeclarations recovery.checked.plan recovery.address)
    (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)
  backend : IxIR2.Pipeline.CompiledRun (Pipeline.LoweredCompilation.ofTrace lowering certificate)
  reuse : IxIR2.Reuse.Selection IxIR2.Validate.defaultLimits
    backend.val.target.artifact.validationContext backend.val.target.artifact.program

def Lowered.compilation {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}
    (lowered : Lowered recovery fuel) : Pipeline.LoweredCompilation .shared fuel :=
  Pipeline.LoweredCompilation.ofTrace lowered.lowering lowered.certificate

def Lowered.attached {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}
    (lowered : Lowered recovery fuel) : IxIR2.Pipeline.CompiledAttachment .shared fuel :=
  lowered.backend.val

def Lowered.maxDepth {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}
    (lowered : Lowered recovery fuel) : Nat := lowered.attached.maxDepth

theorem Lowered.sourceProduced {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.Recursion.Recovered declarations main} {fuel : Nat}
    (lowered : Lowered recovery fuel) : lowered.attached.source = lowered.compilation :=
  lowered.backend.property

inductive Skip where
  | recovery (reason : IxIR0.Recursion.Skip)
  | ownershipLowering (message : String)
  | cfgLowering (error : IxIR2.Lower.Error)
  | cfgAttachment (error : IxIR2.Pipeline.Error)
  deriving Repr

private def attachmentSkip : IxIR2.Pipeline.Error → Skip
  | .lowering error => .cfgLowering error
  | error => .cfgAttachment error

def lower {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    (recovery : IxIR0.Recursion.Recovered declarations main) (fuel : Nat)
    (maxDepth : Nat := 1000) :
    Except Skip (Lowered recovery fuel) := do
  let lowering ←
    (IxIR1.Lower.lowerAllIndexedFullyAddressedWithTrace
      (IxIR0.Recursion.targetDeclarations recovery.checked.plan recovery.address)
      (recovery.checked.plan.directMain recovery.address) .shared fuel).mapError .ownershipLowering
  let certificate ← (Pipeline.checkLoweringCertificate
    (IxIR0.Recursion.targetDeclarations recovery.checked.plan recovery.address)
    (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)).mapError .ownershipLowering
  let compilation := Pipeline.LoweredCompilation.ofTrace lowering certificate.down
  let sidecars ← (buildSidecars recovery.checked.plan recovery.address compilation).mapError attachmentSkip
  let backend ← (IxIR2.Pipeline.attachCompiled compilation sidecars maxDepth).mapError attachmentSkip
  let reuse := IxIR2.Reuse.selectChecked backend.val.target.artifact.validationContext
    backend.val.target.artifact.program backend.val.target.valid
  return { lowering, certificate := certificate.down, backend, reuse }

inductive Outcome (declarations : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (fuel : Nat) where
  | literal (reason : Skip)
  | recovered (recovery : IxIR0.Recursion.Recovered declarations main)
      (lowered : Lowered recovery fuel)

def Outcome.selected {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {fuel : Nat} : Outcome declarations main fuel → IxIR0.Recursion.Selection declarations main
  | .literal (.recovery reason) => .literal reason
  | .literal _ => .literal .rejectedTarget
  | .recovered recovery _ => .recovered recovery

structure Compilation (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config) (eraseFuel lowerFuel : Nat) where
  source : Pipeline.ValidatedCompilation constants root config .shared eraseFuel lowerFuel
  outcome : Outcome source.erasure.result.raw (.ref root) lowerFuel

/-- Keep the original validated artifact through every optional failure.
Neither callers nor the recognizer supply IxIR₁ or IxIR₂ code. -/
def compileValidated (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config := {})
    (checkFuel : Nat := 1000) (eraseFuel : Nat := 1000)
    (validateFuel : Nat := 1000) (lowerFuel : Nat := 1000) (maxDepth : Nat := 1000) :
    Except Pipeline.Error (Compilation constants root config eraseFuel lowerFuel) := do
  let source ← Pipeline.compileValidatedWithTrace constants root config .shared
    checkFuel eraseFuel validateFuel lowerFuel
  let outcome := match IxIR0.Recursion.select source.erasure.result.raw (.ref root) with
    | .literal reason => Outcome.literal (.recovery reason)
    | .recovered recovery =>
        match lower recovery lowerFuel maxDepth with
        | .error reason => .literal reason
        | .ok lowered => .recovered recovery lowered
  return { source, outcome }

end Ix.Compiler.Recursion
