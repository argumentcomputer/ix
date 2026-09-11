import Ix.Compiler.Pipeline
import Ix.Compiler.EraseAddressedSim

/-!
# Source-independent checked ownership lowering

The backend needs the exact IxIR₀ input, the actual lowering/addressing trace,
selected source rows, and the existing closed extern boundary. These facts do
not require that the input still be the literal Ixon erasure. A validated
source compilation projects this record; a checked transformation can seal
its own exact lowering trace with the same executable checks.
-/

namespace Ix.Compiler.Pipeline

open Ixon (Address Owned)

def sourceRowsSelected (declarations : List (Address × IxIR0.Decl)) : Bool :=
  declarations.all fun (address, declaration) =>
    IxIR0.Env.ofList declarations address == some declaration

structure LoweringCertificate (declarations : List (Address × IxIR0.Decl))
    (target : List (Address × IxIR1.Decl)) : Prop where
  selected : sourceRowsSelected declarations = true
  sourceExterns : ValidatedExternsRejected declarations
  targetExterns : ValidatedTargetExternsRejected target

instance (declarations : List (Address × IxIR0.Decl))
    (target : List (Address × IxIR1.Decl)) :
    Decidable (LoweringCertificate declarations target) :=
  decidable_of_iff
    (sourceRowsSelected declarations = true ∧
      firstValidatedExtern? declarations = none ∧ firstValidatedTargetExtern? target = none)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.selected, h.sourceExterns, h.targetExterns⟩⟩

def checkLoweringCertificate (declarations : List (Address × IxIR0.Decl))
    (target : List (Address × IxIR1.Decl)) :
    Except String (PLift (LoweringCertificate declarations target)) :=
  if h : LoweringCertificate declarations target then .ok ⟨h⟩
  else .error "ownership lowering requires selected source rows and closed source/target externs"

structure LoweredCompilation (mainWorld : Owned) (fuel : Nat) where
  declarations : List (Address × IxIR0.Decl)
  main : IxIR0.Expr
  lowering : IxIR1.Lower.FullyAddressedTrace declarations main mainWorld fuel
  certificate : LoweringCertificate declarations
    (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)

namespace LoweredCompilation

def ofTrace {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {fuel : Nat}
    (lowering : IxIR1.Lower.FullyAddressedTrace declarations main mainWorld fuel)
    (certificate : LoweringCertificate declarations
      (lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations)) :
    LoweredCompilation mainWorld fuel :=
  { declarations, main, lowering, certificate }

def targetDecls {mainWorld : Owned} {fuel : Nat}
    (compilation : LoweredCompilation mainWorld fuel) : List (Address × IxIR1.Decl) :=
  compilation.lowering.result.artifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations

def targetDeclEnv {mainWorld : Owned} {fuel : Nat}
    (compilation : LoweredCompilation mainWorld fuel) : IxIR1.Env :=
  AddressEnv.lookup (AddressEnv.build compilation.targetDecls)

theorem declarationSelected {mainWorld : Owned} {fuel : Nat}
    (compilation : LoweredCompilation mainWorld fuel)
    {address : Address} {declaration : IxIR0.Decl}
    (member : (address, declaration) ∈ compilation.declarations) :
    IxIR0.Env.ofList compilation.declarations address = some declaration := by
  have selected := List.all_eq_true.mp compilation.certificate.selected
    (address, declaration) member
  simpa only [beq_iff_eq] using selected

theorem sourceEnv_ne_extern {mainWorld : Owned} {fuel : Nat}
    (compilation : LoweredCompilation mainWorld fuel) {address : Address} {arity : Nat} :
    IxIR0.Env.ofList compilation.declarations address ≠ some (.extern arity) :=
  compilation.certificate.sourceExterns.env_ne_extern

theorem targetDeclEnv_ne_extern {mainWorld : Owned} {fuel : Nat}
    (compilation : LoweredCompilation mainWorld fuel) {address : Address} {arity : Nat} :
    compilation.targetDeclEnv address ≠ some (.extern arity) :=
  compilation.certificate.targetExterns.env_ne_extern

end LoweredCompilation

/-- Project the common compiler boundary without recompilation or an added
runtime check. The validated erasure audit already supplies selected rows. -/
def ValidatedCompilation.lowered
    {constants : List (Address × Ixon.Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config mainWorld eraseFuel lowerFuel) :
    LoweredCompilation mainWorld lowerFuel :=
  { declarations := compilation.erasure.result.declarations
    main := compilation.erasure.result.main
    lowering := compilation.lowering
    certificate :=
      { selected := by
          apply List.all_eq_true.mpr
          intro entry member
          have audit := compilation.erasure.result.addressed_audit
            (EraseAddressed.semanticAudit_of_run_eq_ok compilation.erasure.runEq)
          have selected := IxIR0.Readdress.Result.declaration_lookup_of_mem_of_semanticAudit
            audit member
          simpa [selected]
        sourceExterns := compilation.externsRejected
        targetExterns := compilation.targetExternsRejected } }

end Ix.Compiler.Pipeline
