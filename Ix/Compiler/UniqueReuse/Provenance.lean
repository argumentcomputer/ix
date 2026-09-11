import Ix.Compiler.UniqueReuse.Pipeline
import Ix.Compiler.IxIR1.Optimizer

/-! Canonical IxIR₁ graph and explicit policy provenance. The source identity
commits to the complete Ixon input bytes as well as their supplied keys and
the explicit entry. Diagnostic IxIR₂ JSON has no wire or cache identity. -/

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR

def sourceBytes (constants : List (Address × Constant)) (entry : Pipeline.ClosedEntry) : ByteArray :=
  Encoding.domain "compilatrix/closed-ixon-input/1" ++ Encoding.tag 0 ++
    Encoding.list (fun (address, constant) => Encoding.address address ++ Encoding.blob (Ixon.ser constant)) constants ++
    Encoding.list Encoding.address entry.refs.toList ++
    Encoding.list (fun univ => Encoding.blob (Ixon.ser univ)) entry.univs.toList ++
    Encoding.blob (Ixon.ser entry.source)

def targetLimitBytes (limits : IxIR2.Validate.Limits) : ByteArray :=
  Encoding.list Encoding.nat [limits.maxDeclarations, limits.maxBlocks, limits.maxBlocksPerFunction,
    limits.maxInstructionsPerBlock, limits.maxValueParams, limits.maxCreditParams, limits.maxOperands,
    limits.maxAlternatives, limits.maxValueRegisters, limits.maxCreditRegisters, limits.maxScalarLeafFacts,
    limits.maxFlowWork]

structure Provenance where
  source : Address
  graph : Address
  recursorInstance : Address
  specializedInstance : Address
  checkFuel : Nat
  eraseFuel : Nat
  limits : IxIR2.Validate.Limits
  outcome : Nat

def Provenance.bytes (provenance : Provenance) : ByteArray :=
  Encoding.domain "compilatrix/unique-reuse-provenance/1" ++ Encoding.tag 0 ++
    Encoding.address provenance.source ++ Encoding.address provenance.graph ++
    Encoding.address provenance.recursorInstance ++ Encoding.address provenance.specializedInstance ++
    Encoding.nat provenance.checkFuel ++ Encoding.nat provenance.eraseFuel ++ targetLimitBytes provenance.limits ++
    Encoding.string Ixon.RecursorUsage.policyTag ++ Encoding.string IxIR0.UniqueReverse.policyTag ++
    Encoding.string IxIR2.UniqueLower.policyTag ++ Encoding.string IxIR2.UniqueLower.reusePolicyTag ++
    Encoding.string IxIR2.CreditPolicy.callLocalV0.tag ++ Encoding.nat provenance.outcome

def Provenance.identity (provenance : Provenance) : Address := Address.blake3 provenance.bytes

def Compilation.provenance {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
    {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}
    (compilation : Compilation constants entry config checkFuel eraseFuel limits) : Provenance :=
  { source := Address.blake3 (sourceBytes constants entry)
    graph := IxIR1.Optimizer.graphRoot (artifacts compilation.plan.schema) (mainCode compilation.plan)
    recursorInstance := IxIR0.UniqueReverse.sourceInstance.address
    specializedInstance := compilation.lowered.checked.recovery.address
    checkFuel, eraseFuel, limits
    outcome := match compilation.backend with
      | .ownedOnly _ => 0
      | .translated target => if target.selection.reused then 2 else 1 }

end Ix.Compiler.UniqueReuse
