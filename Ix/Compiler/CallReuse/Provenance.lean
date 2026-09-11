import Ix.Compiler.CallReuse.Pipeline
import Ix.Compiler.CallReuse.MapPipeline
import Ix.Compiler.IxIR1.Optimizer

/-!
# IxIR₁ and policy provenance for call reuse

This identity commits to the canonical addressed IxIR₁ graph and the source,
HPT, and versioned policies that determine its lowering. It is provenance for
rebuilding the selected program, not a content address of serialized IxIR₂.
The diagnostic JSON has no cache or wire-format role.
-/

namespace Ix.Compiler.CallReuse

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.IxIR

structure Provenance where
  sourceRoot : Address
  ir1Root : Address
  hptRoots : List Address
  maxDepth : Nat
  loweringVersion : Nat := 1
  pass : String := IxIR2.CallReuse.policyTag
  execution : IxIR2.CreditPolicy
  optimized : Bool
  specialization : Option (String × Address) := none

def Provenance.bytes (provenance : Provenance) : ByteArray :=
  "compilatrix/call-reuse-provenance/1\x00".toUTF8 ++
    Encoding.address provenance.sourceRoot ++ Encoding.address provenance.ir1Root ++
    Encoding.list Encoding.address provenance.hptRoots ++ Encoding.nat provenance.maxDepth ++
    Encoding.nat provenance.loweringVersion ++ Encoding.blob provenance.pass.toUTF8 ++
    Encoding.blob provenance.execution.tag.toUTF8 ++ Encoding.tag (if provenance.optimized then 1 else 0) ++
    Encoding.list (fun (policy, address) => Encoding.string policy ++ Encoding.address address)
      provenance.specialization.toList

def Provenance.identity (provenance : Provenance) : Address := Address.blake3 provenance.bytes

def Compilation.provenance {constants : List (Address × Constant)} {root : Address}
    {config : Pipeline.Config} {eraseFuel lowerFuel : Nat}
    (compilation : Compilation constants root config eraseFuel lowerFuel) : Provenance :=
  { sourceRoot := root
    ir1Root := IxIR1.Optimizer.graphRoot compilation.attached.source.artifact.targetArtifacts
      compilation.attached.source.artifact.main
    hptRoots := compilation.attached.hpt.result.artifacts.map (·.address)
    maxDepth := compilation.attached.maxDepth
    execution := compilation.selection.policy
    optimized := match compilation.selection with | .optimized .. => true | .baseline .. => false }

def MapLowered.provenance {declarations : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {recovery : IxIR0.MapRecovery.Recovered declarations main} {fuel : Nat}
    (lowered : MapLowered recovery fuel) (root : Address) : Provenance :=
  { sourceRoot := root
    ir1Root := IxIR1.Optimizer.graphRoot lowered.lowering.result.artifacts lowered.lowering.result.main
    hptRoots := lowered.attached.hpt.result.artifacts.map (·.address)
    maxDepth := lowered.attached.maxDepth
    execution := lowered.reuse.policy
    optimized := match lowered.reuse with | .optimized .. => true | .baseline .. => false
    specialization := some (IxIR0.MapRecovery.policyTag, recovery.address) }

end Ix.Compiler.CallReuse
