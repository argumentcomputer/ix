import Compilatrix.IxIR2.WirePipeline

/-! The fixed checked IxIR₂ converging-join workload. It is shared by the
original scaling reference and the native emission comparison. -/
namespace Benchmark.Scaling
open Compilatrix Compilatrix.Ixon

def joinRoot : Address := Address.blake3 "compilatrix/scaling-joins/function/1".toUTF8

def joinArtifact (count : Nat) : IxIR2.Wire.Artifact := Id.run do
  let block := fun values instructions terminator =>
    ({ valueParams := values, creditParams := #[], instructions, terminator } : IxIR2.Block)
  let edge := fun target values => ({ target, values, credits := #[] } : IxIR2.Edge)
  let owned := IxIR2.ValueCap.owned .shared
  let mut blocks := #[]
  for index in [:count] do
    let start := index * 3
    blocks := blocks ++ #[
      block #[owned] #[] (.switchValue (.reg 0) #[]
        (some ⟨edge (start + 1) #[.reg 0], edge (start + 2) #[.reg 0]⟩)),
      block #[owned] #[] (.jump (edge (start + 3) #[.reg 0])),
      block #[.scalar, owned] #[.releaseShared (.reg 1)] (.jump (edge (start + 3) #[.reg 0]))]
  let definition : IxIR2.Function := {
    signature := { params := #[⟨.shared, .owned⟩], result := .shared, papSafe := true }
    blocks := blocks.push (block #[owned] #[] (.ret (.reg 0))) }
  return {
    policy := {
      semantics := IxIR2.Wire.semanticsVersion, validator := IxIR2.Wire.validatorVersion
      lowering := "compiler-scaling-joins/1", passes := #[], layout := "baseline-constructor-world/0", credits := .callLocalV0 }
    dependencies := #[], layouts := #[], schemas := #[], scalarLeaves := #[]
    program := {
      declarations := [(joinRoot, .fn definition)]
      main := {
        signature := { params := #[], result := .shared, papSafe := false }
        blocks := #[block #[] #[.papp joinRoot #[]] (.ret (.reg 0))] } } }

end Benchmark.Scaling
