import Benchmark.ScalingWorker

/-! A supplementary checked IxIR₂ family for converging CFG edges. The
ordinary Ixon lowering currently emits terminal recursor alternatives and no
converging joins. These inputs have explicitly different provenance and never
claim a source certificate or source/HPT timing. -/
namespace Benchmark.Scaling
open Lean System Compilatrix Compilatrix.Ixon Compilatrix.Tools.Check

def joinRoot : Address := Address.blake3 "compilatrix/scaling-joins/function/1".toUTF8

/-- A fixed experiment endpoint bounds encoder cost without changing any
compiler acceptance limit. Larger rows still cross native selection/lowering. -/
def joinEmitsObject (count : Nat) : Bool := count ≤ 8

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

def generateJoins (count : Nat) (path : FilePath) : IO Unit := do
  need (count > 0 && count ≤ 1024) "join parameter must be in 1..1024"
  need (!(← path.pathExists)) s!"input already exists: {path}"
  let artifact := joinArtifact count
  writeJson path (Json.mkObj [
    ("format", toJson "compilatrix/compiler-scaling-joins-input/1"), ("family", toJson "joins"),
    ("size", toJson count), ("edited", toJson false), ("root", toJson artifact.address),
    ("endpoint", toJson (if joinEmitsObject count then "elf" else "native-lower")),
    ("preimage", Coverage.byteJson artifact.preimage)])

def readJoins (path : FilePath) : IO (Nat × IxIR2.Wire.Artifact) := do
  need ((← path.metadata).byteSize ≤ 16 * 1024 * 1024) "join input exceeds 16 MiB"
  let metadata ← readJson path
  need ((← strField metadata "format") == "compilatrix/compiler-scaling-joins-input/1" &&
    (← strField metadata "family") == "joins" && (← field metadata "edited") == toJson false) "wrong join input format"
  let count ← nat (← field metadata "size")
  need (count > 0 && count ≤ 1024) "join parameter must be in 1..1024"
  need ((← strField metadata "endpoint") == (if joinEmitsObject count then "elf" else "native-lower")) "join experiment endpoint changed"
  let generated := joinArtifact count
  let bytes ← checked (unhex (← strField metadata "preimage"))
  let root ← address (← field metadata "root")
  need (root == generated.address && bytes == generated.preimage) "join bytes differ from the workload definition"
  let decoded ← checked (IxIR2.Wire.Artifact.decodeAddressed {} bytes root)
  return (count, decoded.artifact)

def compileJoins (input output : FilePath) : IO Unit := do
  let (count, artifact) ← readJoins input
  fresh output
  IO.FS.writeFile (output / "input.json") (← IO.FS.readFile input)
  let measurements : Measurements := {
    rows := ← IO.mkRef #[], rejection := ← IO.mkRef none, directory := output, timerPairNs := ← timerControl }
  let data ← IO.mkRef [
    ("format", toJson "compilatrix/compiler-scaling-outcome/1"), ("family", toJson "joins"),
    ("size", toJson count), ("edited", toJson false), ("input_stage", toJson "checked-ixir2")]
  try
    let validated ← measure measurements "snapshot-ownership-check" fun _ => artifact.check IxIR2.Validate.defaultLimits
    add data "ixir2_stats" (toJson validated.stats)
    backend measurements data output artifact (joinEmitsObject count)
  catch error =>
    if (← measurements.rejection.get).isNone then throw error
  finish output measurements data (if joinEmitsObject count then "compiled" else "lowered")
  IO.println s!"joins/{count}: {if (← measurements.rejection.get).isSome then "rejected" else "accepted"}"

end Benchmark.Scaling
