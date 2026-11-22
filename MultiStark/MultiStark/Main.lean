import MultiStark
import MultiStark.FunctionGroups
import Aiur.Artifact
import Aiur.Trace.Export
import Aiur.Optimized.Grouping.Snapshot
import Blake3.Rust

open Aiur Lean

private def blake3Hex (bytes : ByteArray) : String :=
  String.join ((Blake3.Rust.hash bytes).val.toList.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    if digits.length == 1 then s!"0{String.ofList digits}" else String.ofList digits)

private instance : ToJson MultiStark.F := ⟨fun x => toJson x.val⟩

unsafe def main (args : List String) : IO Unit := do
  let groups := if args.contains "--ungrouped" then [] else MultiStark.functionGroups
  let mode := args.headD "check"
  unless ["check", "digest", "export", "export-trace", "grouping-snapshot"].contains mode do
    throw (IO.userError "usage: stark-export check|digest|export|export-trace|grouping-snapshot [output] [--aggregate]")
  let aggregate := args.contains "--aggregate"
  let (source, digest) := if aggregate then (MultiStark.aggregateProgram, MultiStark.aggregateDigest)
    else (MultiStark.recursionProgram, MultiStark.recursionDigest)
  if mode == "digest" then
    IO.println digest
    return
  IO.eprintln s!"MultiStark {if aggregate then "aggregate" else "recursion"} program {digest}"
  let entry := if aggregate then "MultiStark::ix_aggr" else "MultiStark::verify_multi_stark_proof"
  let prepared ← IO.ofExcept (Modules.prepare source [entry])
  IO.eprintln "Compiling recursive verifier bytecode..."
  let exported ← IO.ofExcept prepared.exportExecution
  IO.eprintln s!"Exported {exported.bytecode.functions.length} functions."
  if mode == "check" then return
  if mode == "grouping-snapshot" then
    let compiled ← IO.ofExcept (prepared.compileOptimized {})
    let physical ← IO.ofExcept (Optimized.Physical.prepare compiled.circuit.artifact)
    let cfg ← IO.ofExcept (Trace.depthConfig MultiStark.modulus physical)
    let snapshot := Optimized.Grouping.Snapshot.capture compiled.circuit.artifact physical cfg
      (exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)) groups
    let path := args[1]?.getD "/tmp/verifier-grouping.json"
    IO.FS.writeFile path (toJson snapshot).compress
    IO.eprintln s!"Wrote grouping snapshot {path}"
    return
  let (exported, trace) ← if mode == "export-trace" then do
    IO.eprintln "Compiling certified circuits and witness population plans..."
    let compiled ← IO.ofExcept (prepared.compileOptimized {})
    let (exported, trace) ← IO.ofExcept (Trace.exportPlanPar MultiStark.modulus ZMod.val
      compiled.circuit.inlined.program compiled.circuit.artifact exported groups)
    pure (exported, some trace)
  else pure (exported, none)
  let path := args[1]?.getD "/tmp/ix-recursion.ixa"
  let pkg ← IO.ofExcept (Artifact.package exported MultiStark.modulus ZMod.val trace)
  Artifact.write path pkg
  IO.eprintln s!"Wrote {path} (blake3: {blake3Hex pkg})"
