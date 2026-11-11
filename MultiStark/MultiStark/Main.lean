import MultiStark
import MultiStark.FunctionGroups
import MultiStark.Package
import Aiur.Artifact
import Aiur.Trace.Export
import Aiur.Optimized.Grouping.Snapshot

open Aiur Lean

private instance : ToJson MultiStark.F := ⟨fun x => toJson x.val⟩

unsafe def main (args : List String) : IO Unit := do
  let groups := if args.contains "--ungrouped" then [] else MultiStark.functionGroups
  let mode := args.headD "check"
  unless ["check", "digest", "export", "export-trace", "grouping-snapshot"].contains mode do
    throw (IO.userError "usage: stark-export check|digest|export|export-trace|grouping-snapshot [output] [--aggregate]")
  let aggregate := args.contains "--aggregate"
  let (source, entry, digest) := MultiStark.selected aggregate
  if mode == "digest" then
    IO.println digest
    return
  IO.eprintln s!"MultiStark {if aggregate then "aggregate" else "recursion"} program {digest}"
  if mode == "export" || mode == "export-trace" then
    let trace := mode == "export-trace"
    IO.eprintln (if trace
      then "Compiling recursive verifier bytecode, circuits and witness population plans..."
      else "Compiling recursive verifier bytecode...")
    let package ← MultiStark.compilePackage aggregate groups trace
    let path := args[1]?.getD "/tmp/ix-recursion.ixa"
    Artifact.write path package
    IO.eprintln s!"Wrote {path}"
    return
  let prepared ← IO.ofExcept (Modules.prepare source [entry])
  IO.eprintln "Compiling recursive verifier bytecode..."
  let exported ← IO.ofExcept prepared.exportExecution
  IO.eprintln s!"Exported {exported.bytecode.functions.length} functions."
  if mode == "check" then return
  let compiled ← IO.ofExcept (prepared.compileOptimized {})
  let physical ← IO.ofExcept (Optimized.Physical.prepare compiled.circuit.artifact)
  let cfg ← IO.ofExcept (Trace.depthConfig MultiStark.modulus physical)
  let snapshot := Optimized.Grouping.Snapshot.capture compiled.circuit.artifact physical cfg
    (exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)) groups
  let path := args[1]?.getD "/tmp/verifier-grouping.json"
  IO.FS.writeFile path (toJson snapshot).compress
  IO.eprintln s!"Wrote grouping snapshot {path}"
