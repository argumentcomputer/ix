import MultiStark
import MultiStark.FunctionGroups
import MultiStark.Package
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

/-- The function groups: none with `--ungrouped`, those of the JSON file after
`--groups` (`[[name, [function, …]], …]`, as the wrap policies under
`crates/stark-verifier/compress-wrap/` store them), else the verifier's. -/
def readGroups (args : List String) : IO (List (String × List String)) := do
  if args.contains "--ungrouped" then return []
  match args.dropWhile (· != "--groups") with
  | _ :: path :: _ =>
    IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse (← IO.FS.readFile path))))
  | [_] => throw (IO.userError "--groups needs a file")
  | [] => return MultiStark.functionGroups

unsafe def main (args : List String) : IO Unit := do
  let groups ← readGroups args
  let mode := args.headD "check"
  unless ["check", "digest", "export", "export-trace", "grouping-snapshot"].contains mode do
    throw (IO.userError "usage: stark-export check|digest|export|export-trace|grouping-snapshot [output] [--aggregate|--compress-wrap] [--ungrouped|--groups FILE]")
  let aggregate := args.contains "--aggregate"
  let compressWrap := args.contains "--compress-wrap"
  if aggregate && compressWrap then
    throw (IO.userError "--aggregate and --compress-wrap select different programs")
  let (source, entry, digest) := if compressWrap then
      (MultiStark.compressWrapProgram, MultiStark.compressWrapEntry, MultiStark.compressWrapDigest)
    else MultiStark.selected aggregate
  if mode == "digest" then
    IO.println digest
    return
  let label := if compressWrap then "compress-wrap" else if aggregate then "aggregate" else "recursion"
  IO.eprintln s!"MultiStark {label} program {digest}"
  if mode == "export" || mode == "export-trace" then
    let trace := mode == "export-trace"
    IO.eprintln (if trace
      then "Compiling recursive verifier bytecode, circuits and witness population plans..."
      else "Compiling recursive verifier bytecode...")
    let package ← if compressWrap then MultiStark.compileCompressWrapPackage groups trace
      else MultiStark.compilePackage aggregate groups trace
    let path := args[1]?.getD (if compressWrap then "/tmp/ix-compress-wrap.ixa" else "/tmp/ix-recursion.ixa")
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
  let (cfg, _) ← IO.ofExcept
    (Trace.depthConfig MultiStark.modulus compiled.circuit.inlined.program physical)
  let snapshot := Optimized.Grouping.Snapshot.capture compiled.circuit.artifact physical cfg
    (exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name)) groups
  let path := args[1]?.getD "/tmp/verifier-grouping.json"
  IO.FS.writeFile path (toJson snapshot).compress
  IO.eprintln s!"Wrote grouping snapshot {path}"
