import IxVM
import Aiur.Execution.Encode
import Aiur.Optimized.Program
import Aiur.Trace.Export
import IxVM.PropagationBench

/-! Experimental stage-one port of IxVM. Prepare source, export bytecode and
typed data hints, execute Rust, or report circuit widths with `stats`,
`stats-no-propagation`, or `stats-reference`.
`export-trace` includes companion population plans for optimized function rows.
No proof generation runs here. -/
namespace IxVM.Cli
open Aiur Lean

private def sourcePath (relative : String) : IO System.FilePath := do
  for base in ["IxVM", "IxVM/IxVM"] do
    let path := System.FilePath.mk base / relative
    if ← path.pathExists then return path
  throw (IO.userError s!"cannot locate IxVM/{relative}; run from the Ix repository or IxVM package")

private instance : ToJson F := ⟨fun x => toJson x.val⟩
private instance : FromJson F := ⟨fun json => (fun n : Nat => (n : F)) <$> fromJson? json⟩

structure Serialized where
  address : Array Nat
  bytes : Array Nat
  hint : Nat
  deriving FromJson
structure Fixture where
  format : String
  name : String
  address : Array Nat
  addressHex : String
  invalidProof : Serialized
  constants : Array Serialized
  blobs : Array Serialized
  deriving FromJson

private def scalar (n : Nat) : Execution.DataValue F := .field n
private def array (ns : Array Nat) : Execution.DataValue F := .array .field (ns.toList.map scalar)
private def tuple (vs : List (Execution.DataValue F)) : Execution.DataValue F := .tuple vs

/-- The old IOBuffer becomes an explicit, typed dataset: address → (offset,
length), and (channel, offset) → byte. The Rust host prepares dense byte rows
as immutable vectors; the same entries remain usable by Lean's data provider.
Aiur ROM allocation happens inside the program. -/
def Fixture.hints (fixture : Fixture) : Array (Execution.HintEntry F) := Id.run do
  let mut hints : Array (Execution.HintEntry F) := #[]
  for (channel, entries) in [(2,fixture.constants.push fixture.invalidProof), (4,fixture.blobs)] do
    let mut offset := 0
    for entry in entries do
      hints := hints.push ⟨.tuple [.field,.field], tuple [scalar channel, array entry.address],
        tuple [scalar offset, scalar entry.bytes.size], "ixvm.io.info"⟩
      for i in [:entry.bytes.size] do
        hints := hints.push ⟨.field, tuple [scalar channel, scalar (offset+i)], scalar entry.bytes[i]!, "ixvm.io.read"⟩
      offset := offset + entry.bytes.size
      if channel == 2 then
        hints := hints.push ⟨.field, tuple [scalar 3, array entry.address], scalar entry.hint, "ixvm.io.tag"⟩
  -- Sample data for bytes_le. The IxVM host binds
  -- bytes_le to a closure, with no finite precomputed range (see crates/ixvm/src).
  let decompositions : List Nat := List.range 4097 ++ [4294967294,4294967295]
  for n in decompositions do
    hints := hints.push ⟨.array .field 8, scalar n,
      array (((List.range 8).map fun i => (n / 256^i) % 256).toArray), "bytes_le"⟩
  return hints

@[noinline] private def timePhase (enabled : Bool) (label : String)
    (action : Unit → Except String α) : IO α := do
  let start ← IO.monoMsNow
  let result ← IO.ofExcept (action ())
  if enabled then IO.eprintln s!"Phase {label}: {(← IO.monoMsNow) - start}ms"
  return result

private def dumpPropagation {source : Modules.Program F}
    (prepared : Modules.Prepared source) (directory : String) : IO Unit := do
  IO.eprintln "Specializing/inlining propagation fixtures..."
  let specialized ← IO.ofExcept (Generic.specialize prepared.environment.source prepared.entries)
  let inlined ← IO.ofExcept (Inlining.prepare specialized.program specialized.inlineNames prepared.entries)
  IO.FS.createDirAll directory
  for name in ["try_reduce_fin_val_decidable_rec", "put_expr", "get_expr", "blake3_compress"] do
    let some functionDecl := inlined.program.findFunction? (if name == "blake3_compress" then "Blake3::compress" else "IxVM::" ++ name)
      | throw (IO.userError s!"missing function {name}")
    let start ← IO.monoMsNow
    let logical ← IO.ofExcept (Optimized.Compiler.function inlined.program {} functionDecl)
    let chip ← IO.ofExcept (Optimized.layOut {propagateValues := false} logical)
    PropagationBench.write (directory ++ "/" ++ name ++ ".json") chip.chip
    IO.eprintln s!"Saved {name}: {chip.chip.numVars} columns in {(← IO.monoMsNow) - start}ms"

/-- Actual circuit columns, before adding any lookup protocol,
memory-table chips, multiplicities or quotient commitments. -/
private def reportColumns {source : Modules.Program F}
    (prepared : Modules.Prepared source) (path : String)
    (config : Optimized.Config := {}) (reference : Bool := false)
    (profile : Bool := false) : IO Unit := do
  let (system, representatives, unmerged, description) ← if reference then do
    IO.eprintln "Compiling reference circuits..."
    let compiled ← IO.ofExcept prepared.compile
    let system := compiled.circuit.system
    pure (system, system.chips.map (fun c => (c.name, c.name)),
      system.chips.length, "reference")
  else do
    IO.eprintln s!"Compiling circuits: {reprStr config}"
    let artifact ← if profile then do
      let specialized ← timePhase true "specialization" fun _ =>
        Generic.specialize prepared.environment.source prepared.entries
      let inlined ← timePhase true "inlining" fun _ =>
        Inlining.prepare specialized.program specialized.inlineNames prepared.entries
      timePhase true "circuit compilation" fun _ =>
        Optimized.compile inlined.program prepared.entries config
    else do
      let compiled ← IO.ofExcept (prepared.compileOptimized config)
      pure compiled.circuit.artifact
    let physical ← timePhase profile "physical deduplication" fun _ => Optimized.Physical.prepare artifact
    let representatives := artifact.representatives.map fun (name, _) => (name, physical.representative name)
    pure (physical.system, representatives, artifact.unmerged.chips.length,
      reprStr artifact.config)
  let chips := system.stats.map fun s => Json.mkObj [
    ("name", toJson s.name), ("stage1", toJson s.columns),
    ("constraint_degree", toJson s.maxConstraintDegree),
    ("call_lookups", toJson s.callLookups), ("rom_lookups", toJson s.romLookups),
    ("lookup_degree", toJson s.maxLookupDegree)]
  let tables ← system.tables.mapM fun t => do
    let layout ← IO.ofExcept ((system.enums.layout t.rowType).mapError reprStr)
    pure <| Json.mkObj [("name", toJson t.name), ("rows", toJson t.rows.length),
      ("width", toJson layout.width)]
  let columns := system.stats.foldl (fun n s => n + s.columns) 0
  let result := Json.mkObj [
    ("modulus", toJson modulus), ("entries", toJson prepared.entries),
    ("config", toJson description),
    ("function_chips", toJson chips.length), ("function_stage1", toJson columns),
    ("chips", toJson chips), ("representatives", toJson representatives),
    ("unmerged_chips", toJson unmerged),
    ("tables", toJson tables), ("static_maps", toJson system.maps.length)]
  IO.FS.writeFile path (result.pretty 100)
  IO.eprintln s!"Wrote {chips.length} chips / {columns} stage-1 columns to {path}"

/-- The IxVM host binds the library's code hints. The general Lean FFI stays
data-only; it does not acquire a hardcoded registry of arithmetic operations. -/
private def runHost (package : Json) (mode : String) : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr package.compress
    handle.flush
    let result ← IO.Process.output {
      cmd := "cargo"
      args := #["run", "--quiet", "--release", "--locked", "-p", "ixvm", "--bin", "ixvm", "--",
        path.toString, mode] }
    IO.print result.stdout
    IO.eprint result.stderr
    unless result.exitCode == 0 do
      throw (IO.userError s!"IxVM host exited with code {result.exitCode}")

unsafe def main (args : List String) : IO Unit := do
  let totalStart ← IO.monoMsNow
  let mode := args.headD "transitive"
  let profile := mode == "stats-profile"
  if mode == "propagation" || mode == "propagation-trace" then
    let some path := args[1]? | throw (IO.userError "propagation requires a chip snapshot path")
    return ← PropagationBench.run (F := F) path (mode == "propagation-trace")
  unless ["transitive", "constant", "serde", "primitives", "check", "check-claim", "export-claim", "export-claim-trace", "export", "export-trace", "export-primitives", "stats", "stats-profile", "stats-no-propagation", "stats-reference", "dump-propagation"].contains mode do
    throw (IO.userError s!"unknown mode '{mode}'; use transitive, constant, serde, primitives, check, export, export-trace, stats, stats-profile, stats-no-propagation, stats-reference, dump-propagation, propagation, or propagation-trace")
  let entry := match mode with
    | "check-claim" | "export-claim" | "export-claim-trace" => "IxVM::verify_claim"
    | "serde" => "IxVM::verify_serde"
    | "constant" => "IxVM::verify_constant"
    | "primitives" | "export-primitives" => "IxVM::check_primitives"
    | _ => "IxVM::verify_transitive"
  let text ← IO.FS.readFile (← sourcePath "Program.aiur")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{module := `Aiur.Modules.Frontend}] {} 0
  if profile then IO.eprintln s!"Phase initialization: {(← IO.monoMsNow) - totalStart}ms"
  IO.eprintln "Parsing and checking IxVM..."
  let source ← timePhase profile "parsing and source checking" fun _ => IxVM.parse env text
  IO.eprintln "Checking IxVM tables..."
  let start ← IO.monoMsNow
  let entries := if mode == "export" then ["IxVM::verify_transitive", "IxVM::verify_constant", "IxVM::verify_serde", "IxVM::check_primitives", "IxVM::check_port_cases"] else [entry]
  let prepared ← timePhase profile "module/table preparation" fun _ =>
    Modules.prepare source entries
  if mode == "dump-propagation" then
    return ← dumpPropagation prepared (args[1]?.getD "/tmp/aiur-propagation")
  if mode == "stats" || profile || mode == "stats-no-propagation" || mode == "stats-reference" then
    reportColumns prepared (args[1]?.getD "/tmp/aiur-ixvm-columns.json")
      {propagateValues := mode != "stats-no-propagation"} (mode == "stats-reference") profile
    if profile then IO.eprintln s!"Phase total: {(← IO.monoMsNow) - totalStart}ms"
    return
  IO.eprintln s!"Checked in {(← IO.monoMsNow) - start}ms. Compiling bytecode..."
  let exported ← IO.ofExcept prepared.exportExecution
  IO.eprintln s!"Exported {exported.bytecode.functions.length} functions."
  if mode == "check" || mode == "check-claim" then return
  if mode == "export-claim" || mode == "export-claim-trace" then
    let program ← IO.ofExcept (exported.toJson modulus ZMod.val)
    let trace ← if mode == "export-claim-trace" then do
      IO.eprintln "Compiling claim circuits and witness population plans..."
      let compiled ← IO.ofExcept (prepared.compileOptimized {})
      pure <| some (← IO.ofExcept (Trace.exportJson modulus ZMod.val compiled.circuit.inlined.program
        compiled.circuit.artifact exported.bytecode))
    else pure none
    let package := Json.mkObj ([("program", program)] ++ trace.toList.map ("trace", ·))
    let path := args[1]?.getD "/tmp/ix-claim.json"
    IO.FS.writeFile path package.compress
    IO.eprintln s!"Wrote {path}"
    return
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (← sourcePath "fixtures/nat-add-comm.json")))
  let fixture : Fixture ← IO.ofExcept (fromJson? json)
  unless fixture.format == "ixon-v4" do throw (IO.userError "unsupported fixture format")
  IO.eprintln "Building typed hints..."
  let hints := fixture.hints
  IO.eprintln s!"Preparing {hints.size} hint entries..."
  let hints ← IO.ofExcept (exported.prepareHints hints)
  IO.eprintln "Encoding bytecode..."
  let program ← IO.ofExcept (exported.toJson modulus ZMod.val)
  let trace ← if mode == "export-trace" then do
    IO.eprintln "Compiling certified circuits and witness population plans..."
    let compiled ← IO.ofExcept (prepared.compileOptimized {})
    pure <| some (← IO.ofExcept (Trace.exportJson modulus ZMod.val compiled.circuit.inlined.program
      compiled.circuit.artifact exported.bytecode))
  else pure none
  let package := Json.mkObj ([("program", program), ("address", toJson fixture.address),
    ("invalid_address", toJson fixture.invalidProof.address),
    ("hints", Execution.hintsJson ZMod.val hints)] ++ trace.toList.map ("trace", ·))
  if mode.startsWith "export" then
    IO.eprintln "Writing execution package..."
    let path := args[1]?.getD "/tmp/aiur-ixvm-package.json"
    IO.FS.writeFile path package.compress
    IO.eprintln s!"Wrote {path}"
    return
  IO.eprintln s!"Executing {entry}: {fixture.name} / {fixture.addressHex}"
  runHost package mode

end IxVM.Cli

unsafe def main (args : List String) : IO Unit := IxVM.Cli.main args
