import Cli
import Lean
import Ix.Cli.CompressCmd
import MultiStark.Export.WideExport
import MultiStark.Export.TilingExport2

/-!
# Compression stages in one process

`ix compress run-stages` runs the compression stages of a manifest
(`ix-aiur-stages-v1`, `docs/aiur-compression-architecture.md` §8): every
stage proves in this process, through `rs_stages_*`. The Lean exporters the
stages need (`wide_export`, `tiling_export2`) run here as well: a task polls
the stages for export requests and runs the exporter of each in its own dedicated task,
writing into the cache entry the request names. Rust never calls Lean.
-/

namespace Ix.Cli.AiurStages

open Lean Elab Term in
/-- The `depHash` of the Lake build trace of module `mod`, read while this
file is compiled, or `""` when there is none (a build without Lake's traces).
The hash covers the module's source, its transitive imports and the
toolchain, so it identifies the exporter code linked into `ix`; this file
is recompiled whenever it changes, since it imports the module. -/
elab "lake_dep_hash% " mod:ident : term => do
  let hash ← (do
      let olean ← findOLean mod.getId
      let trace ← IO.FS.readFile (olean.withExtension "trace")
      let json ← IO.ofExcept (Json.parse trace)
      IO.ofExcept (json.getObjValAs? String "depHash")
    : IO String).toBaseIO
  return mkStrLit (match hash with | .ok h => h | .error _ => "")

/-- The exporters' identities for the export cache: the Lake trace hashes of
the modules that hold them. An `ix` rebuild that leaves them unchanged keeps
its cached exports. -/
def exporterTrace : List (String × String) :=
  [("wide", lake_dep_hash% MultiStark.Export.WideExport),
   ("tiling2", lake_dep_hash% MultiStark.Export.TilingExport2)]

private opaque StagesNonempty : NonemptyType
/-- A Rust-owned compression run: the pinned manifest, the root and the
export cache. -/
def Stages : Type := StagesNonempty.type
instance : Nonempty Stages := StagesNonempty.property

/-- The manifest at `manifest` checked against `pin` (BLAKE3), with
`options` a JSON object: `root_dir`, `out`, optional `memory_gb`,
`gpu_lock`, `cache`, `exporter_id`, `exporter_trace`. -/
@[extern "rs_stages_open"]
opaque Stages.open (manifest pin options : @& String) : IO Stages

/-- The next export request (`id\tkind\tdir`), blocking; empty once the
run has ended. -/
@[extern "rs_stages_next_export"]
opaque Stages.nextExport (stages : @& Stages) : IO String

/-- Answers request `id`; an empty `error` is success. -/
@[extern "rs_stages_complete_export"]
opaque Stages.completeExport (stages : @& Stages) (id : UInt64) (error : @& String) : IO Unit

/-- Proves every stage; returns the run summary (JSON). -/
@[extern "rs_stages_run"]
opaque Stages.run (stages : @& Stages) : IO String

/-- Runs the exporter `kind` on `dir/input.json`, writing `layout.json`,
`fixed.bin` (and `tables.bin`) beside it, with its diagnostics in
`dir/export.log`. -/
def runExport (kind : String) (dir : System.FilePath) : IO Unit := do
  let file (name : String) := (dir / name).toString
  let log ← IO.FS.Handle.mk (dir / "export.log") .write
  let code ← IO.withStderr (IO.FS.Stream.ofHandle log) do
    match kind with
    | "wide" => Aiur.Tiling.WideExport.main [file "input.json", file "layout.json", file "fixed.bin"]
    | "tiling2" =>
        Aiur.Tiling.TilingExport2.main
          [file "input.json", file "layout.json", file "fixed.bin", file "tables.bin"]
    | other => throw (IO.userError s!"unknown exporter {other}")
  unless code == 0 do
    throw (IO.userError s!"{kind} export failed ({code}); see {dir / "export.log"}")

/-- Serves export requests until the run ends. -/
partial def serve (stages : Stages) : IO Unit := do
  let request ← stages.nextExport
  if request.isEmpty then return
  let [id, kind, dir] := request.splitOn "\t"
    | throw (IO.userError s!"malformed export request {request}")
  let id := id.toNat!.toUInt64
  let _ ← IO.asTask (prio := .dedicated) do
    try
      runExport kind dir
      stages.completeExport id ""
    catch e =>
      stages.completeExport id (toString e)
  serve stages

def runCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    let flag (name : String) : IO String := do
      let some f := p.flag? name | throw (IO.userError s!"--{name} is required")
      return f.as! String
    let manifest ← flag "stages"
    let pin ← flag "stages-blake3"
    let mut options : List (String × Lean.Json) :=
      [("root_dir", .str (← flag "root-dir")), ("out", .str (← flag "out")),
       ("gpu_lock", .bool !(p.hasFlag "no-gpu-lock"))]
    if let some gb := p.flag? "memory-gb" then
      options := options ++ [("memory_gb", .num (gb.as! Nat))]
    if let some cache := p.flag? "cache" then
      options := options ++ [("cache", .str (cache.as! String))]
    if exporterTrace.all (!·.2.isEmpty) then
      options := options ++
        [("exporter_trace", Lean.Json.mkObj (exporterTrace.map fun (k, h) => (k, .str h)))]
    let stages ← Stages.open manifest pin (Lean.Json.mkObj options).compress
    let server ← IO.asTask (prio := .dedicated) (serve stages)
    let result ← stages.run.toBaseIO
    match ← IO.wait server with
    | .error e => IO.eprintln s!"compress run-stages: export server: {e}"
    | .ok () => pure ()
    match result with
    | .ok summary =>
        IO.println summary
        return 0
    | .error e =>
        IO.eprintln s!"compress run-stages: {e}"
        return 1
  catch e =>
    IO.eprintln s!"compress run-stages: {e}"
    return 1

def runStagesCmd : Cli.Cmd := `[Cli|
  "run-stages" VIA runCmd;
  "Run the compression stages of a manifest (ix-aiur-stages-v1) on a raw root in this process: every stage proves and verifies here, the Lean exporters run here, and intermediate proofs pass in memory."
  FLAGS:
    "stages" : String; "Stages manifest (ix-aiur-stages-v1)."
    "stages-blake3" : String; "Independent BLAKE3 pin for the exact manifest bytes."
    "root-dir" : String; "Directory with root-vk.bin, root-claims.bin and root-proof.bin; the root key must match the manifest's pin."
    "out" : String; "Run directory: stage outputs and reports, checks.json, stages.json."
    "memory-gb" : Nat; "Memory budget the stages reserve from (default: the manifest's memory_gb)."
    "cache" : String; "Export cache directory (default: the manifest's cache)."
    "no-gpu-lock"; "Let stages use the GPU concurrently instead of serializing GPU sections."
]

/-- `compress` with the `run-stages` subcommand. -/
def compressCmd : Cli.Cmd :=
  let c := _root_.compressCmd
  .init c.meta c.run (c.subCmds.push runStagesCmd) c.extension?

end Ix.Cli.AiurStages
