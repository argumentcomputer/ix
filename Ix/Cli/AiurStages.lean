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

/-- Notice printed to stderr before running Aiur compression stages: there is no
bundled release L3 verifying key yet, so verification requires an independently
pinned `ix-l3-verifier-v1` bundle or deployed `IxL3PlonkVerifier.sol`. -/
def l3VerificationNotice : String :=
  "Note: --aiur-stages / run-stages emits an IXL3BN1/IXL3BL1 proof whose two-layer \
  terminal statement is verified off-chain via `ix verify --l3-verifier <bundle> \
  --l3-verifier-blake3 <pin>` and on-chain via IxL3PlonkVerifier.sol (no bundled \
  release L3 verifying key is shipped yet)."

/-- Run the single-process Aiur compression stages on an unpacked `rootDir`
(`root-vk.bin`, `root-claims.bin`, `root-proof.bin`) and return the JSON summary. -/
def runStages (manifest pin rootDir out : String)
    (memoryGb? : Option Nat := none) (cache? : Option String := none)
    (gpuLock : Bool := true) : IO String := do
  IO.eprintln l3VerificationNotice
  let mut options : List (String × Lean.Json) :=
    [("root_dir", .str rootDir), ("out", .str out), ("gpu_lock", .bool gpuLock)]
  if let some gb := memoryGb? then
    options := options ++ [("memory_gb", .num gb)]
  if let some cache := cache? then
    options := options ++ [("cache", .str cache)]
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
  | .ok summary => return summary
  | .error e => throw e

private def manifestCurve (manifestPath : String) : IO String := do
  let text ← IO.FS.readFile manifestPath
  let json ← IO.ofExcept (Lean.Json.parse text)
  match json.getObjVal? "curve" with
  | .error _ | .ok .null => return "bn254"
  | .ok (.str "bn254") => return "bn254"
  | .ok (.str "bls12-381") => return "bls12-381"
  | .ok other =>
      throw (IO.userError s!"unknown stages manifest curve {other.compress}: expected bn254 or bls12-381")

def runCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    let flag (name : String) : IO String := do
      let some f := p.flag? name | throw (IO.userError s!"--{name} is required")
      return f.as! String
    let manifest ← flag "stages"
    let pin ← flag "stages-blake3"
    let summary ← runStages manifest pin (← flag "root-dir") (← flag "out")
      ((p.flag? "memory-gb").map (·.as! Nat))
      ((p.flag? "cache").map (·.as! String))
      (!(p.hasFlag "no-gpu-lock"))
    IO.println summary
    return 0
  catch e =>
    IO.eprintln s!"compress run-stages: {e}"
    return 1

/-- Compress a stored or file-backed aggregate `Ixon.Proof` using the single-process
Aiur compression stages manifest (`--aiur-stages` / `--aiur-stages-blake3`), running
full `ClaimPolicy.admit` kernel admission before unpacking `root/` and proving. -/
def runOnProof (p : Cli.Parsed) : IO UInt32 := do
  try
    let req (name : String) : IO String := do
      let some f := p.flag? name | throw (IO.userError s!"--aiur-stages requires --{name}")
      return f.as! String
    let manifest ← req "aiur-stages"
    let pin ← req "aiur-stages-blake3"
    for flag in #["stark-128", "stark-128-zk", "compact", "groth16", "dev-kzg-srs", "dev-final-srs"] do
      if p.hasFlag flag then
        throw (IO.userError s!"--{flag} cannot be combined with --aiur-stages")
    if Ix.Cli.AiurCompression.selected p then
      throw (IO.userError "--aiur-stages cannot be combined with --aiur-gl or --aiur-chain")
    let curve ← manifestCurve manifest
    if p.hasFlag "curve" || p.hasFlag "bn254" || p.hasFlag "bls12-381" then
      let requested ← IO.ofExcept (Ix.Cli.CompressCmd.resolveCurve p)
      if requested != curve then
        throw (IO.userError s!"requested curve {requested} differs from --aiur-stages manifest curve {curve}")
    let input := p.positionalArg! "proof" |>.as! String
    let (addr, wrapper) ← Ix.Cli.Compression.readProofInput input
    Ix.Cli.CompressCmd.checkInput wrapper false
    unless Ix.Cli.FormalCompress.isFormalRoot wrapper.proof do
      throw (IO.userError "compression requires a formal aggregate root (IXAGGR2); legacy Aiur roots are retired")
    let statementText ← Ix.Cli.ClaimPolicy.admit p wrapper.claim (route := .aggregate)
    IO.eprintln s!"Compressing a proof of claim {Address.blake3 (Ix.Claim.ser wrapper.claim)} with Aiur stages ({curve}):\n{statementText}"
    let ctx ← Ix.Cli.FormalAggregate.context p
    let statement := Ix.Cli.FormalAggregate.statementBytes ctx.toKeys wrapper.claim
    let vk ← match (p.flag? "root-vk").map (·.as! String) with
      | some path => IO.FS.readBinFile path
      | none => pure ctx.aggr.key
    let raw ← Ix.Cli.FormalAggregate.rawProof .aggr wrapper.proof
    Ix.Cli.Compression.checkClaim (Ix.Claim.ser wrapper.claim) statement
    let out ← Ix.Cli.CompressCmd.outputDirectory
      { out := (p.flag? "out").map (·.as! String) } addr
    if p.hasFlag "fresh" then
      Ix.Cli.AiurCompression.resetOutput out
    let rootDir : System.FilePath := System.FilePath.mk out / "root"
    IO.FS.createDirAll rootDir
    IO.FS.writeBinFile (rootDir / "root-vk.bin") vk
    IO.FS.writeBinFile (rootDir / "root-claims.bin") statement
    IO.FS.writeBinFile (rootDir / "root-proof.bin") raw
    Ix.Cli.Compression.releaseGpuMemory
    let summary ← runStages manifest pin rootDir.toString out
      ((p.flag? "memory-gb").map (·.as! Nat))
      ((p.flag? "cache").map (·.as! String))
      (!(p.hasFlag "no-gpu-lock"))
    let envelopePath : System.FilePath := System.FilePath.mk out / "l3-proof.bin"
    if ← envelopePath.pathExists then
      let l3ProofBytes ← IO.FS.readBinFile envelopePath
      unless Ix.Cli.FormalAggregate.isL3Proof l3ProofBytes do
        throw (IO.userError s!"{envelopePath} does not carry an IXL3 proof envelope")
      let compressed : Ixon.Proof := { claim := wrapper.claim, proof := l3ProofBytes }
      let serialized := Ixon.Proof.ser compressed
      let artifactPath : System.FilePath := System.FilePath.mk out / "proof.ixon-proof"
      IO.FS.writeBinFile artifactPath serialized
      let proofAddr ← StoreIO.toIO (Store.write serialized)
      IO.eprintln s!"Wrote verifiable L3 Ixon.Proof to {artifactPath} (store address {proofAddr})."
      if let .ok json := Lean.Json.parse summary then
        if let .ok l3 := json.getObjVal? "l3" then
          if let (.ok bPath, .ok bPin) :=
              (l3.getObjValAs? String "verifier_bundle_path",
               l3.getObjValAs? String "verifier_bundle_blake3") then
            IO.eprintln s!"Verify with: ix verify {proofAddr} --l3-verifier {bPath} --l3-verifier-blake3 {bPin}"
      IO.println (toString proofAddr)
    else
      IO.println summary
    return 0
  catch e =>
    IO.eprintln s!"compress: {e}"
    return 1

def runStagesCmd : Cli.Cmd := `[Cli|
  "run-stages" VIA runCmd;
  "Run the compression stages of a manifest (ix-aiur-stages-v1) on a raw root in this process: every stage proves and verifies here, the Lean exporters run here, intermediate proofs pass in memory, and the terminal PLONK stage emits a self-checked IXL3BN1/IXL3BL1 envelope and ix-l3-verifier-v1 bundle."
  FLAGS:
    "stages" : String; "Stages manifest (ix-aiur-stages-v1)."
    "stages-blake3" : String; "Independent BLAKE3 pin for the exact manifest bytes."
    "root-dir" : String; "Directory with root-vk.bin, root-claims.bin and root-proof.bin; the root key must match the manifest's pin."
    "out" : String; "Run directory: stage outputs and reports, checks.json, stages.json."
    "memory-gb" : Nat; "Memory budget the stages reserve from (default: the manifest's memory_gb)."
    "cache" : String; "Export cache directory (default: the manifest's cache)."
    "no-gpu-lock"; "Let stages use the GPU concurrently instead of serializing GPU sections."
]

private def runCompressOrStages (p : Cli.Parsed) : IO UInt32 :=
  if p.hasFlag "aiur-stages" || p.hasFlag "aiur-stages-blake3" then
    runOnProof p
  else
    Ix.Cli.CompressCmd.runCompressCmd p

/-- `compress` with `--aiur-stages` support and the `run-stages` subcommand. -/
def compressCmd : Cli.Cmd :=
  let c := _root_.compressCmd
  .init c.meta runCompressOrStages (c.subCmds.push runStagesCmd) c.extension?

end Ix.Cli.AiurStages
