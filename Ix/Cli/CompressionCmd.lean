/-
  `ix compress layout|normalize|setup` for formal aggregate roots. `layout`
  sizes one fixed layout that holds the root wrap of each given root, from
  each root's trace heights and its wrap's rows; `normalize` proves a root's
  wrap in that layout and writes the FRI worker's root input. Every root
  normalized to one layout compresses under the same FRI verifier. `setup`
  installs the released Ignition proving parameters and the fixed
  preprocessing every stage reads.
-/
module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.FormalCompress

public section
namespace Ix.Cli.CompressionCmd

private def loadRoot (input : String) : IO (Address × Ixon.Proof) := do
  let (addr, wrapper) ← Compression.readProofInput input
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError s!"proof {addr} is already compressed"
  let .checkEnv .. := wrapper.claim
    | throw <| IO.userError s!"proof {addr} is not an aggregate CheckEnv proof"
  unless FormalCompress.isFormalRoot wrapper.proof do
    throw <| IO.userError s!"proof {addr} is not a formal aggregate root (IXAGGR2); legacy Aiur roots are retired"
  return (addr, wrapper)

/-- The layout holding each root's: the largest height per circuit and every
memory circuit any root closes. -/
private def combinedLayout (p : Cli.Parsed) (roots : List (Address × Ixon.Proof))
    (headroom : Nat) : IO String := do
  let ctx ← FormalAggregate.context p
  let mut heights : Array Nat := #[]
  let mut memory : Array (Nat × Nat) := #[]
  let mut claimLen : Option Nat := none
  for (addr, wrapper) in roots do
    FormalAggregate.verifyWrapper ctx .aggr wrapper
    IO.eprintln s!"Sizing the root wrap of {addr}."
    let json ← IO.ofExcept (Lean.Json.parse (← FormalCompress.layout ctx wrapper headroom))
    let logs ← IO.ofExcept (json.getObjValAs? (Array Nat) "log_heights")
    let traces ← IO.ofExcept (json.getObjValAs? (Array (Nat × Nat)) "memory_traces")
    let len ← IO.ofExcept (json.getObjValAs? Nat "claim_len")
    if heights.isEmpty then heights := logs
    else if heights.size != logs.size then
      throw <| IO.userError "roots of different aggregation artifacts"
    else heights := heights.zipWith max logs
    for t in traces do
      unless memory.contains t do memory := memory.push t
    if claimLen.any (· != len) then
      throw <| IO.userError "roots with different claim lengths"
    claimLen := some len
  let some len := claimLen | throw <| IO.userError "no roots to size"
  return (Lean.Json.mkObj [
    ("format", "ix-fixed-root-layout-v1"),
    ("log_heights", Lean.toJson heights),
    ("memory_traces", Lean.toJson (memory.qsort (·.1 < ·.1))),
    ("claim_len", Lean.toJson len)]).pretty

def runLayout (p : Cli.Parsed) : IO UInt32 := do
  try
    let out := p.positionalArg! "out" |>.as! String
    let proofs := (p.variableArgsAs! String).toList
    if proofs.isEmpty then
      throw <| IO.userError "expected at least one aggregate proof file or address"
    let headroom := ((p.flag? "headroom").map (·.as! Nat)).getD 0
    IO.FS.writeFile out (← combinedLayout p (← proofs.mapM loadRoot) headroom)
    IO.println out
    return 0
  catch e =>
    IO.eprintln s!"compress layout: {e}"
    return 1

def runNormalize (p : Cli.Parsed) : IO UInt32 := do
  try
    let (addr, wrapper) ← loadRoot (p.positionalArg! "proof" |>.as! String)
    let layoutPath := p.positionalArg! "layout" |>.as! String
    let out := p.positionalArg! "out" |>.as! String
    let layout ← IO.FS.readFile layoutPath
    let ctx ← FormalAggregate.context p
    IO.eprintln s!"Normalizing aggregate root {addr} to {layoutPath}."
    let root ← FormalCompress.normalize p ctx wrapper layout
    let claim := Ix.Claim.ser wrapper.claim
    Compression.writeRoot ctx.aggr.key root claim
      (FormalAggregate.statementBytes ctx wrapper.claim) layout out
    IO.println out
    return 0
  catch e =>
    IO.eprintln s!"compress normalize: {e}"
    return 1

def layoutCmd : Cli.Cmd := `[Cli|
  layout VIA runLayout;
  "Size one fixed root layout that holds the root wrap of every given formal aggregate root, from the roots' trace heights and the rows each wrap fills."

  FLAGS:
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    headroom : Nat; "Extra doublings of every circuit's height beyond what the largest root and its wrap need (default 0)."

  ARGS:
    out : String; "Output layout JSON file."
    ...proofs : String; "Aggregate Ixon.Proof files or content addresses in the ix store."
]

def normalizeCmd : Cli.Cmd := `[Cli|
  normalize VIA runNormalize;
  "Prove a root's wrap in a fixed layout and write the FRI worker's root input directory."

  FLAGS:
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "max-ram" : Nat; "RAM budget in GiB for proving the normalized root (default 85% of available memory)."
    "gpu-device" : Nat; "Prove the normalized root on this CUDA device (requires a CUDA build)."

  ARGS:
    proof : String; "Aggregate Ixon.Proof file or content address in the ix store."
    layout : String; "Layout JSON from `ix compress layout`."
    out : String; "Empty output directory for root-vk.bin, root-proof.bin, root-claims.bin and fixed-root.json."
]

/-- Download `url` to `path` through a `.part` file, resuming a partial one. -/
private def download (url : String) (path : System.FilePath) : IO Unit := do
  let part := path.toString ++ ".part"
  let status ← (← IO.Process.spawn {
    cmd := "curl"
    args := #["-fL", "--retry", "5", "--retry-all-errors", "-C", "-",
              "--progress-bar", "-o", part, url]
    stdin := .null, stdout := .inherit, stderr := .inherit
  }).wait
  if status != 0 then
    throw <| IO.userError s!"curl exited with {status} downloading {url}"
  IO.FS.rename part path

/-- The published gnark SRS selected during release preparation. -/
private def ignitionRelease := "bn254-ignition-main-197"
private def ignitionUrl :=
  "https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/bn254/ignition/main-197"
private def ignitionFiles := #["srs.bin"]

/-- `IX_PARAMS_DIR`, else `~/.ix/compression/params`. -/
private def parametersDir : IO System.FilePath := do
  if let some dir ← IO.getEnv "IX_PARAMS_DIR" then return dir
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression/params"

private def backendVk (p : Cli.Parsed) : IO ByteArray := do
  return (← FormalAggregate.aggrIdentity p (← FormalProver.Registry.new)).2.key

def runSetup (p : Cli.Parsed) : IO UInt32 := do
  try
    let devKzgSrs := p.hasFlag "dev-kzg-srs"
    if devKzgSrs then
      IO.eprintln "parameters: development setup, nothing to download"
    else if (← IO.getEnv "IX_KZG_SRS").isSome then
      IO.eprintln "parameters: IX_KZG_SRS is set and replaces the release SRS"
    else
      let target := (← parametersDir) / ignitionRelease
      IO.FS.createDirAll target
      for file in ignitionFiles do
        let path := target / file
        if ← path.pathExists then
          IO.eprintln s!"parameters: {path} present"
        else
          IO.eprintln s!"parameters: downloading {ignitionUrl}/{file}"
          download s!"{ignitionUrl}/{file}" path
    Compression.prepare (← backendVk p) (← Compression.cacheDir).toString
      devKzgSrs (p.hasFlag "plonk")
    return 0
  catch e =>
    IO.eprintln s!"compress setup: {e}"
    return 1

def setupCmd : Cli.Cmd := `[Cli|
  "setup" VIA runSetup;
  "Prepare this machine for compression of the bundled version: download the released BN254 Ignition SRS (4.3 GB, public) into IX_PARAMS_DIR (default ~/.ix/compression/params) if missing and check it against its pin, then publish the fixed preprocessing of the first KZG stage and the recursive stage to the fixed cache, checking each derived key against its bundled pin. Present cache entries are only checked."

  FLAGS:
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "dev-kzg-srs"; "Prepare the known-trapdoor development setup instead of Ignition (not production-secure)."
    "plonk"; "Also build the PLONK circuit, keys and parameter exports into the PLONK cache."
]

end Ix.Cli.CompressionCmd

end
