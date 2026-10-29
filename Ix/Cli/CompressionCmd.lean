/-
  `ix compress layout|normalize|fetch-params`. `layout` executes a root wrap
  of each given aggregate proof and sizes one fixed layout that holds all of
  them; `normalize` proves a root's wrap in that layout and writes the FRI
  worker's root input. Every root normalized to one layout compresses under
  the same FRI verifier. `fetch-params` installs the pinned Ignition proving
  parameters.
-/
module
public import Cli
public import Ix.Cli.Compression
public import Ix.Aggr.Backend

public section
namespace Ix.Cli.CompressionCmd

private def loadRoot (input : String) : IO (Address × Ixon.Proof) := do
  let (addr, wrapper) ← Compression.readProofInput input
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError s!"proof {addr} is already compressed"
  let .checkEnv _ _ := wrapper.claim
    | throw <| IO.userError s!"proof {addr} is not an aggregate CheckEnv proof"
  return (addr, wrapper)

private def backend : IO Aggr.VerificationBackend := do
  IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)

def runLayout (p : Cli.Parsed) : IO UInt32 := do
  try
    let out := p.positionalArg! "out" |>.as! String
    let proofs := (p.variableArgsAs! String).toList
    if proofs.isEmpty then
      throw <| IO.userError "expected at least one aggregate proof file or address"
    let headroom := ((p.flag? "headroom").map (·.as! Nat)).getD 0
    let backend ← backend
    let mut rows := #[]
    let mut claimLen := 0
    for hex in proofs do
      let (addr, wrapper) ← loadRoot hex
      IO.eprintln s!"Executing the root wrap of {addr}."
      rows := rows.push (← Compression.rootRows backend.system backend.aggrIdx
        backend.allowed backend.ixvmVk (Ix.Claim.ser wrapper.claim) wrapper.proof)
      claimLen := (Aggr.aggregateOuterClaim backend.allowed backend.aggrIdx wrapper.claim).size
    let layout ← Compression.rootLayout backend.system
      ("[" ++ ",".intercalate rows.toList ++ "]") headroom.toUInt32 claimLen.toUInt32
    IO.FS.writeFile out layout
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
    let backend ← backend
    IO.eprintln s!"Normalizing aggregate root {addr} to {layoutPath}."
    let root ← Compression.normalize backend wrapper layout
    let claim := Ix.Claim.ser wrapper.claim
    Compression.writeRoot backend.system.vkBytes root claim
      (Compression.statementBytes backend wrapper.claim) layout out
    IO.println out
    return 0
  catch e =>
    IO.eprintln s!"compress normalize: {e}"
    return 1

def layoutCmd : Cli.Cmd := `[Cli|
  layout VIA runLayout;
  "Size one fixed root layout that holds the root wrap of every given aggregate proof."

  FLAGS:
    headroom : Nat; "Extra doublings of every circuit's height beyond the largest execution (default 0)."

  ARGS:
    out : String; "Output layout JSON file."
    ...proofs : String; "Aggregate Ixon.Proof files or content addresses in the ix store."
]

def normalizeCmd : Cli.Cmd := `[Cli|
  normalize VIA runNormalize;
  "Prove a root's wrap in a fixed layout and write the FRI worker's root input directory."

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

/-- The published Ignition release: its directory name under the parameters
directory, base URL and files. The pins that authenticate the files live with
the setup policy in `ix-proof-compression`; this mirrors only their names. -/
private def ignitionRelease := "bn254-ignition-main-197"
private def ignitionUrl :=
  "https://argument-kzg-params-063002298335-us-east-1-an.s3.us-east-1.amazonaws.com/bn254/ignition/main-197"
private def ignitionFiles := #["admission.json", "ix-prefix-26.bin"]

/-- `IX_PARAMS_DIR`, else `~/.ix/compression/params`. -/
private def parametersDir : IO System.FilePath := do
  if let some dir ← IO.getEnv "IX_PARAMS_DIR" then return dir
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression/params"

def runFetchParams (_ : Cli.Parsed) : IO UInt32 := do
  try
    let target := (← parametersDir) / ignitionRelease
    IO.FS.createDirAll target
    for file in ignitionFiles do
      let path := target / file
      if ← path.pathExists then
        IO.eprintln s!"{path} exists; skipping download."
      else
        IO.eprintln s!"Downloading {ignitionUrl}/{file}."
        download s!"{ignitionUrl}/{file}" path
    if (← IO.getEnv "IX_KZG_IGNITION_CACHE").isSome then
      IO.eprintln "IX_KZG_IGNITION_* is set and takes precedence over the downloaded release."
    IO.eprintln s!"Authenticating the configured parameters."
    IO.eprintln s!"Using {← Compression.describeSetup false false 0}."
    IO.println target
    return 0
  catch e =>
    IO.eprintln s!"compress fetch-params: {e}"
    return 1

def fetchParamsCmd : Cli.Cmd := `[Cli|
  "fetch-params" VIA runFetchParams;
  "Download the pinned BN254 Ignition proving parameters (4.3 GB, public) into IX_PARAMS_DIR (default ~/.ix/compression/params) and authenticate them."
]

end Ix.Cli.CompressionCmd

end
