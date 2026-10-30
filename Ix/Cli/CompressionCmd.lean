/-
  `ix compress layout|normalize|setup`. `layout` executes a root wrap
  of each given aggregate proof and sizes one fixed layout that holds all of
  them; `normalize` proves a root's wrap in that layout and writes the FRI
  worker's root input. Every root normalized to one layout compresses under
  the same FRI verifier. `setup` installs the released Ignition proving
  parameters and the fixed preprocessing every stage reads.
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

/-- The recursive KZG compressed-proof tag `compress` prefixes its packet with. -/
private def recursiveProofTag : ByteArray := ⟨#[0x49, 0x58, 0x42, 0x4e, 0, 0, 0, 1]⟩

/-- A certificate's claim and compressed proof. A directory is a stage
directory holding `kzg/packet.bin` (a `final-kzg` or `merge` stage) or a
compression output holding one under `final-kzg/` or `merge/`; its claim is
`claimFile`, else the directory's `claim.bin`. Any other input is a
compressed Ixon.Proof file or content address. -/
private def loadCertificate (input : String) (claimFile : Option String) :
    IO (ByteArray × ByteArray) := do
  let dir : System.FilePath := input
  if ← dir.isDir then
    let mut packet? := none
    for stage in [dir, dir / "final-kzg", dir / "merge"] do
      if packet?.isNone && (← (stage / "kzg" / "packet.bin").pathExists) then
        packet? := some (stage / "kzg" / "packet.bin")
    let some packet := packet?
      | throw <| IO.userError s!"{input} holds no kzg/packet.bin"
    let claimPath := claimFile.getD (dir / "claim.bin").toString
    unless ← System.FilePath.pathExists claimPath do
      throw <| IO.userError s!"{input} has no claim.bin; pass its claim file"
    return (← IO.FS.readBinFile claimPath, recursiveProofTag ++ (← IO.FS.readBinFile packet))
  let (addr, wrapper) ← Compression.readProofInput input
  unless Compression.isCompressed wrapper.proof do
    throw <| IO.userError s!"proof {addr} is not compressed"
  return (Ix.Claim.ser wrapper.claim, wrapper.proof)

/-- Merge `inputs` (kind 0 joins two, kind 1 imports one), store the merged
proof under its claim and print its address. -/
private def runMerge (p : Cli.Parsed) (kind : UInt8)
    (inputs : List (String × Option String)) : IO Unit := do
  let certificates ← inputs.mapM fun (input, claim) => loadCertificate input claim
  let empty : ByteArray × ByteArray := (ByteArray.empty, ByteArray.empty)
  let (leftClaim, leftProof) := certificates.headD empty
  let (rightClaim, rightProof) := (certificates.drop 1).headD empty
  let claim ← IO.ofExcept <| Ix.Claim.de
    (← Compression.mergedClaim kind leftClaim rightClaim)
  let out ← match (p.flag? "out").map (·.as! String) with
    | some path => pure path
    | none =>
      let dir := (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"
      let label := if kind == 0 then "join" else "import"
      pure (dir / s!"{label}-{Address.blake3 (leftProof ++ rightProof)}").toString
  let keys := ((p.flag? "merge-keys").map (·.as! String)).getD ""
  IO.eprintln s!"Merging into {claim} in {out}."
  let proof ← Compression.merge kind leftClaim leftProof rightClaim rightProof
    keys out (← Compression.cacheDir).toString (p.hasFlag "dev-kzg-srs")
    (p.hasFlag "fresh")
  let merged : Ixon.Proof := { claim, proof }
  IO.println (toString (← StoreIO.toIO (Store.write (Ixon.Proof.ser merged))))

def runJoin (p : Cli.Parsed) : IO UInt32 := do
  try
    let claim (flag : String) := (p.flag? flag).map (·.as! String)
    runMerge p 0 [
      (p.positionalArg! "left" |>.as! String, claim "left-claim"),
      (p.positionalArg! "right" |>.as! String, claim "right-claim")]
    return 0
  catch e =>
    IO.eprintln s!"compress join: {e}"
    return 1

def runImport (p : Cli.Parsed) : IO UInt32 := do
  try
    runMerge p 1 [(p.positionalArg! "proof" |>.as! String,
      (p.flag? "claim").map (·.as! String))]
    return 0
  catch e =>
    IO.eprintln s!"compress import: {e}"
    return 1

def joinCmd : Cli.Cmd := `[Cli|
  "join" VIA runJoin;
  "Join a closed compressed proof (left) with one that assumes nothing or the left root (right) into one merged proof of their Merkle node; print its address."

  FLAGS:
    "out" : String; "Output directory for the merge stage (default ~/.ix/compression/join-<inputs>). Rerunning with it reuses the stage while its proof verifies."
    "fresh"; "Prove the merge stage again even if a verified one exists."
    "merge-keys" : String; "Development key directory (recursive-vk.bin, statement-prefix.txt and the five family keys) instead of the bundled merge family."
    "dev-kzg-srs"; "Use local development KZG parameters."
    "left-claim" : String; "Claim file of a left stage directory without claim.bin."
    "right-claim" : String; "Claim file of a right stage directory without claim.bin."

  ARGS:
    left : String; "Compressed Ixon.Proof file or content address, or a stage or compression output directory."
    right : String; "Compressed Ixon.Proof file or content address, or a stage or compression output directory."
]

def importCmd : Cli.Cmd := `[Cli|
  "import" VIA runImport;
  "Carry a version 0.1 compressed proof into this version's merge family as a merged proof of the same claim; print its address."

  FLAGS:
    "out" : String; "Output directory for the merge stage (default ~/.ix/compression/import-<input>). Rerunning with it reuses the stage while its proof verifies."
    "fresh"; "Prove the merge stage again even if a verified one exists."
    "merge-keys" : String; "Development key directory (recursive-vk.bin, statement-prefix.txt and the five family keys) instead of the bundled merge family."
    "dev-kzg-srs"; "Use local development KZG parameters."
    "claim" : String; "Claim file of a stage directory without claim.bin."

  ARGS:
    proof : String; "Version 0.1 compressed Ixon.Proof file or content address, or its stage or compression output directory."
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

private def backendVk : IO ByteArray := do
  return (← backend).system.vkBytes

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
    Compression.prepare (← backendVk) (← Compression.cacheDir).toString
      devKzgSrs (p.hasFlag "plonk")
    return 0
  catch e =>
    IO.eprintln s!"compress setup: {e}"
    return 1

def setupCmd : Cli.Cmd := `[Cli|
  "setup" VIA runSetup;
  "Prepare this machine for compression and merges of the bundled version: download the released BN254 Ignition SRS (4.3 GB, public) into IX_PARAMS_DIR (default ~/.ix/compression/params) if missing and check it against its pin, then publish the fixed preprocessing of the first KZG stage, the recursive stage and every merge family member to the fixed cache, checking each derived key against its bundled pin. Present cache entries are only checked."

  FLAGS:
    "dev-kzg-srs"; "Prepare the known-trapdoor development setup instead of Ignition (not production-secure)."
    "plonk"; "Also build the PLONK circuit, keys and parameter exports into the PLONK cache."
]

end Ix.Cli.CompressionCmd

end
