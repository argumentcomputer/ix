/-
  `ix compress derive-vk|setup` for formal aggregate roots. `derive-vk`
  derives the recursive verifying key of a normalization layout without a
  proof. `setup` installs the released Ignition proving parameters and, for
  a layout, the fixed preprocessing the KZG stages read.
-/
module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.FormalAggregate

public section
namespace Ix.Cli.CompressionCmd

/-- The formal aggregation artifact's verifying key. -/
private def aggregationKey (p : Cli.Parsed) : IO ByteArray := do
  return (← FormalAggregate.identity (← FormalAggregate.artifact p) true).key

def runDeriveVk (p : Cli.Parsed) : IO UInt32 := do
  try
    let layoutPath := p.positionalArg! "layout" |>.as! String
    let out := p.positionalArg! "out" |>.as! String
    let layout ← IO.FS.readFile layoutPath
    let vk ← Compression.deriveVk (← aggregationKey p) layout
      (← Compression.cacheDir).toString (p.hasFlag "dev-kzg-srs")
    IO.FS.writeBinFile out vk
    IO.println s!"{out} {Address.blake3 vk}"
    return 0
  catch e =>
    IO.eprintln s!"compress derive-vk: {e}"
    return 1

def deriveVkCmd : Cli.Cmd := `[Cli|
  "derive-vk" VIA runDeriveVk;
  "Derive, from the formal aggregation artifact, a normalization layout and the inner KZG setup alone, the recursive verifying key every compression of such roots proves to. Prints its path and BLAKE3 digest: the pin `ix verify --compression-vk-blake3` takes. Builds the first and recursive stages' fixed preprocessing, which needs about as much memory and time as their setup."

  FLAGS:
    "dev-kzg-srs"; "Use the known-trapdoor development setup (not production-secure)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."

  ARGS:
    layout : String; "Normalization layout JSON, such as a compression's root/fixed-root.json."
    out : String; "Output verifying key file."
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
    let (vk, layout) ← match (p.flag? "fixed-root").map (·.as! String) with
      | some path => pure (← aggregationKey p, ← IO.FS.readFile path)
      | none => pure (ByteArray.empty, "")
    Compression.prepare vk layout (← Compression.cacheDir).toString
      devKzgSrs (p.hasFlag "plonk")
    return 0
  catch e =>
    IO.eprintln s!"compress setup: {e}"
    return 1

def setupCmd : Cli.Cmd := `[Cli|
  "setup" VIA runSetup;
  "Prepare this machine for compression: download the released BN254 Ignition SRS (4.3 GB, public) into IX_PARAMS_DIR (default ~/.ix/compression/params) if missing and check it against its pin. With --fixed-root, also publish the fixed preprocessing of the first KZG stage and the recursive stage for roots of the formal aggregation artifact normalized to that layout. Present cache entries are only checked."

  FLAGS:
    "dev-kzg-srs"; "Prepare the known-trapdoor development setup instead of Ignition (not production-secure)."
    "fixed-root" : String; "Normalization layout JSON whose KZG stages to prepare, such as a compression's root/fixed-root.json."
    "aiur-artifact" : String; "With --fixed-root: trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "With --fixed-root: trusted formal aggregation artifact; otherwise compile/cache local sources."
    "plonk"; "Also build the PLONK circuit, keys and parameter exports of the bundled recursive key into the PLONK cache."
]

end Ix.Cli.CompressionCmd

end
