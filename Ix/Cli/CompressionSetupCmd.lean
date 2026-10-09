module
public import Cli
public import Ix.Cli.Compression

public section
namespace Ix.Cli.CompressionSetupCmd

def runSetup (p : Cli.Parsed) : IO UInt32 := do
  try
    let srs := (p.flag? "srs").map (·.as! String)
    let dev := p.hasFlag "dev-srs"
    unless srs.isSome != dev do
      throw <| IO.userError "specify exactly one of --srs FILE or --dev-srs"
    let rootLog := ((p.flag? "root-log-height").map (·.as! Nat)).getD 20
    let kzgLog := ((p.flag? "log-height").map (·.as! Nat)).getD 24
    unless 1 ≤ rootLog && rootLog ≤ 26 && 16 ≤ kzgLog && kzgLog ≤ 26 do
      throw <| IO.userError "--root-log-height must be 1–26; --log-height must be 16–26"
    if let some path := srs then
      unless ← (System.FilePath.mk path).pathExists do
        throw <| IO.userError s!"SRS file does not exist: {path}"
    if dev then
      IO.eprintln "Using a known-trapdoor development SRS; proofs are not production-secure."
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    let claim := Aiur.buildClaim backend.aggrIdx (Aggr.pubInput backend.allowed ByteArray.empty) #[]
    let dir ← Compression.directory
    let id ← Compression.setup backend.system dir.toString (srs.getD "") dev
      rootLog.toUInt32 kzgLog.toUInt32 claim.size.toUInt32
    IO.eprintln s!"Local compression configuration ready in {dir}."
    IO.println id
    return 0
  catch e =>
    IO.eprintln s!"compression setup: {e}"
    return 1

end Ix.Cli.CompressionSetupCmd
open Ix.Cli.CompressionSetupCmd in
def compressionSetupCmd : Cli.Cmd := `[Cli|
  setup VIA runSetup;
  "Derive and activate a fixed compression verifier locally, without a certificate or proof."
  FLAGS:
    "srs" : String; "Trusted SRS file in IXKZGS01 format."
    "dev-srs"; "Explicitly use a known-trapdoor development setup; not production-secure."
    "root-log-height" : Nat; "Normalized function/memory trace log-height, 1–26 (default 20). Oversized executions are rejected."
    "log-height" : Nat; "KZG partition log-height, 16–26 (default 24); SRS must cover it."
]

def compressionCmd : Cli.Cmd := `[Cli|
  compression NOOP;
  "Configure proof compression locally."
  SUBCOMMANDS:
    compressionSetupCmd
]
end
