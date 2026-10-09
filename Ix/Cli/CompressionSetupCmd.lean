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
    let layoutPath := (p.flag? "root-layout").map (·.as! String)
    if layoutPath.isSome && p.hasFlag "root-log-height" then
      throw <| IO.userError "specify either --root-layout or --root-log-height"
    let rootLayout ← match layoutPath with
      | some path => IO.FS.readFile path
      | none => pure ""
    if layoutPath.isSome && rootLayout.trimAscii.toString.isEmpty then
      throw <| IO.userError "root layout file is empty"
    let friLog := ((p.flag? "fri-log-height").map (·.as! Nat)).getD 23
    let kzgLog := ((p.flag? "log-height").map (·.as! Nat)).getD 24
    let recursiveLog := ((p.flag? "recursive-log-height").map (·.as! Nat)).getD kzgLog
    unless 1 ≤ rootLog && rootLog ≤ 26 && 16 ≤ friLog && friLog ≤ 26 && 16 ≤ kzgLog && kzgLog ≤ 26 && 16 ≤ recursiveLog && recursiveLog ≤ 28 do
      throw <| IO.userError "--root-log-height must be 1–26; --fri-log-height and --log-height must be 16–26; --recursive-log-height must be 16–28"
    if let some path := srs then
      unless ← (System.FilePath.mk path).pathExists do
        throw <| IO.userError s!"SRS file does not exist: {path}"
    if dev then
      IO.eprintln "Using a known-trapdoor development SRS; proofs are not production-secure."
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    let claim := Aiur.buildClaim backend.aggrIdx (Aggr.pubInput backend.allowed ByteArray.empty) #[]
    let dir ← Compression.directory
    let id ← Compression.setup backend.system dir.toString (srs.getD "") dev
      rootLayout rootLog.toUInt32 friLog.toUInt32 kzgLog.toUInt32 recursiveLog.toUInt32 claim.size.toUInt32
    IO.eprintln s!"Local compression configuration ready in {dir}."
    IO.println id
    return 0
  catch e =>
    IO.eprintln s!"compression setup: {e}"
    return 1

def runLayout (p : Cli.Parsed) : IO UInt32 := do
  try
    let log := ((p.flag? "root-log-height").map (·.as! Nat)).getD 20
    unless 1 ≤ log && log ≤ 26 do
      throw <| IO.userError "--root-log-height must be 1–26"
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    IO.println (← Compression.layout backend.system log.toUInt32)
    return 0
  catch e =>
    IO.eprintln s!"compression layout: {e}"
    return 1

end Ix.Cli.CompressionSetupCmd
open Ix.Cli.CompressionSetupCmd in
def compressionSetupCmd : Cli.Cmd := `[Cli|
  setup VIA runSetup;
  "Derive and activate a fixed compression verifier locally, without a certificate or proof."
  FLAGS:
    "srs" : String; "Trusted SRS file in IXKZGS01 format."
    "dev-srs"; "Explicitly use a known-trapdoor development setup; not production-secure."
    "root-layout" : String; "JSON per-trace bounds from `ix compression layout`; edit before setup."
    "root-log-height" : Nat; "Uniform fallback function/memory log-height, 1–26 (default 20); exclusive with --root-layout."
    "fri-log-height" : Nat; "FRI partition log-height, 16–26 (default 23); must fit indivisible hash traces."
    "log-height" : Nat; "Intermediate KZG partition log-height, 16–26 (default 24)."
    "recursive-log-height" : Nat; "Final KZG partition log-height, 16–28 (default: --log-height); SRS must cover both KZG stages."
]

open Ix.Cli.CompressionSetupCmd in
def compressionLayoutCmd : Cli.Cmd := `[Cli|
  layout VIA runLayout;
  "Print a JSON trace-bound template for the local aggregate backend. Edit heights before setup; no proof or SRS needed."
  FLAGS:
    "root-log-height" : Nat; "Initial function/memory log-height, 1–26 (default 20)."
]

def compressionCmd : Cli.Cmd := `[Cli|
  compression NOOP;
  "Configure proof compression locally."
  SUBCOMMANDS:
    compressionSetupCmd;
    compressionLayoutCmd
]
end
