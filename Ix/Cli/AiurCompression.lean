module
public import Cli
public import Ix.Cli.Compression

public section
namespace Ix.Cli.AiurCompression

/-- The key pin authorizes the compiled relation; the artifact pin fixes the
entry schema. Both must come from the same trusted key preparation. Verification
does not need proving powers. -/
structure GlOptions where
  artifact : String
  artifactPin : String
  key : String
  keyPin : String
  maxLogHeight : UInt8 := 24
  quotientDegree : UInt32 := 2

inductive Options where
  | gl (options : GlOptions)
  | chain (manifest pin : String)

def Options.label : Options → String
  | .gl _ => "Aiur CompressGL"
  | .chain .. => "Aiur GL-to-BN chain"

private def glFlags : Array String :=
  #["aiur-gl", "aiur-gl-blake3", "aiur-kzg-key", "aiur-kzg-key-blake3",
    "aiur-max-log-height", "aiur-quotient-degree"]

private def required (p : Cli.Parsed) (name : String) : IO String := do
  let some flag := p.flag? name | throw (IO.userError s!"Aiur compression requires --{name}")
  return flag.as! String

def selected (p : Cli.Parsed) : Bool :=
  p.hasFlag "aiur-chain" || p.hasFlag "aiur-chain-blake3" || glFlags.any p.hasFlag

def options (p : Cli.Parsed) : IO Options := do
  if p.hasFlag "aiur-chain" || p.hasFlag "aiur-chain-blake3" then
    if glFlags.any p.hasFlag then
      throw (IO.userError "--aiur-chain cannot be combined with individual Aiur GL flags")
    return .chain (← required p "aiur-chain") (← required p "aiur-chain-blake3")
  let height := ((p.flag? "aiur-max-log-height").map (·.as! Nat)).getD 24
  let quotient := ((p.flag? "aiur-quotient-degree").map (·.as! Nat)).getD 2
  unless height > 0 && height ≤ 28 && quotient > 0 && quotient ≤ 2^28 do
    throw (IO.userError "invalid Aiur trace/quotient capacity")
  return .gl {
    artifact := ← required p "aiur-gl"
    artifactPin := ← required p "aiur-gl-blake3"
    key := ← required p "aiur-kzg-key"
    keyPin := ← required p "aiur-kzg-key-blake3"
    maxLogHeight := height.toUInt8
    quotientDegree := quotient.toUInt32 }

def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXACG".toUTF8 || proof.extract 0 6 == "IXAUCH".toUTF8

@[extern "rs_aiur_compression_preflight"]
opaque preflight (artifact artifactPin key keyPin : @& String) (maxLog : UInt8) (quotient : UInt32)
  (development : Bool) : IO String

@[extern "rs_aiur_compression_prepare_key"]
opaque prepareKey (artifact artifactPin out : @& String) (maxLog : UInt8) (quotient : UInt32)
  (development : Bool) : IO String

@[extern "rs_aiur_compression_run"]
opaque run (vk raw claim rows : @& ByteArray) (artifact artifactPin key keyPin out : @& String)
  (maxLog : UInt8) (quotient : UInt32) (development fresh : Bool) : IO ByteArray

@[extern "rs_aiur_compression_verify"]
opaque verify (proof vk claim rows : @& ByteArray) (artifact artifactPin key keyPin : @& String)
  (maxLog : UInt8) (quotient : UInt32) (development : Bool) : IO String

@[extern "rs_aiur_chain_preflight"]
opaque chainPreflight (manifest pin : @& String) (development : Bool) : IO String

@[extern "rs_aiur_chain_prepare"]
opaque chainPrepare (template out : @& String) (development : Bool) : IO String

@[extern "rs_aiur_chain_run"]
opaque chainRun (vk raw claim rows : @& ByteArray) (manifest pin out : @& String)
  (development fresh : Bool) : IO ByteArray

@[extern "rs_aiur_chain_verify"]
opaque chainVerify (proof vk claim rows : @& ByteArray) (manifest pin : @& String)
  (development : Bool) : IO String

@[extern "rs_aiur_compression_reset_output"]
opaque resetOutput (out : @& String) : IO Unit

def preflightOptions (options : Options) (development : Bool) : IO String :=
  match options with
  | .gl opts => preflight opts.artifact opts.artifactPin opts.key opts.keyPin
      opts.maxLogHeight opts.quotientDegree development
  | .chain manifest pin => chainPreflight manifest pin development

def runOptions (options : Options) (vk raw claim rows : ByteArray) (out : String)
    (development fresh : Bool) : IO ByteArray :=
  match options with
  | .gl opts => run vk raw claim rows opts.artifact opts.artifactPin opts.key opts.keyPin out
      opts.maxLogHeight opts.quotientDegree development fresh
  | .chain manifest pin => chainRun vk raw claim rows manifest pin out development fresh

def verifyProof (opts : Options) (addr : Address) (wrapper : Ixon.Proof)
    (vk rows : ByteArray) (development : Bool) : IO Unit := do
  let claim := Ix.Claim.ser wrapper.claim
  let setup ← match opts with
    | .gl gl =>
      verify wrapper.proof vk claim rows gl.artifact gl.artifactPin gl.key gl.keyPin
        gl.maxLogHeight gl.quotientDegree development
    | .chain manifest pin => chainVerify wrapper.proof vk claim rows manifest pin development
  if setup == "development" then
    IO.println s!"development-only: algebraic checks passed for {opts.label} proof {addr}, claim {Address.blake3 claim}; the independently pinned KZG setup is not admitted for production verification"
  else
    IO.println s!"ok: {opts.label} proof {addr} verifies claim {Address.blake3 claim} under the independently pinned {setup} KZG verifier"

def runPrepareKey (p : Cli.Parsed) : IO UInt32 := do
  try
    let height := ((p.flag? "max-log-height").map (·.as! Nat)).getD 24
    let quotient := ((p.flag? "quotient-degree").map (·.as! Nat)).getD 2
    unless height > 0 && height ≤ 28 && quotient > 0 && quotient ≤ 2^28 do
      throw (IO.userError "invalid Aiur trace/quotient capacity")
    let digest ← prepareKey (p.positionalArg! "artifact" |>.as! String)
      (← required p "artifact-blake3") (← required p "out") height.toUInt8 quotient.toUInt32 (p.hasFlag "dev-srs")
    IO.println digest
    return 0
  catch error =>
    IO.eprintln s!"compress aiur-key: {error}"
    return 1

def keyCmd : Cli.Cmd := `[Cli|
  "aiur-key" VIA runPrepareKey;
  "Derive an Aiur CompressGL verifier from an independently trusted compiler artifact and setup; print its BLAKE3 pin."
  FLAGS:
    "artifact-blake3" : String; "Independent BLAKE3 pin for the compiler artifact."
    "out" : String; "New output file for the verifying key; existing files are refused."
    "max-log-height" : Nat; "Fixed public trace-height bound (default 24); independent of each execution."
    "quotient-degree" : Nat; "Fixed public quotient-degree budget (default 2)."
    "dev-srs"; "Explicitly select known-trapdoor development parameters."
  ARGS:
    artifact : String; "Trusted wide CompressGL compiler artifact."
]

def runCheck (p : Cli.Parsed) : IO UInt32 := do
  try
    let opts ← options p
    IO.println (← preflightOptions opts (p.hasFlag "dev-srs"))
    return 0
  catch error =>
    IO.eprintln s!"compress aiur-check: {error}"
    return 1

def checkCmd : Cli.Cmd := `[Cli|
  "aiur-check" VIA runCheck;
  "Check that a pinned Aiur compiler artifact, verifier key, setup and public capacity agree."
  FLAGS:
    "aiur-chain" : String; "Trusted GL-to-BN chain manifest with artifact/key pins, capacities and resource limits."
    "aiur-chain-blake3" : String; "Independent BLAKE3 pin for the exact --aiur-chain manifest bytes."
    "aiur-gl" : String; "Trusted CompressGL compiler artifact."
    "aiur-gl-blake3" : String; "Independent BLAKE3 pin for --aiur-gl."
    "aiur-kzg-key" : String; "Independently trusted CompressGL KZG verifier key."
    "aiur-kzg-key-blake3" : String; "Independent BLAKE3 pin for --aiur-kzg-key."
    "aiur-max-log-height" : Nat; "Fixed public Aiur trace-height bound (default 24)."
    "aiur-quotient-degree" : Nat; "Fixed public Aiur quotient-degree budget (default 2)."
    "dev-srs"; "Explicitly select known-trapdoor development parameters."
]

def runPrepareChain (p : Cli.Parsed) : IO UInt32 := do
  try
    let digest ← chainPrepare (p.positionalArg! "template" |>.as! String)
      (← required p "out") (p.hasFlag "dev-srs")
    IO.println digest
    return 0
  catch error =>
    IO.eprintln s!"compress aiur-chain-key: {error}"
    return 1

def chainKeyCmd : Cli.Cmd := `[Cli|
  "aiur-chain-key" VIA runPrepareChain;
  "Derive both Aiur chain keys from pinned compiler artifacts and emit a candidate trusted manifest; print its BLAKE3 digest."
  FLAGS:
    "out" : String; "New directory for GL/BN keys and manifest.json; existing directories are refused."
    "dev-srs"; "Explicitly select known-trapdoor development parameters."
  ARGS:
    template : String; "Chain JSON template with artifact pins, capacities, stage count and resource limits; omit key paths and pins."
]

end Ix.Cli.AiurCompression
end
