module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.CompressionCmd
public import Ix.Aggr.Backend

public section
namespace Ix.Cli.CompressCmd

/-- Selected compression output: the proof system after recursive KZG and the
setup policy. -/
structure Options where
  terminal : UInt8 := 0
  devSrs : Bool := false
  logHeight : Nat := 24
  out : Option String := none
  rootVk : Option String := none
  fixedRoot : Option String := none

/-- `kzg`, `plonk` or `groth16` (`dev-groth16` allows development Groth16 keys). -/
def terminalOf : String → Except String UInt8
  | "kzg" => .ok 0
  | "plonk" => .ok 1
  | "groth16" => .ok 2
  | "dev-groth16" => .ok 3
  | other => .error s!"unknown compression output {other}: expected kzg, plonk or groth16"

/-- Check what can be checked before proving: the setup is configured and
authenticates, and the options are consistent. Returns the setup description. -/
def preflight (opts : Options) : IO String := do
  unless opts.logHeight == 24 || opts.logHeight == 25 do
    throw <| IO.userError "--log-height must be 24 or 25"
  if let some path := opts.fixedRoot then
    unless ← System.FilePath.pathExists path do
      throw <| IO.userError s!"fixed root layout {path} does not exist"
  Compression.describeSetup opts.devSrs

/-- Compress the aggregate root `addr`, persist the compressed proof under the
same claim and return its address. -/
def compressRoot (addr : Address) (opts : Options) : IO Address := do
  let setup ← preflight opts
  let wrapper ← Compression.readProof addr
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError "proof is already compressed"
  let .checkEnv _ _ := wrapper.claim | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
  -- The statement comes from the same backend `ix verify --aggregate` uses;
  -- a trusted root key only replaces the verifying key the FRI stage checks.
  let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
  let statement := Compression.statementBytes backend wrapper.claim
  Compression.checkClaim (Ix.Claim.ser wrapper.claim) statement
  let out ← match opts.out with
    | some path => pure path
    | none =>
      let dir := (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"
      pure (dir / toString addr / toString opts.logHeight).toString
  let vk ← match opts.rootVk with
    | some path => IO.FS.readBinFile path
    | none => pure backend.system.vkBytes
  let layout ← match opts.fixedRoot with
    | some path => IO.FS.readFile path
    | none => Compression.releaseRootLayout vk
  IO.eprintln s!"Normalizing aggregate root {addr} for compression."
  let root ← Compression.normalize backend wrapper layout
  Compression.releaseGpuMemory
  IO.eprintln s!"Compressing aggregate root {addr} with {setup}."
  let proof ← Compression.compress vk root (Ix.Claim.ser wrapper.claim) statement
    layout out (← Compression.cacheDir).toString
    opts.devSrs opts.logHeight.toUInt32 opts.terminal
  let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
  StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    if p.hasFlag "plonk" && p.hasFlag "groth16" then
      throw <| IO.userError "choose at most one of --plonk and --groth16"
    if p.hasFlag "dev-groth16" && !p.hasFlag "groth16" then
      throw <| IO.userError "--dev-groth16 requires --groth16"
    let terminal : UInt8 := if p.hasFlag "groth16" then
        (if p.hasFlag "dev-groth16" then 3 else 2)
      else if p.hasFlag "plonk" then 1 else 0
    let hex := p.positionalArg! "proof" |>.as! String
    let some addr := Address.fromString hex | throw <| IO.userError "expected a 64-character proof address"
    let result ← compressRoot addr {
      terminal
      devSrs := p.hasFlag "dev-srs"
      logHeight := ((p.flag? "log-height").map (·.as! Nat)).getD 24
      out := (p.flag? "out").map (·.as! String)
      rootVk := (p.flag? "root-vk").map (·.as! String)
      fixedRoot := (p.flag? "fixed-root").map (·.as! String) }
    IO.println (toString result)
    return 0
  catch e =>
    IO.eprintln s!"compress: {e}"
    return 1

end Ix.Cli.CompressCmd

open Ix.Cli.CompressCmd in
def compressCmd : Cli.Cmd := `[Cli|
  compress VIA runCompressCmd;
  "Compress an aggregate CheckEnv proof; preserve its claim and print the new proof address."
  FLAGS:
    "out" : String; "Output directory for the stage proofs (default ~/.ix/compression/<root>/<height>). Rerunning with the same directory resumes from the last completed stage."
    "log-height" : Nat; "First KZG partition height: 24 (default) or 25."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "fixed-root" : String; "Override the bundled release normalization layout with a layout from `ix compress layout`."
    "dev-srs"; "Use known-trapdoor development parameters; results are not production-secure."
    "plonk"; "Add a terminal PLONK proof using the compiled curve and selected setup."
    "groth16"; "Add a terminal BN254 Groth16 proof using prepared, independently admitted circuit keys."
    "dev-groth16"; "Allow development Groth16 keys; inner KZG still requires admitted Ignition parameters."
  ARGS:
    proof : String; "Address of an aggregate Ixon.Proof in the ix store."

  SUBCOMMANDS:
    Ix.Cli.CompressionCmd.layoutCmd;
    Ix.Cli.CompressionCmd.normalizeCmd;
    Ix.Cli.CompressionCmd.fetchParamsCmd
]
end
