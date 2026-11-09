module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.CompressionCmd
public import Ix.Cli.FormalAggregate

public section
namespace Ix.Cli.CompressCmd

/-- Selected compression output: the proof system after recursive KZG and the
setup policy. -/
structure Options where
  finalProof : UInt8 := 0
  devKzgSrs : Bool := false
  devFinalSrs : Bool := false
  out : Option String := none
  rootVk : Option String := none
  fixedRoot : Option String := none
  fresh : Bool := false

/-- Select the proof system independently of its setup policy. -/
def finalOf : String → Except String UInt8
  | "kzg" => .ok 0
  | "plonk" => .ok 1
  | "groth16" => .ok 2
  | other => .error s!"unknown compression output {other}: expected kzg, plonk or groth16"

/-- Check what can be checked before proving: the setup is configured and
authenticates, and the options are consistent. Returns the setup description. -/
def preflight (_p : Cli.Parsed) (opts : Options) : IO String := do
  if let some path := opts.fixedRoot then
    unless ← System.FilePath.pathExists path do
      throw <| IO.userError s!"fixed root layout {path} does not exist"
  Compression.describeSetup opts.devKzgSrs opts.devFinalSrs opts.finalProof

/-- Compress the aggregate root `addr`, persist the compressed proof under the
same claim and return its address. -/
private def compressProof (p : Cli.Parsed) (addr : Address) (wrapper : Ixon.Proof)
    (opts : Options) (setup : String) : IO Address := do
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError "proof is already compressed"
  let .checkEnv .. := wrapper.claim | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
  -- The statement comes from the same backend `ix verify --aggregate` uses;
  -- a trusted root key only replaces the verifying key the FRI stage checks.
  let ctx ← FormalAggregate.context p
  let statement := FormalAggregate.statementBytes ctx wrapper.claim
  Compression.checkClaim (Ix.Claim.ser wrapper.claim) statement
  let out ← match opts.out with
    | some path => pure path
    | none =>
      let dir := (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"
      pure (dir / toString addr).toString
  if opts.fresh then IO.eprintln s!"[compress] fresh: replacing stage artifacts in {out}"
  let vk ← match opts.rootVk with
    | some path => IO.FS.readBinFile path
    | none => pure ctx.aggr.key
  -- Without an override the bundled keys apply: the backend must be theirs,
  -- or compression would fail only after proving.
  let layout ← match opts.fixedRoot with
    | some path => IO.FS.readBinFile path
    | none => do
      let layout ← Compression.releaseRootLayout vk
      Compression.checkReleaseStatement (Ix.Claim.ser wrapper.claim) statement
      pure layout
  IO.eprintln s!"Normalizing aggregate root {addr} for compression."
  let root ← FormalAggregate.normalize ctx wrapper layout
  Compression.releaseGpuMemory
  IO.eprintln s!"Compressing aggregate root {addr} with {setup}."
  let proof ← Compression.compress vk root (Ix.Claim.ser wrapper.claim) statement
    layout out (← Compression.cacheDir).toString
    opts.devKzgSrs opts.devFinalSrs opts.finalProof opts.fresh
  let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
  StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))

/-- Compress a stored aggregate proof and return the compressed proof address. -/
def compressRoot (p : Cli.Parsed) (addr : Address) (opts : Options) : IO Address := do
  let setup ← preflight p opts
  compressProof p addr (← Compression.readProof addr) opts setup

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    if p.hasFlag "plonk" && p.hasFlag "groth16" then
      throw <| IO.userError "choose at most one of --plonk and --groth16"
    let finalProof : UInt8 := if p.hasFlag "groth16" then 2
      else if p.hasFlag "plonk" then 1 else 0
    let opts : Options := {
      finalProof
      fresh := p.hasFlag "fresh"
      devKzgSrs := p.hasFlag "dev-kzg-srs"
      devFinalSrs := p.hasFlag "dev-final-srs"
      out := (p.flag? "out").map (·.as! String)
      rootVk := (p.flag? "root-vk").map (·.as! String)
      fixedRoot := (p.flag? "fixed-root").map (·.as! String) }
    let setup ← preflight p opts
    let input := p.positionalArg! "proof" |>.as! String
    let (addr, wrapper) ← Compression.readProofInput input
    let result ← compressProof p addr wrapper opts setup
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
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Require the IxVM artifact's BLAKE3 digest to equal these 64 hex digits (or IX_AIUR_ARTIFACT_DIGEST)."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "aggr-artifact-digest" : String; "Require the aggregation artifact's BLAKE3 digest to equal these 64 hex digits (or IX_AGGR_ARTIFACT_DIGEST)."
    "fresh"; "Replace prior compression stages in --out (or the default output) with newly generated proofs. Reuse parameters, proving keys and fixed preprocessing."
    "out" : String; "Output directory for the stage proofs (default ~/.ix/compression/<root>). Rerunning with the same directory reuses every stage whose proof still verifies."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "fixed-root" : String; "Override the bundled release normalization layout with a layout from `ix compress layout`."
    "dev-kzg-srs"; "Generate local development parameters for inner KZG. With --groth16 or --plonk, also requires --dev-final-srs."
    "dev-final-srs"; "Generate and cache local development Groth16 or PLONK keys for the selected inner verifier. With --dev-kzg-srs, no Ignition parameters are required."
    "plonk"; "Add a final PLONK proof using the compiled curve and selected setup."
    "groth16"; "Add a final BN254 Groth16 proof using prepared, independently admitted circuit keys."
  ARGS:
    proof : String; "Aggregate Ixon.Proof file (including its claim), or its 64-character content address in the ix store. A hexadecimal filename needs a ./ prefix."

  SUBCOMMANDS:
    Ix.Cli.CompressionCmd.layoutCmd;
    Ix.Cli.CompressionCmd.normalizeCmd;
    Ix.Cli.CompressionCmd.setupCmd
]
end
