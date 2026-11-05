module
public import Cli
public import Ix.Cli.Compression
public import Ix.Cli.CompressionCmd

public section
namespace Ix.Cli.CompressCmd

/-- Selected compression output: the proof system after recursive KZG and the
setup policy. -/
structure Options where
  finalProof : UInt8 := 0
  devKzgSrs : Bool := false
  devFinalSrs : Bool := false
  out : Option String := none
  fixedRoot : Option String := none
  fresh : Bool := false
  /-- Extra doublings of every circuit height when sizing the normalization
  layout from the root. -/
  headroom : Nat := 0

/-- Select the proof system independently of its setup policy. -/
def finalOf : String → Except String UInt8
  | "kzg" => .ok 0
  | "plonk" => .ok 1
  | "groth16" => .ok 2
  | other => .error s!"unknown compression output {other}: expected kzg, plonk or groth16"

/-- Check what can be checked before proving: the setup is configured and
authenticates, and the options are consistent. Returns the setup description. -/
def preflight (opts : Options) : IO String := do
  if let some path := opts.fixedRoot then
    unless ← System.FilePath.pathExists path do
      throw <| IO.userError s!"fixed root layout {path} does not exist"
  unless opts.headroom < 8 do throw (IO.userError "--headroom must be below 8")
  Compression.describeSetup opts.devKzgSrs opts.devFinalSrs opts.finalProof

/-- Compress the aggregate root `addr`, persist the compressed proof under the
same claim and return its address. -/
private def compressProof (p : Cli.Parsed) (addr : Address) (wrapper : Ixon.Proof)
    (opts : Options) (setup : String) : IO Address := do
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError "proof is already compressed"
  let .checkEnv .. := wrapper.claim | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
  let _ := (p, addr, opts, setup)
  throw <| IO.userError "compression of formal aggregate roots needs their normalization, \
    which this build lacks; legacy Aiur roots are retired"

/-- Compress a stored aggregate proof and return the compressed proof address. -/
def compressRoot (p : Cli.Parsed) (addr : Address) (opts : Options) : IO Address := do
  let setup ← preflight opts
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
      fixedRoot := (p.flag? "fixed-root").map (·.as! String)
      headroom := ((p.flag? "headroom").map (·.as! Nat)).getD 0 }
    let setup ← preflight opts
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
  "Compress a formal aggregate CheckEnv proof; preserve its claim and print the new proof address."
  FLAGS:
    "fresh"; "Replace prior compression stages in --out (or the default output) with newly generated proofs. Reuse parameters, proving keys and fixed preprocessing."
    "out" : String; "Output directory for the stage proofs (default ~/.ix/compression/<root>). Rerunning with the same directory reuses every stage whose proof still verifies."
    "fixed-root" : String; "Normalization layout from `ix compress layout`, instead of one sized from the root. Roots normalized to one layout compress under one recursive verifying key."
    "headroom" : Nat; "Without --fixed-root: extra doublings of every circuit height beyond the root's own (default 0)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "max-ram" : Nat; "RAM budget in GiB for proving the normalized root (default 85% of available memory)."
    "gpu-device" : Nat; "Prove the normalized root on this CUDA device (requires a CUDA build)."
    "dev-kzg-srs"; "Generate local development parameters for inner KZG. With --groth16 or --plonk, also requires --dev-final-srs."
    "dev-final-srs"; "Generate and cache local development Groth16 or PLONK keys for the selected inner verifier. With --dev-kzg-srs, no Ignition parameters are required."
    "plonk"; "Add a final PLONK proof using the compiled curve and selected setup."
    "groth16"; "Add a final BN254 Groth16 proof using prepared, independently admitted circuit keys."
  ARGS:
    proof : String; "Aggregate Ixon.Proof file (including its claim), or its 64-character content address in the ix store. A hexadecimal filename needs a ./ prefix."

  SUBCOMMANDS:
    Ix.Cli.CompressionCmd.deriveVkCmd;
    Ix.Cli.CompressionCmd.setupCmd
]
end
