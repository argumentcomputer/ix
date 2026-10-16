module
public import Cli
public import Ix.Cli.Compression
public import Ix.Aggr.Backend

public section
namespace Ix.Cli.CompressCmd

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    let setup ← Compression.describeSetup (p.hasFlag "dev-srs")
    let hex := p.positionalArg! "proof" |>.as! String
    let some addr := Address.fromString hex | throw <| IO.userError "expected a 64-character proof address"
    let wrapper ← Compression.readProof addr
    if Compression.isCompressed wrapper.proof then
      throw <| IO.userError "proof is already compressed"
    let .checkEnv _ _ := wrapper.claim | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
    let height := ((p.flag? "log-height").map (·.as! Nat)).getD 24
    unless height == 24 || height == 25 do
      throw <| IO.userError "--log-height must be 24 or 25"
    -- The statement comes from the same backend `ix verify --aggregate` uses;
    -- a trusted root key only replaces the verifying key the FRI stage checks.
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    let statement := Compression.statementBytes backend wrapper.claim
    Compression.checkClaim (Ix.Claim.ser wrapper.claim) statement
    let out ← match (p.flag? "out").map (·.as! String) with
      | some path => pure path
      | none =>
        pure (← Compression.newRunDir addr height (p.hasFlag "dev-srs")).toString
    let vk ← match (p.flag? "root-vk").map (·.as! String) with
      | some path => IO.FS.readBinFile path
      | none => pure backend.system.vkBytes
    IO.eprintln s!"Compressing aggregate root {addr} with {setup}."
    IO.eprintln s!"Compression artifacts: {out}"
    let proof ← Compression.compress vk wrapper.proof (Ix.Claim.ser wrapper.claim) statement
      out (← Compression.cacheDir).toString
      (p.hasFlag "dev-srs") height.toUInt32
    if p.hasFlag "dev-srs" then
      let keyPath := System.FilePath.mk out / "final-kzg/verifier.bin"
      let key ← IO.FS.readBinFile keyPath
      let cached ← Compression.cacheDevelopmentKey proof (Ix.Claim.ser wrapper.claim) statement key
      IO.eprintln s!"Development verifying key: {cached}"
    let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
    let result ← StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))
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
    "out" : String; "Override the fresh run directory created automatically under ~/.ix/compression."
    "log-height" : Nat; "First KZG partition height: 24 (default) or 25."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "dev-srs"; "Use known-trapdoor development parameters; results are not production-secure."
  ARGS:
    proof : String; "Address of an aggregate Ixon.Proof in the ix store."
]
end
