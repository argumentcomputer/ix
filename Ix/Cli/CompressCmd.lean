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
        let dir := (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"
        pure (dir / toString addr / toString height).toString
    let vk ← match (p.flag? "root-vk").map (·.as! String) with
      | some path => IO.FS.readBinFile path
      | none => pure backend.system.vkBytes
    let (root, layout) ← match (p.flag? "fixed-root").map (·.as! String) with
      | some path =>
        let layout ← IO.FS.readFile path
        IO.eprintln s!"Normalizing aggregate root {addr} to {path}."
        pure (← Compression.normalize backend wrapper layout, layout)
      | none => pure (wrapper.proof, "")
    IO.eprintln s!"Compressing aggregate root {addr} with {setup}."
    let proof ← Compression.compress vk root (Ix.Claim.ser wrapper.claim) statement
      layout out (← Compression.cacheDir).toString
      (p.hasFlag "dev-srs") height.toUInt32 (p.hasFlag "plonk")
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
    "out" : String; "Empty output directory for the stage proofs; defaults to a new directory under ~/.ix/compression."
    "log-height" : Nat; "First KZG partition height: 24 (default) or 25."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "fixed-root" : String; "Normalize the root to this layout (from `ix compression layout`) first, so the verifier does not depend on the root's shape."
    "dev-srs"; "Use known-trapdoor development parameters; results are not production-secure."
    "plonk"; "Add a terminal PLONK proof using the compiled curve and selected setup."
  ARGS:
    proof : String; "Address of an aggregate Ixon.Proof in the ix store."
]
end
