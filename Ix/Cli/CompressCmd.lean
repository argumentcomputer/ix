module
public import Cli
public import Ix.Cli.Compression
public import Ix.Aggr.Backend

public section
namespace Ix.Cli.CompressCmd

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    unless p.hasFlag "dev-srs" do
      throw <| IO.userError "compression currently uses a known-trapdoor development SRS; --dev-srs is required (not production-secure)"
    let hex := p.positionalArg! "proof" |>.as! String
    let some addr := Address.fromString hex | throw <| IO.userError "expected a 64-character proof address"
    let wrapper ← Compression.readProof addr
    if Compression.isCompressed wrapper.proof then
      throw <| IO.userError "proof is already compressed"
    let .checkEnv _ _ := wrapper.claim | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
    let height := ((p.flag? "log-height").map (·.as! Nat)).getD 24
    unless height == 24 || height == 25 do
      throw <| IO.userError "--log-height must be 24 or 25"
    Compression.checkClaim (Ix.Claim.ser wrapper.claim)
    let explicitOut := (p.flag? "out").map (·.as! String)
    let out ← match explicitOut with
      | some path => pure path
      | none =>
        let dir := (← StoreIO.toIO Store.getHomeDir) / ".ix/compression"
        pure (dir / toString addr / toString height).toString
    let resume := p.hasFlag "resume" ||
      (explicitOut.isNone && (← (System.FilePath.mk out / "input-id.bin").pathExists))
    let vk ← match (p.flag? "root-vk").map (·.as! String) with
      | some path => IO.FS.readBinFile path
      | none =>
        let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
        pure backend.system.vkBytes
    IO.eprintln "Compressing Init with a development SRS (not production-secure)."
    let proof ← Compression.compress vk wrapper.proof (Ix.Claim.ser wrapper.claim)
      out (← Compression.registryDir).toString resume (p.hasFlag "resident") height.toUInt32
    let compressed : Ixon.Proof := { claim := wrapper.claim, proof }
    let result ← StoreIO.toIO (Store.write (Ixon.Proof.ser compressed))
    IO.eprintln s!"Verifier registered locally; portable key: {out}/final-kzg/verifier.bin"
    IO.println (toString result)
    return 0
  catch e =>
    IO.eprintln s!"compress: {e}"
    return 1

end Ix.Cli.CompressCmd
open Ix.Cli.CompressCmd in
def compressCmd : Cli.Cmd := `[Cli|
  compress VIA runCompressCmd;
  "Compress an aggregate Init proof; preserve its claim and print the new proof address."
  FLAGS:
    "out" : String; "Optional checkpoint directory; defaults to ~/.ix/compression with automatic resume."
    "resume"; "Resume checkpoints bound to this proof, verifier key and profile."
    "resident"; "Keep polynomial checkpoints in RAM; faster but uses more memory."
    "log-height" : Nat; "First KZG partition height: 24 (default) or 25."
    "root-vk" : String; "Trusted root verifier key; omit to use the current aggregate backend."
    "dev-srs"; "Explicitly allow the known-trapdoor development setup; results are not production-secure."
  ARGS:
    proof : String; "Address of an aggregate Ixon.Proof in the ix store."
]
end
