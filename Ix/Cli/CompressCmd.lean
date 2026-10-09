module
public import Cli
public import Ix.Cli.Compression

public section
namespace Ix.Cli.CompressCmd

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  try
    let hex := p.positionalArg! "proof" |>.as! String
    let some addr := Address.fromString hex
      | throw <| IO.userError "expected a 64-character proof address"
    let wrapper ← Compression.readProof addr
    let .checkEnv _ _ := wrapper.claim
      | throw <| IO.userError "compression requires an aggregate CheckEnv proof"
    if Compression.isCompressed wrapper.proof then
      throw <| IO.userError "proof is already compressed"
    let _ ← IO.ofExcept (Aiur.Proof.ofBytesChecked wrapper.proof)
    let dir ← Compression.requireSetup
    let backend ← IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)
    let proof ← Compression.compress backend.system backend.allowed backend.aggrIdx
      (Ix.Claim.ser wrapper.claim) wrapper.proof dir.toString
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
  "Compress an aggregate root with the active local configuration; preserve its claim and print the new store address. Run ix compression setup first."
  ARGS:
    proof : String; "Store address of a root produced by ix aggregate with the current default parameters."
]
end
