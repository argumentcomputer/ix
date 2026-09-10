/-
  `ix compress <aggregate-proof-hex>`: compress a persisted aggregate root
  proof to a BN254 PLONK proof (see `Ix.Cli.Compress`).
-/
module
public import Cli
public import Ix.Address
public import Ix.Cli.Compress
public import Ix.MultiStark

public section

namespace Ix.Cli.CompressCmd

def runCompressCmd (p : Cli.Parsed) : IO UInt32 := do
  let some hex := p.positionalArg? "proof" |>.map (·.as! String) | do
    p.printError "error: compress requires <aggregate-proof-hex>"
    return 1
  let some proofAddr := Address.fromString hex | do
    p.printError s!"error: expected a 64-char hex address, got {hex}"
    return 1
  let opts : Ix.Cli.Compress.Options := {
    wrapOnly := p.hasFlag "wrap-only"
    out := (p.flag? "out").map (·.as! String)
    wrapOut := (p.flag? "wrap-out").map (·.as! String)
    blob := (p.flag? "blob").map (·.as! String)
  }
  Ix.Cli.Compress.compressAggregateRoot MultiStark.defaultRecursionParameters
    opts proofAddr

end Ix.Cli.CompressCmd

open Ix.Cli.CompressCmd in
def compressCmd : Cli.Cmd := `[Cli|
  compress VIA runCompressCmd;
  "Compress an aggregate root proof to a BN254 PLONK proof: verify it in the recursive verifier proven by SP1 Hypercube, then SP1's recursion tail and the gnark PLONK stage (needs IX_SP1_RECURSION=1)"

  FLAGS:
    "wrap-only";        "Stop after the BN254 wrap proof (no gnark stage)."
    out : String;       "Write the PLONK proof JSON here (default: the store's `plonk` cache, `<proof>.json`; the public inputs go next to it as `.inputs.txt`)."
    "wrap-out" : String; "Also write the wrap proof blob here."
    blob : String;      "Cache file for the Hypercube proof blob: read instead of proving when present, written after proving otherwise."

  ARGS:
    proof : String; "Persisted aggregate root proof address (from `ix aggregate`)."
]
