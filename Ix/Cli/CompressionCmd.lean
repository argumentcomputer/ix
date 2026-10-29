/-
  `ix compression layout|normalize`: fixed-root normalization of aggregate
  roots. `layout` executes a root wrap of each given aggregate proof and sizes
  one fixed layout that holds all of them; `normalize` proves a root's wrap in
  that layout and writes the FRI worker's root input. Every root normalized to
  one layout compresses under the same FRI verifier.
-/
module
public import Cli
public import Ix.Cli.Compression
public import Ix.Aggr.Backend

public section
namespace Ix.Cli.CompressionCmd

private def loadRoot (hex : String) : IO (Address × Ixon.Proof) := do
  let some addr := Address.fromString hex
    | throw <| IO.userError s!"expected a 64-character proof address: {hex}"
  let wrapper ← Compression.readProof addr
  if Compression.isCompressed wrapper.proof then
    throw <| IO.userError s!"proof {addr} is already compressed"
  let .checkEnv _ _ := wrapper.claim
    | throw <| IO.userError s!"proof {addr} is not an aggregate CheckEnv proof"
  return (addr, wrapper)

private def backend : IO Aggr.VerificationBackend := do
  IO.ofExcept (← Aggr.buildVerificationBackend Aggr.defaultRecursionParameters)

def runLayout (p : Cli.Parsed) : IO UInt32 := do
  try
    let out := p.positionalArg! "out" |>.as! String
    let proofs := (p.variableArgsAs! String).toList
    if proofs.isEmpty then
      throw <| IO.userError "expected at least one aggregate proof address"
    let headroom := ((p.flag? "headroom").map (·.as! Nat)).getD 0
    let backend ← backend
    let mut rows := #[]
    let mut claimLen := 0
    for hex in proofs do
      let (addr, wrapper) ← loadRoot hex
      IO.eprintln s!"Executing the root wrap of {addr}."
      rows := rows.push (← Compression.rootRows backend.system backend.aggrIdx
        backend.allowed backend.ixvmVk (Ix.Claim.ser wrapper.claim) wrapper.proof)
      claimLen := (Aggr.aggregateOuterClaim backend.allowed backend.aggrIdx wrapper.claim).size
    let layout ← Compression.rootLayout backend.system
      ("[" ++ ",".intercalate rows.toList ++ "]") headroom.toUInt32 claimLen.toUInt32
    IO.FS.writeFile out layout
    IO.println out
    return 0
  catch e =>
    IO.eprintln s!"compression layout: {e}"
    return 1

def runNormalize (p : Cli.Parsed) : IO UInt32 := do
  try
    let (addr, wrapper) ← loadRoot (p.positionalArg! "proof" |>.as! String)
    let layoutPath := p.positionalArg! "layout" |>.as! String
    let out := p.positionalArg! "out" |>.as! String
    let layout ← IO.FS.readFile layoutPath
    let backend ← backend
    IO.eprintln s!"Normalizing aggregate root {addr} to {layoutPath}."
    let root ← Compression.normalize backend wrapper layout
    let claim := Ix.Claim.ser wrapper.claim
    Compression.writeRoot backend.system.vkBytes root claim
      (Compression.statementBytes backend wrapper.claim) layout out
    IO.println out
    return 0
  catch e =>
    IO.eprintln s!"compression normalize: {e}"
    return 1

def layoutCmd : Cli.Cmd := `[Cli|
  layout VIA runLayout;
  "Size one fixed root layout that holds the root wrap of every given aggregate proof."

  FLAGS:
    headroom : Nat; "Extra doublings of every circuit's height beyond the largest execution (default 0)."

  ARGS:
    out : String; "Output layout JSON file."
    ...proofs : String; "Addresses of aggregate Ixon.Proof roots in the ix store."
]

def normalizeCmd : Cli.Cmd := `[Cli|
  normalize VIA runNormalize;
  "Prove a root's wrap in a fixed layout and write the FRI worker's root input directory."

  ARGS:
    proof : String; "Address of an aggregate Ixon.Proof in the ix store."
    layout : String; "Layout JSON from `ix compression layout`."
    out : String; "Empty output directory for root-vk.bin, root-proof.bin, root-claims.bin and fixed-root.json."
]

def runCompression (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.CompressionCmd

open Ix.Cli.CompressionCmd in
def compressionCmd : Cli.Cmd := `[Cli|
  compression VIA runCompression;
  "Fixed-root normalization of aggregate roots for compression"

  SUBCOMMANDS:
    layoutCmd;
    normalizeCmd
]

end
