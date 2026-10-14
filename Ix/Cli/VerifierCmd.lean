module
public import Cli
public import Ix.Cli.Compression

public section
namespace Ix.Cli.VerifierCmd

def runImport (p : Cli.Parsed) : IO UInt32 := do
  try
    let some digest := (p.flag? "digest").map (·.as! String)
      | throw <| IO.userError "--digest must pin an independently trusted verifier file"
    let file := p.positionalArg! "file" |>.as! String
    let registered ← Compression.importVerifier file digest
      (← Compression.registryDir).toString (p.hasFlag "dev-srs")
    if registered.startsWith "development " then
      IO.println s!"Registered {registered} (not production-secure)"
    else
      IO.println s!"Registered {registered}"
    return 0
  catch e =>
    IO.eprintln s!"verifier import: {e}"
    return 1

def run (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0
end Ix.Cli.VerifierCmd

open Ix.Cli.VerifierCmd in
def verifierImportCmd : Cli.Cmd := `[Cli|
  "import" VIA runImport;
  "Register a verifier using a digest obtained independently of the prover."
  FLAGS:
    "digest" : String; "Required BLAKE3 digest of the independently trusted verifier file."
    "dev-srs"; "Allow registering a known-trapdoor development verifier; its proofs are not production-secure."
  ARGS:
    file : String; "Portable verifier.bin file."
]
open Ix.Cli.VerifierCmd in
def verifierCmd : Cli.Cmd := `[Cli|
  verifier VIA run;
  "Manage accepted compression verifiers."
  SUBCOMMANDS:
    verifierImportCmd
]
end
