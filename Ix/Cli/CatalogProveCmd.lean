module

public import Cli
public import Lean.Data.Json

public section

namespace Ix.Cli.CatalogProveCmd

@[extern "rs_catalog_prove"]
opaque rsCatalogProveFFI : @& String → IO String

def runCatalogProving (p : Cli.Parsed) (verifyOnly : Bool) : IO UInt32 := do
  let some arg := p.positionalArg? "ixc"
    | p.printError "error: a catalog directory is required"
      return 1
  let pathFlag (name : String) : Lean.Json :=
    match p.flag? name with
    | some f => .str (f.as! String)
    | none => .null
  let natFlag (name : String) (default : Nat) : Lean.Json :=
    Lean.toJson <| ((p.flag? name).map (·.as! Nat)).getD default
  let request := Lean.Json.mkObj [
    ("catalog", .str (arg.as! String)),
    ("base", pathFlag "base"),
    ("executable", .str (← IO.appPath).toString),
    ("allowAxioms", pathFlag "allow-axioms"),
    ("shards", natFlag "shards" 0),
    ("structuralAbove", natFlag "structural-above" 4096),
    ("maxRam", natFlag "max-ram" 0),
    ("jobs", natFlag "jobs" 0),
    ("execJobs", natFlag "exec-jobs" 0),
    ("traceShards", Lean.toJson (p.hasFlag "trace-shards")),
    ("planOnly", Lean.toJson (p.hasFlag "plan-only")),
    ("verifyOnly", Lean.toJson verifyOnly)]
  try
    let output ← rsCatalogProveFFI request.compress
    let result ← IO.ofExcept (Lean.Json.parse output)
    if p.hasFlag "json" then
      IO.println result.pretty
    else
      let status := ((result.getObjVal? "status").bind (·.getStr?)).toOption.getD "unknown"
      let pathKey := if status == "planned" then "work" else "record"
      let path := ((result.getObjVal? pathKey).bind (·.getStr?)).toOption.getD ""
      IO.println s!"[catalog prove] {status}: {path}"
      if let .ok proof := (result.getObjVal? "rootProof").bind (·.getStr?) then
        IO.println proof
    return 0
  catch e =>
    IO.eprintln s!"catalog proving failed: {e}"
    return 1

def runCatalogProve (p : Cli.Parsed) : IO UInt32 := runCatalogProving p false
def runCatalogVerifyProof (p : Cli.Parsed) : IO UInt32 := runCatalogProving p true

def catalogProveCmd : Cli.Cmd := `[Cli|
  prove VIA runCatalogProve;
  "Certify a catalog, preserving a previous catalog's corpus and reusable shard/aggregate proofs"

  FLAGS:
    base : String; "Previously certified .ixc directory. Its proving.json, retained corpus and proof store must be available."
    "plan-only"; "Prepare/resume the corpus and shard plan, verify the base certificate if supplied, and stop without executing or proving new claims. Writes pending artifacts under the catalog's proving directory."
    "allow-axioms" : String; "Reviewed axiom addresses, one hex address per line (# comments allowed). Defaults to the prior record's policy, or no axioms for a fresh baseline."
    shards : Nat; "Initial shard count for NEW blocks only; 0 (default) seeds roughly 16 MiB per shard. Existing ownership is preserved; the prover can split over-budget shards."
    "max-ram" : Nat; "Prover/aggregate RAM budget in GiB; 0 or omitted uses the existing backend defaults."
    "trace-shards"; "Use trace-sharded leaf and aggregate proving."
    jobs : Nat; "Concurrent aggregate slots; default 0 uses all ready slots subject to the backend RAM gate."
    "exec-jobs" : Nat; "Concurrent leaf executions with --trace-shards; default 0 uses the backend default."
    "structural-above" : Nat; "Structural aggregate threshold (default 4096); must match the base's proof profile."
    json; "Print the planning/result record as JSON; subprocess progress goes to stderr."

  ARGS:
    ixc : String; "Current snapshot's immutable .ixc directory."
]

def catalogVerifyProofCmd : Cli.Cmd := `[Cli|
  "verify-proof" VIA runCatalogVerifyProof;
  "Verify a catalog's proving.json, current-snapshot coverage, axiom policy and aggregate certificate against its retained corpus"

  FLAGS:
    "allow-axioms" : String; "Independently reviewed axiom policy, required for a nonempty recorded policy. Must match the certificate profile."
    "structural-above" : Nat; "Structural threshold used for proving (default 4096)."
    json; "Print the result as JSON."

  ARGS:
    ixc : String; "Certified .ixc directory; its retained corpus and proof store must be available."
]

end Ix.Cli.CatalogProveCmd
