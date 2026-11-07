/-
  `ix shard refine <path.ixe> --ixes M.ixes --out M2.ixes [--shards SEL]
  [--max-ram G] [--jobs N] [--report R.json] [--no-index]` and
  `ix shard claims <path.ixe> --ixes M.ixes [--report R.json]`.
-/
module
public import Cli
public import Ix.Common
public import Ix.Aiur.Protocol
public import Ix.Shard.Check
public import Ix.Shard.Environment
public import Ix.Cli.FormalAiur

public section

namespace Ix.Cli.RefineCmd

def runShardRefineCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"; return 1
  let ixePath := pathArg.as! String
  let some manifest := (p.flag? "ixes").map (·.as! String)
    | p.printError "error: --ixes <manifest.ixes> is required"; return 1
  let some out := (p.flag? "out").map (·.as! String)
    | p.printError "error: --out <refined.ixes> is required"; return 1
  let mut args := #["check", "--ixe", ixePath, "--ixes", manifest, "--out-ixes", out]
  if let some s := (p.flag? "shards").map (·.as! String) then args := args ++ #["--shards", s]
  if let some g := (p.flag? "max-ram").map (·.as! Nat) then args := args ++ #["--ram-budget", toString g]
  if let some j := (p.flag? "jobs").map (·.as! Nat) then args := args ++ #["--jobs", toString j]
  if let some r := (p.flag? "report").map (·.as! String) then args := args ++ #["--report", r]
  let app ← IO.appPath
  FormalAiur.commandStatus app.toString args

end Ix.Cli.RefineCmd

open Ix.Cli.RefineCmd in
def shardRefineCmd : Cli.Cmd := `[Cli|
  "refine" VIA runShardRefineCmd;
  "Refine an existing `.ixes` partition against a prover-RAM budget: execute the selected leaves, cut every over-budget one into parts the peak model says will fit (recursively), and write the result as a refinement of the source manifest"

  FLAGS:
    ixes       : String; "The source `.ixes` manifest (required)."
    out        : String; "Where to write the refined `.ixes` manifest (required)."
    shards     : String; "Leaves to audit: `K`, `a-b`, or a comma list of those. Default: every leaf."
    "max-ram"  : Nat;    "Per-shard prover-RAM budget, GiB."
    jobs       : Nat;    "Concurrent execution threads."
    report     : String; "Write the JSON audit report to this path."
    "no-index";          "Do not consult `~/.ix/cache/shard-proofs`."

  ARGS:
    path : String; "Path to the serialized `.ixe` environment the manifest partitions."
]

namespace Ix.Cli.RefineCmd

/-- `ix shard claims <path.ixe> --ixes M.ixes [--report R.json]`: every leaf's
    `CheckEnv` claim digest, one `id digest blocks consts` line per leaf, from
    one env pass. -/
def runShardClaimsCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"; return 1
  let ixePath := pathArg.as! String
  let some manifest := (p.flag? "ixes").map (·.as! String)
    | p.printError "error: --ixes <manifest.ixes> is required"; return 1
  match (← Ix.Shard.loadEnvAndShards manifest ixePath) with
  | .error e => IO.eprintln e; return 1
  | .ok (ixonEnv, shards) =>
    let ownedAll := Ix.Shard.ownedConstsPer ixonEnv shards
    let mut rows : Array Lean.Json := #[]
    let mut rc : UInt32 := 0
    for k in [0:shards.size] do
      let blocks := (shards[k]?).getD #[]
      let owned := (ownedAll[k]?).getD #[]
      match Ix.Shard.Check.claimDigestOfOwned ixonEnv owned with
      | .error e => IO.eprintln s!"shard {k}: {e}"; rc := 1
      | .ok d =>
        IO.println s!"{k} {d} {blocks.size} {owned.size}"
        rows := rows.push (Lean.Json.mkObj [("id", Lean.toJson k),
          ("claim", Lean.Json.str (toString d)), ("blocks", Lean.toJson blocks.size),
          ("consts", Lean.toJson owned.size)])
    if let some out := (p.flag? "report").map (·.as! String) then
      let report := Lean.Json.mkObj [("schema", Lean.Json.str "ix-refine/0"),
        ("source", Lean.Json.mkObj [("path", Lean.Json.str manifest),
          ("shards", Lean.toJson shards.size)]),
        ("leaves", Lean.Json.arr rows)]
      IO.FS.writeFile out (report.pretty ++ "\n")
      IO.println s!"[claims] report → {out}"
    return rc

end Ix.Cli.RefineCmd

open Ix.Cli.RefineCmd in
def shardClaimsCmd : Cli.Cmd := `[Cli|
  "claims" VIA runShardClaimsCmd;
  "Print every leaf's CheckEnv claim digest of a `.ixes` partition (`id digest blocks consts`, one line per leaf) in one env pass — the identities a claim-keyed runner tracks instead of manifest indices"

  FLAGS:
    ixes   : String; "The `.ixes` manifest (required)."
    report : String; "Also write the rows as a provisional JSON report (`ix-refine/0`) to this path."

  ARGS:
    path : String; "Path to the `.ixe` environment the manifest partitions."
]

end
