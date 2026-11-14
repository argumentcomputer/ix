/-
  `ix shard refine <path.ixe> --ixes M.ixes --out M2.ixes [--shards SEL]
  [--max-ram G] [--jobs N] [--report R.json] [--no-index]`: the local
  refinement of an existing partition, run as `ix check --ram-budget`.
  Every selected leaf (default: all) is executed and its proof planned
  against the per-leaf budget; a leaf whose trace-shard batch cannot fit is
  cut into the part count the peak model suggests and the parts re-executed,
  until everything fits or is a single block. The result is written as a
  refinement of the source manifest: untouched leaves keep their records,
  ids and tree positions, and each split leaf becomes a balanced subtree over
  its parts. A leaf whose claim already has a verified proof in the
  shard-proof index is never executed or split: refinement must never orphan
  a proof. Any failure exits 1 and writes no manifest.
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

/-- The per-leaf prover budget in GiB: `--max-ram G`, or 85% of the memory
    this machine has available when omitted or `0`. -/
def resolveBudget (p : Cli.Parsed) : IO Nat := do
  if let some g := (p.flag? "max-ram").map (·.as! Nat) then
    if g > 0 then return g
  let available := ((← FormalAiur.resources).getObjValAs? Nat "available_bytes").toOption.getD 0
  let gib := available * 85 / 100 / 1024^3
  if gib == 0 then
    throw (IO.userError "cannot detect available memory; pass --max-ram G")
  IO.println s!"[refine] budget {gib} GiB per leaf (detected: 85% of available memory)"
  return gib

/-- The `ix check` arguments of a refinement that runs `concurrent` leaves at
    once. `ix check --ram-budget` divides its budget among them, so the
    per-leaf budget is multiplied by that count. -/
def checkArgs (ixe manifest out : String) (shards report : Option String)
    (budgetGib concurrent : Nat) (index : Bool) : Array String :=
  #["check", "--ixe", ixe, "--ixes", manifest, "--out-ixes", out,
    "--ram-budget", toString (budgetGib * concurrent), "--jobs", toString concurrent,
    "--keep-going"]
    ++ (match shards with | some s => #["--shards", s] | none => #[])
    ++ (match report with | some r => #["--report", r] | none => #[])
    ++ (if index then #["--skip-proven"] else #[])

#guard checkArgs "e.ixe" "m.ixes" "o.ixes" none none 64 3 true ==
  #["check", "--ixe", "e.ixe", "--ixes", "m.ixes", "--out-ixes", "o.ixes",
    "--ram-budget", "192", "--jobs", "3", "--keep-going", "--skip-proven"]

def runShardRefineCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"; return 1
  let ixePath := pathArg.as! String
  let some (manifest : String) := (p.flag? "ixes").map (·.as! String)
    | p.printError "error: --ixes <manifest.ixes> is required"; return 1
  let some out := (p.flag? "out").map (·.as! String)
    | p.printError "error: --out <refined.ixes> is required"; return 1
  let shards := (p.flag? "shards").map (·.as! String)
  let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
  let selected ← match shards with
    | some s => pure (← IO.ofExcept (Ix.Shard.Check.parseShardSelection s)).size
    | none => pure view.shards.size
  -- `ix check` divides its budget by --jobs, so pass exactly the number of
  -- leaves that run at once; each is then planned against the full budget.
  let concurrent := max 1 (min (← FormalAiur.jobCount p) selected)
  let budget ← resolveBudget p
  let args := checkArgs ixePath manifest out shards ((p.flag? "report").map (·.as! String))
    budget concurrent (!p.hasFlag "no-index")
  FormalAiur.commandStatus (← IO.appPath).toString args

end Ix.Cli.RefineCmd

open Ix.Cli.RefineCmd in
def shardRefineCmd : Cli.Cmd := `[Cli|
  "refine" VIA runShardRefineCmd;
  "Refine an existing `.ixes` partition against a per-leaf prover-RAM budget: execute the selected leaves, cut every leaf whose trace-shard batch cannot fit into parts (recursively), and write the result as a refinement of the source manifest — untouched leaves keep their records, ids and aggregation-tree positions; a leaf that already has a verified proof in the shard-proof index is never split"

  FLAGS:
    ixes       : String; "The source `.ixes` manifest (required)."
    out        : String; "Where to write the refined `.ixes` manifest (required). Written only when every selected leaf settles: any failure exits 1 and writes nothing, and the report lists every failed leaf."
    shards     : String; "Leaves to audit: `K`, `a-b`, or a comma list of those. Default: every leaf. Unselected leaves are carried over unchanged."
    "max-ram"  : Nat;    "Per-leaf prover-RAM budget in GiB, the budget each leaf's proof will be planned against. Omitted or 0: 85% of this machine's available memory."
    jobs       : Nat;    "Leaves executed at once (default 1; 0 uses available cores). Each is planned against the full --max-ram, so their executions must fit in memory together."
    report     : String; "Write the ix-formal-run/1 report (per-leaf parts, status, plans) to this path."
    "no-index";          "Do not consult the shard-proof index (`~/.ix/cache/formal-shard-proofs`): execute and split leaves even when a verified proof of their claim exists."

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
