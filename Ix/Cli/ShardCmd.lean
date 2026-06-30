/-
  `ix shard <path.ixprof>`: partition a profiled environment into shards,
  minimizing cross-shard delta-unfold ingress (see `plans/sharding.md`).

  Two modes (precedence in `runShardCmd`):
  - default / `--max-ram G` / `--max-cycles C`: **bin-pack to a per-shard
    cycle/RAM cap** — the fewest shards that each stay under the budget, each
    packed as full as the dependency structure allows (no `--max-ram` ⇒ sized to
    detected system RAM). Not balanced: packing yields the minimal shard count.
  - `--shards N`: force exactly `N` **balanced** min-cut shards (manual override).

  Reads the `.ixprof` produced by `ix profile` (pure offline graph work, so the
  budget/`N` is cheap to re-tune without re-running the kernel). Writes a `.ixes`
  manifest and prints a what-if report (per-shard cost + total cross-shard
  ingress). The partitioner is self-contained — no external graph-library
  dependency.
-/
module
public import Cli
public import Ix.KernelCheck

public section

open Ix.KernelCheck

namespace Ix.Cli.ShardCmd

def runShardCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixprof file"
      return 1
  let espPath := pathArg.as! String
  let balancePct : Nat :=
    match p.flag? "balance" with
    | some flag => flag.as! Nat
    | none      => 5
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default manifest mirrors the profile's base name: `init.ixprof` →
    -- `init.ixes` (not `init.ixprof.ixes`).
    | none      =>
      let base := if espPath.endsWith ".ixprof" then espPath.dropRight 7 else espPath
      base ++ ".ixes"
  let shardsFlag : Option Nat := (p.flag? "shards").map (·.as! Nat)
  let maxCycles  : Option Nat := (p.flag? "max-cycles").map (·.as! Nat)
  let maxRam     : Option Nat := (p.flag? "max-ram").map (·.as! Nat)
  -- Provers the prove-time estimate assumes (wall clock = max(seq/P, slowest
  -- shard)). Sharded proving is sequential today, so the default is 1.
  let parallelism : Nat :=
    match p.flag? "parallelism" with
    | some flag => max 1 (flag.as! Nat)
    | none      => 1

  -- Precedence: explicit --shards (fixed count) > explicit --max-cycles/--max-ram
  -- (budget) > default (size to detected system RAM).
  match shardsFlag with
  | some n =>
    IO.println s!"Sharding {espPath} into {n} shards (balance ±{balancePct}%)"
    rsShardEspFFI espPath (toString n) (toString balancePct) (toString parallelism)
      outPath
  | none =>
    if maxCycles.isNone && maxRam.isNone then
      IO.println s!"Sharding {espPath} to detected system RAM (balance ±{balancePct}%)"
    else
      IO.println s!"Sharding {espPath} to budget (max-cycles={maxCycles.getD 0}, max-ram={maxRam.getD 0} GiB, balance ±{balancePct}%)"
    rsShardEspCapFFI espPath (toString (maxCycles.getD 0)) (toString (maxRam.getD 0))
      (toString balancePct) (toString parallelism) outPath
  if !outPath.isEmpty then
    IO.println s!"[shard] wrote {outPath}"
  return 0

end Ix.Cli.ShardCmd

open Ix.Cli.ShardCmd in
def shardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runShardCmd;
  "Partition a `.ixprof` into shards: pack to a RAM/cycle cap (default) or N balanced shards"

  FLAGS:
    shards       : Nat;    "Fixed number of shards N (overrides the default budget sizing)"
    "max-cycles" : Nat;    "Per-shard guest-cycle budget (overrides the default RAM sizing)"
    "max-ram"    : Nat;    "Per-shard host-RAM budget, GiB (default: detected system RAM)"
    balance      : Nat;    "Per-bisection balance tolerance, percent (default 5)"
    parallelism  : Nat;    "Provers assumed for the prove-time estimate (default 1 = sequential)"
    out          : String; "Output .ixes manifest path (default: <prof>.ixes, e.g. init.ixprof → init.ixes)"

  ARGS:
    path : String; "Path to a .ixprof produced by `ix profile`"
]

end
