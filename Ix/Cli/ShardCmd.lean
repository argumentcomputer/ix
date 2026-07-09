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

  `ix shard extract <path.ixe> --consts <n1,n2,…>`: the pipeline's scoping
  step — extract the named constants' dependency closure from a serialized
  env into a standalone `.ixe`, without recompiling from source. The output
  carries the closure's genuine constant bytes, blobs, and reducibility
  hints, plus each closure constant's name→address entry, so it composes
  with everything that consumes a `.ixe` (`ix profile` → `ix shard`,
  `ix check-rs --consts`, the zkVM hosts, `bench-typecheck`).
-/
module
public import Cli
public import Ix.KernelCheck
public import Ix.Cli.ConstsFile

public section

open Ix.KernelCheck

namespace Ix.Cli.ShardCmd

def runShardExtractCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let names ← Ix.Cli.ConstsFile.gather p
  if names.isEmpty then
    p.printError "error: pass at least one name via --consts or --consts-file"
    return 1
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default output mirrors the first constant's slug next to the source
    -- env: `init.ixe --consts Nat.add_comm` → `nat_add_comm.ixe`.
    | none =>
      let slug := names[0]!.map fun c =>
        if c.isAlphanum then c.toLower else '_'
      s!"{slug}.ixe"
  let quiet := !(p.flag? "verbose" |>.isSome)
  rsEnvExtractFFI envPath names outPath quiet
  IO.println s!"[extract] wrote {outPath} ({names.size} root name(s))"
  return 0

def shardExtractCmd : Cli.Cmd := `[Cli|
  "extract" VIA runShardExtractCmd;
  "Extract named constants + their dependency closure from a `.ixe` into a standalone `.ixe`"

  FLAGS:
    consts        : String; "Comma-separated EXACT constant names (displayed form) to extract, e.g. `Nat.add_comm,String.append`. Same flag/shape as `ix check-rs --consts`. A mutual-block member extracts its whole block."
    "consts-file" : String; "Additionally read names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    out           : String; "Output `.ixe` path. Defaults to a slug of the first name (e.g. `nat_add_comm.ixe`)."
    verbose;                "Print extraction details to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
]

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
      let base := if espPath.endsWith ".ixprof" then (espPath.dropEnd 7).toString else espPath
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

  SUBCOMMANDS:
    shardExtractCmd
]

end
