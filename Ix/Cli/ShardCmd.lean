module
public import Cli
public import Ix.Common
public import Ix.KernelCheck
public import Ix.Cli.ConstsFile
public import Ix.Cli.RefineCmd

/-!
  `ix shard <path.ixe>`: partition an environment into shards for the
  Aiur (IxVM) checking pipeline using the static strategy.

  Computed from the `.ixe` alone — no out-of-circuit kernel run.
  Byte-balanced min-cut over the env's static walk-edge nets (the
  relation that generates each shard's thin frontier, i.e. its real
  ingress), then a global rebalance post-pass toward equal predicted
  Aiur FFT cost (fitted model — constants and provenance in
  `ixon::shard::STATIC_OWNED_PER_BYTE`). By default the count is seeded
  from the same static block-shape score for the host budget `ix prove`
  runs under (`MemTotal` less the 20% host reservation), so no flag is
  needed and both commands agree. `--max-ram G` sizes it for a different
  process budget, with the same meaning as `ix prove --max-ram`; `--shards N`
  fixes the count.

  Writes a `.ixes` manifest and prints a what-if report. The
  partitioner is self-contained — no external graph-library dependency.

  `ix shard extract <path.ixe> --consts <n1,n2,…>`: the pipeline's scoping
  step — extract the named constants' dependency closure from a serialized
  env into a standalone `.ixe`, without recompiling from source. The output
  carries the closure's genuine constant bytes, blobs, and reducibility
  hints, plus each closure constant's name→address entry, so it composes
  with everything that consumes a `.ixe`.
-/

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
    consts        : String; "Comma-separated EXACT constant names (displayed form) to extract, e.g. `Nat.add_comm,String.append`. A mutual-block member extracts its whole block."
    "consts-file" : String; "Additionally read names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    out           : String; "Output `.ixe` path. Defaults to a slug of the first name (e.g. `nat_add_comm.ixe`)."
    verbose;                "Print extraction details to stderr."

  ARGS:
    path : String; "Path to the source `.ixe` (e.g. from `ix compile`)."
]

def runShardGraphCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    | none =>
      let base := if envPath.endsWith ".ixe" then (envPath.dropEnd 4).toString else envPath
      base ++ ".graph"
  rsShardStaticGraphFFI envPath outPath
  IO.println s!"[graph] wrote {outPath}"
  return 0

def shardGraphCmd : Cli.Cmd := `[Cli|
  "graph" VIA runShardGraphCmd;
  "Dump a `.ixe`'s static block-level reference graph (`block`/`edge` text lines) for offline partitioner prototyping"

  FLAGS:
    out : String; "Output text path. Defaults to the env's base name with `.graph` (e.g. `init.ixe` → `init.graph`)."

  ARGS:
    path : String; "Path to the source `.ixe`."
]

def runShardCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let balancePct : Nat :=
    match p.flag? "balance" with
    | some flag => flag.as! Nat
    | none      => 5
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    | none      =>
      let base := if envPath.endsWith ".ixe" then (envPath.dropEnd 4).toString else envPath
      base ++ ".ixes"
  let shardsFlag : Option Nat := (p.flag? "shards").map (·.as! Nat)
  let maxRam     : Option Nat := (p.flag? "max-ram").map (·.as! Nat)

  match shardsFlag, maxRam with
  | some n, _ =>
    if n == 0 then
      p.printError "error: --shards must be positive"; return 1
    IO.println s!"Sharding {envPath} into {n} shards \
      (static strategy, balance ±{balancePct}%)"
    rsShardEnvStaticFFI envPath n.toUSize 0 balancePct.toUInt64 outPath
  | none, some gib =>
    if gib == 0 then
      p.printError "error: --max-ram must be positive"; return 1
    IO.println s!"Sharding {envPath} for a {gib} GiB process budget \
      (static block-shape seed, balance ±{balancePct}%)"
    rsShardEnvStaticFFI envPath 0 gib.toUInt64 balancePct.toUInt64 outPath
  | none, none =>
    IO.println s!"Sharding {envPath} for the default process budget, \
      MemTotal less 20% (static block-shape seed, balance ±{balancePct}%)"
    rsShardEnvStaticFFI envPath 0 0 balancePct.toUInt64 outPath
  if !outPath.isEmpty then
    IO.println s!"[shard] wrote {outPath}"
  return 0

end Ix.Cli.ShardCmd

open Ix.Cli.ShardCmd Ix.Cli.RefineCmd in
def shardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runShardCmd;
  "Partition a `.ixe` env into shards using the static strategy (no kernel run), sized for the host budget `ix prove` uses by default"

  FLAGS:
    shards       : Nat;    "Fixed number of shards N (overrides budget sizing)"
    "max-ram"    : Nat;    "Process RAM budget in GiB to size the partition for, with the same meaning as `ix prove --max-ram` (default: MemTotal less 20%). Pass it only when proving under a different budget, such as a harness's cgroup limit."
    balance      : Nat;    "Per-bisection balance tolerance, percent (default 5)"
    out          : String; "Output .ixes manifest path (default: env base name + `.ixes`, e.g. init.ixe → init.ixes)"

  ARGS:
    path : String; "Path to a serialized `.ixe` environment"

  SUBCOMMANDS:
    shardExtractCmd;
    shardGraphCmd;
    shardRefineCmd;
    shardClaimsCmd
]

end
