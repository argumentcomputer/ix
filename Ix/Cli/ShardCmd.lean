/-
  `ix shard <path.ixe> [--profile <path.ixprof>]`: partition an environment
  into shards for the Aiur (IxVM) checking pipeline.

  Two strategies:
  - **Static (default, no `--profile`)**: computed from the `.ixe` alone —
    no out-of-circuit kernel run. Byte-balanced min-cut over the env's
    static walk-edge nets (the relation that generates each shard's thin
    frontier, i.e. its real ingress), then a global rebalance post-pass
    toward equal predicted Aiur FFT cost (fitted model — constants and
    provenance in `ix_kernel::shard::STATIC_OWNED_PER_BYTE`). `--shards N`
    fixes the count; `--max-ram G` seeds it from the same static block-shape
    score, mildly superlinear in both library scale and inverse RAM budget.
    Measured against the profiled strategy on the 8-shard Init / 24-shard Std
    harnesses: mean shard FFT −30%, max shard −44/−51%, stddev 17.7%→7.1% /
    30.6%→8.9%.
  - **Profiled (`--profile <path.ixprof>`)**: the original pipeline over an
    `ix profile` run, unchanged. Modes (precedence in `runShardCmd`):
    default / `--max-ram G` / `--max-cycles C` **bin-pack to a per-shard
    cycle/RAM cap** (no `--max-ram` ⇒ sized to detected system RAM);
    `--shards N` forces exactly `N` balanced min-cut shards.

  Both write the same `.ixes` manifest and print a what-if report. The
  partitioner is self-contained — no external graph-library dependency.

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
public import Ix.Common
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

def runShardGraphCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- `init.ixe` → `init.graph`, mirroring the `.ixprof` default naming.
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
  let profileFlag : Option String := (p.flag? "profile").map (·.as! String)
  -- Old CLI shape took the `.ixprof` positionally; catch it so scripts
  -- fail loudly instead of parsing a profile as an env.
  if profileFlag.isNone && envPath.endsWith ".ixprof" then
    p.printError "error: the positional argument is now the `.ixe` env; \
      pass the profile via --profile <path.ixprof> (or drop it for the \
      static strategy)"
    return 1
  let balancePct : Nat :=
    match p.flag? "balance" with
    | some flag => flag.as! Nat
    | none      => 5
  let outPath : String :=
    match p.flag? "out" with
    | some flag => flag.as! String
    -- Default manifest mirrors the env's base name: `init.ixe` →
    -- `init.ixes` (not `init.ixe.ixes`).
    | none      =>
      let base := if envPath.endsWith ".ixe" then (envPath.dropEnd 4).toString else envPath
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

  match profileFlag with
  | none =>
    -- STATIC strategy (no out-of-circuit profiling): byte-balanced min-cut
    -- over the env's walk-edge nets + predicted-FFT rebalance post-pass.
    -- `--shards N` fixes the count. Under `--max-ram G`, Rust chooses a
    -- seed only after building the static block profile: the fitted owned
    -- score sees both bytes and their per-block shape, unlike `.ixe` file
    -- size. Boundaries and budget fitting are still measured where execution
    -- happens anyway (the prove gate splits over-budget shards inline and the
    -- corrected manifest remembers the leaves).
    if maxCycles.isSome then
      p.printError "error: --max-cycles requires --profile (its budget \
        model is calibrated on profiled op counters)"
      return 1
    match shardsFlag, maxRam with
    | some n, _ =>
      if n == 0 then
        p.printError "error: --shards must be positive"; return 1
      IO.println s!"Sharding {envPath} into {n} shards \
        (static strategy, balance ±{balancePct}%)"
      rsShardEnvStaticFFI envPath (toString n) "0" (toString balancePct) outPath
    | none, some gib =>
      if gib == 0 then
        p.printError "error: --max-ram must be positive"; return 1
      IO.println s!"Sharding {envPath} for a {gib} GiB prover budget \
        (static block-shape seed, balance ±{balancePct}%)"
      rsShardEnvStaticFFI envPath "0" (toString gib) (toString balancePct) outPath
    | none, none =>
      p.printError "error: the static strategy (no --profile) requires \
        --shards N or --max-ram G"
      return 1
  | some espPath =>
    -- Profiled strategy, unchanged: partition the `.ixprof`.
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
  "Partition a `.ixe` env into shards: static strategy by default (`--shards N`, no kernel run), or the profiled pipeline via `--profile <path.ixprof>`"

  FLAGS:
    profile      : String; "Path to a `.ixprof` from `ix profile`. When given, use the profiled strategy (cap budgeting / balanced min-cut over measured costs); when absent, the static strategy partitions the `.ixe` directly."
    shards       : Nat;    "Fixed number of shards N (static strategy; overrides --max-ram sizing and the profiled default budget sizing)"
    "max-cycles" : Nat;    "Per-shard guest-cycle budget (profiled strategy only)"
    "max-ram"    : Nat;    "Per-shard prover-RAM budget, GiB. Static strategy: seed the shard count from the `.ixe` block-shape score (serialized block size + a superlinear large-body term), with fitted scale and budget exponents anchored at Mathlib; the execution gate measures and corrects every boundary. Profiled strategy: budget from measured op counters (default: detected system RAM)."
    balance      : Nat;    "Per-bisection balance tolerance, percent (default 5)"
    parallelism  : Nat;    "Provers assumed for the prove-time estimate (profiled strategy only; default 1 = sequential)"
    out          : String; "Output .ixes manifest path (default: env base name + `.ixes`, e.g. init.ixe → init.ixes)"

  ARGS:
    path : String; "Path to a serialized `.ixe` environment"

  SUBCOMMANDS:
    shardExtractCmd;
    shardGraphCmd
]

end
