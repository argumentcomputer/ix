/-
  `ix shard <path.ixe>`: coarse min-cut partition of an environment
  into a shard manifest (`.ixes`) — the cluster-proving planner.
  Chunks are computed from serialized structure alone (no kernel
  run), so already-serialized env pieces can be shipped across the
  wire to separate prover machines (`ix shard extract` cuts a
  standalone `.ixe` closure per chunk). On a single box nothing plans:
  `ix prove --env` runs the whole env in one process and cuts spans at
  prover level by measurement, where the record's retained bytes reach
  the threshold derived from the RAM budget.

  Two strategies:
  - Static (no `--profile`): computed from the `.ixe` alone —
    byte-balanced min-cut over the env's static walk-edge nets (the
    relation that generates each shard's thin frontier, i.e. its real
    ingress), then a global rebalance post-pass toward equal predicted
    FFT cost (fitted model — constants and provenance in
    `ix_kernel::shard::STATIC_OWNED_PER_BYTE`). Requires `--shards N`.
    Measured against the profiled strategy on the 8-shard Init /
    24-shard Std harnesses: mean shard FFT −30%, max shard −44/−51%,
    stddev 17.7%→7.1% / 30.6%→8.9%.
  - Profiled (`--profile <path.ixprof>`): partition an `ix profile`
    run. Modes (precedence in `runShardCmd`): default / `--max-ram G`
    / `--max-cycles C` **bin-pack to a per-shard cycle/RAM cap** (no
    `--max-ram` ⇒ sized to detected system RAM); `--shards N` forces
    exactly `N` balanced min-cut shards.

  Both strategies write the same `.ixes` manifest and print a what-if
  report. The partitioner is self-contained — no external
  graph-library dependency.

  `ix shard extract <path.ixe>` is the pipeline's materialization step. It
  accepts either named roots (`--consts <n1,n2,…>`) or one immutable manifest
  work unit (`--shards <path.ixes> --shard K`) and writes the selected owned
  blocks plus their dependency closure as a standalone `.ixe`, without
  recompiling from source. The output carries the closure's genuine constant
  bytes, blobs, and reducibility hints, plus each closure constant's
  name→address entry, so it composes with everything that consumes a `.ixe`
  (`ix profile` → `ix shard`, `ix check-rs --consts`, the zkVM hosts,
  `bench-typecheck`).
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
  let shardsFlag : Option String := (p.flag? "shards").map (·.as! String)
  let shardFlag : Option Nat := (p.flag? "shard").map (·.as! Nat)
  let hasNamedInput :=
    (p.flag? "consts").isSome || (p.flag? "consts-file").isSome
  let quiet := !(p.flag? "verbose" |>.isSome)

  match shardsFlag, shardFlag with
  | some _, none =>
      p.printError "error: --shards requires --shard K"
      return 1
  | none, some _ =>
      p.printError "error: --shard requires --shards <path.ixes>"
      return 1
  | some manifestPath, some shard =>
      if hasNamedInput then
        p.printError "error: --shards/--shard cannot be combined with --consts or --consts-file"
        return 1
      let outPath : String :=
        match p.flag? "out" with
        | some flag => flag.as! String
        | none =>
          let base :=
            if envPath.endsWith ".ixe" then
              (envPath.dropEnd 4).toString
            else envPath
          s!"{base}.shard-{shard}.ixe"
      rsEnvExtractShardFFI envPath manifestPath (toString shard) outPath quiet
      IO.println s!"[extract] wrote {outPath} (manifest shard {shard})"
      return 0
  | none, none =>
      let names ← Ix.Cli.ConstsFile.gather p
      if names.isEmpty then
        p.printError "error: pass --consts/--consts-file or --shards <path.ixes> --shard K"
        return 1
      let outPath : String :=
        match p.flag? "out" with
        | some flag => flag.as! String
        -- `init.ixe --consts Nat.add_comm` → `nat_add_comm.ixe`.
        | none =>
          let slug := names[0]!.map fun c =>
            if c.isAlphanum then c.toLower else '_'
          s!"{slug}.ixe"
      rsEnvExtractFFI envPath names outPath quiet
      IO.println s!"[extract] wrote {outPath} ({names.size} root name(s))"
      return 0

def shardExtractCmd : Cli.Cmd := `[Cli|
  "extract" VIA runShardExtractCmd;
  "Extract named constants or one `.ixes` manifest shard + dependency closure from a `.ixe` into a standalone `.ixe`"

  FLAGS:
    consts        : String; "Comma-separated EXACT constant names (displayed form) to extract, e.g. `Nat.add_comm,String.append`. Same flag/shape as `ix check-rs --consts`. A mutual-block member extracts its whole block."
    "consts-file" : String; "Additionally read names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    shards        : String; "Path to a `.ixes` manifest. Extracts one immutable work unit and requires --shard K; cannot be combined with --consts/--consts-file."
    shard         : Nat;    "Zero-based shard index in --shards, with the same meaning as `ix prove --shard K`."
    out           : String; "Output `.ixe` path. Defaults to a slug of the first name, or `<env>.shard-K.ixe` in manifest mode."
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
    -- Fixed shard count only for now — the cap modes' cycle/RAM budgeting
    -- is calibrated against the profiled op counters, which the static
    -- profile does not carry.
    let some n := shardsFlag
      | p.printError "error: the static strategy (no --profile) requires \
          --shards N; --max-cycles/--max-ram budgeting needs --profile"
        return 1
    if maxCycles.isSome || maxRam.isSome then
      p.printError "error: --max-cycles/--max-ram require --profile (their \
        budget model is calibrated on profiled op counters)"
      return 1
    IO.println s!"Sharding {envPath} into {n} shards (static strategy, balance ±{balancePct}%)"
    rsShardEnvStaticFFI envPath (toString n) (toString balancePct) outPath
  | some espPath =>
    -- Profiled strategy: partition the `.ixprof`.
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
  "Coarse min-cut partition of a `.ixe` env into a `.ixes` shard manifest for cluster proving — no kernel run: statically with `--shards N`, or from an `ix profile` run via `--profile`. Prove the shards with `ix prove --env E --shards P.ixes [--shard K]`."

  FLAGS:
    profile      : String; "Path to a `.ixprof` from `ix profile`. When given, use the profiled strategy (cap budgeting / balanced min-cut over measured costs); when absent, the static strategy partitions the `.ixe` directly."
    shards       : Nat;    "Fixed number of shards N (required for the static strategy; overrides the profiled default budget sizing)"
    "max-cycles" : Nat;    "Per-shard guest-cycle budget (profiled strategy only)"
    "max-ram"    : Nat;    "Per-shard host-RAM budget, GiB (profiled strategy only; default: detected system RAM)"
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
