/-
  `ix shard <path.ixe> [--backend aiur|zisk]`: plan an environment's
  shard manifest (`.ixes`) for the proving pipeline.

  Backends (`--backend`, default `aiur`):
  - **aiur (default)**: the measured-manifest planner — ONE whole-env
    execution through the codegen'd Aiur kernel, cut into fine segments
    (quarter-budget trigger; sloppy cuts of small pieces are harmless),
    each measured exactly at seal, then grouped into shard-sized proof
    units under the exact RAM model's from-raws bound. Every emitted
    shard is under budget by construction. This is the plan phase of the
    plan → prove pipeline (prove = `ix check --prove --shards`, which
    re-measures each shard exactly and self-heals any that seal over).
    Costs a full env execution.
  - **zisk**: no kernel run. Two strategies:
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

  Every backend writes the same `.ixes` manifest format. The zisk
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
public import Ix.KernelCheck
public import Ix.Cli.ConstsFile
public import Ix.Aiur.Compiler
public import Ix.Aiur.Protocol
public import Ix.IxVM
public import Ix.IxVM.Toplevel

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

  let backend : String := ((p.flag? "backend").map (·.as! String)).getD "aiur"
  match backend with
  | "aiur" =>
    -- Aiur backend: the measured-manifest planner. One whole-env kernel
    -- execution, fine cuts measured exactly at seal, grouped under the
    -- exact RAM model's from-raws bound.
    if profileFlag.isSome || shardsFlag.isSome || maxCycles.isSome
        || maxRam.isSome then
      p.printError "error: --profile/--shards/--max-cycles/--max-ram are \
        `--backend zisk` options; the aiur backend plans by measuring \
        and takes only --out, --jobs, and --fail-fast"
      return 1
    let toplevel ← match IxVM.ixVM with
      | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
      | .ok t => pure t
    let compiled ← match toplevel.compile with
      | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
      | .ok c => pure c
    let segFunIdx ← match compiled.getFuncIdx `verify_claim with
      | some i => pure i
      | none => IO.eprintln "error: verify_claim missing"; return 1
    let blockFunIdx ← match compiled.getFuncIdx `verify_block with
      | some i => pure i
      | none => IO.eprintln "error: verify_block missing"; return 1
    let envHandle ← match Aiur.EnvHandle.fromIxe envPath with
      | .error e => IO.eprintln s!"EnvHandle.fromIxe {envPath}: {e}"; return 1
      | .ok h => pure h
    let workers := (p.flag? "jobs").map (·.as! Nat) |>.getD 0
    -- Planning wants the full reject inventory by default (a reject
    -- degrades its one fine segment, never the plan); --fail-fast
    -- restores halt-on-first for debugging runs.
    let failFast := if p.hasFlag "fail-fast" then "1" else "0"
    let aiurSystem := Aiur.AiurSystem.build compiled.bytecode
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
    IO.println s!"Planning {envPath} into measured shards \
      (budget: measured available RAM)"
    match aiurSystem.executeEnvProveWithEnv segFunIdx blockFunIdx envHandle
        (toString workers) failFast "1" outPath with
    | .error e => IO.eprintln s!"plan failed: {e}"; return 1
    | .ok () =>
      IO.println s!"[shard] wrote {outPath}"
      return 0

  | "zisk" =>
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
  | other =>
    p.printError s!"error: unknown --backend {other} (expected `aiur` or `zisk`)"
    return 1

end Ix.Cli.ShardCmd

open Ix.Cli.ShardCmd in
def shardCmd : Cli.Cmd := `[Cli|
  "shard" VIA runShardCmd;
  "Plan a `.ixe` env's shard manifest: `--backend aiur` (default) plans by executing — one whole-env kernel run with exact per-segment RAM measurement; `--backend zisk` partitions without a kernel run (statically with `--shards N`, or from an `ix profile` run via `--profile`)"

  FLAGS:
    backend      : String; "Proof backend the manifest targets. `aiur` (default): plan by EXECUTING — one whole-env run through the codegen'd Aiur kernel cut into fine segments, each measured exactly at seal, grouped into proof units under the exact RAM model's bound (budget: available RAM measured at run start; IX_SCAN_RAM_GIB overrides); every emitted shard is under budget by construction; prove the manifest with `ix check --prove --shards`. `zisk`: no kernel run — static byte-balanced min-cut from the `.ixe` alone (requires --shards N), or the profiled pipeline via --profile."
    jobs         : Nat;    "aiur backend: worker threads (default 0 = autoscale to the box)."
    "fail-fast";           "aiur backend: halt on the first kernel reject instead of recording it and degrading its fine segment (the default keeps going — a plan wants the full reject inventory)."
    profile      : String; "zisk backend: path to a `.ixprof` from `ix profile`. When given, use the profiled strategy (cap budgeting / balanced min-cut over measured costs); when absent, the static strategy partitions the `.ixe` directly."
    shards       : Nat;    "zisk backend: fixed number of shards N (required for the static strategy; overrides the profiled default budget sizing)"
    "max-cycles" : Nat;    "zisk backend: per-shard guest-cycle budget (profiled strategy only)"
    "max-ram"    : Nat;    "zisk backend: per-shard host-RAM budget, GiB (profiled strategy only; default: detected system RAM)"
    balance      : Nat;    "zisk backend: per-bisection balance tolerance, percent (default 5)"
    parallelism  : Nat;    "zisk backend: provers assumed for the prove-time estimate (profiled strategy only; default 1 = sequential)"
    out          : String; "Output .ixes manifest path (default: env base name + `.ixes`, e.g. init.ixe → init.ixes)"

  ARGS:
    path : String; "Path to a serialized `.ixe` environment"

  SUBCOMMANDS:
    shardExtractCmd;
    shardGraphCmd
]

end
