/-
  `ix check`: execute the IxVM Aiur kernel over a Lean or `.ixe`
  environment, one constant at a time.
  The Rust kernel typechecker that used to live under this name is now `ix check-rs`.

  Usage shape:

      ix check Nat.add_comm                            # from compiled-in Lean env
      ix check --ixe arena.ixe foo bar baz             # from .ixe, named targets
      ix check --ixe arena.ixe                         # iterate every named const
      ix check --interp Nat.add_comm                   # Aiur interpreter (richer errors)
      ix check --stats-out STATS Nat.add_comm          # redirect per-circuit stats

  Stats print when exactly one constant is targeted. Multi-target +
  whole-env iteration both suppress stats so the log stays usable.
  The Rust-side `[compile_env]` / `[Env::put]` progress logs are off
  unless `IX_VERBOSE=1`; they add nothing at this layer.
-/
module
public import Cli
public import Ix.Shard.Check

public section
namespace Ix.Cli.CheckCmd
open Ix.Check Ix.Shard Ix.Shard.Check

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  let interpMode : Option String := (p.flag? "interp").map (·.as! String)
  let interpSource := interpMode == some "source"
  let useBytecode := interpMode == some "bytecode"
  match interpMode with
  | none | some "source" | some "bytecode" => pure ()
  | some other =>
    IO.eprintln s!"error: --interp expects \"source\" or \"bytecode\", got \"{other}\""
    return 1
  let keepGoing := p.hasFlag "keep-going"
  let statsOut : Option String :=
    (p.flag? "stats-out").map (·.as! String)
  let ixePath : Option String :=
    (p.flag? "ixe").map (·.as! String)
  let claimHex : Option String :=
    (p.flag? "claim").map (·.as! String)
  let names := (p.variableArgsAs! String).toList
  let ixesPath := (p.flag? "ixes").map (·.as! String)
  let shardK := (p.flag? "shard").map (·.as! Nat)
  -- a single targeted constant, a `--claim`, or a single shard each print
  -- per-circuit stats; whole-env / whole-partition iteration suppresses them.
  let printStats := names.length == 1 || claimHex.isSome || (ixesPath.isSome && shardK.isSome)
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  -- `runOne` consumes `(claim, envHandle?, target, label)`. For the
  -- codegen path it dispatches via `runCompiled`. For `--interp`
  -- it builds a `ClaimWitness` from the target — `.leanW` is
  -- already a witness; `.addr` would require running the Rust
  -- witness builder Lean-side, which `--interp` is meant to
  -- bypass. So `--interp` rejects `.addr`/`.shard` targets here;
  -- the legacy `runShardCheckManifest` path is used for `--interp`
  -- shard mode.
  let runOne : Ix.Claim → Option Aiur.EnvHandle → Target → String → IO UInt32 ←
    if interpSource then do
      let decls ← match toplevel.mkDecls with
        | .error e => IO.eprintln s!"mkDecls failed: {e}"; return 1
        | .ok d => pure d
      let go (_ : Ix.Claim) (_ : Option Aiur.EnvHandle) (target : Target)
          (label : String) : IO UInt32 :=
        match target with
        | .leanW w => runInterp decls w label
        | _ => do
          IO.eprintln s!"{label}: --interp requires a Lean witness; \
            addr/shard targets unreachable here"
          pure 1
      pure go
    else do
      let compiled ← match toplevel.compileWithGroups IxVM.functionGroups with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let go (_ : Ix.Claim) (envHandle? : Option Aiur.EnvHandle) (target : Target)
          (label : String) : IO UInt32 :=
        runCompiled compiled printStats statsOut useBytecode envHandle? target label
      pure go
  match ixePath, ixesPath, shardK with
  | some ixe, some manifest, some k =>
    if interpSource then
      return (← runShardCheckManifest manifest ixe k
        (fun c w l => runOne c none (.leanW w) l))
    else do
      let compiled ← match toplevel.compileWithGroups IxVM.functionGroups with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      return (← runShardCheckManifestNative manifest ixe k compiled printStats statsOut useBytecode)
  | some ixe, some manifest, none   =>
    if interpSource then
      return (← runShardCheckAll manifest ixe ((p.flag? "jobs").map (·.as! Nat))
        (fun c w l => runOne c none (.leanW w) l))
    else do
      let compiled ← match toplevel.compileWithGroups IxVM.functionGroups with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      let json? := (p.flag? "json").map fun f =>
        (f.as! String, ((p.flag? "json-name").map (·.as! String)).getD "env")
      -- `--ram-budget G` gates the audit; `--ram-budget 0` detects this
      -- machine's budget (85% of MemAvailable, fail closed); omitted = the
      -- plain batch check, no gate.
      let (maxRamBytes, budgetSource) ← match (p.flag? "ram-budget").map (·.as! Nat) with
        | none => pure (0, "none")
        | some g =>
          if g > 0 then pure (g * gibBytes, "flag")
          else
            let b ← Aiur.detectedRamBudgetBytes
            if b == 0 then
              IO.eprintln "--ram-budget 0: cannot detect MemAvailable (/proc/meminfo unreadable)"
              return 1
            IO.println s!"[split-audit] budget {toGib b} GiB (detected: 85% of MemAvailable)"
            pure (b, "detected")
      let selection? ← match (p.flag? "shards").map (·.as! String) with
        | none => pure none
        | some s => match parseShardSelection s with
          | .error e => IO.eprintln s!"error: {e}"; return 1
          | .ok ids => pure (some ids)
      return (← runShardBatchNative manifest ixe
        ((p.flag? "jobs").map (·.as! Nat)) compiled useBytecode json?
        maxRamBytes ((p.flag? "out-ixes").map (·.as! String))
        { selection := selection?, report := (p.flag? "report").map (·.as! String),
          command := s!"ix check --ixe {ixe} --ixes {manifest}", budgetSource })

  | _, _, _ =>
    -- `--jobs N` (N ≠ 1) with an `--ixe` env and no `--claim` takes the
    -- parallel batch path: one FFI call, rayon over the target list,
    -- each claim checked over task-private data. `--jobs 1` (or no
    -- flag) keeps the sequential per-claim loop unchanged.
    match (p.flag? "jobs").map (·.as! Nat), ixePath with
    | some jobs, some ixe =>
      if jobs != 1 && !interpSource && claimHex.isNone then
        runBatchCheck ixe names jobs toplevel useBytecode
      else
        forEachClaim ixePath claimHex names keepGoing "check" interpSource
          runOne
    | _, _ =>
      forEachClaim ixePath claimHex names keepGoing "check" interpSource
        runOne

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck Lean / `.ixe` constants through the IxVM Aiur kernel"

  FLAGS:
    interp : String;        "Use an interpreter instead of the codegen'd IxVM Rust kernel. Modes: `source` = Aiur source interpreter (richer per-execution error diagnostics, slowest); `bytecode` = generic Aiur bytecode interpreter (skips the regen + cargo rebuild cycle when iterating on `Ix/IxVM/*.lean`). Omit the flag entirely for the native codegen kernel."
    "keep-going";           "Continue past failures and report them at the end instead of halting on the first."
    "ixe"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--ixe` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Redirect the per-circuit statistics dump to this file (only used when exactly one constant is targeted)."
    "ixes"      : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: check the constants owned by shard K (ingress their closure, skip the frontier). Without --shard: check every shard of the partition concurrently, after a coverage check."
    "shard"     : Nat;      "0-based shard index K (with --ixe + --ixes): check the constants owned by shard K of the manifest's partition."
    "jobs"      : Nat;      "Parallelism. With --ixes (no --shard): max shards checked concurrently (default: all at once). With --ixe alone and N ≠ 1: check the targeted constants on N Rust threads (0 = all cores), each claim over its own private record — peak RAM is bounded by N in-flight claim closures."
    "json"      : String;   "With --ixes (no --shard): append one env-keyed results row (see Ix.Benchmark.Results) for the batch to this file — check-time, throughput, peak-rss, constants, shards. Used by `ix bench run --backend aiur-sharded-env`."
    "json-name" : String;   "Row key for the --json row (default: `env`)."
    "ram-budget" : Nat;     "The destination prove box's per-shard RAM budget, GiB (with --ixes, no --shard): after the batch, cut every shard whose projected prover peak exceeds the budget into the peak model's suggested part count and re-batch the parts, wave by wave, until everything fits — the exec-only split audit. Under-filled partitions get a printed suggestion (the shard count the measured total says would fit), never an extra execution: re-shard with --shards N and let the next run's mandatory executions verify it inline. Same unit and model as `ix prove --max-ram`, but no auto-detection: the budget describes the prove box the partition is destined for, not the machine running the check. Omit for a plain check."
    "out-ixes"  : String;   "With --ram-budget: write the partition the wave loop actually validated as a refinement of the source manifest — untouched leaves keep their records, ids and aggregation-tree positions, each split leaf becomes a subtree over its parts. Skipped if any shard failed. The manifest the next run of this env should start from."
    "shards"    : String;   "With --ixes (no --shard): restrict the batch to these leaves — `K`, `a-b`, or a comma list of those. Every other leaf is left untouched (and, with --out-ixes, carried over unchanged)."
    "report"    : String;   "With --ixes (no --shard): write the provisional JSON audit report (`ix-refine/0`: per-leaf status, predicted peaks, claim digests, split parts with their new ids, failures) to this path."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

end
