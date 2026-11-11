module
public import Cli
public import Ix.Cli.FormalAiur
public import Ix.TracingTexray

/-!
  `ix check`: execute the IxVM Aiur kernel over a Lean or `.ixe`
  environment, one constant at a time or over a `.ixes` shard manifest.

  When `IX_TEXRAY_JSON` names a file, every claim execution's
  `aiur/execute` span is written to it as JSON Lines
  (`{"span","seconds"}`). Execution runs in this process, so a manifest
  check with several jobs writes every shard's span to the one file.
-/

public section
namespace Ix.Cli.CheckCmd

/-- Install the texray subscriber with its JSON sink at `IX_TEXRAY_JSON`,
    when that names a file. The sink truncates the file. -/
def texraySink : IO Unit := do
  let some path ← IO.getEnv "IX_TEXRAY_JSON" | return
  if path.isEmpty then return
  TracingTexray.init { namePrefixes := "aiur/", trackRam := false, streaming := false }
  TracingTexray.jsonSink path

def runCheckCmd (p : Cli.Parsed) : IO UInt32 := do
  texraySink
  FormalAiur.run p false

end Ix.Cli.CheckCmd

open Ix.Cli.CheckCmd in
def checkCmd : Cli.Cmd := `[Cli|
  check VIA runCheckCmd;
  "Typecheck Lean / `.ixe` constants through IxVM"

  FLAGS:
    "gpu-device" : Nat; "Use this CUDA device with the Aiur host (requires a CUDA build)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "keep-going";           "Continue past failures and report them at the end instead of halting on the first."
    "ixe"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--ixe` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Write raw per-circuit measurements and Lean-computed FFT costs as JSON (use with one target)."
    "ixes"      : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: check the constants owned by shard K (ingress their closure, skip the frontier). Without --shard: check every shard of the partition concurrently, after a coverage check."
    "shard"     : Nat;      "0-based shard index K (with --ixe + --ixes): check the constants owned by shard K of the manifest's partition."
    "jobs"      : Nat;      "Concurrent manifest claims, default 1 (0 = all cores), sharing the RAM budget and CPU threads."
    "json"      : String;   "With --ixe and --ixes: write one benchmark results row (`Ix.Benchmark.Results`: constants, shards, fft-cost, check-time, throughput, peak-rss) to this file, keyed by --json-name. A failed leaf marks the row rejected and exits 3."
    "json-name" : String;   "Row key for the --json row (default: `env`)."
    "ram-budget" : Nat;     "Total RAM budget in GiB, shared among --jobs. Each leaf is executed and its proof planned against its share; a leaf whose trace-shard batch cannot fit is cut into parts by blocks and the parts checked. Without it, leaves are only executed."
    "out-ixes"  : String;   "With --ixes and --ram-budget: write the partition this run validated, splits included, as a refinement of the source manifest. Skipped if any leaf failed."
    "shards"    : String;   "With --ixes (no --shard): restrict the batch to these leaves — `K`, `a-b`, or a comma list of those."
    "skip-proven";          "With --ixes: a leaf whose claim has a proof in the shard-proof index (`~/.ix/cache/formal-shard-proofs`) that decodes, bundles exactly that claim and verifies is settled by it: not executed, and never cut. `ix shard refine` uses this so a refinement never orphans a proof."
    "report"    : String;   "Write the ix-formal-run/1 report to this path."
    "batch-time" : String;  "With --ixes (no --shard): write the wall-clock seconds of executing the selected shards, after the env load and before the report, and the constants they own, to this path as JSON (`seconds`, `constants`)."
    "plan-only";            "Print selected manifest leaves and RAM reservations without execution."
    "assume-binding";       "Check assuming the environment's role binding meets the specifications."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

end
