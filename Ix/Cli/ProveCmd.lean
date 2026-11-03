module
public import Cli
public import Ix.Cli.FormalAiur
public import Ix.Cli.FormalAggregate

/-!
  `ix prove`: generate a STARK proof against an `Ix.Claim`. Mirrors
  the CLI shape of `ix check`.
-/

public section

namespace Ix.Cli.ProveCmd

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  let _ ← FormalAiur.selected p
  if p.hasFlag "lanes" || p.hasFlag "aggregate" then
    FormalAggregate.runPipeline p
  else
    FormalAiur.run p true

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for an `Ix.Claim` (mirrors `ix check`'s CLI shape)"

  FLAGS:
    "gpu-device" : Nat; "Use this CUDA device with the Aiur host (requires a CUDA build)."
    "legacy"; "Retired legacy Aiur backend flag."
    "formal"; "Compatibility alias for the default certified Aiur backend; conflicts with --legacy."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact for --aggregate/--lanes; otherwise compile/cache local sources."
    "direct-joins"; "With --aggregate/--lanes: accepted for compatibility; claims always join directly."
    "structural-above" : Nat; "With --aggregate/--lanes: use structural joins above N subject leaves (default 0: every join). Verify with the same value."
    "range" : Nat; "Rejected: the aggregate controller never wraps a single claim; claims join directly."
    "no-cache"; "With --aggregate/--lanes: bypass aggregate cache reads and writes; leaf proofs still follow --no-index."
    "jobs" : Nat; "Aiur: CPU prover lanes for manifest claims or --aggregate (default 1; 0 uses available cores). One shared execution pool; the RAM budget and prover threads are divided among lanes."
    "aggregate"; "Aiur: prove manifest claims and their joins on the aggregate controller (CPU lanes, --jobs), check the root against the manifest's expected statement, and print it. Requires --ixe, --ixes and --trace-shards. --lanes selects this automatically on GPUs."
    "report" : String; "Aiur: write per-part plans, timings and persisted proof addresses to this JSON file (with --ixes). With --aggregate/--lanes only the verified root is written; progress is the controller's `[lanes]` log."
    "shard-rows" : Nat; "Aiur: maximum rows per function/memory chip per trace shard (power of two; default 0, which lets the planner choose the largest shards within the RAM budget and, on CUDA, the device cell budget AIUR_TRACE_SHARD_MAX_CELLS, default 1.5e9). Small caps multiply recursive verification work."
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first."
    "texray";           "Stream per-phase `[texray]` timing/RSS lines (execute, witness, STARK stages) to stderr as each span closes."
    "ixe"   : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env. The file must carry a role binding: its claims are relative to it."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--ixe` env (single proof, skips per-const iteration)."
    "ixes"  : String;   "Path to a `.ixes` shard manifest (with --ixe). With --shard K: prove shard K. Without --shard: prove every shard in the partition."
    "shard" : Nat;      "0-based shard index K (with --ixes and --ixe): prove that one shard's CheckEnv claim."
    "shards" : String;  "With --ixes and no --shard: prove only these leaves — `K`, `a-b`, or a comma list of those — in one process (one env load); every other leaf is carried over unchanged by --out-ixes."
    "out-ixes" : String; "Write the partition this run actually proved — splits included — as a `.ixes` manifest to this path: the manifest `ix verify --ixes` checks these proofs against, and the one the next run of this env should start from. Skipped if any shard failed."
    "binding-proof" : String; "With --lanes/--aggregate: a proof of the `binding` claim for the env's role binding (`ix prove-binding`), as a file or store address. Every claim then assumes its binding instead of validating it, and the controller discharges that condition once, at the root and before the root is wrapped, so the binding's roles are validated once per aggregate rather than in every claim."
    "assume-binding";  "With --ixes: prove each shard's claim assuming the env's role binding meets the specifications (validator 4) instead of validating its roles in every shard proof. With --lanes/--aggregate it requires --binding-proof, which discharges the assumption at the root; otherwise `ix aggregate --binding-proof` discharges it, and `ix verify --binding-proof` checks the claims beside a proof of the binding claim."
    "exec-only";        "Execute each shard and measure its projected prover peak, splitting over-budget shards as usual, but never start a STARK. The cheap way to audit a partition's split behavior at scale."
    "trace-shards";     "Prove an over-budget shard as a batch of trace shards that each fit --max-ram, from one execution, instead of cutting it into parts; a shard no trace-shard count can fit stops the run rather than being cut. With --exec-only, reports the planned shard count and the heaviest shard's projected peak without proving."
    "retention" : String; "With --trace-shards: what the batch keeps between its two rounds — `retain` (every shard's stage 1, nothing recomputed), `regenerate` (headers only; each shard rebuilt for round two), or `auto` (default: retain when the RAM model says the retained batch fits --max-ram). Fixing it lets one plan be measured under both policies."
    "lanes" : Nat;      "With --ixes and --trace-shards: prove on N GPUs using a shared execution pool. --max-ram and --exec-jobs are per-GPU values. Environment claims exceeding the 128 GiB record ceiling (AIUR_RECORD_MAX_BYTES overrides it) are bisected automatically. Rerunning resumes the checkpointed partition and completed proofs. --out-ixes writes the final partition. Prints the verified root address on stdout."
    "exec-jobs" : Nat;  "Concurrent executions ahead of the provers. Aiur defaults to --jobs; with --aggregate/--lanes the value is per lane and 0 (the default) divides the available cores among the lanes. Records and prover workspaces share --max-ram."
    "plan-only";        "Aiur: print selected manifest leaves and RAM reservations without execution."
    "skip-proven";      "With --ixes: before executing a leaf, look its claim up in the shard-proof index (`~/.ix/cache/shard-proofs/<claim-digest>`); a recorded proof that decodes, bundles exactly that claim and verifies natively is reused — its address printed, nothing executed — instead of proving again. How a partially proved partition resumes after a refinement."
    "no-index";         "Neither read nor write the shard-proof index (every persisted proof is normally recorded there under its claim digest)."
    "max-ram" : Nat;    "Aiur: total RAM budget across --jobs in GiB, default 85% of available memory."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
