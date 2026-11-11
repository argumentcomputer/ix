module
public import Cli
public import Ix.Cli.FormalAiur
public import Ix.Cli.FormalAggregate
public import Ix.Cli.CompressCmd

/-!
  `ix prove`: generate a STARK proof against an `Ix.Claim`. Mirrors
  the CLI shape of `ix check`.

  With `--ixe` and `--ixes`, every manifest shard's claim is proven and its
  proof address printed: one leaf proof per shard, which `ix verify --ixes`
  checks and `ix aggregate` joins. `--aggregate` (CPU), `--lanes` (GPUs) or
  `--compress` instead prove the leaves and their recursive joins through one
  resident controller and print the verified root.
-/

public section

namespace Ix.Cli.ProveCmd

/-- Flags the aggregation pipeline does not read. -/
private def nonAggregateFlags : Array String :=
  #["shards-only", "assume-binding", "keep-going", "claim", "cells"]

def runProveCmd (p : Cli.Parsed) : IO UInt32 := do
  let fresh := p.hasFlag "fresh"
  if fresh && p.hasFlag "skip-proven" then
    IO.eprintln "--fresh cannot be combined with --skip-proven"
    return 1
  if fresh then IO.eprintln "[prove] fresh: bypassing earlier proof checkpoints"
  let aggregate := p.hasFlag "lanes" || p.hasFlag "aggregate" || p.hasFlag "compress"
  if aggregate then
    for flag in nonAggregateFlags do
      if p.hasFlag flag then
        IO.eprintln s!"--{flag} cannot be combined with --aggregate, --lanes or --compress"
        return 1
  let ixePath : Option String := (p.flag? "ixe").map (·.as! String)
  -- Compression continues from a whole environment's aggregate root.
  let canCompress := ixePath.isSome && p.hasFlag "ixes"
    && !p.hasFlag "shard" && !p.hasFlag "shards" && !p.hasFlag "distributed" && !p.hasFlag "exec-only"
  let compress? ← match (p.flag? "compress").map (·.as! String) with
    | none =>
      if p.hasFlag "fixed-root" || p.hasFlag "dev-kzg-srs" || p.hasFlag "dev-final-srs" || p.hasFlag "compression-out" then
        IO.eprintln "--fixed-root, --dev-kzg-srs, --dev-final-srs and --compression-out require --compress"; return 1
      pure none
    | some output =>
      if !canCompress then
        IO.eprintln "--compress requires aggregating a whole environment (--ixe and --ixes)"; return 1
      match Ix.Cli.CompressCmd.finalOf output with
      | .error e => IO.eprintln s!"--compress: {e}"; return 1
      | .ok finalProof =>
        let opts : Ix.Cli.CompressCmd.Options := {
          finalProof
          fresh
          out := (p.flag? "compression-out").map (·.as! String)
          devKzgSrs := p.hasFlag "dev-kzg-srs"
          devFinalSrs := p.hasFlag "dev-final-srs"
          fixedRoot := (p.flag? "fixed-root").map (·.as! String) }
        try
          IO.eprintln s!"Compression will use {← Ix.Cli.CompressCmd.preflight p opts}."
          pure (some opts)
        catch e => IO.eprintln s!"--compress: {e}"; return 1
  if p.hasFlag "lanes" || p.hasFlag "aggregate" || compress?.isSome then
    let onRoot : Address → IO Unit := match compress? with
      | none => fun _ => pure ()
      | some opts => fun addr => do
        IO.println (toString (← Ix.Cli.CompressCmd.compressRoot p addr opts))
    FormalAggregate.runPipeline p onRoot
  else
    FormalAiur.run p true

end Ix.Cli.ProveCmd

open Ix.Cli.ProveCmd in
def proveCmd : Cli.Cmd := `[Cli|
  prove VIA runProveCmd;
  "Generate a STARK proof for an `Ix.Claim` (mirrors `ix check`'s CLI shape)"

  FLAGS:
    "gpu-device" : Nat; "Use this CUDA device with the Aiur host (requires a CUDA build)."
    "aiur-artifact" : String; "Trusted exported formal IxVM artifact; otherwise compile/cache local sources."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "aggr-artifact" : String; "Trusted formal aggregation artifact for --aggregate/--lanes; otherwise compile/cache local sources."
    "aggr-artifact-digest" : String; "Refuse an aggregation artifact whose BLAKE3 digest is not this one."
    "direct-joins"; "With --aggregate/--lanes: join raw IxVM leaves directly instead of wrapping each leaf first (higher RAM)."
    "structural-above" : Nat; "With --aggregate/--lanes: use structural joins above N subject leaves (default 4096; 0 means every join)."
    "range" : Nat; "With --aggregate/--lanes: wrap a leaf proof with more than N trace shards through a range-sum tree (default 0: wrap whole)."
    "no-cache"; "With --aggregate/--lanes: bypass aggregate cache reads and writes; leaf proofs still follow --no-index."
    "fresh"; "Bypass prior leaf, aggregation and compression proofs, replacing their cache entries with newly verified results. Reuse parameters, proving keys and fixed preprocessing. Incompatible with --skip-proven."
    "jobs" : Nat; "Aiur: CPU prover lanes for manifest claims or --aggregate (default 1; 0 uses available cores). One shared execution pool; the RAM budget and prover threads are divided among lanes."
    "aggregate"; "Aiur: prove manifest leaves and ready recursive joins through one resident controller on CPU, then verify and print the root. Requires --ixe and --ixes. --lanes does the same on GPUs, and --compress implies it."
    "report" : String; "Aiur: write per-part plans, timings and persisted proof addresses to this JSON file."
    "shard-rows" : Nat; "Aiur: maximum rows per function/memory chip per trace shard (power of two; default 0, which lets the planner choose the largest shards within the RAM budget and, on CUDA, the device cell budget AIUR_TRACE_SHARD_MAX_CELLS, default 1.5e9). Small caps multiply recursive verification work."
    "keep-going";       "Continue past failures and report them at the end instead of halting on the first."
    "texray";           "Stream per-phase `[texray]` timing/RSS lines (execute, witness, STARK stages) to stderr as each span closes."
    "ixe"   : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env. The file must carry a role binding: its claims are relative to it."
    "claim" : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, proves the persisted claim against the `--ixe` env (single proof, skips per-const iteration)."
    "ixes"  : String;   "Path to a `.ixes` shard manifest (with --ixe). By default, prove every shard's claim and print each proof's address; `ix verify --ixes` checks them and `ix aggregate` joins them. With --shard K or --shards: prove only those shards. With --aggregate, --lanes or --compress: also join the shard proofs into one root and print its address."
    "shard" : Nat;      "0-based shard index K (with --ixes and --ixe): prove that one shard's CheckEnv claim."
    "shards" : String;  "With --ixes and no --shard: prove only these leaves — `K`, `a-b`, or a comma list of those — in one process (one env load); every other leaf is carried over unchanged by --out-ixes."
    "shards-only";      "With --ixe and --ixes: prove each shard's claim and stop. This is the default; the flag makes it explicit and rejects --aggregate, --lanes and --compress."
    "out-ixes" : String; "Write the partition this run actually proved — splits included — as a `.ixes` manifest to this path: the manifest `ix verify --ixes` checks these proofs against, and the one the next run of this env should start from. Skipped if any shard failed."
    "binding-proof" : String; "With --aggregate, --lanes or --compress: a proof of the `binding` claim for the env's role binding (`ix prove-binding`). Every claim then assumes its binding instead of validating it, and the root discharges that condition once, so the binding's roles are validated once per aggregate rather than in every claim."
    "assume-binding";  "Without aggregation: prove each claim assuming the env's role binding meets the specifications (validator 4) instead of validating its roles in every proof; `ix aggregate --binding-proof` or `ix verify --binding-proof` then discharges that condition once. When aggregating, pass --binding-proof instead."
    "exec-only";        "Execute each shard and measure its projected prover peak, splitting over-budget shards as usual, but never start a STARK. The cheap way to audit a partition's split behavior at scale."
    "trace-shards";     "With --ixe and --ixes, without aggregation: never cut a manifest shard into parts. Every proof is already a batch of trace shards planned within --max-ram, from one execution; by default a shard whose batch still cannot fit is cut into parts by blocks and each part proven, and with this flag it stops the run instead. Aggregation (--aggregate, --lanes, --compress) bisects such a leaf and joins its parts back into the leaf's statement, so this flag is accepted there and changes nothing."
    "retention" : String; "What a trace-shard batch keeps between its two rounds — `retain` (every shard's stage 1, nothing recomputed), `regenerate` (headers only; each shard rebuilt for round two), or `auto` (default: retain when the RAM model says the retained batch fits --max-ram). Fixing it lets one plan be measured under both policies."
    "distributed";      "With --ixes and no --shard: prove the WHOLE environment as one `CheckEnv` claim, with one worker record per chunk — each shard of the manifest is one worker's chunk, the constants it owns — executing in parallel (calls into other workers' constants cross records through the lookup argument) and every record's trace shards in one batch. Writes one proof; no manifest is refined."
    "cells" : Nat;      "With --distributed: per-shard committed-cell budget each worker record is planned to (e.g. 1800000000 for a 96 GB device). 0 (default) proves each record as one shard."
    "lanes" : Nat;      "With --ixe and --ixes: prove and aggregate on N GPUs using a shared execution pool. --max-ram and --exec-jobs are per-GPU values. Environment claims exceeding the 128 GiB record ceiling (AIUR_RECORD_MAX_BYTES overrides it) are bisected automatically. Rerunning resumes the checkpointed partition and completed proofs. --out-ixes writes the final partition. Prints the verified root address on stdout."
    "exec-jobs" : Nat;  "Concurrent executions ahead of the provers. Aiur defaults to --jobs (or available cores with --lanes); 0 uses available cores. Positive values are per GPU with --lanes. Records and prover workspaces share --max-ram. Distributed Aiur first measures call counts and trace shapes, then replays one record at a time; regenerate replays again for round two."
    "plan-only";        "Aiur: print selected manifest leaves and RAM reservations without execution."
    "skip-proven";      "With --ixes: before executing a leaf, look its claim up in the shard-proof index (`~/.ix/cache/formal-shard-proofs/<claim-digest>`); a recorded proof that decodes, bundles exactly that claim and verifies natively is reused — its address printed, nothing executed — instead of proving again. How a partially proved partition resumes after a refinement. Aggregation always resumes this way."
    "no-index";         "Neither read nor write the shard-proof index (every persisted proof is normally recorded there under its claim digest)."
    "compress" : String; "With --ixe and --ixes: compress the aggregate root to `kzg`, `plonk` or `groth16` and print the compressed proof's address after the root's. The setup is checked before proving."
    "compression-out" : String; "With --compress: directory for compression stage files; --fresh replaces prior stages there."
    "fixed-root" : String; "With --compress: override the bundled release normalization layout with a layout from `ix compress layout`."
    "dev-kzg-srs";      "With --compress: generate local development inner KZG parameters. Final Groth16/PLONK proofs also require --dev-final-srs."
    "dev-final-srs"; "With --compress groth16 or plonk: generate and cache local development final keys. With --dev-kzg-srs, no Ignition parameters are required."
    "max-ram" : Nat;    "Aiur: total RAM budget across --jobs in GiB, default 85% of available memory."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to prove. With none, iterate every named constant in the env (sorted)."
]

end
