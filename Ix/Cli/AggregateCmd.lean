/-
  `ix aggregate --ixe E --ixes M <shard-proof>...`
  or `ix aggregate --ixc <cat.ixc> <member-root>...`
-/
module
public import Cli
public import Ix.Cli.FormalAggregate
public import Ix.Cli.CatalogAggregate

public section

namespace Ix.Cli.AggregateCmd

def runAggregateCmd (p : Cli.Parsed) : IO UInt32 := do
  let _ ← FormalAiur.selected p
  if let some ixc := (p.flag? "ixc").map (·.as! String) then
    return ← CatalogAggregate.aggregateCatalog p ixc
  FormalAggregate.run p

end Ix.Cli.AggregateCmd

open Ix.Cli.AggregateCmd in
def aggregateCmd : Cli.Cmd := `[Cli|
  aggregate VIA runAggregateCmd;
  "Wrap shard proofs and fold multi-shard manifests into one recursive aggregate"

  FLAGS:
    "gpu-device" : Nat; "Use this CUDA device with the Aiur host (requires a CUDA build)."
    "legacy"; "Retired legacy Aiur backend flag."
    "formal"; "Compatibility alias for the default certified Aiur backend; conflicts with --legacy."
    "aiur-artifact" : String; "Trusted formal IxVM artifact; otherwise compile/cache local sources."
    "aggr-artifact" : String; "Trusted formal aggregation artifact; otherwise compile/cache local sources."
    "shard-rows" : Nat; "Aiur: maximum rows per function/memory chip per trace shard (power of two; default 0, which lets the planner choose the largest shards within the RAM budget and, on CUDA, the device cell budget AIUR_TRACE_SHARD_MAX_CELLS, default 1.5e9). Small caps multiply recursive verification work."
    "retention" : String; "Aiur: auto, retain or regenerate (default auto)."
    "ixe" : String;  "Path to the serialized environment whose shards were proven. It must carry the role binding the shard claims are relative to."
    "ixes" : String; "Path to the shard manifest; its bisection tree determines join order."
    "ixc" : String;  "A .ixc catalog directory: join the aggregate roots of its members, one per member (`ix aggregate --ixe <piece> --ixes <manifest> --binding-proof <proof>` on each piece), into one root. Members whose role bindings have one literal class are joined first, in manifest order (cross-binding pairs, under the class), then the classes into a Catalog claim. Each join is proven as trace shards within --max-ram. A member's statement is its piece's canonical claim, or the claim of `<label>.ixes` when the catalog directory holds that shard manifest beside the piece."
    "plan-only";     "Validate coverage and print the wrap/join slot plan without loading or proving shard proofs."
    "no-cache";      "Bypass aggregate cache reads and intermediate cache writes; the root wrapper is still persisted unless --no-write."
    "texray";        "Stream per-phase `[texray]` timing/RSS lines (execute, witness, STARK stages of every slot) to stderr as each span closes."
    "no-write";      "Do not change the proof store or aggregate cache; useful with --reprove-slot for a read-only spot check."
    "reprove-slot" : Nat; "Recompute exactly Stage 2 slot N from verified cached immediate children, bypassing that slot's cache entry."
    "jobs" : Nat;    "Maximum concurrent aggregate slots (Aiur default 1; 0 uses available cores). Budget and CPU threads are divided among jobs."
    "max-ram" : Nat; "Total in-flight RAM budget in GiB (Aiur default 85% of available memory). Aiur rejects slots that cannot fit through trace sharding."
    "structural-above" : Nat; "Use structural joins when a node contains more than N subject leaves (default 0: every join)."
    "direct-joins";  "Accepted for compatibility; the aggregate controller always joins claims directly."
    "trace-shards";  "Prove each slot as a batch of trace shards within its share of --max-ram (the budget divided by --jobs) instead of one unbudgeted proof; a slot no shard count can fit fails the run."
    "exec-ahead" : Nat; "Slots executing ahead of the provers (default 1): a ready join executes and plans while the previous one proves, so one GPU prover never waits for an execution; each slot ahead holds its execution record. 0: each slot executes and proves on one worker, --jobs at a time."
    "wrap-root";     "Wrap the root proof, each wrap a proof that verifies the previous one, until the final proof is a single trace shard."
    "binding-proof" : String; "A proof of the `binding` claim for the env's role binding (`ix prove-binding`), as a file or store address. The shard claims (proven with `--assume-binding`) assume their binding, and the controller discharges that condition once, at the root and before --wrap-root wraps it; the final claim is the one an aggregate of claims that validate their binding states. With --subtree or --reprove-slot nothing is discharged: the printed proof still assumes the binding, and a later full run discharges it at the root."
    "subtree" : Nat; "Prove only the plan subtree rooted at slot N (slot numbers as --plan-only prints them) from the proofs of the leaves under it, and print that slot's proof address; root validation and --wrap-root do not apply. The proof is published through the aggregate cache, where a later full run finds it and proves only what is above it, needing no proofs of the shards under it. With --plan-only, print `subtree N shards: <ids>`, the --shards argument for `ix prove` over those leaves."
    "range" : Nat;   "Rejected: the aggregate controller never wraps a single claim; claims join directly."
    "report" : String; "Write summary JSON report to this path."

  ARGS:
    ...proofs : String; "Persisted proof wrapper addresses, in any order: shard claim proofs, and optionally aggregate proofs of plan slots. A claim proof is needed only for a shard that no supplied or verified cached aggregate above it covers (none with --plan-only or replay with aggregate children)."
]

end
