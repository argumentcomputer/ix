module
public import Lean.Data.Name
public import Lean.Declaration
public import Ix.Address

/-!
  Environment extraction and static sharding FFI bindings.
-/

public section

namespace Ix.KernelCheck

/-- Kernel or compiler check error returned by test and CLI check helpers. -/
inductive CheckError where
  | kernelException (msg : String)
  | compileError (msg : String)
  deriving Repr, BEq

def CheckError.message : CheckError → String
  | .kernelException m => s!"kernel: {m}"
  | .compileError m => s!"compile: {m}"

/-- FFI: extract the named constants' dependency closure from a serialized
    env into a standalone `.ixe` — genuine constant bytes, blobs, and
    reducibility hints, plus the closure constants' Named entries so names
    still resolve — without recompiling from source. Names resolve by
    displayed form; a mutual-block member pulls its whole block. Errors on an
    unresolvable name. -/
@[extern "rs_env_extract"]
opaque rsEnvExtractFFI :
    @& String →                          -- source .ixe path
    @& Array String →                    -- constant names (displayed form)
    @& String →                          -- output .ixe path
    @& Bool →                            -- quiet
    IO Unit

/-- FFI: partition a `.ixe` with the STATIC strategy (no out-of-circuit
    profiling): a byte-balanced min-cut over the static walk-edge nets + a
    predicted-FFT-cost rebalance post-pass (`ixon::shard::shard_static`;
    model constants documented there). A nonzero `numShards` fixes the count; otherwise `ramGib`
    selects the static block-shape seed after the `.ixe` has been profiled.
    Writes a `.ixes` manifest; prints the report to stderr. -/
@[extern "rs_shard_env_static"]
opaque rsShardEnvStaticFFI :
    @& String →                          -- .ixe path
    USize →                              -- num_shards (N; 0 = score seed)
    UInt64 →                             -- max RAM GiB (used when N = 0)
    UInt64 →                             -- balance percent
    @& String →                          -- .ixes output path ("" = skip)
    USize →                              -- executions ahead of each prover (trace-shard seed)
    IO Unit

/-- FFI: dump the static block-level reference graph of a `.ixe` as text:
    `block <hex> <bytes> <consts>` per ingress unit and
    `edge <consumer> <producer>` per deduped claim-walk edge at block
    granularity. The walk-edge relation is what generates a shard's thin
    frontier, so a partition's ingress cost is computable offline from
    this file alone (partitioner-prototype input; no kernel run). -/
@[extern "rs_shard_static_graph"]
opaque rsShardStaticGraphFFI :
    @& String →                          -- .ixe path
    @& String →                          -- output text path
    IO Unit

end Ix.KernelCheck

end
