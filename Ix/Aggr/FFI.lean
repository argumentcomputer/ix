module
public import Ix.Aiur.Protocol

/-! Native aggregation execution, proving, and manifest binding.
Extern symbols and record layout are shared with `crates/ffi/src/aiur/aggregate/ffi.rs`. -/

public section
namespace Aiur

/-- Manifest-bound aggregate root reconstructed and audited by the native
Stage 2 controller. `claimBytes` is the exact root `Ix.Claim` wire encoding;
`constantCount` is the number of environment constants proven to occur once. -/
structure AggregateExpected where
  claimBytes : ByteArray
  constantCount : Nat
  deriving Nonempty


namespace Bytecode.Toplevel

/-- Native execution of the `ix_aggr` aggregation entrypoint. Serialized child
proof transport (from `AiurSystem.proofToAdviceBytes`), claims, and the fixed
vk/output/allowed blobs are passed without
per-byte Lean field boxing; `preimagesBlob`, `treesBlob`, and `pathsBlob` use the compact
count/key/length framing produced by `Aggr.preimagesBlob` and
`Aggr.treesBlob` / `Aggr.pathsBlob`. Rust expands them directly into IO
channels 0–6 (the shape hint and structural paths share channel 6 with
disjoint key shapes). Wrap shapes pass empty right-child/path blobs —
the circuit never reads them. As with `executeMultiStark`, `useBytecode`
selects the generic interpreter over the generated production aggregator,
and the codegen'd path is only valid when `toplevel` is the production
`Aggr.ixAggr` bytecode. -/
@[extern "rs_aiur_ix_aggr_execute"]
opaque executeIxAggr (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G) (shape : @& Nat)
  (leftProofAdviceBytes rightProofAdviceBytes ixvmVkBytes selfVkBytes : @& ByteArray)
  (leftClaimsBytes rightClaimsBytes outputClaimBytes allowedBytes : @& ByteArray)
  (preimagesBlob treesBlob pathsBlob : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Array QueryCount)


end Bytecode.Toplevel
namespace AiurSystem

/-- Prove one `ix_aggr` execution — any shape — over raw child proof/claim
advice. Both proof blobs must come from `AiurSystem.proofToAdviceBytes`;
the compact preimage/tree/path blobs are produced by `Aggr.preimagesBlob`,
`Aggr.treesBlob`, and `Aggr.pathsBlob`; wrap and flat shapes pass empty
right-child blobs. Malformed framing is returned as an error; as with
`prove`/`proveMultiStark`, callers must supply an accepting execution
witness. Only valid when `system` was built from the production
`Aggr.ixAggr` bytecode (unless `useBytecode` is set). The final native IO
buffer is intentionally not marshalled back to Lean. -/
@[extern "rs_aiur_ix_aggr_prove"]
opaque proveIxAggr (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G) (shape : @& Nat)
  (leftProofAdviceBytes rightProofAdviceBytes ixvmVkBytes selfVkBytes : @& ByteArray)
  (leftClaimsBytes rightClaimsBytes outputClaimBytes allowedBytes : @& ByteArray)
  (preimagesBlob treesBlob pathsBlob : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Proof)

/-- Run the production aggregate-first Stage 2 pipeline natively after Lean
has compiled the IxVM and `ix_aggr` systems. Rust owns all data-dependent
orchestration: manifest/environment binding, shard-claim reconstruction,
statement folding, cache validation, dependency scheduling, recursive advice,
proving, and persistence. `proofHexes` is one store address per line;
`cacheFriBytes` is the stable 40-byte recursion-FRI cache identity.
`reproveSlotCode` is zero for a full run and `slot + 1` for a targeted replay;
the latter loads and verifies only the target's immediate cached children.
When `writeOutputs` is false, proofs are hashed but neither the store nor cache
is changed. Returns the root or replayed proof address. -/
@[extern "rs_aiur_stage2_aggregate"]
opaque aggregateStage2 (ixvmSystem aggrSystem : @& AiurSystem)
  (envHandle : @& EnvHandle) (manifestPath proofHexes : @& String)
  (verifyIdx aggrIdx jobs ramBudgetBytes structuralAbove reproveSlotCode : @& Nat)
  (directJoins planOnly : Bool) (cacheFriBytes : @& ByteArray)
  (useCache writeOutputs : Bool) :
    Except String String

/-- Reconstruct and audit the manifest-relative aggregate root entirely in
Rust, using the same ownership, frontier, pruning, and statement-fold code as
`aggregateStage2`. This is the native orchestration path for `ix verify` and
does not construct shard statements or schedule Lean tasks. -/
@[extern "rs_aiur_aggregate_expected"]
opaque aggregateExpected (envHandle : @& EnvHandle)
  (manifestPath : @& String) (structuralAbove : @& Nat) :
    Except String AggregateExpected


end AiurSystem
end Aiur
end
