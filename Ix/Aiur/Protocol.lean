module
public import Ix.Aiur.Semantics.BytecodeFfi

/-!
AiurSystem, Proof, FRI params, and `buildClaim` — the "prove & verify" FFI surface.

The bytecode-execution FFI that used to live here has moved to
`Ix/Aiur/Bytecode/ExecuteFfi.lean` so that `Bytecode/Eval.lean` can be built
without pulling in the proving backend.
-/

public section

namespace Aiur

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

namespace Proof

@[extern "rs_aiur_proof_to_bytes"]
opaque toBytes : @& Proof → ByteArray

@[extern "rs_aiur_proof_of_bytes"]
opaque ofBytes : @& ByteArray → Proof

end Proof

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

/-- Canonical Aiur parameters, shared by `ix prove`, `ix verify`, and the
`ix check` statistics. Until these become flags / commit to the proof
header, every flow MUST use the same values or proofs won't verify. -/
def defaultCommitmentParameters : CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }

def defaultFriParameters : FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

/-- Shape of one compiled circuit, built directly by Rust
(`LeanAiurCircuitShape` in `crates/ffi/src/lean.rs`; field order must
match). Heights of function and memory circuits are execution-dependent
and are not part of the shape; `preprocessedHeight` doubles as the fixed
trace height of the byte-gadget circuits (256 and 65536), whose witness
builders always emit the full table. -/
structure CircuitShape where
  mainWidth : Nat
  stage2Width : Nat
  quotientDegree : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  deriving Inhabited

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

/-- Result of a prove FFI call, built directly by Rust
(`LeanAiurProveResult` in `crates/ffi/src/lean.rs`). `ioData`/`ioMap`
are the flattened `IOBuffer`; see `IOBuffer.ofArrays`. -/
structure ProveResult where
  claim : Array G
  proof : Proof
  ioData : Array (G × Array G)
  ioMap : Array ((G × Array G) × IOKeyInfo)
  deriving Nonempty

/-- Result of a with-env prove FFI call, built directly by Rust
(`LeanAiurProveEnvResult` in `crates/ffi/src/lean.rs`). `claimBytes`
is the claim's wire serialization (`ixon::Claim::put`). -/
structure ProveEnvResult where
  claimBytes : ByteArray
  proof : Proof
  ioData : Array (G × Array G)
  ioMap : Array ((G × Array G) × IOKeyInfo)
  deriving Nonempty

namespace AiurSystem

@[extern "rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → AiurSystem

/-- Serialize the verifying key (`System<AiurCircuit>`) to bytes. -/
@[extern "rs_aiur_system_vk_bytes"]
opaque vkBytes : @& AiurSystem → ByteArray

/-- Per-circuit shapes in canonical system order: constrained functions
(ascending index), memories, `Bytes1`, `Bytes2`. -/
@[extern "rs_aiur_system_circuit_shapes"]
opaque circuitShapes : @& AiurSystem → Array CircuitShape

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    ProveResult

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let r := prove' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray
  (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    ProveResult

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let r := proveIxVM' system funIdx args ioBuffer.data.toArray ioBuffer.map.toArray
  (r.claim, r.proof, .ofArrays r.ioData r.ioMap)

/-- Prove the MultiStark recursive verifier over raw proof/vk/claims
    byte blobs. The IO advice buffer is built natively in Rust (see
    `Bytecode.Toplevel.executeMultiStark`); the execute step inside
    the prove routes through the codegen'd verifier
    (`crates/ixvm-codegen/src/aiur_multi_stark.rs`) unless
    `useBytecode` is set. Only valid when `system` was built from the
    production `MultiStark.multiStark` bytecode. Returns the claim
    (`#[functionChannel, funIdx] ++ pubInput ++ output`) and the
    `Proof`; the final buffer is not returned. -/
@[extern "rs_aiur_multi_stark_prove"]
opaque proveMultiStark (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (proofBytes vkBytes claimBytes : @& ByteArray) (useBytecode : Bool := false) :
    Array G × Proof

@[extern "rs_aiur_system_prove_addr_with_env"]
private opaque proveAddrWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool →
    Except String ProveEnvResult

/-- Per-claim prove against a Rust-owned `EnvHandle`. Returns
    `(claimBytes, proof, ioBuffer)` — Rust serializes the
    reconstructed `Ix.Claim` via `ixon::Claim::put` so Lean can
    deserialize directly without re-running the closure walk.
    `useBytecode` routes the witness-generating execution through the
    generic Aiur bytecode interpreter instead of the codegen'd IxVM
    kernel (same toggle as `checkAddrWithEnv`). -/
def proveAddrWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (addrBytes : ByteArray)
  (useBytecode : Bool := false) :
    Except String (ByteArray × Proof × IOBuffer) :=
  (proveAddrWithEnv' system funIdx envHandle addrBytes useBytecode).map
    fun r => (r.claimBytes, r.proof, .ofArrays r.ioData r.ioMap)

/-- Result of a per-shard prove: the claim's wire bytes, the proof, and
    the projected prover RAM peak of the record that produced it
    (`AiurSystem::peak_prove_bytes`).

    `proof` is `none` exactly when the peak exceeded the budget — a
    RESULT rather than an error, since the caller's answer is to split
    the shard and prove the halves, and `peakBytes` is what it decides
    on. The claim bytes are filled either way (the claim is known before
    proving starts).

    The final IO buffer is not returned — it is the shard's whole
    ingested byte scope and no caller reads it. -/
structure ShardProveResult where
  claimBytes : ByteArray
  proof : Option Proof
  peakBytes : Nat

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → @& Nat →
    Except String ShardProveResult

/-- Per-shard prove against a Rust-owned `EnvHandle`: ONE execution,
    whose record is proven from directly.

    `maxRamBytes` is a per-shard prover-RAM budget checked against that
    record's projected peak before the witness phase begins; `0` means
    detect (85% of `MemAvailable`, the policy the check batch's RAM gate
    uses), and an unreadable `/proc/meminfo` disables the check rather
    than guessing. Over budget, the record is dropped and `proof` is
    `none` — learning that here costs one execution instead of an OOM
    part-way through an FFT. The peak comes back either way, so a prove
    run yields the same split/merge signal a check run does. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (ownedBlob : ByteArray) (maxRamBytes : Nat := 0) :
    Except String ShardProveResult :=
  shardProveWithEnv' system funIdx envHandle ownedBlob maxRamBytes

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

namespace Bytecode.Toplevel

/-- One shard's result from `shardCheckBatchWithEnv`. `weights` is the
    shard's per-constant virtual-gas table, packed as 48-byte rows —
    32-byte address, then `vspan` and `mult` as little-endian `UInt64`s
    (see `ShardResult.foldWeights`). Empty unless the batch ran with
    `profile := true`; the record it is read from is reduced to these
    rows and dropped inside the shard's own task, so a whole partition's
    weights fit in RAM when its records could not. -/
structure ShardResult where
  error : String
  peakBytes : Nat
  weights : ByteArray
  deriving Inhabited

/-- Bytes per packed `weights` row: 32 address + 8 vspan + 8 mult. -/
def shardWeightRow : Nat := 48

/-- Little-endian `UInt64` at `off`. -/
private def readU64LE (ba : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for b in [0 : 8] do
    v := v ||| ((ba.get! (off + b)).toUInt64 <<< (8 * b).toUInt64)
  return v

/-- Fold `f` over the packed `(addrBytes, vspan, mult)` rows of `weights`.
    Trailing bytes that do not complete a row are ignored. -/
@[inline] def ShardResult.foldWeights {α : Type} (r : ShardResult) (init : α)
    (f : α → ByteArray → UInt64 → UInt64 → α) : α := Id.run do
  let mut acc := init
  for i in [0 : r.weights.size / shardWeightRow] do
    let off := i * shardWeightRow
    acc := f acc (r.weights.extract off (off + 32))
      (readU64LE r.weights (off + 32)) (readU64LE r.weights (off + 40))
  return acc

@[extern "rs_aiur_toplevel_shard_check_batch"]
private opaque shardCheckBatchWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool → @& Nat →
  @& CommitmentParameters → @& FriParameters → Bool → @& Nat →
    Except String (Array ShardResult)

/-- Check EVERY shard of a partition in one call: rayon over the shard
    list with true work-stealing (no chunk barriers), each shard
    through the exact single-shard machinery over its own private
    record and witness io. `shardsBlob` encodes, per shard, a 4-byte LE
    owned-constant count followed by that many 32-byte addresses.
    Returns one `ShardResult` per shard in shard order: empty error =
    clean, and `peakBytes` is the analytic prover RAM peak
    ([`AiurSystem::peak_prove_bytes`] Rust-side) of the shard's executed
    record — the split/merge input (0 on failure). `profile` turns on the
    virtual-gas meter and fills each result's `weights` with the shard's
    per-constant cost rows, read off the record inside the shard's own
    task; `checkConstIdx` names the `check_const` function whose queries
    those rows come from (ignored when not profiling).
    `jobs = 0` uses rayon's default pool width (all cores): peak RSS
    is bounded by the Rust-side RAM gate (a byte-weighted admission
    semaphore over estimated per-shard execution RSS vs available
    system RAM), not by thread count — pass `jobs` only to narrow
    CPU use. -/
def shardCheckBatchWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (shardsBlob : ByteArray) (useBytecode : Bool := false) (jobs : Nat := 0)
  (commitmentParameters : CommitmentParameters := defaultCommitmentParameters)
  (friParameters : FriParameters := defaultFriParameters)
  (profile : Bool := false) (checkConstIdx : Nat := 0)
  : Except String (Array ShardResult) :=
  shardCheckBatchWithEnv' toplevel funIdx envHandle shardsBlob useBytecode
    jobs commitmentParameters friParameters profile checkConstIdx

end Bytecode.Toplevel

/-- One-shot variant of `AiurSystem.circuitShapes` for flows that never
build an `AiurSystem` (the `ix check` statistics): Rust builds the system,
extracts the shapes, and drops it. -/
@[extern "rs_aiur_circuit_shapes"]
opaque circuitShapes :
  @& Bytecode.Toplevel → @& CommitmentParameters → @& FriParameters →
    Array CircuitShape

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end
