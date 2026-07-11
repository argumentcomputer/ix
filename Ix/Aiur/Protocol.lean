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

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

namespace AiurSystem

@[extern "rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → AiurSystem

/-- Serialize the verifying key (`System<AiurCircuit>`) to bytes. -/
@[extern "rs_aiur_system_vk_bytes"]
opaque vkBytes : @& AiurSystem → ByteArray

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := prove' system funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := proveIxVM' system funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_addr_with_env"]
private opaque proveAddrWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
    Except String (ByteArray × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- Per-claim prove against a Rust-owned `EnvHandle`. Returns
    `(claimBytes, proof, ioBuffer)` — Rust serializes the
    reconstructed `Ix.Claim` via `ixon::Claim::put` so Lean can
    deserialize directly without re-running the closure walk. -/
def proveAddrWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (addrBytes : ByteArray) :
    Except String (ByteArray × Proof × IOBuffer) :=
  match proveAddrWithEnv' system funIdx envHandle addrBytes with
  | .error e => .error e
  | .ok (claimBytes, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claimBytes, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_shard_prove_with_env"]
private opaque shardProveWithEnv' : @& AiurSystem →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray →
    Except String (ByteArray × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- Per-shard prove against a Rust-owned `EnvHandle`. -/
def shardProveWithEnv (system : @& AiurSystem)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle) (ownedBlob : ByteArray) :
    Except String (ByteArray × Proof × IOBuffer) :=
  match shardProveWithEnv' system funIdx envHandle ownedBlob with
  | .error e => .error e
  | .ok (claimBytes, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claimBytes, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

/-- Compress an Aiur proof by re-verifying it inside the SP1 zkVM and
    producing a recursive SP1 proof of that verification (`sp1-compress/`).
    Arguments: verifying-key bytes (`AiurSystem.vkBytes`), the claim as
    canonical u64 LE bytes, `Proof.toBytes` bytes, the FRI parameters the
    proof was made with, the SP1 mode
    (`execute | core | compressed | groth16 | plonk`), and a path to save
    the SP1 proof to (`""` = don't save). Stub that always errors unless
    `ix` was built with `IX_SP1=1`. -/
@[extern "rs_sp1_compress_aiur_proof"]
opaque sp1CompressAiurProof : @& ByteArray → @& ByteArray → @& ByteArray →
  @& FriParameters → @& String → @& String → Except String Unit

/-- Upgrade a saved *compressed* SP1 proof file to `groth16`/`plonk` without
    redoing the core/compress STARK stages (only shrink → wrap → gnark run).
    Arguments: input path (the SDK `.save()` format `--output` writes), the
    target mode, and an output path (`""` = don't save). Stub that always
    errors unless `ix` was built with `IX_SP1=1`. -/
@[extern "rs_sp1_wrap_saved_proof"]
opaque sp1WrapSavedProof : @& String → @& String → @& String →
  Except String Unit

end Aiur

end
