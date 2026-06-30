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
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem

/-- Serialize the verifying key (`System<AiurCircuit>`) to bytes. -/
@[extern "rs_aiur_system_vk_bytes"]
opaque vkBytes : @& AiurSystem → ByteArray

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := prove' system friParameters funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_ixvm"]
private opaque proveIxVM' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Array G × Proof × Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)

/-- IxVM-native prove: same shape as `prove`, but routes execution
    through the codegen'd Rust kernel (`execute_generated`) instead
    of the bytecode interpreter. The resulting `Proof` is
    verification-compatible with one from `prove`. Only valid when
    `system.toplevel` is the IxVM kernel's bytecode. -/
def proveIxVM (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  let (claim, proof, ioData, ioMap) := proveIxVM' system friParameters funIdx args
    ioData ioMap
  let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_addr_ixvm"]
private opaque proveAddrIxVM' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& ByteArray → @& ByteArray →
    Except String (Array G × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- End-to-end per-claim prove: Rust builds the witness for
    `Claim.check addr none` from the memory-mapped `.ixe` env at
    `ixePath`, runs `execute_ixvm`, then drives the STARK prove
    pipeline. Single FFI trip — the `IOBuffer` never crosses the
    language boundary before prove time. Falls back to `proveIxVM`
    on a Lean-built witness when the claim variant isn't
    `check addr none`. -/
def proveAddrIxVM (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (ixePath : ByteArray) (addrBytes : ByteArray) :
    Except String (Array G × Proof × IOBuffer) :=
  match proveAddrIxVM' system friParameters funIdx ixePath addrBytes with
  | .error e => .error e
  | .ok (claim, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_prove_env_bytes_ixvm"]
private opaque proveEnvBytesIxVM' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& ByteArray → @& ByteArray →
    Except String (Array G × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- Bytes-blob variant of `proveAddrIxVM`: the env is passed in as a
    serialized blob (Lean's `Ixon.serEnv`) instead of a `.ixe` path.
    Used by `ix prove NAME` without `--ixe`. -/
def proveEnvBytesIxVM (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (envBytes : ByteArray) (addrBytes : ByteArray) :
    Except String (Array G × Proof × IOBuffer) :=
  match proveEnvBytesIxVM' system friParameters funIdx envBytes addrBytes with
  | .error e => .error e
  | .ok (claim, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_shard_prove_ixvm"]
private opaque shardProveIxVM' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& ByteArray → @& ByteArray →
    Except String (Array G × Proof ×
      Array (G × Array G) × Array ((G × Array G) × IOKeyInfo))

/-- End-to-end per-shard prove. Rust builds the `CheckEnv` witness
    over `ownedBlob` (flat 32-byte addresses), runs `execute_ixvm`,
    and drives the STARK prove. Same return shape as
    `proveAddrIxVM`. -/
def shardProveIxVM (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (ixePath : ByteArray) (ownedBlob : ByteArray) :
    Except String (Array G × Proof × IOBuffer) :=
  match shardProveIxVM' system friParameters funIdx ixePath ownedBlob with
  | .error e => .error e
  | .ok (claim, proof, ioData, ioMap) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    .ok (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem → @& FriParameters →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end
