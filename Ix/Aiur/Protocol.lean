module
public import Std.Data.HashMap
public import Ix.Aiur.Goldilocks
public import Ix.Address

/-!
Pure Lean protocol types (`IOBuffer`, `QueryCount`, `CommitmentParameters`,
`FriParameters`, `ShardRetention`, `buildClaim`) and Rust-backed environment /
manifest FFI (`EnvHandle`, `shardManifestRefine`,
`detectedRamBudgetBytes`).
-/

public section

namespace Aiur

structure IOKeyInfo where
  idx : Nat
  len : Nat
  deriving DecidableEq

instance : BEq IOKeyInfo where
  beq a b := a.idx == b.idx && a.len == b.len

instance : LawfulBEq IOKeyInfo where
  eq_of_beq {a b} h := by
    simp [BEq.beq, Bool.and_eq_true] at h
    cases a; cases b; simp_all
  rfl {a} := by simp [BEq.beq]

structure IOBuffer where
  /-- Per-channel data arenas. `idx` slots into `data[channel]`. -/
  data : Std.HashMap G (Array G)
  /-- Channel-keyed info map. Same `key` on different channels resolves
  to distinct `IOKeyInfo`. -/
  map : Std.HashMap (G × Array G) IOKeyInfo
  deriving Inhabited

/-- Append `data` to the `channel` arena and register `key → (idx, len)`
on the same channel. -/
def IOBuffer.extend (ioBuffer : IOBuffer) (channel : G) (key data : Array G) :
    IOBuffer :=
  let arena := ioBuffer.data.getD channel #[]
  let idx := arena.size
  let len := data.size
  { ioBuffer with
    data := ioBuffer.data.insert channel (arena ++ data)
    map := ioBuffer.map.insert (channel, key) { idx, len } }

/-- Rebuild an `IOBuffer` from the flat arrays produced by the Rust FFI. -/
def IOBuffer.ofArrays (data : Array (G × Array G))
    (map : Array ((G × Array G) × IOKeyInfo)) : IOBuffer :=
  ⟨data.foldl (fun acc (k, v) => acc.insert k v) ∅,
   map.foldl (fun acc (k, v) => acc.insert k v) ∅⟩

instance : BEq IOBuffer where
  beq x y :=
    @BEq.beq _ Std.HashMap.instBEq x.data y.data &&
    @BEq.beq _ Std.HashMap.instBEq x.map y.map

/-- Per-circuit query counts for one circuit. -/
structure QueryCount where
  uniqueRows : Nat
  totalHits : Nat
  deriving Inhabited

private opaque EnvHandleNonempty : NonemptyType
def EnvHandle : Type := EnvHandleNonempty.type
instance : Nonempty EnvHandle := EnvHandleNonempty.property

namespace EnvHandle

@[extern "rs_aiur_env_handle_from_ixe"]
private opaque fromIxe' : @& ByteArray → Except String EnvHandle

/-- Load an `EnvHandle` from a `.ixe` file path (UTF-8 ByteArray). -/
def fromIxe (path : String) : Except String EnvHandle :=
  fromIxe' path.toUTF8

@[extern "rs_aiur_env_handle_from_bytes"]
private opaque fromBytes' : @& ByteArray → Except String EnvHandle

/-- Build an `EnvHandle` from a serialized env blob. -/
def fromBytes (bytes : ByteArray) : Except String EnvHandle :=
  fromBytes' bytes

end EnvHandle

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

/-! The STARK parameters every Aiur proof uses, mirroring Rust's
`aiur::trace::stark::Parameters::DEFAULT` and `stark_key::security`; the Rust
test `lean_mirror_matches` reads the values below from this file, so keep one
`name := value` per field. `docs/stark-parameters.md` explains them, and
`lake exe fri-security` computes their security. -/

def defaultCommitmentParameters : CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }

def defaultFriParameters : FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

/-- The floor on `logBlowup · numQueries + queryProofOfWorkBits` (the
ethSTARK conjecture's query-phase bits) that every key must meet. -/
def minConjecturedSecurityBits : Nat := 220

/-- The most proof-of-work bits either FRI grinding phase may require. -/
def maxProofOfWorkBits : Nat := 32

/-- The conjectured query-phase bits of `commitment` and `fri`. -/
def conjecturedSecurityBits (commitment : CommitmentParameters) (fri : FriParameters) : Nat :=
  commitment.logBlowup * fri.numQueries + fri.queryProofOfWorkBits

/-- Whether `commitment` and `fri` meet the floor Rust enforces
(`stark_key::security::check`). -/
def meetsSecurityFloor (commitment : CommitmentParameters) (fri : FriParameters) : Bool :=
  1 ≤ commitment.logBlowup && commitment.logBlowup ≤ 4 && 0 < fri.numQueries &&
    fri.commitProofOfWorkBits ≤ maxProofOfWorkBits &&
    fri.queryProofOfWorkBits ≤ maxProofOfWorkBits &&
    minConjecturedSecurityBits ≤ conjecturedSecurityBits commitment fri

theorem default_meets_security_floor :
    meetsSecurityFloor defaultCommitmentParameters defaultFriParameters = true := by
  decide

structure CircuitShape where
  mainWidth : Nat
  stage2Width : Nat
  quotientDegree : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  deriving Inhabited

/-- What a trace-shard batch keeps of each shard between its two rounds. -/
inductive ShardRetention where
  | auto
  | retain
  | regenerate
  deriving Repr, DecidableEq

def ShardRetention.parse : String → Option ShardRetention
  | "auto" => some .auto
  | "retain" => some .retain
  | "regenerate" => some .regenerate
  | _ => none

def ShardRetention.code : ShardRetention → Nat
  | .auto => 0
  | .retain => 1
  | .regenerate => 2

@[extern "rs_shard_manifest_refine"]
opaque shardManifestRefine : @& EnvHandle → @& String →
  @& ByteArray → @& ByteArray → @& String → IO ByteArray

@[extern "rs_aiur_detected_ram_budget"]
private opaque detectedRamBudgetFFI : IO UInt64

def detectedRamBudgetBytes : IO Nat := do
  pure (← detectedRamBudgetFFI).toNat

abbrev functionChannel : G := .ofNat 1

def buildClaim (funIdx : Nat) (input output : Array G) : Array G :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end
