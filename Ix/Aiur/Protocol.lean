module
public import Std.Data.HashMap
public import Ix.Aiur.Goldilocks
public import Ix.Address
public import Ix.Aiur.Parameters

/-!
Pure Lean protocol types (`IOBuffer`, `QueryCount`, `ShardRetention`,
`buildClaim`; the STARK parameters are in `Ix.Aiur.Parameters`) and Rust-backed environment /
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
