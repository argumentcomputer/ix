module
public import Ix.Aiur.Stages.Bytecode
public import Std.Data.HashMap

/-!
Opaque Rust FFI for bytecode execution. Split out of `Protocol.lean` so the
Lean-native reference evaluator (`Bytecode/Eval.lean`) can stand alone.

The Rust executor is the production backend; our Lean reference is the specification.
A follow-up theorem relates the two under a purity assumption on IO.
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

instance : BEq IOBuffer where
  beq x y :=
    @BEq.beq _ Std.HashMap.instBEq x.data y.data &&
    @BEq.beq _ Std.HashMap.instBEq x.map y.map

-- A `LawfulBEq IOBuffer` instance is not provided here. The reflexivity/
-- symmetry/transitivity facts needed downstream (`IOBuffer.equiv_refl`,
-- `_symm`, `_trans`) are proved directly in `Ix/Aiur/Proofs/IOBufferEquiv.lean`
-- via `Std.HashMap.beq_iff_equiv` + `Std.HashMap.Equiv.{refl,symm,trans}`,
-- bypassing the need for `LawfulBEq` on the outer `IOBuffer`.

/-- Per-circuit query counts for one circuit (one per function circuit, then
one per memory size). `uniqueRows` is the trace height; `totalHits` is the sum
of query multiplicities. The difference `totalHits - uniqueRows` is the number
of cache hits. -/
structure QueryCount where
  uniqueRows : Nat
  totalHits : Nat
  deriving Inhabited

namespace Bytecode.Toplevel

@[extern "rs_aiur_toplevel_execute"]
private opaque execute' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String (Array G ×
      (Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)) ×
      Array (Nat × Nat))

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
returning the raw output of the function, the updated `IOBuffer`, and an array
of per-circuit `QueryCount`s. Returns `Except.error msg` when execution
fails (e.g. `assert_eq!` mismatch from a typechecker rejecting a constant), so
callers can recover instead of crashing. -/
def execute (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × IOBuffer × Array QueryCount) :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  match execute' toplevel funIdx args ioData ioMap with
  | .error e => .error e
  | .ok (output, (ioData, ioMap), queryCounts) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    let queryCounts := queryCounts.map fun (uniqueRows, totalHits) => { uniqueRows, totalHits }
    .ok (output, ⟨ioData, ioMap⟩, queryCounts)

@[extern "rs_aiur_toplevel_execute_ixvm"]
private opaque executeIxVM' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String (Array G ×
      (Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)) ×
      Array (Nat × Nat))

/-- IxVM-native execution: same shape as `execute`, but routes the
    function invocation through the codegen'd Rust kernel
    (`crate::ix::aiur_ixvm::execute_generated`) instead of the
    generic bytecode interpreter. The resulting `QueryRecord` is
    byte-for-byte identical (modulo the standing codegen parity
    invariant). Only valid when `toplevel` is the IxVM kernel's
    `Bytecode.Toplevel` — other toplevels produce undefined results
    because the generated function bodies are fixed at codegen time. -/
def executeIxVM (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × IOBuffer × Array QueryCount) :=
  let ioData := ioBuffer.data.toArray
  let ioMap := ioBuffer.map.toArray
  match executeIxVM' toplevel funIdx args ioData ioMap with
  | .error e => .error e
  | .ok (output, (ioData, ioMap), queryCounts) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    let queryCounts := queryCounts.map fun (uniqueRows, totalHits) => { uniqueRows, totalHits }
    .ok (output, ⟨ioData, ioMap⟩, queryCounts)

@[extern "rs_aiur_toplevel_shard_check_ixvm"]
private opaque shardCheckIxVM' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& ByteArray → @& ByteArray →
    Except String (Array G ×
      (Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)) ×
      Array (Nat × Nat))


/-- IxVM-native shard check: builds the witness in Rust (no
    per-byte boxing into Lean values), then dispatches through
    `execute_ixvm`. Replaces `buildShardCheckEnvWitness` + `executeIxVM`
    with a single FFI call.

    `ixePath` is a UTF-8 path to a memory-mappable `.ixe` env;
    Rust loads it lazily. `ownedBlob` is a flat ByteArray of 32-byte
    address blocks (one per owned const). -/
def shardCheckIxVM (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (ixePath : ByteArray) (ownedBlob : ByteArray)
  : Except String (Array G × IOBuffer × Array QueryCount) :=
  match shardCheckIxVM' toplevel funIdx ixePath ownedBlob with
  | .error e => .error e
  | .ok (output, (ioData, ioMap), queryCounts) =>
    let ioData := ioData.foldl (fun acc (k, v) => acc.insert k v) ∅
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    let queryCounts := queryCounts.map fun (uniqueRows, totalHits) => { uniqueRows, totalHits }
    .ok (output, ⟨ioData, ioMap⟩, queryCounts)

end Bytecode.Toplevel

end Aiur

end
