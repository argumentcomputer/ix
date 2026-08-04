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

/-- Rebuild an `IOBuffer` from the flat arrays produced by the Rust FFI.
Hashmaps don't cross the FFI boundary; Rust returns arrays and the
hashmaps are populated here. -/
def IOBuffer.ofArrays (data : Array (G × Array G))
    (map : Array ((G × Array G) × IOKeyInfo)) : IOBuffer :=
  ⟨data.foldl (fun acc (k, v) => acc.insert k v) ∅,
   map.foldl (fun acc (k, v) => acc.insert k v) ∅⟩

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

/-- Result of an execution FFI call, built directly by Rust
(`LeanAiurExecuteResult` in `crates/ffi/src/lean.rs`). `ioData`/`ioMap`
are the flattened `IOBuffer`; see `IOBuffer.ofArrays`. -/
structure ExecuteResult where
  output : Array G
  ioData : Array (G × Array G)
  ioMap : Array ((G × Array G) × IOKeyInfo)
  queryCounts : Array QueryCount

-- ===========================================================================
-- EnvHandle: Rust-owned `ixon::Env` exposed to Lean as an opaque handle.
-- Built once per CLI invocation; reused across every per-claim and
-- per-shard FFI call so the env is parsed exactly once.
-- ===========================================================================

private opaque EnvHandleNonempty : NonemptyType
def EnvHandle : Type := EnvHandleNonempty.type
instance : Nonempty EnvHandle := EnvHandleNonempty.property

namespace EnvHandle

@[extern "rs_aiur_env_handle_from_ixe"]
private opaque fromIxe' : @& ByteArray → Except String EnvHandle

/-- Load an `EnvHandle` from a `.ixe` file path (UTF-8 ByteArray).
    Rust mmap's the file zero-copy; the handle keeps the mapping
    alive for as long as Lean retains it. -/
def fromIxe (path : String) : Except String EnvHandle :=
  fromIxe' path.toUTF8

@[extern "rs_aiur_env_handle_from_bytes"]
private opaque fromBytes' : @& ByteArray → Except String EnvHandle

/-- Build an `EnvHandle` from a serialized env blob (e.g. produced
    by `Ixon.serEnv` on the compiled-Lean-env code path). -/
def fromBytes (bytes : ByteArray) : Except String EnvHandle :=
  fromBytes' bytes

end EnvHandle

namespace Bytecode.Toplevel

@[extern "rs_aiur_toplevel_execute"]
private opaque execute' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String ExecuteResult

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
returning the raw output of the function, the updated `IOBuffer`, and an array
of per-circuit `QueryCount`s. Returns `Except.error msg` when execution
fails (e.g. `assert_eq!` mismatch from a typechecker rejecting a constant), so
callers can recover instead of crashing. -/
def execute (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × IOBuffer × Array QueryCount) :=
  (execute' toplevel funIdx args ioBuffer.data.toArray ioBuffer.map.toArray).map
    fun r => (r.output, .ofArrays r.ioData r.ioMap, r.queryCounts)

@[extern "rs_aiur_toplevel_execute_ixvm"]
private opaque executeIxVM' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String ExecuteResult

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
  (executeIxVM' toplevel funIdx args ioBuffer.data.toArray ioBuffer.map.toArray).map
    fun r => (r.output, .ofArrays r.ioData r.ioMap, r.queryCounts)

/-- MultiStark-native execution of `verify_multi_stark_proof`: the IO
    advice buffer (channel 0 = proof, 1 = vk, 2 = claims, key `[0]`
    each) is built natively in Rust from the raw byte blobs — no
    per-byte boxing into Lean `G`s, no buffer marshalling across FFI.
    `useBytecode` selects the generic Aiur bytecode interpreter over
    the codegen'd verifier (`crates/ixvm-codegen/src/aiur_multi_stark.rs`);
    as with `executeIxVM`, the codegen'd path is only valid when
    `toplevel` is the production `MultiStark.multiStark` bytecode —
    other toplevels (e.g. `multiStarkTests`) must pass
    `useBytecode := true`. Returns the output and per-circuit query
    counts; the final buffer is not returned (the verifier only reads
    its advice). -/
@[extern "rs_aiur_multi_stark_execute"]
opaque executeMultiStark (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (pubInput : @& Array G)
  (proofBytes vkBytes claimBytes : @& ByteArray) (useBytecode : Bool := false) :
    Except String (Array G × Array QueryCount)

-- (EnvHandle opaque type + constructors live above `namespace
-- Bytecode.Toplevel`; see `Aiur.EnvHandle`. The with-env FFI
-- declarations below reference `EnvHandle` and `Bytecode.Toplevel`
-- from the same scope.)

@[extern "rs_aiur_toplevel_check_addr_with_env"]
private opaque checkAddrWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool →
    Except String ExecuteResult

/-- Per-claim check against a Rust-owned `EnvHandle`. `useBytecode`
    selects the generic Aiur bytecode interpreter
    (`Bytecode.Toplevel.execute`) over the codegen'd IxVM kernel
    (`execute_ixvm`); useful for tight iteration loops on Lean-side
    IxVM source where regenerating the Rust kernel is too slow. -/
def checkAddrWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (addrBytes : ByteArray) (useBytecode : Bool := false)
  : Except String (Array G × IOBuffer × Array QueryCount) :=
  (checkAddrWithEnv' toplevel funIdx envHandle addrBytes useBytecode).map
    fun r => (r.output, .ofArrays r.ioData r.ioMap, r.queryCounts)

@[extern "rs_aiur_toplevel_shard_check_with_env"]
private opaque shardCheckWithEnv' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& ByteArray → Bool →
    Except String ExecuteResult

/-- Per-shard check with the witness shape (wrapper-augmented byte
    scope for the kernel's kernel-side blake3'd projection addrs). Claim and
    digest are identical to `shardCheckWithEnv`'s. -/
def shardCheckWithEnv (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (envHandle : @& EnvHandle)
  (ownedBlob : ByteArray) (useBytecode : Bool := false)
  : Except String (Array G × IOBuffer × Array QueryCount) :=
  (shardCheckWithEnv' toplevel funIdx envHandle ownedBlob useBytecode).map
    fun r => (r.output, .ofArrays r.ioData r.ioMap, r.queryCounts)

/-- Scan-and-cut sharding: execute the env's check schedule through the
    codegen'd kernel as incrementally-grown thin-frontier `CheckEnv`
    claims — the same claim type the prover pays for — with a running
    FFT-cost readout, cutting shard boundaries where the measured cost
    reaches the RAM budget's FFT equivalent (see
    `crates/ffi/src/aiur/scan.rs`). Witness bytes fault in lazily, so a
    scanner's RAM tracks one segment's touched set. Writes the `.ixes`
    manifest plus a `.costs.csv` sidecar carrying the MEASURED per-shard
    FFT mapped through the calibrated resource lines. Numeric params are
    decimal strings (ABI-simple): budget GiB, cut headroom percent,
    parallel chunk scanners (0 = autoscale), fail-fast ("0" skips
    kernel-rejected blocks, recording them in a `.failed.csv` sidecar;
    anything else aborts on the first). -/
@[extern "rs_aiur_scan_shards_with_env"]
opaque scanShardsWithEnv : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& EnvHandle → @& String → @& String → @& String →
  @& String → @& String → Except String Unit

end Bytecode.Toplevel

end Aiur

end
