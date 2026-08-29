module
public import Blake3.Rust
public import Ix.Aggr.Circuit
public import Ix.Aggr.Host
public import Ix.AssumptionTree
public import Ix.MultiStark

/-!
# The `ixAggr` toplevel

`ixAggr` is the recursive aggregation system for IxVM proofs. It reuses the
Ix-agnostic Multi-STARK verifier modules (`Ix/MultiStark/…`, unmodified) and
adds the heterogeneous `ix_aggr` entrypoint from `Ix/Aggr/Circuit.lean` — one
circuit that wraps or joins any mix of IxVM and `ix_aggr` child proofs, with
the shape chosen by advice. There is no separate lift stage: an IxVM proof
enters the recursion system through a wrap or directly as a join child.

This module is also the single home of the host half of the wire contracts:
the allowed blob, the public input packing, and the shape codes. Callers must
reproduce these byte-for-byte — the blob and the output claim are Blake3
digest-bound in-circuit.
-/

public section

namespace Aggr

/-- The full aggregation toplevel: every Multi-STARK verifier module (via
`MultiStark.multiStarkFull`, unmodified) plus the `ix_aggr` circuit —
unpruned. Only tests should build on this; production uses `ixAggr`. -/
def ixAggrFull : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← MultiStark.multiStarkFull
  t.merge circuit

/-- The production aggregation toplevel: `ixAggrFull` pruned to `ix_aggr`'s
call closure. Every compiled function is a committed circuit whose openings
pad every proof of the system's execution, so functions only reachable from
unrelated entries (`verify_multi_stark_proof`, kernel-oriented helpers of the
shared modules, test/bench entries) cost real proof bytes if kept. -/
def ixAggr : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← ixAggrFull
  pure (t.prune [`ix_aggr])

/-! ## Identity and public input -/

/-- Pack a Blake3 digest four bytes per Goldilocks element, little-endian —
the layout `b3_pack` produces in-circuit. -/
def digestGs (bytes : ByteArray) : Array Aiur.G :=
  let h := (Blake3.Rust.hash bytes).val.data
  (Array.range 8).map fun i =>
    .ofNat (h[4*i]!.toNat + 256 * h[4*i+1]!.toNat
      + 65536 * h[4*i+2]!.toNat + 16777216 * h[4*i+3]!.toNat)

/-- The digest-bound 80-byte identity blob:

`blake3(ixvm vk) ‖ verify_claim index as u64-LE ‖ blake3(self vk) ‖
ix_aggr index as u64-LE`.

The verifying keys stay outside the public input. Their digests and both
entrypoint indices form the stable identity that every node of an aggregation
tree pins transitively — the blob is identical at every node regardless of
shape. The indices must be explicit because the Source DSL cannot materialize
its compiler-assigned function index inside a circuit. -/
def allowedBlob (ixvmVkBytes : ByteArray) (verifyClaimIdx : Nat)
    (selfVkBytes : ByteArray) (aggrIdx : Nat) : ByteArray :=
  let ixvmDigest := (Blake3.Rust.hash ixvmVkBytes).val.data
  let selfDigest := (Blake3.Rust.hash selfVkBytes).val.data
  ⟨ixvmDigest ++ MultiStark.u64le verifyClaimIdx ++
    selfDigest ++ MultiStark.u64le aggrIdx⟩

/-- Public input of `ix_aggr`: the packed Blake3 digest of the identity blob
followed by the packed digest of the output `CheckEnv` claim bytes. -/
def pubInput (allowed outClaimBytes : ByteArray) : Array Aiur.G :=
  digestGs allowed ++ digestGs outClaimBytes

/-! ## Shapes -/

/-- Which system a child proof verifies against. -/
inductive ChildKind where
  | ixvm
  | aggr
  deriving BEq, Repr

def ChildKind.code : ChildKind → Nat
  | .ixvm => 0
  | .aggr => 1

/-- The advice byte selecting a wrap or flat pair: `0`/`1` wrap one IxVM /
`ix_aggr` child; `2`–`5` fold a flat pair, `2 + 2·left + right` with IxVM = 0
and `ix_aggr` = 1. -/
def shapeCode : (children : ChildKind × Option ChildKind) → Nat
  | (kind, none) => kind.code
  | (left, some right) => 2 + 2 * left.code + right.code

/-- Structural pair shapes `6`–`9`: `6 + 2·left + right`. Wraps have no
structural form. -/
def structuralShapeCode (left right : ChildKind) : Nat :=
  6 + 2 * left.code + right.code

/-! ## Native-FFI advice framing

`executeIxAggr` / `proveIxAggr` take the digest-addressed advice as compact
byte blobs and expand them into IO channels natively. The circuit still
re-hashes/re-roots every payload; these host-side keys only make the advice
addressable — they are not trusted bindings. -/

/-- Four little-endian bytes of `n`, used only by the compact native-FFI
framing below. Advice blobs are bounded by the `ByteArray`/Rust address
space in practice and therefore never approach the `u32` limit. -/
private def u32le (n : Nat) : Array UInt8 :=
  (Array.range 4).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Encode content-addressed byte blobs for the native FFI as

`count:u32-LE ‖ (key:32 ‖ length:u32-LE ‖ payload)*`. -/
private def keyedBlobs
    (entries : Array (ByteArray × ByteArray)) : ByteArray := Id.run do
  assert! entries.size < 4294967296
  let mut out := u32le entries.size
  for (key, payload) in entries do
    assert! key.size == 32
    assert! payload.size < 4294967296
    out := out ++ key.data ++ u32le payload.size ++ payload.data
  return ⟨out⟩

/-- Pack `CheckEnv` claim preimages for the native FFI. Each key is computed
as Blake3(payload), matching IO channel 4's packed-digest lookup. -/
def preimagesBlob (preimages : Array ByteArray) : ByteArray :=
  keyedBlobs <| preimages.map fun bytes =>
    ((Blake3.Rust.hash bytes).val, bytes)

/-- Pack serialized canonical trees for the native FFI. Channel 5 keys use
the raw 32-byte tree root. The in-circuit loader independently checks strict
leaf order and recomputes the canonical root. -/
def treesBlob (trees : Array Ix.AssumptionTree) : ByteArray :=
  keyedBlobs <| trees.map fun tree =>
    (tree.root.hash, Ix.AssumptionTree.ser tree)

/-- Encode one structural-discharge choice. A missing path means "carry" and
encodes as `0`; a present path encodes as
`1 ‖ count:u8 ‖ (side:u8 ‖ sibling:32)*`. The side byte is zero when the
sibling is on the left and one when it is on the right. -/
def pathPayload (path? : Option Ix.Merkle.MerklePath) : ByteArray := Id.run do
  match path? with
  | none => return ⟨#[0]⟩
  | some path =>
    assert! path.size ≤ 64
    let mut out : Array UInt8 := #[1, UInt8.ofNat path.size]
    for (sibling, isLeft) in path do
      out := out.push (if isLeft then 0 else 1)
      out := out ++ sibling.hash.data
    return ⟨out⟩

/-- Pack one structural-discharge choice per unique input-assumption candidate
for IO channel 6. -/
def pathsBlob
    (paths : Array (Address × Option Ix.Merkle.MerklePath)) : ByteArray :=
  keyedBlobs <| paths.map fun (candidate, path?) =>
    (candidate.hash, pathPayload path?)

/-! ## Interpreter-side advice assembly

These helpers place advice on the IO channels exactly as the circuit reads
them, for the pure-Lean `Bytecode.Toplevel.execute` path. The native
execute/prove FFI will consume byte blobs with the same channel layout. -/

/-- One byte per Goldilocks element, the layout `#read_byte_stream` expects. -/
def byteGs (bytes : ByteArray) : Array Aiur.G :=
  bytes.data.map .ofUInt8

/-- Channel 4: a `CheckEnv` claim preimage, keyed by its packed digest. The
circuit re-hashes the payload against the key, so host keys are addressing,
not trusted bindings. -/
def extendPreimage (io : Aiur.IOBuffer) (bytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 4 (digestGs bytes) (byteGs bytes)

/-- Channel 5: one serialized canonical tree, keyed by its raw 32-byte root.
The circuit independently checks strict leaf order and recomputes the
canonical root. -/
def extendTree (io : Aiur.IOBuffer) (tree : Ix.AssumptionTree) : Aiur.IOBuffer :=
  io.extend 5 (byteGs tree.root.hash) (byteGs (Ix.AssumptionTree.ser tree))

/-- Channel 6: one structural carried/discharged choice keyed by the raw
candidate address. The 32-element address key cannot collide with the shape's
one-element `[0]` key. -/
def extendPath (io : Aiur.IOBuffer) (candidate : Address)
    (path? : Option Ix.Merkle.MerklePath) : Aiur.IOBuffer :=
  io.extend 6 (byteGs candidate.hash) (byteGs (pathPayload path?))

/-- Channels 0/2 for one child slot: expanded proof advice and serialized
claims. Compact proof wire bytes are not an in-circuit input. -/
def extendChild (io : Aiur.IOBuffer) (key : Nat)
    (proofAdviceBytes claimsBytes : ByteArray) : Aiur.IOBuffer :=
  let io := io.extend 0 #[.ofNat key] (byteGs proofAdviceBytes)
  io.extend 2 #[.ofNat key] (byteGs claimsBytes)

/-- Channels 3 and 6: the identity blob and the shape byte. -/
def extendIdentity (io : Aiur.IOBuffer) (allowed : ByteArray)
    (shape : Nat) : Aiur.IOBuffer :=
  let io := io.extend 3 #[.ofNat 0] (byteGs allowed)
  io.extend 6 #[.ofNat 0] #[.ofNat shape]

/-- Channel 1: vk bytes for one child kind (key 0 = IxVM, key 1 = self). -/
def extendVk (io : Aiur.IOBuffer) (kind : ChildKind)
    (vkBytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 1 #[.ofNat kind.code] (byteGs vkBytes)

/-- Channel 2 key 2: the output claim bytes of a pair fold. Wrap shapes bind
the output digest against the child claim directly and read no output bytes. -/
def extendOutputClaim (io : Aiur.IOBuffer) (bytes : ByteArray) : Aiur.IOBuffer :=
  io.extend 2 #[.ofNat 2] (byteGs bytes)

end Aggr

end
