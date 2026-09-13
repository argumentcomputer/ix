# Byte-capable IxBy execution in Flock

Status: bounded native byte values, canonical codecs, all 35 existing crypto-v0
primitives, guest BLAKE3, and direct execution proofs are implemented. The full
registry is an explicit upgrade from the older thirty-opcode byte setup. This
does not itself implement structured values; the separate
[constructor setup](IxbyFlockObjects.md) supplies that bounded extension.
Neither completes a compiled crypto guest, the native
constraint-to-reference theorem, or Stage 4.

## Approved setup and unchanged scalar keys

`compile_exec_byte_profile(profile, machineCapacity, byteCapacity, primitives,
backend)` takes only verifier-owned setup. It accepts no guest, Stage 2 key,
proof, trace, heap or host acceptance result. `SemanticProfile::bytes` uses
the existing 68-byte profile envelope, setting parameter 9 to the per-array
bound. Constructor/Nat/String bounds remain zero and value depth remains one.
Input and output serialization capacities must match.

The implementation, capacity and primitive identities distinguish this class
from scalar-only execution. The transcript prefix is `ix:ixby:byte-exec:v0`,
followed by the approved setup digest. Compression backend selection is also
explicit and bound into setup. The proof envelope and P/B/I/O/S commitment
functions are unchanged. Only the two F128 limbs of externally expected S
are variable public outputs; the verifier needs neither private artifacts nor
native execution.

The legacy scalar constructors, tables, declaration order and transcript
remain unchanged. Their pinned setup digest is still
`41163b87f03675917ac93824d8b1c11ab0c489c2fc2e03abece34d11fa3255f7`.
Passing byte opcodes or the expanded word registry to scalar-only compilation
explicitly rejects; the expanded registry uses byte-profile compilation.

## Immutable byte values and their constraints

Frames still hold two-word tagged cells. Physical tag 6 denotes bytes; its
payload is a canonical u32 index into an immutable record bank. It is neither
array contents nor a digest. The serialized scalar tag remains the existing
crypto-v0 tag 4 followed by u32 length and the exact bytes.

Every setup reserves one record for each program operand slot, one for each
input value slot, and one for each transition. Program literals and input
values derive their own allocation indices from those fixed positions. Each
record contains length, a presence bit, and sixteen bytes per F128 data word.
Absent records are all zero; a present empty array has its presence bit set.
Unused metadata and data bytes are constrained zero.

The two decoders derive all initial records from the authenticated original
bytes. Reads constrain the entire index, selected presence, length and padding.
Unselected records are authenticated at their producers, not by the read gate.
Each transition's array result replaces only its preassigned future-zero
record with constrained output wires. No free heap, selected data, allocation
result or one-hot hint enters the circuit. Copies, calls and returns retain
handles; previous arrays remain immutable.

The byte dispatch checks existing opcode/arity/type rules, exact conversion
lengths, canonical field decoding, checked append capacity, and complete u32
index/start/length arithmetic. Out-of-range access and wrapped/truncated slices
reject. Equality compares both full length and contents. Enabled opcodes are:

| Opcodes | Operations |
| --- | --- |
| 11, 12 | Word32 / four little-endian bytes |
| 19, 20 | Goldilocks / eight canonical little-endian bytes |
| 29, 30 | Length and checked byte access |
| 31, 32, 33 | Append, checked slice and equality |
| 34 | Unkeyed BLAKE3, returning exactly 32 bytes |

These join the original twenty scalar opcodes in
`PrimitiveSet::crypto_bytes()`. That constructor retains its thirty-opcode
subset and existing setup identity. `PrimitiveSet::crypto()` explicitly
admits all 35 existing reference crypto primitives; `with_crypto(opcodes)`
admits a chosen subset, rejecting duplicates and out-of-registry opcodes.

## Complete word arithmetic upgrade

The complete registry adds the five previously unsupported word operations:

| Opcodes | Constrained result |
| --- | --- |
| 1 | Subtraction modulo `2^32` |
| 2 | Multiplication modulo `2^32` |
| 6, 7 | Logical left/right shift; count ≥32 returns zero |
| 8 | Rotate right with count modulo 32 |

Subtraction uses a Boolean borrow chain. Multiplication constrains shifted
partial products and their carry chains, discarding only bits above bit 31.
Five-stage barrel networks implement shifts/rotation; shifts additionally
check every high count bit. No result, partial product, count selector, or
carry is accepted as unconstrained advice. Both arguments must be canonical
Word32 cells with exact binary arity; the result's entire tag and payload,
including unused bits, are constrained.

The word prepare table grows from inner exponent 14 to 15 only for registries
admitting one of these five operations. Legacy registries emit the exact
original matrices. The primitive registry, actual matrices, wiring and
transcript remain bound to verifier-owned setup; no proof header can approve
the upgrade. This is primitive coverage, not a new guest instruction set or
a same-key capacity/registry upgrade.

Guest BLAKE3 uses the constrained bounded hash network, sharing compression,
selection and ROOT tables with the commitment chain. Every transition emits
the same network regardless of its opcode or private length. A host-computed
digest is not an accepted operation result. The final encoder dereferences
the genuinely halted return value and derives the complete canonical `IXBO`
output, preserving the distinction between empty bytes and erased rejection.
This provides the byte-result representation needed by the proposed Ixon ABI;
it does not certify the source wrapper or its success condition.

## Evidence and physical limits

The small packed byte and full-crypto proof corpora use:

| Capacity | Value |
| --- | ---: |
| Program bytes / functions / blocks / operands | 192 / 1 / 2 / 3 |
| Locals / continuations / arguments | 4 / 1 / 3 |
| Input bytes / values / output bytes | 192 / 3 / 192 |
| Per-array bytes / physical transitions | 65 / 3 |
| Row exponent / effective PCS exponent / tables | 12 / 23 / 36 |

The original thirty-opcode byte setup digest is
`5d2443a7f909e97fd1414963e8a4c4c5e534c43c8c477419763b84d2381b8092`.
Twenty-three real executions share that setup, each producing a 264,243-byte proof.
They cover all ten byte opcodes, scalar dispatch, empty and 65-byte values,
multi-block guest hashing, input returns, program literals, a 34-byte proposed
success result and erased rejection. Fresh verifier
processes receive only approved setup, expected S and proof, with a cleared
environment and working directory outside the repository.

Two further proofs replace a read row with recomputed advice for changed
record bytes, or replace an operation row with recomputed advice for a forged
hash digest. Both rows are locally valid; both proofs reject at
`Wiring(Gkr(ProductMismatch))`. Proof mutations, wrong expected output,
changed primitive registry and rewritten setup headers also reject.

Seven additional 388,683-byte proofs use a separate 33-byte-array, ten-step
setup to cover copies, both branches, calls, tail calls, self calls, returns,
byte-comparison-driven branching, and preservation of older allocations.
Two legacy-compression byte proofs cover append and multi-block guest hashing
with 251,227-byte bundles. They preserve the same semantic statement but
reject under packed setup, including after rewriting the proof's setup header.
Together these three suites check 32 successful byte-profile executions.

The full 35-opcode packed setup, with the same capacities and 36 table types,
has digest
`5cc6dd8434d9ca4a7ba350267467c4c5183eb0a3e8ae44cc562f1bc8c43a0707`.
Its 49-case corpus covers every crypto opcode under one setup plus subtraction
wraparound, multiplication carry/overflow and shift/rotate boundary counts.
Each complete proof is 268,147 bytes, versus 264,243 for the older registry.
Two malicious proofs fully recompute a locally valid word row after changing
either count 33 to 1 or shift to rotate; both fresh verifiers reject at
`Wiring(Gkr(ProductMismatch))`. Old/reduced registry replays, rewritten setup
headers and changed expected output also reject.

A separate seven-transition corpus composes multiply → subtract → rotate →
canonical word bytes → guest BLAKE3 → return → halt, under both packed and
legacy compression. Its capacities are program 256 bytes/one function/six
blocks/two operands, seven locals/one continuation/two arguments, input and
output 128 bytes/two inputs, and 33 bytes per array. Its row/effective PCS
exponents are 12/23, and its largest table inner exponent is 21. These two
additional proofs are 324,147 bytes (packed) and 346,267 bytes (legacy), bringing
the full-crypto corpus to 51 successful executions. Cross-backend pipeline
replays reject, including with a rewritten setup header. All 51 proofs verify
in fresh processes receiving only their verifier-owned setup, expected S and
proof. The same-source ordinary native suite passes 113 tests; 15 opt-in tests
remain ignored by the ordinary runner.

The initial wider control corpus exceeded a 32 GiB virtual-address limit:
its largest decoder table had k=23 with nu=13. The successful bounded control
corpus uses k=22 and nu=12. Effective PCS exponent alone does not predict
virtual witness memory. These are test fixtures, not a production guest-size
or peak-RSS benchmark.

The constructors admit per-array bounds 1–4096, up to 1024 immutable records
and at most 32768 bank words. Existing whole-program/input/output limits are
still 512 bytes, with at most four functions, eight blocks per function and
64 transitions. Larger numeric admission does not establish affordable proof
generation. This selector-bank construction is a bounded prototype, not a
scalable memory proof.

Ordinary constraint tests cover all partial input lengths through 65, exact
literal allocations, reserved/high bits, absence versus empty, noncanonical
field bytes, full-width indices, capacity boundaries, wrapped slices,
terminal/output conditions, forged outputs, and poisoned/recycled buffers.
`Tests.Ixby.Flock.Bytes` independently checks the pure Lean codec/interpreter,
all ten operations, BLAKE3 and the complete shared statement golden. It also
kernel-checks a three-transition byte-append reference trace and exact fuel.
That trace is not a proof about the native matrices.

The extended word tests also cover every single-bit input pair, multiplication
cross-carries, deterministic mixed words, every high shift-count bit, complete
result-cell bit mutations, malformed types/arity/padding and recycled buffers.
`Tests.Ixby.Flock.Words` independently checks 19 exact word boundary vectors,
the seven-transition word/byte/hash composition and its full statement digest.
It kernel-checks a three-transition wrapping-multiply reference trace and
insufficient fuel, without importing the native implementation.

## Remaining Stage 3 work

Structured constructors, closures/PAPs/application, scalable guest-size
execution, and a real compiled Stage 2 guest remain. The native
constraint-to-`Codec.Evaluates` refinement, certified
source/output ABI and compiler reflection are separate unfinished obligations.
No new production claim, cryptographic security approval, reviewed
zero-knowledge guarantee, or compact terminal proof follows from these tests.

Ordinary PR tests do not start these provers. Merge/manual CI has separate
600-second, 32 GiB tiers for byte and full-crypto proofs, both excluded from
the component-proof tier. Run the ordinary and opt-in proof tests with
explicit resource bounds:

```sh
cargo test --release --offline --locked --manifest-path flock-stage3/Cargo.toml -p ixby-flock
prlimit --as=34359738368 -- timeout 1200 env RAYON_NUM_THREADS=4 \
  cargo test --release --offline --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock ixby::exec::byte_tests:: -- --ignored --test-threads=1 --nocapture
prlimit --as=34359738368 -- timeout 1200 env RAYON_NUM_THREADS=4 \
  cargo test --release --offline --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock ixby::exec::crypto_tests:: -- --ignored --test-threads=1 --nocapture
lake build Tests.Ixby.Flock.Bytes Tests.Ixby.Flock.Words
```
