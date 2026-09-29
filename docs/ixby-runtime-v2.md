# Ixby runtime revision 2 integration

Compilatrix now emits format 1, semantics 2 for IXBF programs, IXFI inputs,
and IXFO outputs. All 15 vendored Ixby source files match upstream revision
`6836a77c3f432c83c42428490e56811f4a69808d`; there are no mixed-revision codec
exceptions. The compiler uses Lean 4.34.0. The [vendor inventory](../vendor/ixby/upstream.json)
and [binary specification](ixby-binary.md) define the exact source and wire ABI.

The typed runtime uses unboxed Nat/Word32/Field conversions, native persistent
arrays, checked byte slices, and immutable writer builders. Its certificates
bind 97 runtime and ten wire helpers to complete emitted bodies. The
[representation contracts](ixby-representation.md) and unrestricted
[chunked executor simulation](../Compilatrix/Ixby/Runtime/Chunked/Simulation.lean)
use ordinary Lean logic. General LCNF/source-image refinement and native
collection-circuit refinement remain open.

## Artifacts and commitments

The [machine-readable record](../fixtures/ixby-stage2/runtime-v2-integration.json)
contains SHA-256/BLAKE3 hashes, sizes, P/B/I/O/S commitments, compiler/observer
provenance, the complete CSLib helper census, and the fresh native-verification
receipt. Each profile is 184 bytes, independently encoded from the ten u128
limits and u64 step budget, then compared with the pinned upstream codec.
Independent `b3sum` calls derive:

```text
H_d(x) = BLAKE3("IxBy/commit/v0" || 00 || u8(d) || x)
P = H_0(profile)       B = H_1(P || program)
I = H_2(B || input)    O = H_3(B || output)
S = H_4(P || B || I || O)
```

| Image | Program / input / output bytes | Expected statement S |
| --- | ---: | --- |
| Stage2 Init | 991,142 / 8,555,864 / 49 | `7716996c249d5abb9e6ab0b93ad1da212ca9ed6d96c4f27a4cb11c8db5a49239` |
| CSLib | 1,005,374 / 4,813,238 / 49 | `606c7970ae81d1773249b6652dd1a31b685ea2b0d54fc73bd4fd786ae808caeb` |
| Eleven-opcode runtime fixture | 248 / 21 / 78 | `f400d5a93a4d6fb68520ccc322316c2872f1b5f0767f5ac0cf44b51dc81736bb` |
| Direct conversion fixture | 77 / 25 / 19 | `53f7f210d951fd77f45fb24c69d96cc595be9778fb625f5f112f4c5bb1f77876` |

Small current fixtures are retained under [runtime-v2](../fixtures/ixby-stage2/runtime-v2/README.md)
and [conversions-v2](../fixtures/ixby-stage2/conversions-v2/README.md).
The historical [revision 1 record](ixby-nat-word32.md) and `conversions-v1`
artifacts remain explicitly historical; current loaders reject their revisions.
No old statement or proof is reused as evidence for changed artifact bytes.

Full Stage2/CSLib program, input, expected output, profile, and statement files
are exported locally under `plans/ixby-runtime-v2/handoff/{stage2,cslib}`.
The adjacent handoff includes compiler/observer sources, reports, and logs.
These large local exports are gitignored; their identities and results are in
the committed integration record. Reproducing CSLib requires the retained
CSLib keys and native proof payload identified by that record.

## Measured CSLib execution

The adapted Stage2 compiler uses the retained CSLib keys, child entry 766,
and aggregate entry 243. Two fresh compilations produce identical binaries
and inventories. The observer runs the chunked machine directly and converts
its final result once; it never flattens builders for per-step observation.
The universal simulation establishes that its logical transitions are the
reference transitions. It compares the complete canonical output against the
retained independent source-verifier result. Re-encoded I/O bodies are byte
identical to the retained payloads; only their semantic headers change.

| Measurement | Revision 1 | Revision 2 |
| --- | ---: | ---: |
| Logical transitions | 2,033,412,182 | 360,337,913 |
| Maximum observed Nat width | 65 | 65 |
| Maximum frame locals observed | 73 | 66 |
| Maximum continuations observed | 647 | 647 |

The reduction is **1,673,074,269 transitions, or 82.28%**. This is measured
logical work, not a proof-generation speedup. The local revision 2 observer
used 72.61 seconds wall time, 72.17 seconds user time, and 574,524 KiB maximum
RSS on an AMD Ryzen 9 7950X3D, with warm build artifacts and other proof-build
work in the session. The observer implementation changed, so these timings
do not establish a controlled wall-time comparison.

Its 303,848,647 Eval, 55,345,920 Return, and 1,143,346 Apply transitions sum to
the exact total. The census attributes Eval steps to actual function indices
and validates every function's block span. `natural`, `lowWord`, and the
weighted conversion helpers have zero Eval steps in this workload. Interpreted
array-tree and byte-tree helpers are absent. Remaining leading helper costs:

| Helper | Own Eval transitions |
| --- | ---: |
| `Array.getInternal` | 33,909,018 |
| `Array.size` | 27,285,520 |
| `Ixby.Runtime.toList` | 17,724,990 |
| Wire `writeBytes` | 11,490,354 |
| `Array.push` | 9,148,888 |

Counts include a function's call instructions; callee work belongs to the
callee. Scalar/byte maxima inspect operands, newly bound locals, returns, and
applications, rather than traversing the complete reachable heap.

The paged backend still has physical Nat128 and heap/frame bounds. Observing
65-bit values in this run is not a universal admission theorem. No complete
CSLib native proof or setup was produced by this integration.

## Native fixture verification

The runtime fixture exercises all eleven revision 2 opcodes, nested persistent
updates, an input array, unaligned 31/34-byte chunks, and a slice. Compiler and
independent upstream encodings agree byte for byte. Execution takes 15 logical
transitions and yields the exact 78-byte output transport. Upstream's native
record reports 75 physical microsteps.

A fresh local process compiled the fixed bytes-class setup and accepted the
existing **517,843-byte revision 2 root proof**, with the independently derived
S above. Its setup identity is
`3fcc2e3d943c6e41e7826e3f0b93ed6ca726ff0f903aff0ba743f4d9ffbcd4f0`;
setup took 149.678 seconds and verification 23.144 seconds, using two workers
and `MALLOC_ARENA_MAX=2`. The committed receipt binds the exact verifier and
proof hashes. The proof was verified locally, not regenerated locally.
Upstream's retained source record separately records eleven rejected
statement/proof mutations.

```sh
env MALLOC_ARENA_MAX=2 /tmp/ixby-runtime-v2-20260916/paged-execution-native-v2 verify \
  --profile fixtures/ixby-stage2/runtime-v2/profile.ixfp --class bytes --threads 2 \
  --counts 1,3,1,1,1,1,1,1,1,1,1 \
  --statement fixtures/ixby-stage2/runtime-v2/expected.statement \
  --proof /tmp/ixby-runtime-v2-20260916/proof/root.flock
```

The direct-conversion fixture has regenerated current artifacts and a checked
seven-transition execution. Its historical revision 1 root does not prove the
new statement; no revision 2 root is claimed for that separate fixture.

## Compiler validation

The required gate retains all previous 2,414 exact axiom assertions and all
267 runtime failure assertions. It adds 235 ordinary-logical theorem roots,
22,794 chunked/reference comparisons, and 94 decoded binary executions.
The helper suite passes 40,839 independent expected-result cases, 900 bounds
rejections, 107 caller cases, 65 resource cases, and 391 exact-fuel cases.
All 2,240 body/layout/binding mutations reject; 1,404 remain structurally
admitted. The original 4,585 source comparisons and two compiler rejections
remain. The [coverage mapping](ixby-representation.md#required-validation-and-retained-coverage)
records replacement of obsolete boxed/cache/tree execution cases.

The Stage2 image passes all retained cases from serialized bytes:

| Case | Result | Logical transitions |
| --- | --- | ---: |
| Valid proof | Exact 34-byte claim | 711,293,203 |
| Changed claim root | Erased | 218,497,724 |
| Empty proof | Erased | 28,497,638 |
| Truncated proof | Erased | 144,861,894 |
| Trailing public byte | Erased | 70 |
| Trailing proof byte | Erased | 144,864,721 |
| Wrong claim kind | Erased | 147 |
| Malformed proof | Erased | 28,497,638 |

The source backend additionally passes 33 cases, 270 generated programs,
29 rejections, five canonical runs, and 35 artifact corruptions. Its symbolic
backend passes 44 certificates, 576 reference runs, 203 canonical runs,
30 rejections, and seven artifact corruptions. Both use the current profile
and reject retired revisions. Required Nix checks retain fresh artifact
comparison, independent decoding, standalone execution, trust auditing, the
complete proof aggregate, and every Stage2 case.
