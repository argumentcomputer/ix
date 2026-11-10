# Canonical Aiur bytecode, version 1

*Part of the [legacy Aiur bytecode model](aiur-backend.md#status-in-the-plan), which
neither Aiur route of the plan uses; frozen, to be retired or re-pinned.*

`aiur-bytecode/1` gives the complete pinned `IxCC.Vendor.Aiur.Bytecode.Toplevel` a
canonical binary representation and BLAKE3 content root. The implementation
is [IxCC.Aiur.Wire](../IxCC/Aiur/Wire.lean). It preserves every
field, including layouts, debug text, circuit membership, and call-component
metadata. Reader limits are supplied by the consumer and are not encoded.

This is the IxCC wire boundary. The upstream IxVM exporter and AIR
constraint dump are still needed to instantiate it on the production IxVM.
Decoding does not establish SSA validity, circuit partition validity, bytecode
execution, or correspondence to a keyed AIR. The separate component check
retains exactly the pinned upstream check described below.

## Frame and primitives

The preimage is the following concatenation, with no alignment or padding:

```text
ASCII("aiur-bytecode/1") || 00 || string(revision) || toplevel
revision = "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03"
root = BLAKE3(preimage)                       # 32 bytes
```

The revision is an exact, case-sensitive string. The fixed header occupies
57 bytes: 16 domain bytes, a one-byte length of 40, and the revision's ASCII
bytes. It identifies the eleven upstream modules recorded in
[upstream.json](../IxCC/Vendor/upstream.json). This format has its own
version; it is not the native Aiur FFI serialization.

| Notation | Bytes |
| --- | --- |
| `N` | Minimal unsigned LEB128 over arbitrary-precision natural numbers: low seven bits first, bit 7 means continuation. Zero is `00`; redundant high zero groups are forbidden. |
| `F` | Exactly eight little-endian bytes for a Goldilocks representative strictly below `p = 2^64 - 2^32 + 1`. No modular reduction on input. |
| `B` | Exactly `00` for false or `01` for true. |
| `string` | `N` UTF-8 byte length, then exactly those bytes. Invalid UTF-8 is rejected; NUL and empty strings are preserved. |
| `array(T)` | `N` element count, followed by each `T` in order. |
| `option(T)` | `00` for none, or `01` followed by `T` for some. |

Indices, selectors, sizes, component orders, and all length prefixes use
`N`; none are truncated to a machine word. Array order and duplicates remain
part of identity. `none`, `some ""`, and `some #[]` retain their distinct
spellings. The wire layer performs no sorting, deduplication, or name cleanup.

## Records and control trees

Every record is the concatenation of the fields in this table, with no
record tag. The names describe the pinned upstream fields.

| Record | Fields in wire order |
| --- | --- |
| `Toplevel` | `array(Function) functions`, `array(N) memorySizes`, `array(Circuit) circuits`, `array(CallComponent) callComponents` |
| `Function` | `Block body`, `FunctionLayout layout`, `B entry`, `B constrained` |
| `FunctionLayout` | `N inputSize`, `N selectors`, `N auxiliaries`, `N lookups` |
| `Circuit` | `string name`, `array(N) members`, `FunctionLayout layout` |
| `CallComponent` | `N order`, `B ranked` |
| `Block` | `array(Op) ops`, `Ctrl ctrl` |
| case | `F key`, `Block body` |

`Ctrl` starts with one byte, followed by these payloads:

| Tag | Constructor | Payload |
| --- | --- | --- |
| 0 | `match` | `N value`, `array(case) cases`, `option(Block) fallback` |
| 1 | `return` | `N selector`, `array(N) values` |
| 2 | `yield` | `N selector`, `array(N) values` |
| 3 | `matchContinue` | `N value`, `array(case) cases`, `option(Block) fallback`, `N outputSize`, `N sharedAuxiliaries`, `N sharedLookups`, `Block continuation` |

All other control tags are rejected. A continuation is serialized exactly
once at its position in the tree. It is not duplicated into each branch.

## Opcodes

`Op` starts with one tag byte. Tags follow the pinned constructor order;
their payloads below are the complete constructor arguments in that order.
`Ns` abbreviates `array(N)`.

| Tag | Constructor | Payload |
| --- | --- | --- |
| 0 | `const` | `F value` |
| 1 | `add` | `N left`, `N right` |
| 2 | `sub` | `N left`, `N right` |
| 3 | `mul` | `N left`, `N right` |
| 4 | `eqZero` | `N value` |
| 5 | `call` | `N function`, `Ns arguments`, `N outputSize`, `B unconstrained` |
| 6 | `store` | `Ns values` |
| 7 | `load` | `N size`, `N pointer` |
| 8 | `assertEq` | `Ns left`, `Ns right`, `option(string) message` |
| 9 | `ioGetInfo` | `N arg0`, `Ns arg1` |
| 10 | `ioSetInfo` | `N arg0`, `Ns arg1`, `N arg2`, `N arg3` |
| 11 | `ioRead` | `N arg0`, `N arg1`, `N size` |
| 12 | `ioWrite` | `N arg0`, `Ns arg1` |
| 13 | `u8BitDecomposition` | `N value` |
| 14 | `u8ShiftLeft` | `N value` |
| 15 | `u8ShiftRight` | `N value` |
| 16 | `u8Xor` | `N left`, `N right` |
| 17 | `u8Add` | `N left`, `N right` |
| 18 | `u8Mul` | `N left`, `N right` |
| 19 | `u8Sub` | `N left`, `N right` |
| 20 | `u8And` | `N left`, `N right` |
| 21 | `u8Or` | `N left`, `N right` |
| 22 | `u8LessThan` | `N left`, `N right` |
| 23 | `u32LessThan` | `N left`, `N right` |
| 24 | `u8XorSplit7` | `N left`, `N right` |
| 25 | `u8XorSplit4` | `N left`, `N right` |
| 26 | `debug` | `string message`, `option(Ns) values` |
| 27 | `u8RangeCheck` | `N left`, `N right` |
| 28 | `unconstrainedBigUintDivMod` | `N numerator`, `N denominator` |
| 29 | `unconstrainedGToBytes` | `N value` |
| 30 | `unconstrainedGInverse` | `N value` |
| 31 | `unconstrainedU32Add` | `Ns left`, `Ns right` |
| 32 | `unconstrainedU32Add3` | `Ns first`, `Ns second`, `Ns third` |
| 33 | `u32ToField` | `Ns bytes` |

All other opcode tags are rejected. These argument names are descriptive;
the wire contract is the argument type and position, not an execution
specification for the operation.

## Admission and proved guarantees

The default `Wire.Limits` allow 16,777,216 input bytes, 64 bytes per natural,
65,536 elements per array, 1,048,576 bytes per string, and 128 nested block
entries along any path. Entering a function body uses one depth unit; each
branch, fallback, or shared continuation uses one more. A return/yield does
not consume another unit. Depth zero admits an empty toplevel. The fixed
header is compared directly rather than parsed as a budgeted string.

`decode` checks total size before parsing, bounds counts before traversal,
requires complete consumption, and compares the complete re-encoding with
the input. This last check also rejects nonminimal LEB128 spellings. Low-level
`get*` readers are implementation components; `decode` is the strict ingress
boundary. `encodeChecked` returns bytes with their exact-preimage and
representability proofs. Raising a budget changes admission, not identity.

[CodecProofs](../IxCC/Aiur/Wire/CodecProofs.lean) proves round-trip for
every toplevel satisfying `Fits limits`, canonical bytes and `Fits` for every
successful decode, and preimage injectivity within that representable domain.
The proofs cover all opcodes and recursive controls. They use only the
ordinary logical axioms. The fixed-width field proof reuses a kernel-proved
eight-byte integer reconstruction lemma.

`decodeAddressed` also checks the supplied BLAKE3 root. `Addressed.matches`
recovers an expected artifact from root equality under an explicit pairwise
`Address.Blake3NoCollision` premise. Addressed theorems inherit the existing
ledgered native BLAKE3 exception; no new hash interface or axiom is added.
Equal 256-bit digests are not assumed globally injective.

`checkComponents` uses the pinned `Toplevel.validCallComponents` when the
component array is nonempty. Empty components select the general ranked
fallback. Before running the upstream analysis, it caps function count,
depth, candidate count, declared value allocations, and an analysis work
score. These are separate consumer limits because a small LEB128 integer
can otherwise request an enormous upstream array. The score is conservative
admission policy, not a proved machine-time bound. `ComponentChecked` retains
both the budget predicate and the exact Boolean result. `ingest` combines
this evidence with addressed decoding.

The result does not prove the upstream checker sound for the AIR, verify
actual rank columns, or validate a circuit partition. Those obligations
remain with bytecode semantics, static-certificate soundness, and extraction
from the keyed constraint system.

## Fixtures and exporter handoff

[The fixture inventory](../fixtures/aiur-bytecode/expected.json) freezes four
binary preimages, roots, and record counts. The empty, unit-counter, and
ranked-mutual cases exercise distinct component modes. `wire-corpus` covers
all 34 opcodes, all four controls, shared continuations, Unicode/NUL strings,
option forms, metadata, and a natural larger than a machine word. It
deliberately includes semantically invalid indices and circuit membership;
its acceptance tests only representation and the stated component check.

The expected bytes are handwritten in
[WireFixtures](../IxCCTests/Aiur/WireFixtures.lean), independently of
the encoder. `tests-aiur` compares those bytes and runs 308 wire assertions
in addition to the original 25 trace regressions. `check-aiur` compares a
fresh fixture process against the frozen files, replays each in another
process, checks its root/counts, and rejects seven corruptions. Its original
vendor-inventory and four inventory mutation checks remain required.

```sh
lake build tests-aiur check-aiur IxCCTests.Fences.AiurWire
lake exe tests-aiur
lake exe check-aiur --root .
lake exe check-aiur --bytecode fixtures/aiur-bytecode/unit-counter.bin \
  --expect-root 9f3d24e0e80b7bb3a788b657cc16608a652ba30da0d0fb3abb0ab58a16658307
nix build .#checks.x86_64-linux.ixcc-aiur
```

The bytecode CLI emits a JSON report; optional `--output PATH` writes its
canonical re-encoding after all checks succeed. File reads are capped before
allocation. The required proof aggregate contains 33 additional exact axiom
assertions for the wire proofs and small component examples.

An ix exporter should write the exact frame above from the complete pinned
post-lowering `Toplevel`, preserving every field and order. Export its
BLAKE3 root and the corresponding counts alongside the `.bin` file, then
compare all four frozen fixtures before exporting the IxVM. The certificate
already resides in `callComponents`; omitting it changes the artifact and
selects the ranked fallback. An AIR dump, descriptor/key identity, and source
identity will need their own explicit binding to this bytecode root. They
are not present or certified by version 1 of this bytecode frame.
