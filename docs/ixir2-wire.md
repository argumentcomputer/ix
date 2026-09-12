# Canonical IxIR₂ snapshots

Version: `ixir2-snapshot/1`. Reviewed 2026-09-12.

This contract freezes the complete binary snapshot of an IxIR₂ program and
its finite validation context. Its BLAKE3 root commits to actual declaration
bodies, signatures, capabilities, block order, instructions, terminators,
schemas, exact layout preimages, scalar-leaf facts, dependencies, and policies.
The [semantic specification](ixir2-spec.md) separately defines execution.
Wire version 1 supports both existing credit policies.

The implementation is
[`Wire.lean`](../Compilatrix/IxIR2/Wire.lean),
[`Serialize.lean`](../Compilatrix/IxIR2/Serialize.lean),
[`Decode.lean`](../Compilatrix/IxIR2/Decode.lean), and
[`WireCheck.lean`](../Compilatrix/IxIR2/WireCheck.lean).
Changing a tag, field order, primitive encoding, or domain requires a new
wire version. Diagnostic JSON is an inspection view and has no identity role.

## Identity and ordering

The preimage is the exact ASCII string `compilatrix/ixir2/snapshot/1`, one
NUL byte, and the encoded `Artifact` below. The root is the 32-byte BLAKE3
digest of that entire preimage. The root itself is supplied separately to
addressed ingress; it is not embedded in its own preimage.

Declaration keys are retained as exact logical symbols. They may originate
in the addressed IxIR₁ graph or in a checked specialization. The snapshot
does not claim they hash their current IxIR₂ bodies. Storing every body in
one finite snapshot avoids recursive hash equations, including for mutually
recursive declarations. A changed body changes the preimage even when its
logical key and the source dependency roots stay the same.

All arrays and lists retain their given order, including declarations,
dependencies, layouts, schemas, scalar facts, blocks, alternatives, and pass
versions. Reordering changes identity. Block IDs remain array indices and
value/credit IDs remain local ordinals. Canonical renumbering or rekeying would
be a separate checked transform with its own semantic obligations.

Dependency rows commit to a role and a root. The baseline source adapter
records the actual IxIR₁ optimizer graph root; the source fixtures also record
their Ixon entry root. These fields commit to the supplied provenance inputs;
parsing them does not establish a derivation from those inputs. Similarly,
layout keys commit to the exact supplied layout preimages. Their target ABI
meaning requires the contract selected by the layout policy.

Consumer resource budgets are outside byte identity. A cache storing checker
results or semantic evidence must additionally key the applicable checking
budgets, policies, and premises. This format provides an independently
comparable intermediate root; it does not implement a durable transactional
store or modular source certificates. Existing native ELF provenance retains
its documented IxIR₁-plus-policy contract until a consumer explicitly adopts
this snapshot format.

## Primitive grammar

Concatenation has no alignment, padding, or implicit lengths. Products encode
their fields in the order listed below. Every sum begins with one raw tag
byte. All unspecified tags are invalid.

| Primitive | Encoding |
| --- | --- |
| `Nat` | Minimal unsigned LEB128 over arbitrary-precision naturals; zero is `00` |
| `Bool` | One byte: false `00`, true `01` |
| `Owned` | One byte: unique `00`, shared `01` |
| `Address`, `LayoutId` | Exactly 32 raw bytes |
| `Blob` | `Nat` byte length, followed by those bytes |
| `String` | `Blob` containing valid UTF-8, with no Unicode normalization |
| `Seq T` | `Nat` element count, then each encoded `T` in order; common to arrays and lists |

Natural-number encoding never passes through `UInt64`. In particular, `2⁶⁴`
encodes as `80 80 80 80 80 80 80 80 80 02`. A string's limit counts UTF-8
bytes, not characters. Different Unicode normalization forms have different
bytes and roots. No integer or length may use an overlong spelling.

## Product fields

The Lean records use the following exact sequence of fields. Namespace
qualifiers are omitted where the names are unambiguous.

| Product | Fields in wire order |
| --- | --- |
| `Artifact` | `Policy`, `Seq Dependency`, `Seq Layout`, `Seq Schema`, `Seq ScalarLeafFact`, `Program` |
| `Policy` | semantics `String`, validator `String`, lowering `String`, passes `Seq String`, layout `String`, `CreditPolicy`, allowExtern `Bool` |
| `Dependency` | role `String`, root `Address` |
| `Layout` | identity `LayoutId`, preimage `Blob` |
| `Schema` | world `Owned`, constructor `CtorId`, definition `CtorSchema` |
| `CtorId` | block `Address`, indIdx `Nat`, cidx `Nat` |
| `CtorSchema` | layout `LayoutId`, fields `Seq Owned` |
| `ScalarLeafFact` | `Owner`, block `Nat`, value `Nat`, `CtorId` |
| `Program` | declarations `Seq DeclEntry`, main `Function` |
| `DeclEntry` | key `Address`, `Decl` |
| `Function` | `Signature`, blocks `Seq Block` |
| `Signature` | params `Seq Param`, result `Owned`, papSafe `Bool` |
| `Param` | world `Owned`, `ParamPassing` |
| `Block` | valueParams `Seq ValueCap`, creditParams `Seq CreditCap`, instructions `Seq Instr`, `Terminator` |
| `Edge` | target `Nat`, values `Seq Atom`, credits `Seq Nat` |
| `CtorAlt` | `CtorId`, `Edge` |
| `NatPeel` | zero `Edge`, succ `Edge` |

For example, an empty-declaration program with an argument-free shared main,
one empty block and return literal `42` has the program suffix
`00 00 01 00 01 00 00 00 03 01 00 2a`. This is a program suffix, not a complete
framed artifact. Both this vector and `2⁶⁴` are kernel-evaluated guards in
[`WireTests.lean`](../Compilatrix/IxIR2/WireTests.lean).

## Sum tags

Numbers in the tag column are decimal single-byte values. Fields after the
constructor use the product and primitive grammar above.

| Type | Tag and constructor with fields |
| --- | --- |
| `Literal` | 0: nat `Nat`; 1: str `String` |
| `Atom` | 0: reg `Nat`; 1: lit `Literal`; 2: erased |
| `ParamPassing` | 0: owned; 1: borrowed |
| `BorrowLender` | 0: caller; 1: value `Nat` |
| `ValueCap` | 0: scalar; 1: owned `Owned`; 2: borrowed `Owned` `BorrowLender` |
| `CreditCap` | 0: required `LayoutId`; 1: optional `LayoutId` |
| `Option NatPeel` | 0: none; 1: some `NatPeel` |
| `Decl` | 0: fn `Function`; 1: extern `Nat` |
| `CreditPolicy` | 0: callLocalV0; 1: suspendedCallsV1 |
| `Owner` | 0: main; 1: declaration `Address` |

| `Instr` tag | Constructor and fields |
| ---: | --- |
| 0 | move `Atom` |
| 1 | alloc `Owned` `CtorId` `Seq Atom` |
| 2 | allocWith credit `Nat` `Owned` `CtorId` `Seq Atom` |
| 3 | discardCredit `Nat` |
| 4 | takeUnique `Atom` `CtorId` |
| 5 | resetShared `Atom` `CtorId` |
| 6 | retainShared `Atom` |
| 7 | releaseShared `Atom` |
| 8 | dropUnique `Atom` |
| 9 | freeUnique `Atom` `CtorId` |
| 10 | fetch `Atom` `CtorId` field `Nat` |
| 11 | call `Address` `Seq Atom` |
| 12 | callSelf `Seq Atom` |
| 13 | papp `Address` `Seq Atom` |
| 14 | apply `Atom` `Seq Atom` |
| 15 | extern `Address` `Seq Atom` |

| `Terminator` tag | Constructor and fields |
| ---: | --- |
| 0 | jump `Edge` |
| 1 | switchValue `Atom` `Seq CtorAlt` `Option NatPeel` |
| 2 | branchCredit credit `Nat` present `Edge` absent `Edge` |
| 3 | ret `Atom` |
| 4 | tailCall `Address` `Seq Atom` |
| 5 | tailCallSelf `Seq Atom` |

## Bounded decoding and validation

[`IxIR/Bounded.lean`](../Compilatrix/IxIR/Bounded.lean) defines inclusive reader
limits, supplied by the consumer:

| Limit | Default |
| --- | ---: |
| Complete framed input | 16 MiB |
| Bytes per LEB128 natural, including counts | 64 |
| Elements in any one sequence | 65,536 |
| Bytes in any one blob or UTF-8 string | 1 MiB |

The default natural limit admits values through `2⁴⁴⁸ − 1`. It is a parsing
budget, independent of the native Word representation. Counts and blob sizes
are checked before traversing their payload; the input cap is checked before
parsing. Counted lists use an accumulator and the grammar has fixed nesting
depth. Full consumption, exact re-encoding, and the recursive representation
predicate are required before decoding succeeds.

`Artifact.Fits limits` states both the total encoded-byte bound and every
nested natural/count/blob bound. `encodeChecked` checks the nested bounds,
then constructs the encoding and checks its total length. Its total-byte test
is not a preflight bound on allocating the encoding of an already supplied
in-memory artifact. Untrusted file ingress uses
[`WireIO.readBounded`](../Compilatrix/IxIR2/WireIO.lean), which reads at most
the input cap plus one byte, even if the file grows. Files of exactly the cap
are admitted. The parser does not rely on a prior file-size observation.

The public boundaries are deliberately separate:

| API | Successful result establishes |
| --- | --- |
| `Artifact.decodePreimage` | Exact canonical bytes and `Fits` for the supplied limits |
| `Artifact.decodeAddressed` | The above and equality to the separately supplied BLAKE3 root |
| `Artifact.check` | Finite metadata coherence and acceptance by the existing policy-indexed ownership validator |
| `Artifact.ingest` | Addressed decoding and checking, retaining both results in an `Ingress` |

Checking requires semantics `ixir2-semantics/0` and validator
`ixir2-ownership-flow/1`. Dependency roles must be nonempty and unique;
layout identities and `(world, constructor)` schema keys must be unique.
Every layout preimage must hash to its key. Schema layouts and block credit
layouts must occur in the layout inventory. Each scalar fact must identify
an existing function and block. The old ownership validator then checks the
actual program against the decoded finite context, declared credit policy,
and caller-supplied `Validate.Limits`.

Lowering, pass, and layout-policy strings remain committed provenance inputs;
this generic checker does not interpret every possible producer policy.
Scalar-fact coordinate checks do not prove the claimed semantic fact.
Successful ingress alone therefore supplies neither source certification nor
ABI interpretation of opaque layout bytes. Consumers retain those premises
or recover them from an independently certified expected artifact.

## Proof and source boundary

`Artifact.decodePreimage_roundtrip` covers every artifact satisfying the
declared `Fits` domain. `decodePreimage_canonical` covers every successful
decode, including arbitrary input bytes; `decodePreimage_fits` exposes its
resource bounds. `preimage_injective` follows on that representable domain.
`Encoded.roundtrip` packages the public checked-encoder result.

`Addressed.root_eq` relates the actual input bytes to the supplied root.
`Addressed.matches` recovers equality with a bounded expected artifact under
the existing pairwise `Address.Blake3NoCollision` premise. There is no claim
that a 256-bit digest is globally injective. `Ingress.validated` exposes exact
bytes, root equality, coherent sidecars, and acceptance of the decoded program
by the original validator.

[`WirePipeline.lean`](../Compilatrix/IxIR2/WirePipeline.lean) exports every
checked `CompiledAttachment` and actual shared-call-reuse selection.
[`WireBorrow.lean`](../Compilatrix/IxIR2/WireBorrow.lean) exports the actual
borrow selection, including fallback. Their program/context equalities and
validator-acceptance theorems preserve the original checked target. Their
`matches` theorems recover that exact program and context from independently
parsed bytes under root equality, representability, and the pairwise collision
premise. Baseline versions are `structured-ownership-lowering/1` and
`baseline-constructor-world/0`; selected pass versions are
`shared-call-reuse/1` and `borrowed-direct-calls/1`. Fallback retains the empty
baseline pass list. The underlying source and ownership hypotheses remain
those of the existing attachments.

Twenty exact axiom cones are pinned in
[`Fence.lean`](../Compilatrix/Fence.lean). The bounded codec and roundtrip laws
use only existing logical axioms. Addressed and source-context compositions
expose the existing BLAKE3 native exception; this adds no native interface.
See the [trust ledger](trusted-extern-ledger.md).

## Executable gate

The Nix `ixir2-identity` check builds two fresh artifact sets and compares
their complete inventories and bytes against each other and a
[frozen report](../fixtures/ixir2/expected.json).
[`Tools/IxIR2Check.lean`](../Compilatrix/Tools/IxIR2Check.lean) has an independent
strict parser without importing the IxIR₂ codec, compiler, or evaluator.
It decodes every binary field, reconstructs the complete inspection JSON,
recomputes roots/layout keys and structural statistics, and checks decoded
results and terminal heaps against the source inputs. The process driver
also probes the real public decoder and checker.

The retained matrix has 12 snapshots: one full-syntax fixture, one checked
finite-context fixture, and baseline/selected pairs for three actual Ixon
maps and two actual Ixon borrowed-call sources. Ten source snapshots execute
before and after decoding with identical values, stores, counters, and fuel;
their returned heaps are fully reclaimed. The full-syntax fixture exercises
all tags and cyclic logical references and is intentionally outside ownership
acceptance. The other eleven snapshots pass ingress.

The producer checks 51 identity mutations, 56 malformed/resource/ingress
boundaries, all 18,802 proper prefixes of the snapshots, and eight exact/over
file-size boundaries. Mutations preserve their own decodability while changing
bytes and roots and failing under the old root. The independent gate rejects
15 corrupted artifacts/reports, including a report corruption that agreement
between fresh producers alone would miss. No benchmark or general compiler-scaling claim follows
from this finite matrix.

```sh
lake build ixir2-fixture check-ixir2
./.lake/build/bin/check-ixir2 --fixture .lake/build/bin/ixir2-fixture
./.lake/build/bin/ixir2-fixture /tmp/new-ixir2-artifacts
./.lake/build/bin/ixir2-fixture --ingest FILE.ixir2 ROOT_HEX
nix build .#checks.x86_64-linux.ixir2-identity
```

The artifact-output directory must not already exist. The checker defaults
to `fixtures/ixir2/expected.json`; changing that golden requires reviewing the
complete format/source change and updating its trust-ledger integrity pin.
