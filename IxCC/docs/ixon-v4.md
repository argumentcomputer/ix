# Ix frontend and Ixon v4

IxCC consumes closures produced by ix's shared Lean frontend: usage,
ownership, relative locality and scoped shared borrowing are written in the
source and carried, as contracts, in the content-addressed objects. Aiur is
one consumer. IxCC consumes the resulting binary objects; it does not
introduce another parser or elaborator.

Three ix sources matter, for three different things:

- **The wire** is Ixon **v4** (`ixon-v4`), as this repository's `ix` writes it
  (`Ix/Ixon.lean`; the version-5 envelope adds the role binding, [byte
  contract](byte-contract.md)).
- **The codec** that reads and writes it is a Lake dependency: ix's `IxCK/`
  package (`«ix-ck»`), beside IxCC in the ix workspace (`../IxCK`), of which
  IxCC imports the 11 modules of `IxCK.Ixon.Canonical`'s import closure (Init
  only), and, to read role-bound environments, the kernel's role vocabulary
  (`IxCK.Kernel.Key`, with `IxCK.Kernel.Name`; [byte contract](byte-contract.md)). They are ix's Ixon codec under the `IxCK` module root, without an unused error type, and with a TagN fast path:
  two `@[csimp]` theorems make compiled code use copies of `putTagN` and
  `getTagN` specialized to the flag widths 0, 2 and 4. It is the only reader
  and writer of constant, expression and universe bytes. The trust ledger pins
  it by the SHA-256 of each of those files ([trust
  ledger](trusted-extern-ledger.md), `lean_dependencies`); they were last
  reviewed as of the integrity pins recorded there.
- **The data model** was adapted from an earlier ix
  (Ixon v3, a revision outside this repository's history; v3 introduced the
  contract-carrying model and v4 changed only the wire), with the primitive
  table (`V3.PrimAddrs`), which follows this repository's `Ix/PrimAddrs.lean`
  (`refreeze-ixon tc-primitives`). The erased type checker adapted with it
  was deleted by the switch to the certified kernel
  ([kernel front end](kernel-front-end-design.md)), and IxCC's private v4
  resource checker/adapter (`V3.Resource`, `V3.Validate`, `V3.Source`,
  `Src.Resource`) was retired ahead of the Ixon v5 migration.

The producer of the committed fixtures is the ix of this repository (`lake
build ix`): `ix compile --equations` writes the role-bound closures and their
unfolding equations ([corpus](corpus.md), "Refreezing";
`lean --run IxCC/tools/Regenerate.lean --check` says whether they are current). The erased
checker's typing bundles went with the checker. IxCC's catalog support
(catalog-v2 admission under validator 1, which certified the erased checker's
typing) is retired: ix retired validator 1, and reading catalogs again means
building against its current validator.

## Contract and wire boundary

[`IxCC.Ixon.V3`](../IxCC/Ixon/V3.lean) is the data model: all
twelve expression constructors with these addressed fields (the namespace
keeps the name of the Ixon version that introduced it):

| Field | Meaning and encoding |
| --- | --- |
| `Uses` | Erased, linear, affine or many; low two binder bits |
| `ValueContract.owned` | Shared or unique; independent of usage |
| `ValueContract.locality` | Unrestricted or confined to an implicit scope |
| `BinderContract` | Usage plus input value contract; four bits |
| Forall result | Separate ownership and locality; six bits for the complete input/result byte |
| `LetContract` | Binder byte plus `nonDep` and `value`/`borrowShared` flags |

For example, the producer syntax `(~!1 x : A)` denotes a linear, unique,
local input. `(~1 x : A)` is linear, shared and local. Ordinary inputs are
many/shared/unrestricted. A local result annotation belongs to its arrow;
it is not inferred from the lambda's input. `let borrow (~ view : A)` creates
a shared loan bounded by that let body's scope. An ordinary local let does
not create a loan. Native `@&` metadata is a separate calling convention hint.

Locality constrains escape through results, captures, stores and loans.
It does not promise stack placement, a region allocator or RC elimination.
Unified contract mode accessors (`usage`, `isUnique`, `isBorrowed`, `isDefault`,
`binderMode`, `isErased`) in `IxCC.Ixon.V3.Contracts` insulate downstream passes
and relevance proofs from the wire representation.

**The wire.** Every integer is a TagN integer (ix's `putTagN`/`getTagN`): a
flag of `f` bits and a value in rungs of 1, 2, 3, 4, 5 or 9 bytes, one
encoding per value. Sharing is canonical. The environment header is TagN(4)
flag `0xE` value 4 (the single byte `0xE4`, unbound) or value 5 (`0xE5`,
role-bound: the same sections with a role binding after the assumptions,
[byte contract](byte-contract.md)); there is no v3 reader or writer (a v3
header, `0xE3`, is rejected). Raw constant bytes carry no
self-identifying version, so consumers must select this API from an
authenticated versioned boundary. The v4 primitive inventory is ix's
[`primitives.tsv`](../fixtures/ixon-v4/primitives.tsv) (copied unchanged); 66
of the primitive addresses moved from v3.

[`Ixon.V4.Convert`](../IxCC/Ixon/V4/Convert.lean) is the total
structural correspondence between ix's `Ixon.*` data and ours (the only
failure is an ix address of other than 32 bytes), and
[`Ixon.V3.Wire`](../IxCC/Ixon/V3/Wire.lean) defines our encoders as
ix's (`constantBytes c = Ixon.serConstant (constantToIx c)`, likewise
expressions and universes). `decodeConstant` runs ix's
`Ixon.Canonical.deConstant` (a byte and universe-expansion budget, the wire
domain check, and re-encoding to exactly the input), converts, applies the
consumer budgets below, and retains `constantBytes value = bytes` as evidence.
This is not a universal codec roundtrip or source-typing theorem; ix proves
its codec's roundtrip at the same revision (`IxCK.Ixon.Verify`), which we do not
import. Src terms remain the consumer's own data types.

[`Ixon.V3.Env`](../IxCC/Ixon/V3/Env.lean) frames environments itself,
after ix's `Env.getEnv` (whose module is outside the pure package): it checks
sorted address tables, every blob's and constant's hash, the complete
constant-set Merkle root, main membership, assumptions and hint indices.
Hashes are **pure BLAKE3** (`Blake3.Pure`, through `Address.blake3Pure` and
`Merkle.rootCanonicalBy`): ix's certified reader treats addresses as keys, so
authentication is ours, and it involves no foreign hash. Metadata after the
hint section is retained as opaque bytes and is outside admission, matching
the producer's anonymous-reader boundary.

Default consumer budgets are 16 MiB per environment, 1 MiB per object,
16,384 environment entries per table, 4,096 entries per counted list of a
constant (sharing, references, universes, mutual members, constructors,
rules, universe arguments) and 256 expression depth (a `share` node is a
leaf), checked on the decoded value. Universes are bounded by ix's decoder:
65,536 expanded constructors per constant.
Budget restrictions do not change committed bytes.

Typing is the certified kernel's, on every compile path (its own budgets are
in the [kernel front end](kernel-front-end-design.md#resource-bounds)); these
consumer limits can reject a well-typed producer environment and do not
establish a wall-time or host-memory bound.

## Ingress and retired v4 resource admission

IxCC's private v4 resource checker, validation API and handoff bindings
(`Ixon.V3.Resource.*`, `Ixon.V3.Validate`, `Ixon.V3.Source`, `Src.Resource.*`,
`Program.resource`, `check-ixon-v3`, and `fixtures/ixon-v4/handoff/`) were
retired ahead of the Ixon v5 migration.

The compiler's front end ([compiler design](compiler-design.md)) starts from
`Src.load`: strict decoding and the certified kernel's acceptance of the
role-bound environment. Its ownership checker (`Own.Plain.checkOwned`)
re-establishes every ownership guarantee on the compiled program. Aiur
Ixon/DSL lowering remains a later target milestone.

## Evidence and provenance

The [K1 pack](../fixtures/ixon-v4/k1/README.md) adds a 1,596-constant closure
of ordinary Lean programs (`fib`, a `for` loop, Ackermann, `tak`, `gcd`) with
the unfolding theorems of every recursive definition it reaches. The suite
checks strict ingress, the recorded root, definition and equation addresses,
and the certified kernel's acceptance of the whole closure.

The portable fixture package (expressions, addressed constants, the text
grammar and the primitive inventory) is copied byte for byte from the root
package's `Tests/Fixtures/ixon-v4/`. The compiled `tests-ixon-v3` suite decodes
and re-encodes them with this boundary, checks every binder/arrow bit pattern,
truncation and trailing bytes, role-binding admission, the primitive table
against `primitives.tsv`, `Nat` literal bytes, the K1 pack, and regression
cases (malformed bytes, a v3 header, exhausted ingress budgets). The package
also retains upstream text/primitive fixtures as provenance; this adapter
implements no text parser. The kernel's refusals are tested in
`tests-kernel-front`.

Contract bit roundtrips and quantity laws have 10 exact kernel axiom fences in
`IxCCTests.Fences.IxonV3`, retaining the standard axiom basis (every address is
pure BLAKE3). Production imports exclude all fixtures and fences. Required CI
runs `tests-ixon-v3` and includes the proof/fence, module-graph and trust
inventories.

The MIT/Apache notices are retained beside the frozen fixtures. The `IxCK`
package (codec, role vocabulary, executable kernel and, for `IxCCGrounding`
only, the model statement) and `Blake3.Pure` are the only Lean dependencies (no
native code, standard axioms).

## Name clashes

ix's codec declares a root-namespace `Address` (and `hexOfByte`,
`bytesOfHex`, …) and the root namespace `Ixon`. In a module that imports the
codec (directly or through `Ixon.V3.Env`), a bare `Address` under
`open IxCC.Ixon` is ambiguous, and `Ixon.X` under `open IxCC`
outside the `IxCC` namespace can resolve to ix's; write
`Ixon.Address` inside `namespace IxCC …` and `IxCC.Ixon.X`
elsewhere.
