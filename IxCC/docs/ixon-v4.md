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
- **The data model and the resource rules** were adapted from an earlier ix
  (Ixon v3, a revision outside this repository's history; v3 introduced the
  contract-carrying model and v4 changed only the wire), with the primitive
  table (`V3.PrimAddrs`), which follows this repository's `Ix/PrimAddrs.lean`
  (`refreeze-ixon tc-primitives`). The erased type checker adapted with them
  was deleted by the switch to the certified kernel
  ([kernel front end](kernel-front-end-design.md)).

The producer of the committed fixtures is the ix of this repository (`lake
build ix`): `ix compile --equations` writes the role-bound closures and their
unfolding equations ([corpus](corpus.md), "Refreezing";
`tools/regenerate.sh --check` says whether they are current). The erased
checker's typing bundles went with the checker. IxCC's catalog support
(catalog-v2 admission under validator 1, which certified the erased checker's
typing) is retired: ix retired validator 1, and reading catalogs again means
building against its current validator.

This source pin is independent of the Aiur target snapshot in
[`IxCC/Vendor/README.md`](../IxCC/Vendor/README.md). That target contains the
counter, memory and rank work on which the existing target proofs depend.
Changing the source producer does not replace that target vocabulary.

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
The resource algorithms preserve upstream's scope, owner availability,
capture, quantity and supported projection rules.

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
import. Src terms remain the consumer's own data types. Resource-selection
metadata is checked again on the `Recheck.run` path using the pinned pure
codec's framing operations and pure BLAKE3; this adds those pure modules to
its import closure. The full ix kernel and the ix resource checker remain
outside the production dependency closure. Resource metadata is input data,
not an external acceptance result used as a proof premise.

[`Ixon.V3.Env`](../IxCC/Ixon/V3/Env.lean) frames environments itself,
after ix's `Env.getEnv` (whose module is outside the pure package): it checks
sorted address tables, every blob's and constant's hash, the complete
constant-set Merkle root, main membership, assumptions and hint indices.
Hashes are **pure BLAKE3** (`Blake3.Pure`, through `Address.blake3Pure` and
`Merkle.rootCanonicalBy`): ix's certified reader treats addresses as keys, so
authentication is ours, and it involves no foreign hash. Metadata after the
hint section is retained as opaque bytes and is outside admission, matching
the producer's anonymous-reader boundary.

Default consumer budgets are 16 MiB per environment, 1 MiB per object/profile,
16,384 environment entries per table, 4,096 entries per counted list of a
constant (sharing, references, universes, mutual members, constructors,
rules, universe arguments) and 256 expression depth (a `share` node is a
leaf), checked on the decoded value. Universes are bounded by ix's decoder:
65,536 expanded constructors per constant. Resource admission allows profile
depth at most 256 and 500,000 steps per declaration. The default profile still
selects 100,000 steps; using the higher cap requires explicit profile bytes and
their new address. Optimization toward 100,000 steps remains a follow-up target.
Budget restrictions do not change committed bytes.

Typing is the certified kernel's, on every compile path (its own budgets are
in the [kernel front end](kernel-front-end-design.md#resource-bounds)); these
consumer limits can reject a well-typed producer environment and do not
establish a wall-time or host-memory bound.

## Admission and claims

[`validate`](../IxCC/Ixon/V3/Validate.lean) runs resource admission and
fixes Nat/String literal types to the canonical primitive identities. It types
nothing: on every compile path the certified kernel's acceptance of the whole
role-bound environment runs first, and this API also reads unbound
environments (the handoff vectors). Its `ValidatedInput` retains the original
environment/profile byte indices and equations for both checks. The literal-pin theorem proves that an optional selected type
is either absent or the canonical address.

[`admitResources`](../IxCC/Ixon/V3/Source.lean) returns a `ResourceInput`
indexed by the original environment/profile bytes. It carries equations for
their decoding and the actual addressed resource check. The adapter rebuilds
all references, sharing, mutual members and supported fields from canonical
raw bytes. There is no materialized cache that can replace those bytes.

Profiles commit to explicit external interfaces, shareable types, selection
behavior, literal pins and checker limits under `ixon-v4/resource-v1`
(TagN counts and limits). The native Resource claim (TagN(4) flag `0xE`
value 9, the bytes `E8 01`) binds object format 4, validator 2, the complete
constant-set root and that profile's address. `checkClaimBinding` verifies
only those identities on a resource-only input. `ValidatedInput.checkClaim`
checks the binding after validation. The command runs that boundary:

```sh
lake exe check-ixon-v3 fixtures/ixon-v4/handoff/accepted.ixe \
  fixtures/ixon-v4/handoff/profile.bin \
  fixtures/ixon-v4/handoff/accepted.claim
```

Successful validation certifies execution of these algorithms. A semantic
soundness theorem for the resource checker is not provided by the adapter.
IxVM Resource proofs remain unsupported.

The compiler's front end ([compiler design](compiler-design.md)) starts from
this boundary (`Src.load`: decoding and the certified kernel's acceptance
of the role-bound environment, no resource admission). Its ownership checker re-establishes every contract on the
compiled program, so resource admission is an early, diagnosable gate rather
than a proof premise, and stronger guarantees are granted only by that
checker. Aiur Ixon/DSL lowering remains a later target milestone.

## Evidence and provenance

The [K1 pack](../fixtures/ixon-v4/k1/README.md) adds a 1,596-constant closure
of ordinary Lean programs (`fib`, a `for` loop, Ackermann, `tak`, `gcd`) with
the unfolding theorems of every recursive definition it reaches. The suite
checks strict ingress, the recorded root, definition and equation addresses,
and the certified kernel's acceptance of the whole closure.

The portable fixture package (expressions, addressed constants and profile,
claims, the 66 resource cases, the handoff, the text grammar and the primitive
inventory) is copied byte for byte from the root package's
`Tests/Fixtures/ixon-v4/`. The compiled `tests-ixon-v3` suite (2,300
assertions) decodes and re-encodes them with this boundary, checks every
binder/arrow bit pattern, truncation and trailing bytes, native claim framing,
and the complete handoff. The accepted linear local identity has subject
`f0e971f93ae7a7aa0fbf87df16a2445afdbb8d89dc0c20934cb9ae7901958269`.
Changing its result to unrestricted changes its address/root and fails
resource admission with `unrestrictedEscape`. Malformed bytes, wrong scopes,
wrong claim bindings, a v3 header and exhausted ingress budgets are regression
cases. The package also retains upstream text/primitive fixtures as
provenance; this adapter implements no text parser.

The validation part checks that the API types nothing (an ill-typed component
the resource analysis skips passes it; the kernel refuses it at ingress), the
primitive table against `primitives.tsv`, and the `Nat` literal bytes. The
erased checker's typing cases and its four primitive bundles went with the
checker; the kernel's refusals are tested in `tests-kernel-front`.

Contract bit roundtrips, quantity laws and the executed state invariants have
exact kernel axiom fences in `IxCCTests.Fences.IxonV3`. In particular,
the scope theorem rules out an origin in a fresh scope escaping to an older
destination; owner transfer requires a live unique owner with no active loan.
These are selected invariants, not a machine soundness theorem for the whole
resource checker or an allocation backend. Production imports exclude the
larger state proofs and all fixtures/fences. Required CI runs the focused
suite and includes the proof/fence, module-graph and trust inventories.

Seven additional pin/input fences preserve the standard axiom basis (every
address is pure BLAKE3).

The adapted source files identify their upstream origin. Resource algorithms
come from `Ix/Resource/{Basic,Check,Admit,Addressed}.lean`; local changes are
module factoring, AST/address interfaces and explicit consumer budgets. The
MIT/Apache notices are retained beside the frozen fixtures. The ix codec is
the only added dependency (no native code, standard axioms).

Typing modules retain the upstream algorithm boundaries, including their
large mutual recursion groups. Local adaptations replace namespace and AST
interfaces, supply pure integer-byte helpers and sized hashes, use
`Std.TreeMap` for ordered universe-normalization entries, and omit frontend,
parallel-worker, metadata-ingress and egress dependencies. Anonymous metadata
types remain only to preserve the checker's mode parameterization. The driver
adds the consumer bounds above and accounts for every raw constant key.

## Name clashes

ix's codec declares a root-namespace `Address` (and `hexOfByte`,
`bytesOfHex`, …) and the root namespace `Ixon`. In a module that imports the
codec (directly or through `Ixon.V3.Env`), a bare `Address` under
`open IxCC.Ixon` is ambiguous, and `Ixon.X` under `open IxCC`
outside the `IxCC` namespace can resolve to ix's; write
`Ixon.Address` inside `namespace IxCC …` and `IxCC.Ixon.X`
elsewhere. The vendored Aiur reference is under `IxCC.Vendor`, so the
codec's `IxCK.Ixon.*`/`IxCK.Address.Core` are the only ix modules imported.
