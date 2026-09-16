# Ix frontend and Ixon v3

Compilatrix's new source boundary consumes ix `jcb/aiur-frontend` at
`2afb4eac340cd4cbe94ed9e507561f3ad8375ebd`. The producer implements a shared
Lean frontend with usage, ownership, relative locality and scoped shared
borrowing. Aiur is one consumer. Compilatrix consumes the resulting binary
objects; it does not introduce another parser or elaborator.

This source pin is independent of the Aiur target snapshot in
[`vendor/aiur/README.md`](../vendor/aiur/README.md). That target contains the
counter, memory and rank work on which the existing target proofs depend.
Changing the source producer does not replace that target vocabulary.

## Contract and wire boundary

[`Compilatrix.Ixon.V3`](../Compilatrix/Ixon/V3.lean) retains all twelve
expression constructors with these addressed fields:

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

The environment header is format **3**, protocol **`ixon-v3`**. Raw constant
bytes carry no self-identifying version, so consumers must select this API
from an authenticated versioned boundary. Never try v2 decoding as a fallback
or reuse v2 primitive addresses. The frozen v3 primitive inventory is in
[`primitives.tsv`](../fixtures/ixon-v3/primitives.tsv).

The strict expression/constant decoders reject reserved bits, noncanonical
encodings, truncation and trailing bytes. Successful decoding retains an
equality proof to the canonical reencoding. This is not a universal codec
roundtrip or source-typing theorem. Unlike the old v2 source gate, the v3
adapter admits upstream's single-use sharing entries.

Anonymous environment ingress checks sorted address tables, object hashes,
the complete constant-set Merkle root, main membership, assumptions and
hint indices. Metadata after the hint section is retained as opaque bytes
and is outside admission, matching the producer's anonymous-reader boundary.
It is not validated as a complete metadata serialization.

Default consumer budgets are 16 MiB per environment, 1 MiB per object/profile,
16,384 environment entries per table, 4,096 entries per constant field and
256 expression depth. Universe successor expansion retains the existing
4,096 bound. Resource admission allows profile depth at most 256 and 100,000
steps per declaration. Budget restrictions do not change committed bytes.

## Admission and claims

[`admitResources`](../Compilatrix/Ixon/V3/Source.lean) returns a `ResourceInput`
indexed by the original environment/profile bytes. It carries equations for
their decoding and the actual addressed resource check. The adapter rebuilds
all references, sharing, mutual members and supported fields from canonical
raw bytes. There is no materialized cache that can replace those bytes.

Profiles commit to explicit external interfaces, shareable types, selection
behavior, literal pins and checker limits under `ixon-v3/resource-v1`.
The native Resource claim binds object format 3, validator 2, the complete
constant-set root and that profile's address. `checkClaimBinding` verifies
only those identities. The command makes that scope explicit:

```sh
lake exe check-ixon-v3 fixtures/ixon-v3/handoff/accepted.ixe \
  fixtures/ixon-v3/handoff/profile.bin \
  fixtures/ixon-v3/handoff/accepted.claim
```

Upstream's full `Resource.validate` also runs erased Lean typechecking over
the same bytes and fixes literal types to kernel primitive identities. That
typing check is **not** implemented by this adapter. A resource-admitted
input or matching claim is therefore not a validated typing/resource claim.
IxVM Resource proofs are explicitly unsupported upstream.

The existing native and Ixby compiler entry points retain their frozen v2
source types and proof scope. V3 does not implicitly project into them:
v2 linear/affine inputs imply uniqueness, while v3 usage and ownership are
independent. Erased typing and a contract-preserving, source-bound backend
simulation are required before v3 lowering can grant ownership/locality
optimizations. Aiur Ixon/DSL lowering remains a later target milestone.
V3 catalog manifests also changed to version 2 with format/validator fields;
the old catalog command rejects that version. Catalog-v2 admission is separate
work and must not strip these fields to reuse a v2 identity.

## Evidence and provenance

The complete portable fixture package is copied byte-for-byte from the
producer snapshot. The compiled `tests-ixon-v3` suite checks expression
vectors, every binder/arrow bit pattern, all 66 resource cases, addressed
constant/profile identities, native claim framing, and complete handoff
files. The accepted linear local identity has subject
`f0e971f93ae7a7aa0fbf87df16a2445afdbb8d89dc0c20934cb9ae7901958269`.
Changing its result to unrestricted changes its address/root and fails
resource admission with `unrestrictedEscape`. Malformed bytes, wrong scopes,
wrong claim bindings and exhausted ingress budgets are regression cases.
The package also retains upstream text/primitive fixtures as provenance;
this adapter implements neither a text parser nor primitive regeneration.

Contract bit roundtrips, quantity laws and the executed state invariants have
exact kernel axiom fences in `CompilatrixTests.Fences.IxonV3`. In particular,
the scope theorem rules out an origin in a fresh scope escaping to an older
destination; owner transfer requires a live unique owner with no active loan.
These are selected invariants, not a machine soundness theorem for the whole
resource checker or an allocation backend. Production imports exclude the
larger state proofs and all fixtures/fences. Required CI runs the focused
suite and includes the proof/fence, module-graph and trust inventories.

The adapted source files identify their upstream origin. Resource algorithms
come from `Ix/Resource/{Basic,Check,Admit,Addressed}.lean`; local changes are
module factoring, AST/address/codec interfaces and explicit consumer budgets.
The MIT/Apache notices are retained beside the frozen fixtures. No Lean
toolchain, native dependency or axiom is added.
