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

The checker dispatches primitive reductions by these v3 identities. Its
`eagerReduce` entry is a reserved synthetic marker: the ordinary declaration
has the same content address as `id`, and cannot select special reduction
by its address. The regression suite checks this producer exception.

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

Typing additionally caps declaration counts and variable/field indices at
4,096, expression conversion at 100,000 steps and 1,024 pending frames, and
recursive checker dispatch at 1,024. It resets a 100,000 recursive-fuel budget
for each checked source key. These consumer limits can reject a well-typed
producer environment; they do not establish a wall-time or host-memory bound.

## Admission and claims

[`validate`](../Compilatrix/Ixon/V3/Validate.lean) runs resource admission,
fixes Nat/String literal types to the canonical primitive identities, and
runs erased typing over the same decoded environment. Its `ValidatedInput`
retains the original environment/profile byte indices and equations for all
three checks. The literal-pin theorem proves that an optional selected type
is either absent or the canonical address.

[`admitResources`](../Compilatrix/Ixon/V3/Source.lean) returns a `ResourceInput`
indexed by the original environment/profile bytes. It carries equations for
their decoding and the actual addressed resource check. The adapter rebuilds
all references, sharing, mutual members and supported fields from canonical
raw bytes. There is no materialized cache that can replace those bytes.

Profiles commit to explicit external interfaces, shareable types, selection
behavior, literal pins and checker limits under `ixon-v3/resource-v1`.
The native Resource claim binds object format 3, validator 2, the complete
constant-set root and that profile's address. `checkClaimBinding` verifies
only those identities on a resource-only input. `ValidatedInput.checkClaim`
checks the binding after combined validation. The command runs that combined
boundary:

```sh
lake exe check-ixon-v3 fixtures/ixon-v3/handoff/accepted.ixe \
  fixtures/ixon-v3/handoff/profile.bin \
  fixtures/ixon-v3/handoff/accepted.claim
```

The anonymous checker adapts upstream `Ix/Tc`: universes, inference,
definitional equality, safety, inductive positivity and generated-recursor
comparison. It decodes raw constants afresh, always verifies their hashes,
rejects cyclic sharing, and checks every source key. Empty mutual blocks and
orphan projections fail. There is no caller-supplied checker verdict or
materialized cache that can replace the bytes.

Successful admission certifies execution of these algorithms, conditional
on the existing native BLAKE3 boundary and the pinned checker's correctness.
A whole-checker semantic soundness theorem is not provided by the adapter.
IxVM Resource proofs remain unsupported.

The existing native and Ixby compiler entry points retain their frozen v2
source types and proof scope. V3 does not implicitly project into them:
v2 linear/affine inputs imply uniqueness, while v3 usage and ownership are
independent. A contract-preserving, source-bound backend simulation is still
required before v3 lowering can grant ownership/locality
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

The typing suite also rejects ordinary ill-typed declarations that resource
analysis skips, and confirms that erased typing alone accepts the local-escape
fixture. It covers scope/universe errors, sharing cycles, unsafe references,
positivity, constructor headers, canonical recursors and tampered rules.
Four [primitive bundles](../fixtures/ixon-v3/typing/README.md) retain producer
bytes for Nat, Nat.add, String and Quot.lift. The larger closures passed
upstream Rust checking; required tests run combined admission, valid literals,
`20 + 22 = 42`, and rejection of false arithmetic and redirected literal pins.

Contract bit roundtrips, quantity laws and the executed state invariants have
exact kernel axiom fences in `CompilatrixTests.Fences.IxonV3`. In particular,
the scope theorem rules out an origin in a fresh scope escaping to an older
destination; owner transfer requires a live unique owner with no active loan.
These are selected invariants, not a machine soundness theorem for the whole
resource checker or an allocation backend. Production imports exclude the
larger state proofs and all fixtures/fences. Required CI runs the focused
suite and includes the proof/fence, module-graph and trust inventories.

Eight additional typing/pin/input fences preserve the existing logical and
native BLAKE3 axiom basis. Hash finalization uses an explicit kernel proof of
its 32-byte length bound, avoiding the dependency's default native reflection.

The adapted source files identify their upstream origin. Resource algorithms
come from `Ix/Resource/{Basic,Check,Admit,Addressed}.lean`; local changes are
module factoring, AST/address/codec interfaces and explicit consumer budgets.
The MIT/Apache notices are retained beside the frozen fixtures. No Lean
toolchain, native dependency or axiom is added.

Typing modules retain the upstream algorithm boundaries, including their
large mutual recursion groups. Local adaptations replace namespace and AST
interfaces, supply pure integer-byte helpers and sized hashes, use
`Std.TreeMap` for ordered universe-normalization entries, and omit frontend,
parallel-worker, metadata-ingress and egress dependencies. Anonymous metadata
types remain only to preserve the checker's mode parameterization. The driver
adds the consumer bounds above and accounts for every raw constant key.
