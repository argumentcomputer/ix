# Ixon v3 resource checking

The Lean and Rust resource validators consume the same canonical addressed
environment and an explicit profile. Both production compilers run this
validation, together with erased typechecking, before emitting annotated
constants. Resource claims bind the complete constant set and profile address.

The executable modules are [Basic](../Ix/Resource/Basic.lean),
[Check](../Ix/Resource/Check.lean), and [Admit](../Ix/Resource/Admit.lean).
[Rust](../crates/ixon/src/resource.rs) implements the same transitions.
The production boundaries are [Validate](../Ix/Resource/Validate.lean) and
[the Rust kernel adapter](../crates/kernel/src/resource.rs).

## Preconditions and admission

Resource checking supplements ordinary typechecking. The
[address adapter](../Ix/Resource/Addressed.lean) verifies raw bytes, hashes,
canonical decoding, projection wrappers, reference closure, and blob identity.
It ignores optional metadata and materialized caches. It constructs a program
whose declaration kinds, references, sharing expansions, and field rules come
from verified addressed constants. Its internal global indices are analysis
data; they are not a new expression encoding. A successful call on a manually
constructed `Program` is conditional on those prerequisites.

Admission computes which declarations have resource obligations. A contract
on a declaration, a referenced interface, or another member of the same
addressed mutual block makes the declaration subject to resource checking.
This prevents an ordinary-looking alias from erasing an imported contract.
Wholly ordinary components retain their ordinary typechecking path.

Resource-bearing definitions are checked against their interfaces. Constructors
must retain local, finite-use, and unique captures in every partial application
and in the final result. External resource interfaces, special selection
behavior, and shareable representations require explicit profile entries.
The canonical profile binds those entries to addresses.
They cannot be inferred from names or optional source metadata.

## Uses and availability

Demands use the four-element domain `0`, `1`, `&`, and many. Sequential
demands add, calls scale argument demand by the input contract, and alternative
paths join. Erased computation and type formation contribute zero demand.
A binder is checked when its scope finishes; exactly one rejects an optional
or absent consumption.

Zero demand still checks the full resource structure of argument types. An
erased owner or view cannot be made usable by borrowing or reborrowing it.

The checker separately records whether each owner is live, still unique, and
subject to active loans. A unique transfer requires all three conditions:
live, unique, and no loans. Permanent sharing clears uniqueness. Ending a
loan removes that loan and preserves both the liveness and sharing state.
A branch join preserves availability only when every incoming path does.

Constructing a closure transfers captured unique owners. That transfer counts
even when the closure's body only borrows the captured owner. A reusable shared
closure cannot hide a finite-use or uniquely consumed capture. A unique
closure can carry these captures and is consumed when invoked. Borrowing does
not turn such a closure into a reusable shared callback.

## Scopes and calls

Scopes form an internal parent tree. Values retain all local origins that can
be reached through them. Checking a local conversion requires each retained
origin to be an ancestor of the destination scope. Unrestricted conversion
requires no retained local origin.

The destination of a local call result is inferred from its surrounding use.
For example, a function can forward a local input through a local identity
helper and return it to its caller. An inner local let or loan still cannot
escape: its origin is a younger scope than that return destination.

A call with an unrestricted result checks its local inputs in the current
scope. This permits a reader to inspect a temporary view and return a fresh,
unrestricted value. Narrowing that fresh value to an outer local scope does
not make the inspected view escape.

Ordinary lets use transfer or permanent aliasing. A borrow let resolves its
initializer to a variable or a supported projection chain, opens a shared
loan, and adds that scope to the view's origins. Reborrows retain their parent
origins and root owner. Projected loans suspend the whole owner.
Capturing a shared view to reborrow it captures that view; it does not transfer
the root owner whose availability is already suspended by the outer loan.

Closures and aggregates retain origins. Projection rules preserve the field's
ownership restrictions: a shared aggregate cannot expose a stored unique
closure as a reusable shared function. Every returned place is materialized
before the lexical scope ends, so inference cannot defer a prohibited move
until after a loan has been removed.

## Explicit bounds of the initial checker

The checker requires visible arrow interfaces after bounded beta, let, sharing,
and definition reduction. Higher-order types must agree in every contract.
It does not guess a resource interface when normalization is unsupported.
Abstract unique function values are not assumed safe to borrow as reusable
callbacks. A representation needs a checked or explicitly admitted rule before
the checker grants that permission.

Field rules must be derived from transparent constructor interfaces. The
initial projection fragment requires closed field types and field usage
`many`; other projection transformations are rejected before artifact emission.
It does not split availability between fields of the same owner.

Special alternative-path analysis requires a profile-bound selection primitive
with the specified evaluation behavior. Such a primitive must be fully applied
and cannot escape through an ordinary callback value. An arbitrary ordinary
function does not acquire branch semantics because its name resembles a
conditional.

Recursion uses the declared interfaces of the mutually checked definitions.
Calls conservatively retain all origins permitted by those interfaces, rather
than assuming that an unknown recursive body has no captures. Ordinary
typechecking remains responsible for the language's recursion admissibility.

The default analysis bounds are depth 256 and 100,000 steps per declaration.
Exhaustion is a rejection. Open sharing is analyzed in each binding context;
its resource result is never cached by expression identity alone.

## Profiles, claims, and consumers

A canonical profile begins with the UTF-8 bytes
`ixon-v3/resource-v1/profile` and a zero byte, followed by:

1. Assumptions, shareable type addresses, and selection primitive addresses:
   each list has a minimal Tag0 count and strictly increasing 32-byte addresses.
2. Optional Nat and String type addresses: a byte `0`, or `1` and an address.
3. Nonzero depth and step limits, each a minimal Tag0 unsigned integer.

Selection primitives must also be assumptions. Literal types, when selected,
must match the kernel's pinned v3 primitive identities. The profile address is
BLAKE3 of these exact bytes. Changing limits or assumptions changes the claim.
The default profile admits no external resource interfaces and only grants
shareability to present canonical Nat, Bool, and String types.

`makeClaim` validates before producing a `Resource` claim. `checkClaim` checks
the complete subject root and profile address, then reruns combined validation.
The claim has format byte `3` and validator byte `2` (`resource-v1`).
Assumptions describe admitted behavior; they do not remove constants from the
required closure. Merely parsing a claim or proof wrapper validates no program.

| Consumer | Advertised validation |
| --- | --- |
| Lean and Rust resource admission | Resources plus erased typing, with a committed profile |
| Ix.Tc and the Rust ordinary kernel | Erased Lean typing |
| IxVM `Check` and `CheckEnv` | Erased Lean typing, validator byte `1` |
| IxVM `Reveal` and `Contains` | Structural validation, validator byte `0` |
| IxVM `Resource` | Explicitly unsupported; native success is not a circuit proof |

IxVM preserves all v3 fields in serialization and revelation. Its typing
conversion erases contracts and interprets a borrow let as an ordinary let.
The committed validator identity prevents these typing proofs from claiming
resource validity. Backends relying on ownership or locality must require
resource admission separately. The [consumer handoff](compilatrix-ixon-v3.md)
records the supported interfaces and migration fixtures.

## Verification and regression coverage

Lean proofs connect the executed checks to these facts:

- accepted demands cover the admitted natural-number consumptions;
- the bounded ancestor walk establishes lexical containment;
- allocating a scope preserves the backwards-pointing parent tree;
- a fresh scope cannot escape to an older scope;
- moving requires a live unique owner without loans;
- sharing permanently clears unique availability;
- ending a loan preserves liveness and uniqueness;
- joins only preserve availability present on both paths.

These are executable-check and transition invariants. They do not replace the
ordinary typechecking prerequisite or claim a proof of a machine backend's
allocation behavior.

[Shared resource fixtures](../Tests/Fixtures/ixon-v3/resource.tsv) exercise
accepted and rejected terms in both implementations. The suites also cover
all 64 input/result combinations, imported-interface aliases, mutual groups,
profile omissions, constructor captures, and bounded rejection of cyclic
sharing. Tests explicitly distinguish wire validity from resource admission.
