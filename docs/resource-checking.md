# Ixon resource checking (resource-v1)

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

Two call-boundary rules refine the scaling. A value of a profile-shareable type
is an immediate: the callee receives a copy that holds no resource, so passing
it to a nonzero input counts as one consumption whatever the callee's
multiplicity. The caller's own reads still add, and a zero-use input still has
zero demand. A closure boundary crosses in the same way: a captured value of a
profile-shareable type is copied into the closure, so neither its finite use
nor its uniqueness makes the closure one-shot. A curried definition such as
`(1 x : Nat) → (1 y : Nat) → Nat` therefore keeps its shared intermediate
result, while a finite or unique capture of any other type still requires a
unique (one-shot) closure. An argument whose domain is a proposition is a proof,
which is erased computation: it has no demand, owner transfer, or origin. The
adapter recognizes propositions from addressed universes (only a literal
`Sort 0` is `Prop`); the unreduced type is typed first, because reduction can
unfold a proposition such as `a ≤ b` to a class projection that has no field
rule. A proof returned or bound by a let is still checked as a value. A safe
theorem's own proof carries no resource obligation; its statement still takes
part in relevance.

Zero demand still checks the full resource structure of argument types. An
erased owner or view cannot be made usable by borrowing or reborrowing it.

The checker separately records whether each owner is live, still unique, and
subject to active loans. A unique transfer requires all three conditions:
live, unique, and no loans. Permanent sharing clears uniqueness. Ending a
loan removes that loan and preserves both the liveness and sharing state.
A branch join preserves availability only when every incoming path does.

Constructing a closure transfers captured unique owners. That transfer counts
even when the closure's body only borrows the captured owner. A reusable shared
closure cannot hide a finite-use or uniquely consumed capture, unless the
captured value is a shareable immediate (above). A unique
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

Field rules must be derived from transparent constructor interfaces of
structures (one constructor, no indices). The projection fragment requires
field usage `many`; other projection transformations are rejected before
artifact emission. A field type may depend on the structure's parameters and
on earlier fields (`Prod`, `PProd`, `Subtype`, `Sigma`, class structures): its
rule stays open over the constructor telescope, and a projection instantiates
it with the type arguments of the projected value's type and with the earlier
fields as projections of the same value. A projected value whose type does not
reduce to the structure applied to exactly its parameters is rejected. The
fragment does not split availability between fields of the same owner.

Special alternative-path analysis requires a profile-bound selection primitive
with the specified evaluation behavior. Such a primitive must be fully applied
and cannot escape through an ordinary callback value. An arbitrary ordinary
function does not acquire branch semantics because its name resembles a
conditional.

A choice (for example `ite`, `dite`, `cond`) is applied to at least as many
arguments as its type has leading arrows; further arguments are passed on to
both alternatives. Its last two arguments are the alternatives, analyzed from
the same state and joined; the others are strict. An alternative whose
expected type takes proofs (`dite`) is entered with fresh proof binders. The
chosen alternative is the result, so the caller's contract applies to it (or,
without one, the primitive's result contract). A choice may be an assumed
definition: its body is then not checked.

With the profile's case behavior, three more forms are analyzed without
closures; the consumer must compile them the same way:

- A recursor application whose minor premises ignore their induction
  hypotheses, on an inductive type without indices (one motive, one minor per
  constructor), is a case split. Parameters, motives and indices have no
  run-time demand. The major premise is inspected, not consumed: its read is
  charged, but no ownership is transferred. Each minor binds the constructor's
  fields, which keep all of the major's origins and loan root and are unique
  only when both the major and the field binder are; the alternatives are
  joined. A minor that uses an induction hypothesis is rejected.
- An unannotated definition whose body only wraps such a case split
  (`casesOn`, matchers) is unfolded at a full application. An argument of a
  default binder that is a variable, a value form, a type or a proof is
  substituted; any other argument is bound by a `let` with the binder's own
  contract, so it is evaluated once, before the body, as a call evaluates it.
- A beta-redex binds its arguments the same way.

Case splits on indexed families are not supported (their index unification
needs casts this checker's conversion does not follow); such matchers remain
ordinary calls.

An application whose function is a proof (its type is a proposition) is
erased computation, as a proof argument is.

Recursion uses the declared interfaces of the mutually checked definitions.
Calls conservatively retain all origins permitted by those interfaces, rather
than assuming that an unknown recursive body has no captures. Ordinary
typechecking remains responsible for the language's recursion admissibility.

The default analysis bounds are depth 256 and 100,000 steps per declaration.
Exhaustion is a rejection. Open sharing is analyzed in each binding context;
its resource result is never cached by expression identity alone.

## Profiles, claims, and consumers

A canonical profile begins with the UTF-8 bytes
`ixon-v4/resource-v1/profile` and a zero byte, followed by:

1. Assumptions, shareable type addresses, and selection primitive addresses:
   each list has a TagN (`f = 0`) count and strictly increasing 32-byte addresses.
2. Optional Nat and String type addresses: a byte `0`, or `1` and an address.
3. Nonzero depth and step limits, each a TagN (`f = 0`) unsigned integer.
4. An optional extension, present only when it is not empty: a TagN (`f = 0`)
   behavior flag (`1`: case splits, case wrappers and beta-redexes, above; no
   other value), then a TagN (`f = 0`) count of admitted interfaces, each a
   32-byte address (strictly increasing), a TagN (`f = 0`) length, and that
   many bytes, one packed input/result contract byte per leading arrow.

Selection primitives and admitted interfaces must also be assumptions. An
admitted interface replaces the declaration's own arrow contracts for its
callers (for example `List.length` reading a `~` input and returning a fresh
unrestricted value); the declaration's body is not checked against it. Literal types, when selected,
must match the kernel's pinned primitive identities. The profile address is
BLAKE3 of these exact bytes. Changing limits or assumptions changes the claim.
The default profile admits no external resource interfaces and only grants
shareability to present canonical Nat, Bool, and String types.

`ix compile --profile FILE` replaces the standard profile with a profile
source: one directive per line (`#` starts a comment): `standard` (the
standard profile's entries), `shareable NAME`, `assume NAME`, `choice NAME`,
`interface NAME C…` (one contract token per leading arrow, `INPUT[:RESULT]`
in source prefix syntax, `_` for the default), `cases`, and `limits DEPTH
STEPS`. Names are resolved against the compiled closure, entries outside it
are omitted, and the command prints the effective profile address; the
validation itself binds addresses only. The published Lean core profile is
[`profiles/lean-core.profile`](../profiles/lean-core.profile): the standard
entries, the scalar immediates `Char` and `UInt8`–`UInt64`, the choices `ite`,
`dite` and `cond`, case behavior, and readers (`List.length`, `Array.size`,
`String.length`) with a local input.

`makeClaim` validates before producing a `Resource` claim. `checkClaim` checks
the complete subject root and profile address, then reruns combined validation.
The claim has format byte `4` and validator byte `2` (`resource-v1`).
Assumptions describe admitted behavior; they do not remove constants from the
required closure. Merely parsing a claim or proof wrapper validates no program.

| Consumer | Advertised validation |
| --- | --- |
| Lean and Rust resource admission | Resources plus erased typing, with a committed profile |
| Ix.Tc and the Rust ordinary kernel | Erased Lean typing |
| IxVM `Check` and `CheckEnv` | Erased Lean typing, validator byte `1` |
| IxVM `Reveal` and `Contains` | Structural validation, validator byte `0` |
| IxVM `Resource` | Explicitly unsupported; native success is not a circuit proof |

IxVM preserves every contract field in serialization and revelation. Its typing
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

[Shared resource fixtures](../Tests/Fixtures/ixon-v4/resource.tsv) exercise
accepted and rejected terms in both implementations; `resource-modes.tsv`
covers usage crossing, proofs and open field rules, and `resource-cases.tsv`
case splits, case wrappers, beta-redexes and choices. The suites also cover
all 64 input/result combinations, imported-interface aliases, mutual groups,
profile omissions, constructor captures, and bounded rejection of cyclic
sharing. Tests explicitly distinguish wire validity from resource admission.
