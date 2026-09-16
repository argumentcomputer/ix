# Ixon v3: usage, ownership, and relative locality

This specification describes the implemented Ixon v3 format and the admitted
Ix source fragment. Relative locality replaces explicit lifetime parameters.
The format is incompatible with v2; all typed addresses and primitive pins
must be regenerated.

See the [text format](ixon-text-v3.md) and the
[resource checker](resource-checking.md) for supported behavior and checking
limits, and the [consumer handoff](compilatrix-ixon-v3.md) for migration fixtures.
Native resource claims are implemented. IxVM checks erased Lean typing and
explicitly rejects resource-proof requests. The [verification record](ixon-v3-verification.md)
lists the executed gates and formal trust boundary.

## 1. Independent contracts

Three properties are tracked independently:

| Property | Choices | Meaning |
| --- | --- | --- |
| Usage | `0`, `1`, `&`, unmarked | Zero, exactly one, at most one, or any number of computational consumptions |
| Ownership | `!`, unmarked | Unique ownership or shared access |
| Locality | `~`, unmarked | Confined to an implicit scope or unrestricted escape |

`~!` combines local scope with unique ownership. Neither `!` nor `~` changes
the usage annotation. Every combination is representable. An implicit or
instance binder is not erased merely because it is implicit. Native Lean
`@&` remains a compiler hint, separate from every checked contract here.

```text
ValueContract  = { owned : unique | shared, locality : unrestricted | local }
BinderContract = { uses : erased | linear | affine | many, value : ValueContract }
LetContract    = { nonDep : Bool, kind : value | borrowShared, binder : BinderContract }
```

Defaults are explicit: many uses, shared ownership, unrestricted locality.
Each forall records its input binder contract and its result value contract.
This includes every intermediate arrow of a curried function. A final unique
result does not imply unique intermediate closures. Lambda input contracts
must agree with the corresponding forall.

Exported defaults have these fixed meanings. Future inference may infer
omitted contracts within an implementation, but must preserve explicit
annotations and check the published interface. Inference cannot silently
strengthen or weaken an imported contract.

### Quantities

The usage domain approximates sets of natural-number consumptions:
`0 = {0}`, `1 = {1}`, `& = {0,1}`, `many = Nat`.

Sequential demands add: zero is neutral, and two nonzero demands yield many.
Invocation scales demand: zero absorbs, one is neutral, affine times affine
is affine, and all other nonzero products are many. Alternatives join: equal
zero or one stays unchanged, any many yields many, and other joins are affine.
A declaration accepts an inferred demand only if it includes every possibility.
In particular, exactly one rejects both zero and affine demand.

Type formation and erased computation have zero runtime demand. A shared
borrow does not consume its owner; uses of the view count against the view's
quantity. A linear owner must still be transferred, returned, or consumed
exactly once after its temporary loans. Closure invocation scales the demands
on captured resources. An affine capture cannot be hidden in a closure that
is callable arbitrarily often.

## 2. Relative locality

There are no lifetime names, lifetime arguments, declaration region lists,
outlives clauses, or region abstraction/application in the semantic format.
`App`, `Ref`, and `Recur` carry their ordinary data. Local contracts work on
function values as well as directly referenced declarations.

The checker maintains implicit scopes and the origins of values. These are
analysis state, not externally bound lifetime variables. Function bodies and
scoped lets establish the relevant containment boundaries. A value may carry
several local origins through a closure, aggregate, or branch join; erasing
their names does not allow the checker to forget a shorter-lived origin.

For a function arrow, both input and result locality are relative to the
caller's surrounding scope. Inside the function, local inputs are known to
come from outside the function's scope:

- A local input and unrestricted result prohibit retaining that input in the
  result or in escaping storage.
- A local input and local result allow the result to retain that input, with
  the caller's scope restriction preserved.
- A value confined to a scope created inside the function cannot escape that
  scope merely because the arrow's result is marked local.

An unmarked value may be used locally by forgetting its escape permission.
A local value cannot be promoted to unrestricted merely because its immediate
type is unchanged. The initial checked fragment has no automatic mode crossing
for abstract resources or hidden representations.

Locality applies through reachable retained data. A closure that retains a
local value inherits its restriction. A local function argument's own contract
and the contract on that callback's inputs are distinct: one governs storing
the callback, and the other governs what the callback may retain from a call.
Partial applications preserve the contracts of every remaining arrow and all
restrictions of the captures they create.

Locality is an escape contract, not a promise of stack allocation. A backend
may choose an allocation strategy compatible with the checked contract.

## 3. Ownership and scoped shared borrowing

Unique input requires exclusive ownership on entry. Unique transfer consumes
the original binding's availability. Many usage never permits two transfers
of that same availability. Passing unique storage to shared escaping access
permanently relinquishes exclusivity.

`~!` is a uniquely owned value with a scope restriction. It is not a shared
view that has acquired uniqueness. Shared borrowing cannot manufacture `!`.

An owner is a particular binding and, where supported, a checked projection
path. Distinct owners can belong to the same implicit scope. The initial
projected-loan rule suspends the whole owner; field splitting requires its
own checked rule.

A let with `kind = borrowShared` interprets its initializer as an owner place:

```text
let[borrowShared, view contract] view : viewType := ownerPlace in body
```

The initializer must resolve, including through sharing, to a variable or a
chain of checked projections from a variable. Its type must match the view's
type. The view contract must be shared and local. The body's lexical scope
is the loan boundary. The view retains restrictions inherited from its root
owner and any parent view. Shared reborrows may coexist but cannot outlive
their parent or root owner.

Unique access to the root owner is suspended while a relevant loan exists.
Scope exit checks the result, captures, aggregates, and supported stores before
ending that scope's loans. Unique access returns only when the original owner
is still live, was unique, and has not acquired a permanent alias. Ending a
scope cannot restore a moved or permanently shared owner.

Ordinary lets retain ordinary transfer/aliasing semantics. Locality annotation
alone does not mark the point at which a temporary shared loan was created.
The frontend emits the explicit borrow-let kind for temporary loans. A direct
call that needs such a loan is elaborated with a scope covering all uses of
its local result, rather than restoring uniqueness immediately after the call.

Branch joins retain all possible use states, scope restrictions, and owner
origins. Unique access is available after a join only if it is available on
every incoming path. Recursive calls use checked contracts; recursive capture
and resource summaries require a finite conservative fixed point. Unknown
behavior must not be interpreted as no capture or no loan.

Opaque/external contracts are semantic interface assumptions bound into the
addressed interface or an admitted primitive identity and checker profile.
Ordinary typechecking and native calling-convention hints do not certify them.

## 4. Representation and canonical wire layout

The binary environment version is **3** and the typed-constant protocol
identifier is **`ixon-v3`**. Constants remain BLAKE3-addressed canonical bytes;
the surrounding catalog/artifact protocol binds the format. Blob addresses
remain BLAKE3 of raw bytes. No v2 fallback or mixed-version typed environment
is admitted.

The original twelve expression variants remain. Lambda and forall payloads
carry complete contracts. The let payload carries `LetContract`. Declaration
records keep their ordinary headers, including their universe-parameter count;
there is no added lifetime list on any declaration or mutual member.

Contract codes are:

| Field | Encoding |
| --- | --- |
| Usage | `0` erased, `1` linear, `2` affine, `3` many |
| Ownership | `0` unique, `1` shared |
| Locality | `0` unrestricted, `1` local |
| Value contract | ownership in bit 0, locality in bit 1; higher bits zero |
| Binder contract | usage in bits 0–1, value contract in bits 2–3; higher bits zero |
| Forall contract | binder contract in bits 0–3, result value contract in bits 4–5; higher bits zero |

The four value codes are `0 = !`, `1 = unmarked`, `2 = ~!`, `3 = ~`.
Lambda binders require one contract byte and forall binders require one
contract byte. Application, lambda, and forall use their original maximal
ordinary telescopes, with no term/region packet discriminants.

Let uses its existing Tag4 category `0xA`. The size encodes the non-dependent
flag in bit 0 and `borrowShared` in bit 1. Sizes above 3 are invalid. The
payload is one binder-contract byte followed by type, initializer, and body
expressions, in that order. Ordinary let sizes remain 0 or 1; shared-borrow
sizes are 2 or 3. Borrowing introduces no new expression constructor or tag.

All counts and indices use the shortest existing unsigned encodings. Readers
reject nonminimal tags, reserved mode bits, invalid enum/Boolean flags, empty
or nonmaximal telescopes, impossible counts, truncation, and trailing bytes
at a whole-object boundary. Native readers bound count-based preallocation by
the remaining byte budget. IxVM parses counted lists incrementally and rejects
exhausted input through strict byte reads, without a preliminary byte traversal.
Readers do not normalize adversarial bytes into other addresses.

Source annotations, semantic contracts, canonical bytes, structural sharing
hashes, equality, and cache keys must all distinguish the four value modes,
four quantities, independent arrow results, and two let kinds.

## 5. Admission, transport, and verification

Wire validation establishes representation. Scope/type validation establishes
term scope, types, and permitted owner-place shapes. Resource validation
establishes usage, uniqueness, locality, captures, loans, and escape for the
admitted fragment. Every advertised claim must state the validation it binds.

Source elaboration resolves occurrence contracts before canonicalization or
sharing. Caches must include those effective contracts and the relevant
context, or use an expression representation that contains them. Imported and
opaque interfaces follow the same contract path as local declarations.

Open shared expressions are checked in each use's binding/scope context;
context-free memoization is not a scope or resource-validity proof. Unsupported
annotated transformations fail before artifact emission. Kernel erasure of a
borrow let is its ordinary let; erasure follows the checked resource boundary
whenever that boundary advertises resource validity.

The Lean, Rust, and IxVM codecs, FFI layouts, text syntax, source frontend,
decompiler, sharing, consumers, catalogs, and claims must agree on the format.
The smaller schema does not remove the obligation to transport contracts or
to bind the validator, configuration, and primitive assumptions in proofs.

Verification must connect quantitative soundness, codec inverses, ordinary
erasure, and scope/loan invariants to the executable definitions. No new axioms
or `sorry` placeholders are permitted. Negative tests must cover hidden
captures, closure/aggregate escape, repeated unique transfer, stale or aliased
owner restoration, branch/recursion paths, malformed bytes, and imported
contract mismatches, alongside accepted nontrivial higher-order examples.
