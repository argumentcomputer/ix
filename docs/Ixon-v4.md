# Ixon v4: contracts, TagN integers, and canonical sharing

This specification describes the Ixon v4 format and the admitted Ix source
fragment.

Version 4 keeps the contract model that v3 introduced: usage, ownership and
relative locality, with no explicit lifetime parameters (§1–§3). It changes
the byte grammar in two ways (§5):

- **TagN integers.** One integer code, TagN, replaces v3's Tag0, Tag2 and
  Tag4 everywhere.
- **Canonical sharing.** A constant's sharing table is part of its canonical
  definition, built by the two-phase construction instead of a heuristic.

The format is incompatible with v3: all typed addresses, primitive pins,
claims and `.ixe` files must be regenerated.

This file replaces the v3 specification (`Ixon-v3.md`). That file's content
is preserved here: §1–§3 and §6 are unchanged, and §4 has been updated for
v4. The byte-level reference is [Ixon](Ixon.md).

See the [text format](ixon-text-v3.md) and the
[resource checker](resource-checking.md) for supported behavior and checking
limits, and the [consumer handoff](compilatrix-ixon-v3.md) for migration
fixtures. Native resource claims are implemented. IxVM checks erased Lean
typing and explicitly rejects resource-proof requests. The
[v3 verification record](ixon-v3-verification.md) lists the gates executed
for the contract model.

<!-- PENDING: [format][route][ids] everything specific to v4 in this file (TagN, version 4, canonical sharing as the compiler route, format byte 4, ixon-v4 identifiers) depends on plan §2–§3. At 93e2895c every integer is TagN, but the version is 3, the identifiers are the v3 ones and the compilers use heuristic sharing. A v4 verification record (plan §9) is not written yet. -->

<!-- PENDING: [ixvm] the IxVM codecs read and write TagN and the v4 headers (plan §5). -->

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

The binary environment version is **4**, the `.ixe` header byte is `0xE4`
(`TagN(0xE, 4)`), and the typed-constant protocol identifier is
**`ixon-v4`**. Constants remain BLAKE3-addressed canonical bytes; the
surrounding catalog/artifact protocol binds the format. Claims and proofs
carry object format `4`, and the resource validator identity is
`ixon-v4/resource-v1`. Blob addresses remain BLAKE3 of raw bytes. No v3
fallback or mixed-version typed environment is admitted.

<!-- PENDING: [format][ids] Env.VERSION = 4, header 0xE4, wireFormatId "ixon-v4", object-format byte 4, validatorId "ixon-v4/resource-v1" (plan §0b-2, §0b-7, §2). At 9611c3b6 these are 3 / 0xE3 / "ixon-v3" / 3 / "ixon-v3/resource-v1". -->

The `0xE4` header byte is also the byte of the Check claim tag (`0xE3` was
also the Eval claim tag). Readers interpret it by context, and the enclosing
protocol identifies the object kind.

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

Let uses expression flag `0xA` (a TagN header with a 4-bit flag). The header
value encodes the non-dependent flag in bit 0 and `borrowShared` in bit 1.
Values above 3 are invalid. The payload is one binder-contract byte followed
by type, initializer, and body expressions, in that order. Ordinary lets use
values 0 or 1; shared borrows use 2 or 3. Borrowing introduces no new
expression constructor or flag.

All counts, indices and headers use TagN (§5). TagN is bijective, so no value
has a non-minimal encoding. Readers reject:

- invalid TagN codes and values reaching `2^64`;
- reserved mode bits and invalid enum/Boolean flags;
- empty or non-maximal telescopes;
- impossible counts;
- truncation, and trailing bytes at a whole-object boundary.

Native readers bound count-based preallocation by the remaining byte budget.
IxVM parses counted lists incrementally and rejects exhausted input through
strict byte reads, without a preliminary byte traversal. Readers do not
normalize adversarial bytes into other addresses.

Source annotations, semantic contracts, canonical bytes, structural sharing
IDs, equality, and cache keys must all distinguish the four value modes,
four quantities, independent arrow results, and two let kinds.

## 5. Integers and canonical sharing

These are the two byte-level changes from v3. [Ixon](Ixon.md) gives the full
layouts, examples and proof references.

**TagN.** Every variable-length integer is a TagN integer. That is one header
byte `[flag : f bits][payload : 8 − f bits]` with `f ∈ {0, 2, 4}`, followed
by 0, 1, 2, 4 or 8 bytes:

- `f = 4` is used for expression, constant, environment, claim and proof
  headers;
- `f = 2` for universe terms;
- `f = 0` for counts, indices and lengths.

The rungs hold 1, 2, 3, 5 and 9 bytes, and each rung starts where the
previous one ends, so the code is bijective. Values below 128, 32 or 8 (for
`f` = 0, 2 or 4) encode to the same single byte as v3's Tag0, Tag2 or Tag4.
Larger values encode differently: for example, `Share(8)` is `B8 00`, and the
Resource claim tag is `E8 01`. The Lean proofs of injectivity, canonicity
and rejection are in `Ix/Compile/Verify/TagN.lean`.

**Canonical sharing.** A constant's sharing table, and every `Share`
occurrence, is determined by its expanded anonymous expressions. It is the
output of the two-phase construction `canonicalSharingTiered .tagN`:

1. **Phase 1:** an exact minimum of the uniform-width model at each width
   `w ∈ {1, 2, 3}`.
2. **Phase 2:** an exact first tier of at most eight 1-byte slots, followed by
   the Kahn priority order.
3. **Phase 3:** minimum-length re-materialization of each part at the real
   TagN widths.
4. **Selection:** the candidate with the fewest real bytes is kept, ties going
   to the lower `w`.

The construction keeps two properties:

- **Backward references.** Entry `i` references only entries below `i`.
- **Independence from metadata and history.** Metadata never influences the
  table, and neither do pointer sharing, construction history or the
  compiler that ran.

**Scope of the guarantees.**

- **Machine-checked (Lean).**
  - Phase 1 returns the `setPrec`-least minimum of the uniform model over
    tables of in-degree ≥ 2 terms (`optimizeUniform_minimum`,
    `optimizeUniform_least`).
  - Phases 2 and 3 and the width selection meet their per-phase
    specifications (`allocate_spec`, `materializeTable_min`,
    `rematerialize_spec`, `canonicalTiered_select`).
- **Not claimed.**
  - The composed result is not claimed to be a global byte minimum.
  - The Rust implementation is checked by differential tests, not proofs.
  - Equality between the model length and the serialized TagN length, and
    the wire validity of the output, are not yet proved.

<!-- PENDING: [route] both compilers use canonicalSharingTiered .tagN and the heuristic is removed (plan §3). -->

<!-- PENDING: [proof] model length = TagN serialized length (codec theorems restated with tagNBytes) and the tiered wireWF / capacity / SharingWF endpoint theorem (plan §0b-3, §4). -->

**Metadata expressions.** A `Share(i)` inside a metadata expression (the
collapsed call-site arguments in `ConstantMeta.metaSharing`) refers to:

- primary entry `i` when `i < p`, where `p` is the size of the primary table;
- `metaSharing[i − p]` when `i ≥ p`.

The compilers emit no such `Share` today, and a canonical metadata
construction is deferred.

<!-- PENDING: [meta] readers resolve the extended index space (plan §11). At 9611c3b6 both decompilers resolve against the primary table only. -->

**Compilation failures.** The construction runs under explicit resource
limits. Exceeding one is a compile error. There is no fallback construction.

<!-- PENDING: [limits] defaults far above every corpus maximum and a CLI override (plan §0b-4). -->

These changes do not affect the contract model: §1–§3 and the admission
rules of §6 are the same as in v3.

## 6. Admission, transport, and verification

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
