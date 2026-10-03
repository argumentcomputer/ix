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
zero demand. A closure boundary crosses in the same way on the usage axis: a
captured value of a profile-shareable type is copied into the closure, so its
finite use does not make the closure one-shot (the linearity of an immediate
has no run-time meaning; see "Named assumptions"). A curried definition such
as `(1 x : Nat) → (1 y : Nat) → Nat` therefore keeps its shared intermediate
result. Ownership is not exempt: a capture that the closure body *moves* (a
unique transfer, a freeze, the invocation of a unique closure) makes the
closure one-shot whatever its type, since a second call would move it again
— a reusable closure returning a captured unique `String` or `Nat` as unique
on every call is rejected. A unique immediate that the body only reads keeps
the closure reusable. A finite or unique capture of any other type still
requires a unique (one-shot) closure. An argument whose domain is a proposition is a proof,
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
A joined result keeps every owner reference: when the alternatives return
different places and no contract is expected at the join (the result is
projected or applied, for example), consuming or invoking the joined value
acts on every owner it may be — conservatively, since only one of them is
the actual value — and a view of such a value cannot be borrowed.

A unique value of a *plain-data* type — an inductive type of an addressed
block whose constructors all carry only default contracts, so that the value
holds nothing finite-use or unique — may enter a shared position as its last
use (a *freeze*): the owner is moved, so any later use, unique or shared, is
rejected. A pair `(xs, xs)` of a unique list is therefore still rejected (the
second use finds the owner moved). Functions, type parameters and abstract
types never freeze. A fully applied constructor allocates a fresh value, which
is unique whatever the constructor's declared result contract (a nullary
constructor and a literal likewise); this rests on a named assumption below:
a consumer must not substitute a shared static object for it. A plain-data owner may be
borrowed: the loan suspends it as it does a shareable one, and the view's
origins keep it inside the loan.

Constructing a closure transfers captured unique owners. That transfer counts
even when the closure's body only borrows the captured owner. A reusable shared
closure cannot hide a finite-use or uniquely consumed capture; only the finite
use of a shareable immediate is exempt (above), never a capture the body
moves. A unique
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
  fields as views of the major, as a projection is: a field keeps all of the
  major's origins and loan root and names the major's owner as its place, so
  reading a field requires the major to be live, consuming a field shares
  (or, for a unique field of a unique major, moves) the major's owner, and a
  field read after the major was moved, or a unique move of the major after
  a field was consumed, is rejected. A constructor field with a contract has
  no case rule: such a split is rejected, and the adapter derives case shapes
  only for recursors whose major premise has a plain-data type (constructors
  with default contracts only), so a recursor type cannot hide a field
  contract. The alternatives are joined. A minor in which an induction hypothesis occurs at all is rejected:
  the test is syntactic, so a hypothesis passed to a dead binder or to an
  erased argument, or mentioned in a type, counts (a consumer that computes
  hypotheses eagerly would recurse there); a minor that does not mention its
  hypotheses lets the consumer skip computing them.
- A *case definition* bound by the profile (`casesOn` and matchers; `ix
  compile` binds exactly those Lean records, see below) is unfolded at a full
  application when its body is an unannotated lambda telescope around a full
  application of such a case split or of another bound case definition. Its
  parameters are classified from that body: a parameter is *by need* when
  every occurrence lies in an alternative (a minor premise, or a by-need
  position of the inner case definition), after at most the binders the case
  enters there, as the head of an application whose arguments do not mention
  it; occurrences in different alternatives are allowed, since one
  alternative runs. Every other parameter — a discriminant, a motive, one
  used under a closure, twice in one alternative, or not at all — is strict.
  The argument at a by-need position is substituted, so it is evaluated only
  in its own branch (a matcher alternative `h_i ()`); every other argument is
  bound strictly (next item).
- Every other application binds its arguments strictly: a beta-redex's
  arguments, and the arguments of every definition that is not a bound case
  definition, however match-shaped (a user helper `sel b x y := match b with
  …`, `Option.getD`, `String.push`), which is an ordinary call against its
  declared interface. A strict argument is substituted only when evaluating
  it has no effect: a variable, a type or proof (erased computation), a sort,
  a constant that is not a nullary constructor, or a closed lambda (which
  captures and moves nothing). Any other argument — literals, constructor
  applications and nullary constructors (fresh values), lambdas with free
  variables (closures that capture), every other computation — is bound by a
  `let` with the binder's own contract, so it is analysed exactly once,
  before the body, whether or not the binder occurs, as a strict consumer
  evaluates it. Whether a parameter "occurs at most once" is never a reason
  to substitute: a dead argument is still evaluated, a once-used one is not
  moved into a branch, and one used under a closure is not re-evaluated per
  call.

Case splits on indexed families are not supported (their index unification
needs casts this checker's conversion does not follow); such matchers remain
ordinary calls.

An application whose function is a proof (its type is a proposition) is
erased computation, as a proof argument is.

Recursion uses the declared interfaces of the mutually checked definitions.
Calls conservatively retain all origins permitted by those interfaces, rather
than assuming that an unknown recursive body has no captures. Ordinary
typechecking remains responsible for the language's recursion admissibility.

A kernel recursion encoding (`brecOn`, `WellFounded.fix`) passes values
through motives with default contracts, so an annotated recursive definition
generally fails as written. A profile may instead bind an *unfolding
equation* `(f, theorem)`: `f` is then checked through the theorem's statement
`∀ xs, f xs = rhs` (`f.eq_def`), as the body `fun xs => rhs` with `f`'s own
input contracts, against `f`'s declared type; recursive calls in `rhs` use
that interface. The statement must be an equality (the profile's `Eq`, pinned
to the kernel primitive) whose left side is `f` applied to exactly the
statement's binders, in order, and the theorem must be a safe theorem (its
proof is checked by erased typing). The profile binds the consumer to run `f`
by that equation; the kernel body is then not checked. `ix compile
--equations --profile FILE` adds every realized `f ↦ f.eq_def` association
as an `equation` directive, and only those: `equation` is a generated
directive, which a written profile may not contain, so the theorem bound to
`f` is always Lean's own unfolding theorem (`Ix.Compile.Equations.realize`),
never an author's theorem about `f` (a true but different equation, `f xs = f
xs`, or a false one). Admission also refuses a definition whose bound
equation depends on an axiom other than `propext`, `Quot.sound` and
`Classical.choice` (`sorryAx` or any user axiom): the adapter records every
other axiom of the closure by address (`Program.axioms`; the three standard
ones are pinned by their Ixon v4 content addresses) and admission propagates
that dependency through the reverse reference graph. Under `--profile`, the
equation sidecar lists, under `"resourceChecked"`, the `(definition,
equation)` pairs through which admission checked a definition (bound,
resource-relevant, not assumed): the consumer must run each of these
definitions by its equation.

The default analysis bounds are depth 256 and 100,000 steps per declaration.
Exhaustion is a rejection. Open sharing is analyzed in each binding context;
its resource result is never cached by expression identity alone.

## Named assumptions

Some rules rest on facts about the consumer that the checker cannot see. Each
is stated here and in the header of the Lean core profile; a consumer relying
on resource admission must establish it.

- **A fresh value is a new object.** A fully applied constructor, a nullary
  constructor reference and a literal are fresh: the checker treats every
  evaluation of one as a new object referenced nowhere else, so its result
  is unique whatever the constructor's declared result contract (R20; this
  is what lets `x :: acc` or `.node r k l` be returned as `!`). The consumer
  must allocate such a value anew at each evaluation that reaches a unique
  position: it must not replace it by a shared static object (hoisting,
  common-subexpression elimination, float-out, closed-term extraction,
  persistent literal objects), or else it must keep the run-time exclusivity
  check before any in-place update of it. Lean's own compiler extracts
  closed terms and string literals into persistent objects and relies on
  that run-time check; a consumer that skips the check because a contract
  says `!` must not do the same. Making the checker independent of this
  assumption would mean treating fresh results as shared, which would reject
  most unique results (`x :: acc`, `[]`, `.node …`); that is not done.
- **The linearity of a shareable immediate has no run-time meaning.** A value
  of a profile-shareable type (`Nat`, `Bool`, `String`, the scalar types of
  the core profile) is copied across call and closure boundaries; a `1` or
  `&` contract on it bounds how often the program names it, not a resource
  the consumer may rely on (no move-only handle, no single-use capability is
  represented by an immediate). The checker therefore lets a linear immediate
  cross into a many callee or a reusable closure. Uniqueness is not covered
  by this assumption: a unique immediate is moved, and a closure that moves
  its captured immediate is one-shot.
- **A field is an owned reference.** A value extracted from an aggregate, by
  a projection or by a case split, is a reference the consumer owns (Lean's
  reference-counted representation takes one when it extracts a field): it
  stays valid after the aggregate is dropped. The checker ties a field to its
  aggregate only until the field is consumed — consuming it shares the
  aggregate's owner, so the aggregate is never updated in place afterwards —
  but lets the field outlive the aggregate. A consumer that represents
  fields as loans into the aggregate's cell must not rely on admission.

The behaviour a profile states is a consumer obligation as well: under the
Lean core profile, choices by need; case splits and bound case definitions
without closures and without computing dead induction hypotheses; every other
call strict; and each definition the equation sidecar lists under
`resourceChecked` run by its unfolding equation.

## Profiles, claims, and consumers

A canonical profile begins with the UTF-8 bytes
`ixon-v4/resource-v1/profile` and a zero byte, followed by:

1. Assumptions, shareable type addresses, and selection primitive addresses:
   each list has a TagN (`f = 0`) count and strictly increasing 32-byte addresses.
2. Optional Nat and String type addresses: a byte `0`, or `1` and an address.
3. Nonzero depth and step limits, each a TagN (`f = 0`) unsigned integer.
4. An optional extension, present only when it is not empty: a TagN (`f = 0`)
   behavior flag (bit 0: case splits, bound case definitions and
   beta-redexes; bit 1: unfolding equations; bit 2: case definitions; no
   other bits), then a TagN (`f = 0`) count of admitted interfaces, each a
   32-byte address (strictly increasing), a TagN (`f = 0`) length, and that
   many bytes, one packed input/result contract byte per leading arrow; then,
   when bit 1 is set, the `Eq` type address and a nonzero TagN (`f = 0`) count
   of `(definition, theorem)` address pairs, strictly increasing by
   definition; then, when bit 2 is set (which requires bit 0), a nonzero TagN
   (`f = 0`) count of case definition addresses, strictly increasing.

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
in source prefix syntax, `_` for the default), `cases`, `equation NAME
THEOREM`, and `limits DEPTH STEPS`. Names are resolved against the compiled closure, entries outside it
are omitted, and the command prints the effective profile address; the
validation itself binds addresses only. The published Lean core profile is
[`profiles/lean-core.profile`](../profiles/lean-core.profile): the standard
entries, the scalar immediates `Char` and `UInt8`–`UInt64`, the choices `ite`,
`dite` and `cond`, case behavior, and readers (`List.length`, `Array.size`,
`String.length`) with a local input.
With `--equations`, the realized unfolding equations are added to the
profile source, so annotated recursion is checked through them.

A profile is a trust root for what it states by design: an `assume`,
`interface`, `choice` or `shareable` entry is an explicit claim that the
checker does not verify (a false interface or a strict function declared a
choice is admitted as stated). The directives whose truth is a fact about
Lean's own declarations are instead generated and never written: `equation`
(above) and `case`.

The directive `case NAME` (a case definition) is generated, never written: a
profile file containing it is rejected. When the file asks for `cases`, `ix
compile` adds `case NAME` for every constant of the compiled closure that
Lean records as a `casesOn` recursor or a matcher
(`Ix.Compile.ResourceProfile`), except a declaration with a native
implementation (`@[extern]`, `@[implemented_by]`), whose Lean body is only a
model. A bound name whose body is not a case wrapper is an ordinary call.

A declaration with a native implementation (`@[extern]`, `@[implemented_by]`)
is therefore never unfolded: callers use its declared interface only (for
example `String.push`'s shared result). When it carries a resource contract,
`ix compile` admits it only as an explicit profile assumption (`assume NAME`,
or a `choice`/`interface` entry) and refuses the compile otherwise (the
standard profile assumes nothing): its Lean body is only a model of the code
that runs, so checking the contract against it would certify the model, not
the implementation.

Because the case definitions and the equations are those of the compiled
closure, the effective profile address depends on the program, as name
resolution already makes it do; a consumer pins the address `ix compile`
prints for that closure. (A stable address would need the claim to commit to
a fixed base profile and, separately, to the per-program bindings; the claim
format has one profile address, so this is not done.)

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
covers usage crossing, proofs and open field rules, `resource-cases.tsv`
case splits, case wrappers, beta-redexes and choices,
`resource-equations.tsv` checking through unfolding equations,
`resource-freeze.tsv` freezing, fresh constructors and plain-data borrows,
`resource-strict.tsv` strict arguments of calls and beta-redexes against
by-need alternatives of bound case definitions, and `resource-fields.tsv`
case-split fields as views of the major and joins without an expected
contract. The suites also cover
all 64 input/result combinations, imported-interface aliases, mutual groups,
profile omissions, constructor captures, and bounded rejection of cyclic
sharing. Tests explicitly distinguish wire validity from resource admission.
