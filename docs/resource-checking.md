# Ixon resource checking (resource-v1)

The Lean and Rust resource validators consume the same canonical addressed
environment and an explicit profile. Both production compilers run this
ownership admission, erased typechecking, and source-contract transport
validation before emitting annotated constants. Resource claims bind the complete constant set and profile address.

The executable modules are [Basic](../Ix/Resource/Basic.lean),
[Check](../Ix/Resource/Check.lean), and [Admit](../Ix/Resource/Admit.lean).
[Rust](../crates/ixon/src/resource.rs) implements the same transitions.
The production boundaries are [Validate](../Ix/Resource/Validate.lean) and
[the Rust kernel adapter](../crates/kernel/src/resource.rs).

## Source-contract transport boundary

The combined native validators additionally reconstruct logical source types
from the same authenticated bytes, retaining complete universe parameters and
contract fields. Profile interfaces are runtime assumptions; they never replace
these logical source types. Low-level `Addressed.checkResources`, Rust
`addressed::check_resources`, and raw `Program` checks remain ownership
diagnostics, conditional on source typing and the other stated prerequisites.

[Lean Transport](../Ix/Resource/Transport/Validate.lean) and
[Rust Transport](../crates/kernel/src/resource/transport/validate.rs) check the
source signatures and bodies in the forward dependency closure of resource
obligations and selected equations, including theorem bodies and bodies whose
runtime behavior the profile assumes. Obligations include both source and
runtime interface dependencies. Equation bindings must retain the original
universe parameters and argument telescope; specialization to `Prop` cannot
stand for a polymorphic equation.

Runtime coverage is granted only where ownership admission checked that exact
computational expression. Proof, type, and erased arguments do not inherit
coverage from a surrounding runtime application. An uncovered computational
witness must pass a contextual ownership check, or belong to the closed default
fragment without resource-sensitive dependencies. A validated replacement
covers only its original definition's public header promises, not arbitrary
subterms in the original body.

Canonical equality endpoints receive a distinct checking role, not runtime
ownership coverage. A safe definition or theorem returning canonical equality
may defer an argument's ownership check only while its instantiated body is
rechecked at those actual arguments. Proof and type subterms reset this role;
opaque declarations cannot supply that body justification. This rule does not
grant a general exemption to indexed-family arguments.
A direct lambda application constructing a canonical equality type checks its
actual domain and argument, then checks the complete substituted body without
runtime coverage. Proof witnesses in that body retain their ownership checks;
this rule does not apply to arbitrary computational lambda applications.

Successful typing, conversion, universe instantiation, and normalization results
may be memoized within one fixed authenticated source/runtime program pair.
Keys retain complete contracts, ordered lexical types and ownership contracts,
expected types, universe instances, and coverage modes as applicable. Failed or
pending checks are never cached, and cache hits still consume checking fuel.

The current conservative fragment admits selected safe primitive families with
default-contract transitive primitive syntax. Unsafe inductives bypass erased
positivity checking and are explicitly refused when selected. Annotated
primitive rules require a further contract-sensitive primitive justification.
Conversion preserves contracts and supports bounded universe operations,
beta/zeta/delta reduction, constructor projections and recursor iota, typed
proof irrelevance, and checked function eta. Unsupported operations and budget
exhaustion refuse admission; there is no fallback to erased equality.

This fragment intentionally has false refusals. The harmless K00 cast changes a
function contract and is refused. Some generated recursive equation theorems
also fail their computational witness obligations or exhaust the typing budget;
equation-enabled closure results must be reported separately from closures
without those extra theorems. Acceptance of a plain core closure does not imply
acceptance of its equation-enabled export. These checks do not establish a
consumer execution theorem or enable an exclusivity optimization on their own.

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
requires a unique (one-shot) closure. Crossing is a profile choice: it
applies exactly to the types the profile declares `shareable` (and to types
themselves, which are erased), with no other exemption in either checker.
The standard profile (Nat, Bool, String) and the Lean core profile (also
`Char`, `UInt8`–`UInt64`) rely on it; the strict profile
([`profiles/lean-core-strict.profile`](../profiles/lean-core-strict.profile))
declares no shareable type, so a `1` or `&` value is consumed exactly or at
most once on every type, at calls and in closures alike, as in Idris 2 and
Linear Haskell. An argument whose domain is a proposition is a proof,
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
types never freeze.

A literal (`.nat`, `.str`) is static data: a consumer may keep one persistent
object for it, so it is shared, never fresh, and cannot enter a unique (`!`)
position (`SharedToUnique`); a unique value needs an explicit copy. Lean
elaborates numerals, scientific literals, characters, string interpolation
and array literals into calls (`OfNat.ofNat`, `OfScientific.ofScientific`,
`Char.ofNat`, `toString`/`++`, `List.toArray`), whose results are the
ordinary shared results of those functions. A fully applied constructor is
classified by its *run-time fields* — the arguments after the inductive
type's parameters whose domain is neither a type former nor a proposition:

- with no run-time field (`Nat.zero`, `[]`, `none`, `.leaf`), it is an
  immediate: it has no heap cell (Lean and Compilatr represent it as a
  scalar), so it is unique;
- with exactly one run-time field, of a type that may have only this
  constructor (a single-constructor type, or one whose block the program
  does not show), it is represented by that field (Lean's trivial
  structures, Compilatr's unboxed single-field structures such as `Subtype`
  and `Fin`): it allocates nothing and takes its declared result contract
  (shared);
- otherwise it allocates a cell, which is *fresh* — unique whatever the
  constructor's declared result contract — only when a run-time field
  depends on a run-time local (a variable of the definition whose type is
  neither a type former nor a proposition, reached through projections,
  application heads and run-time arguments): `x :: acc`, `.node r k l`,
  `[x]`. A closed construction (`[1, 2, 3]`, `.node .nil .nil`, `some 3`)
  is static data, like a literal, which a consumer may extract as a
  persistent closed term: shared.

Freshness rests on a named assumption below: a consumer must allocate a
fresh construction anew at each evaluation. A plain-data owner may be
borrowed: the loan suspends it as it does a shareable one, and the view's
origins keep it inside the loan.

Constructing a closure transfers captured unique owners. That transfer counts
even when the closure's body only borrows the captured owner. A reusable shared
closure cannot hide a finite-use or uniquely consumed capture; only the finite
use of a shareable immediate is exempt (above), never a capture the body
moves. A unique
closure can carry these captures and is consumed when invoked. Borrowing does
not turn such a closure into a reusable shared callback.

### Usage crossing on plain data (the plain profile)

[`profiles/lean-core-plain.profile`](../profiles/lean-core-plain.profile)
(the directive `crossing plain`, profile extension bit 3) adopts OxCaml's
division of the usage axis. In OxCaml, uniqueness and linearity are separate
modes, and "linearity is about functions: its purpose is to track unique
values in closures … Linearity is irrelevant for types that do not contain
functions" (OxCaml, `jane/doc/extensions/modes/intro.md`, the linearity
axis); values of types that do not contain functions mode-cross to `many`
(`jane/doc/extensions/kinds/02-syntax.md`, `everything`), and a field
declared `@@ many` makes its type cross even when it holds a function
(`kinds/01-intro.md`, modalities). Every constructor field of an admitted ix
inductive carries the default contract (`many`, shared): annotated
constructors are refused by the frontend, and a `1` or non-duplicable value
cannot be stored in a field. So the faithful predicate for ix is plain data
(`plainData`): an inductive of an addressed block whose constructors all
carry default contracts in their effective interfaces (the profile's
`interface` lines applied), whatever its parameters and even with function
fields.

Under `crossing plain`, a type *crosses* the usage axis (`crosses`) when,
after weak-head reduction, it is plain data or profile-shareable, and the
profile does not opt it out (`linear NAME`, extension bit 4, for capability
tokens). `Prod`, `Sigma`, `Subtype`, `Fin`, `Decidable`, class dictionaries,
`List`, `Option`, `Thunk`, `Task`, nested and recursive inductives cross;
so do `Nat`, `String`, `Bool`, `Char`, `UInt8`–`UInt64` and `Array`, whose
blocks are visible in Ixon v4 (no `shareable` declaration is needed).
Arrows and Π-types (`IO α`, `StateM`, `Unit → α` once unfolded), type
variables of the definition (at a call site the caller's argument type
decides), inductives with an annotated constructor, and types without a
visible block (axioms, `opaque` types) do not cross, unless the profile
declares them `shareable`. On a crossing type:

- both bounds of a written `1`/`&` contract are dropped — OxCaml has no
  relevance axis, and its `once` is "at most once" — and `ix compile`
  reports the binder (`[compile] resource: plain-data crossing: …`;
  `AddressedProgram.crossed`);
- passing the value to a many-use callee is one consumption, and capturing
  it does not make a closure one-shot on the usage axis.

`0` (erased) inputs and the zero demand of proof arguments are unchanged.
Ownership is unchanged: uniqueness, moves, freeze, locality, borrows, the
one-shot rule for a closure that moves a capture, and case-split field views
apply on every type exactly as under the strict profile (the plain profile
has no shareable type). This rests on the named assumption "usage on plain
data carries no consumer obligation" below. Compilatr.ix compiles usage
contracts on data to nothing, so its code is not affected.

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
  compile` binds exactly those Lean generates, see below) is unfolded at a full
  application when its body is an unannotated lambda telescope around a full
  application of such a case split or of another bound case definition. Its
  parameters are classified from that body: a parameter is *by need* when
  every occurrence lies in an alternative (a minor premise, or a by-need
  position of the inner case definition), after at most the binders the case
  enters there, as the head of an application whose arguments do not mention
  it; occurrences in different alternatives are allowed, since one
  alternative runs. Every other parameter — a discriminant, a motive, one
  used under a closure, twice in one alternative, or not at all — is strict.
  The body also determines how many arguments are supplied to each by-need
  parameter, including case-supplied fields, hypotheses and extra arguments
  not consumed by explicit leading lambdas. Thus a bare field minor `h`
  receives the same count as its eta-expanded form `fun x => h x`, including
  through nested case wrappers. A lambda alternative, or an evaluation-free argument (below),
  is substituted and entered only in its selected branch. At a zero-argument
  minor an application headed by a lambda is also eligible: this is an
  executed alternative such as an inner `h_i ()`. A matcher thunk, which
  takes at least one argument, does not accept a computation returning a
  lambda as an alternative: `mk ys` and `(fun _ => mk ys) ()` are both bound
  strictly, once before the case. Merely having a lambda at the application
  head does not exempt that computation.
- Arguments beyond the arity of a case split, bound case definition or
  choice must be evaluation-free (the criterion in the next item). The
  checker refuses an effectful over-application argument such as `bump xs`;
  a source-level `let` must specify where it is evaluated. This prevents
  moving or mutating the major before it is inspected when a consumer
  evaluates extra arguments before dispatch. A variable extra argument is
  allowed: reading its value does not perform the eventual callee's move.
- Every other application binds its arguments strictly: a beta-redex's
  arguments, and the arguments of every definition that is not a bound case
  definition, however match-shaped (a user helper `sel b x y := match b with
  …`, `Option.getD`, `String.push`), which is an ordinary call against its
  declared interface. A strict argument is substituted only when evaluating
  it has no effect: a variable, a type or proof (erased computation), a sort,
  a constant that is not a nullary constructor, or a closed lambda (which
  captures and moves nothing). Any other argument — literals, constructor
  applications and nullary constructors (fresh or static values), lambdas with free
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
directive, which a written profile may not contain. A theorem is associated
with `f` only when it is Lean's own unfolding theorem
(`Ix.Compile.Equations.notGenuine`, second review R2-5): the name `f.eq_def`
proves nothing, since a metaprogram can `addDecl` a theorem of that name past
Lean's reserved-name check (`cnt xs u = cnt xs u`, a true but different
equation) and `getUnfoldEqnFor?` then returns it. `ix compile` re-derives the
statement Lean generates — `∀ xs, f xs = body` from the pre-definition
`fun xs => body` Lean recorded when it compiled `f`'s recursion (its
structural, well-founded or `partial_fixpoint` equation record), or from
`f`'s own value when `f` is not recursive — and requires the theorem's
statement and universe parameters to equal it; the proof is irrelevant. The
unfolding theorem of a well-founded definition's `_unary`/`_binary`/`_mutual`
auxiliary has no recorded pre-definition; it is accepted when the
definition's well-founded record names that auxiliary and the theorem lies
in the auxiliary's module (Lean adds it while elaborating the definition, so
the name cannot be taken first) or is Lean's importer alias of that private
original. Any other theorem is not associated: the sidecar lists `f` under
`failures` with `equation not genuine: …`, and an annotated `f` is then
refused as annotated recursion without a bound equation (below). The
records consulted are themselves environment state that a metaprogram could
overwrite, so this check is defense in depth, not the premise of resource
safety: that is consumer obligation (c) (below). Admission also refuses a definition whose bound
equation depends on an axiom other than `propext`, `Quot.sound` and
`Classical.choice` (`sorryAx` or any user axiom): the adapter records every
other axiom of the closure by address (`Program.axioms`; the three standard
ones are pinned by their Ixon v4 content addresses) and admission propagates
that dependency through the reverse reference graph.

Annotated recursion is admitted only through a bound equation (second
review, R2-3): `ix compile` refuses an annotated recursive definition — one
Lean realizes an unfolding theorem for, or whose kernel body references a
recursion auxiliary (`brecOn`, `binductionOn`, `WellFounded.fix`, a
`_unary`/`_binary`/`_mutual`/`_f` auxiliary) — unless it is checked through
its bound equation (`--equations --profile FILE`) or the profile assumes it
(`Ix.Compile.ResourceProfile.checkRecursion`), and it confirms after the
compile that each such definition is among the checked pairs. Its kernel
body, with its unchecked `_f`/`_unary` auxiliaries, is not what a consumer
runs, so it is never the checked path; under the standard profile, which
binds no equation, annotated recursion is therefore refused outright.

Whenever resource admission runs or a profile is given, the equation
sidecar records the closure root, the effective profile (address and
canonical bytes) and, under `"resourceChecked"`, the `(definition,
equation)` pairs through which admission checked a definition (bound,
resource-relevant, not assumed), each with both addresses, the profile
address and the contracts the equation carries ([source
contracts](source-contracts.md), "Checked pairs"): the consumer must run
each of these definitions by the bound equation's right-hand side, fetched
by address. `ix check-equations SIDECAR CLOSURE` re-verifies the list
against the closure.

The default analysis bounds are depth 256 and 100,000 steps per declaration.
Exhaustion is a rejection. Open sharing is analyzed in each binding context;
its resource result is never cached by expression identity alone.

## Named assumptions

Some rules rest on facts about the consumer that the checker cannot see. Each
is stated here and in the header of the Lean core profile; a consumer relying
on resource admission must establish it.

- **A fresh construction is a new object.** Literals and closed
  constructions are shared (static data), so they need no assumption. A
  construction with a run-time field that depends on a run-time local is
  fresh: the checker treats every evaluation of it as a new object
  referenced nowhere else, so its result is unique (this is what lets
  `x :: acc` or `.node r k l` be returned as `!`). The consumer must
  allocate it anew at every evaluation in the checked body: it
  must not share one object between evaluations (common-subexpression
  elimination of two constructions, float-out or full laziness out of a
  closure or loop, or inlining a local and then extracting the now closed
  term), or else it must keep the run-time exclusivity check before any
  in-place update, reuse or unconditional free justified by that inferred
  uniqueness. This condition is on allocation sites of the executed checked
  body; it does not require guessing whether a particular result eventually
  reaches a unique position. The construction must also be a cell of its own:
  the checker counts a one-run-time-field constructor as unboxed only when
  the program shows no other constructor of its type, so a consumer that
  unboxes a constructor the checker counts as a cell (for example one of a
  multi-constructor type) must not rely on admission. Making the checker
  independent of this assumption would mean treating every construction as
  shared, which would reject all unique results (`x :: acc`, `.node …`).
- **A constructor without run-time fields is an immediate.** `Nat.zero`,
  `[]`, `none` (a constructor whose arguments are only parameters, types
  and proofs) are unique: they have no heap cell, so uniqueness grants
  nothing to update or free. The consumer must represent such a value
  without a heap object, as Lean and Compilatr do (a scalar), or allocate it
  anew; it must not use a shared static object that a `!` consumer could
  free or reuse.
- **The linearity of a shareable immediate has no run-time meaning.** A value
  of a profile-shareable type (`Nat`, `Bool`, `String`, the scalar types of
  the core profile) is copied across call and closure boundaries; a `1` or
  `&` contract on it bounds how often the program names it, not a resource
  the consumer may rely on (no move-only handle, no single-use capability is
  represented by an immediate). The consumer must not elide an increment or
  decrement on the strength of that usage grade; Nat and String can be heap
  objects even when the profile calls them shareable. The checker therefore lets a linear immediate
  cross into a many callee or a reusable closure. Uniqueness is not covered
  by this assumption: a unique immediate is moved, and a closure that moves
  its captured immediate is one-shot. The standard and Lean core profiles
  rely on this assumption; the strict profile, which has no shareable type,
  does not.
- **Usage on plain data carries no consumer obligation** (the plain
  profile; it extends the previous assumption from the shareable immediates
  to every crossing type). A `1` or `&` contract on a value of a plain-data
  type bounds nothing the consumer may rely on: no elided drop or increment,
  no move-only representation, no single-use capability. Ownership (`!`) on
  such a value is still checked and may be relied on. A data type that does
  represent a capability must be opted out with `linear NAME`. The worst
  outcome of a consumer wrongly trusting such a `1` is a leak (an elided
  drop), not an unsafe access, since no ownership is inferred from it.
- **A field is an owned reference.** A value extracted from an aggregate, by
  a projection or by a case split, is a reference the consumer owns (Lean's
  reference-counted representation takes one when it extracts a field): it
  stays valid after the aggregate is moved, reused, updated or freed. An RC
  backend must increment the field reference (or provide an equivalent
  lifetime guarantee) before any such operation. The checker ties a field to its
  aggregate only until the field is consumed — consuming it shares the
  aggregate's owner, so the aggregate is never updated in place afterwards —
  but lets the field outlive the aggregate. A consumer that represents
  fields as loans into the aggregate's cell must not rely on admission.

The behaviour a profile states is a consumer obligation as well: under the
Lean core profile, choices by need; case splits and bound case definitions
without closures and without computing dead induction hypotheses; every other
call strict; and each definition the equation sidecar lists under
`resourceChecked` run by its bound equation's right-hand side, fetched by
address (no annotated recursive definition is admitted any other way). The
next section states these obligations precisely.

## Consumer obligations

Resource admission checks the program under the evaluation
order the profile states. A consumer relying on admission must run exactly
that program in that order. The obligations are lettered as in the second
review of the checker; each names the objects it covers and what it
forbids, so that a compiler's correctness proof can state it as a premise.

- **(a) Case alternatives and strict arguments.** *Covers:* arguments at
  body-derived by-need positions of a bound case definition. *Requires:*
  eligible lambda alternatives are entered in their selected branch without
  first allocating capturing closures. Zero-argument minors may contain the
  executed lambda application described above. Every ineligible argument is
  evaluated exactly once, before dispatch, by the strict `let` introduced by
  `bindArguments`. *Forbids:* deferring an arbitrary computation that produces
  a matcher thunk, including a beta-wrapped one; or building a lambda
  alternative's captures before branch selection while relying on admission.
  Shared `resource-order.tsv` fixtures exercise the two checker paths;
  source probes N03/N03Beta and the lambda control exercise generated matchers.
- **(b) Over-application has no evaluation effects.** *Covers:* every
  argument past a choice's or case split's arity, including through a bound
  case definition. *Requires:* the argument satisfies `substitutable` before
  branch analysis; otherwise admission refuses it. Its eventual consumption
  remains in the selected branch. *Forbids:* hiding a move or update in an
  extra argument whose evaluation could precede inspection of the major.
  Shared case/wrapper/choice fixtures and source N04/N15 with value controls
  cover the restriction. This check does not license code motion of an
  explicit strict `let` across dispatch.
- **(c) Run exactly the body that was checked.** *Covers:* every
  definition of the admitted closure that resource admission checked (a
  resource-relevant definition the profile does not assume). *Requires:* a
  definition listed under `resourceChecked` in the equation sidecar runs by
  the right-hand side `rhs` of the theorem fetched by its `equationAddress`
  (its statement `∀ xs, f xs = rhs`, instantiated at the call's arguments;
  recursive calls in `rhs` are calls of the listed definitions, run the same
  way); every other checked definition runs by its exported Ixon body, the
  value at its own address. *Forbids:* running, for a checked definition,
  Lean's compiled code (its `_unsafe_rec` twin, a `partial def`'s
  implementation, an `@[implemented_by]`/`@[extern]` replacement, a
  `@[csimp]` replacement), a recompilation from its Lean source or from any
  other theorem about it, or its kernel recursion encoding (`brecOn`,
  `WellFounded.fix` with its `_f`/`_unary` auxiliaries) in place of the bound
  equation. Resource safety rests on this obligation, not on the equation
  being genuine: the program checked is then the program run, whatever
  theorem was bound, so a forged (second review R2-5), smuggled (R2-4) or
  false equation could only break functional agreement with Lean, never an
  ownership guarantee. `ix compile` binds only Lean's own unfolding theorem
  (above) and refuses annotated recursion that is not checked through it;
  `ix check-equations` re-verifies the listed pairs by address.
- **(d) No unchecked compiler replacement.** *Covers:* every checked
  definition and every call of one, including `@[csimp]` redirections.
  *Requires:* the exact body rule in (c). Ixon resource admission does not
  authorize Lean's csimp map: the map is not exported in Ixon, and equality
  of functions does not show that two implementations obey the same
  ownership or allocation contract. *Forbids:* applying a replacement solely
  because its source body was admitted or because a csimp theorem proves
  functional equality. No replacement path is supported by this admission
  API. A future consumer supporting one must check the replacement against
  the replaced declaration's full contract under the same effective profile,
  bind its executed body by address, and preserve the allocation and
  evaluation-order conditions here. Checking a replacement only against its
  own weaker interface is insufficient. The CSimp/CSimpReplacement source
  regression has a registered replacement of the same function type: the
  original fresh construction is admitted and the aliasing replacement is
  rejected.
- **(e) Case definitions are taken from the profile, by address, with
  by-need positions derived from the bound body.** *Covers:* every
  application, in a checked definition, of a constant the effective profile
  binds as a case definition (`case NAME`; the canonical profile lists their
  addresses, extension bit 2). *Requires:* the consumer treats exactly the
  constants whose addresses the profile lists as case definitions, and for
  each derives its by-need positions from that constant's bound body by the
  rule above (a parameter is by need when every occurrence lies in an
  alternative of the inner case split or case definition, as the head of an
  application whose arguments do not mention it); every other position, and
  every other constant, is strict. *Forbids:* recognising case definitions
  by the consumer's own criteria (a name ending in `casesOn` or `match_N`, an
  auxiliary-recursor tag, `MatcherInfo`), compiling a constant the profile
  lists as an ordinary strict function while relying on the admission, or
  taking by need a position the bound body does not make by need. `ix
  compile` lists only the verifiably generated `casesOn`s and matchers
  (below), so a user definition never acquires branch semantics; resource
  safety rests on this obligation, which holds whichever constants are
  listed, since the consumer then evaluates exactly what was checked.

### Evidence and remaining consumer obligations

| Executed-program condition | Evidence or check | Remaining obligation |
| --- | --- | --- |
| Fresh allocations are not shared across evaluations; no static cell is treated as a fresh heap cell | Literal/closed/unboxed-constructor resource fixtures | Backend allocation/code-motion audit, or retained exclusivity checks before reuse/update/free |
| Usage crossing grants no RC or representation optimization | strict/plain shared fixtures and crossed-binder diagnostics | Consumer ignores crossing usage grades; `linear` opts capability types out |
| Extracted fields retain their own lifetime | field-view and use-after-move shared fixtures | Backend increments/retains the field reference before moving or freeing its aggregate |
| (a) Eligible alternatives enter only their selected branch; other arguments are strict | order/strict fixtures; N03 variants and controls | Consumer must implement those exact positions, without eager captured closures |
| (b) Over-application arguments have no evaluation effects | `requireValue`/`require_value`, order fixtures, N04/N15 | Preserve strict-let order and branch-local consumption |
| (c) The executed body is the authenticated checked body | bound pairs and `ix check-equations`; R2-3/R2-5 regressions | Consumer verifies addresses and runs that body |
| (d) Admission does not authorize csimp | CSimp source regression, no replacement map in Ixon | Consumer declines unchecked redirects; a supported target needs a new contract check |
| (e) Case behavior is selected by the effective profile's addresses and derived shape | generated-case checks and N01/N02; order shape regressions | Consumer uses that exact profile/shape, not independent naming or metadata rules |

These checks are regression evidence, not a soundness theorem for the resource
checker. Compilatr.ix continues to treat its verdict as a diagnostic: its
separate Own checks and compiler correctness proofs are not discharged by an
ix acceptance. In particular, its strict argument binding for ordinary
matcher wrappers is not by itself evidence of (a) or (e).

## Profiles, claims, and consumers

A canonical profile begins with the UTF-8 bytes
`ixon-v4/resource-v1/profile` and a zero byte, followed by:

1. Assumptions, shareable type addresses, and selection primitive addresses:
   each list has a TagN (`f = 0`) count and strictly increasing 32-byte addresses.
2. Optional Nat and String type addresses: a byte `0`, or `1` and an address.
3. Nonzero depth and step limits, each a TagN (`f = 0`) unsigned integer.
4. An optional extension, present only when it is not empty: a TagN (`f = 0`)
   behavior flag (bit 0: case splits, bound case definitions and
   beta-redexes; bit 1: unfolding equations; bit 2: case definitions; bit 3:
   usage crossing on plain data; bit 4: linear types; bit 5: explicit scalar types; no
   other bits), then a TagN (`f = 0`) count of admitted interfaces, each a
   32-byte address (strictly increasing), a TagN (`f = 0`) length, and that
   many bytes, one packed input/result contract byte per leading arrow; then,
   when bit 1 is set, the `Eq` type address and a nonzero TagN (`f = 0`) count
   of `(definition, theorem)` address pairs, strictly increasing by
   definition; then, when bit 2 is set (which requires bit 0), a nonzero TagN
   (`f = 0`) count of case definition addresses, strictly increasing; then,
   when bit 4 is set, a nonzero TagN (`f = 0`) count of linear (opted-out)
   type addresses, strictly increasing; then, when bit 5 is set, a nonzero
   TagN (`f = 0`) count of explicit scalar type addresses, strictly increasing.
   Bit 3 carries no data.

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
standard profile's entries), `literals` (only the standard profile's Nat and
String literal types, no shareable type), `shareable NAME`, `scalar NAME` (disabled
by default; separate representation assumption below), `assume NAME`, `choice NAME`,
`interface NAME C…` (one contract token per leading arrow, `INPUT[:RESULT]`
in source prefix syntax, `_` for the default), `cases`, `crossing plain` (usage
crossing on plain data), `linear NAME` (opt a type out of it), `equation NAME
THEOREM`, and `limits DEPTH STEPS`. Names are resolved against the compiled closure, entries outside it
are omitted, and the command prints the effective profile address; the
validation itself binds addresses only. The published Lean core profile is
[`profiles/lean-core.profile`](../profiles/lean-core.profile): the standard
entries, the scalar immediates `Char` and `UInt8`–`UInt64`, the choices `ite`,
`dite` and `cond`, case behavior, and readers (`List.length`, `Array.size`,
`String.length`) with a local input. The strict Lean core profile
[`profiles/lean-core-strict.profile`](../profiles/lean-core-strict.profile)
is the same with `literals` in place of `standard` and no scalar
immediates: it has no shareable type, so no usage contract crosses (see "Uses
and availability"); choices and case behavior are unchanged, since they are
about evaluation, not crossing. The plain-data Lean core profile
[`profiles/lean-core-plain.profile`](../profiles/lean-core-plain.profile)
is the strict profile with `crossing plain`: usage crosses on plain data
and is enforced on everything else ("Usage crossing on plain data").
With `--equations`, the realized unfolding equations are added to the
profile source, so annotated recursion is checked through them.

A profile is a trust root for what it states by design: an `assume`,
`interface`, `choice` or `shareable` entry is an explicit claim that the
checker does not verify (a false interface or a strict function declared a
choice is admitted as stated). `crossing plain` rests on the named assumption
that usage on plain data carries no consumer obligation; `linear` only adds
checking. The directives whose truth is a fact about
Lean's own declarations are instead generated and never written: `equation`
(above) and `case`.

The directive `case NAME` (a case definition) is generated, never written: a
profile file containing it is rejected. When the file asks for `cases`, `ix
compile` adds `case NAME` for every constant of the compiled closure that
Lean records as a `casesOn` recursor or a matcher and that is verifiably
generated (`Ix.Compile.ResourceProfile.caseDefinitions`; second review
R2-6), except a declaration with a native implementation (`@[extern]`,
`@[implemented_by]`), whose Lean body is only a model. A record alone proves
nothing: a metaprogram can tag any definition as an auxiliary recursor
(`markAuxRecursor`) or give it `MatcherInfo`. So:

- `I.casesOn` qualifies only when `I` is an inductive type and Lean's own
  construction (`mkCasesOnImp`, the kernel's `casesOn` generator) re-derives
  exactly that declaration (universe parameters, type and value) from `I`'s
  recursor;
- a matcher qualifies only when its value is a lambda telescope of exactly
  its `MatcherInfo` arity (parameters, motive, discriminants, alternatives)
  around an application — after β-reducing its head, as for a match with an
  equality hypothesis — of such a generated `casesOn`, and every
  alternative parameter takes at least the arguments its `MatcherInfo`
  records, at least one (an alternative without fields takes a `Unit`), so
  no alternative is a plain value.

Every other recorded constant gets no `case` line and is an ordinary call;
`ix compile` reports it (`… is recorded as a casesOn or matcher but is not one
Lean generates`). Lean's matchers over a sparse `casesOn` (`_sparseCasesOn`,
for overlapping or wildcard patterns) are among them; they were ordinary
calls before as well, since a sparse `casesOn` is not a case definition. A
bound name whose body is not a case wrapper is an ordinary call.

A declaration with a native implementation (`@[extern]`, `@[implemented_by]`)
is therefore never unfolded: callers use its declared interface only (for
example `String.push`'s shared result). When it carries a resource contract,
`ix compile` admits it only as an explicit profile assumption (`assume NAME`,
or a `choice`/`interface` entry) and refuses the compile otherwise (the
standard profile assumes nothing): its Lean body is only a model of the code
that runs, so checking the contract against it would certify the model, not
the implementation. The same holds for an `opaque` (its value is an
inhabitant the compiler never runs) and so for every `partial def`, which
Lean compiles from its `_unsafe_rec` twin while the kernel sees only the
opaque inhabitant (second review, R2-2): `ix compile` counts both as native
implementations (`Ix.Compile.ResourceProfile.native`). A *definition* with
an `_unsafe_rec` twin (structural or well-founded recursion) is not: it is
admitted only through its bound unfolding equation (above).

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
| Lean and Rust combined native validators | Ownership, erased typing, and source-contract transport, with a committed profile |
| Addressed/raw resource diagnostics | Ownership under the documented source-typing prerequisites |
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
`resource-freeze.tsv` freezing, fresh constructors, literals and static
constructions, and plain-data borrows,
`resource-strict.tsv` strict arguments of calls and beta-redexes against
by-need alternatives of bound case definitions, and `resource-fields.tsv`
case-split fields as views of the major and joins without an expected
contract, and `resource-noshare.tsv` the absence of usage crossing without
shareable types (the strict profile), and `resource-plain.tsv` usage crossing
on plain data with an opted-out type (the plain profile). The suites also cover
all 64 input/result combinations, imported-interface aliases, mutual groups,
profile omissions, constructor captures, and bounded rejection of cyclic
sharing. Tests explicitly distinguish wire validity from resource admission.

### Compilatr.ix source inspection (Phase 1.5)

The consumer evidence is narrower than the conditions above. In Compilatr.ix,
`Src.Lazify.byNameRanges` grants laziness to pinned lazy primitives and
recognized cases/recursors; an ordinary matcher wrapper retains strict
arguments. `Src.Semantics.eval` evaluates a strict application argument before
applying the function, and `Lam.Erase.Term.bindArgs` introduces strict lets.
Consequently these paths do not establish branch-local construction of an
arbitrary matcher alternative, nor profile-selected case semantics: (a) and
(e) remain unmet for general wrappers. For recognized saturated cases,
`Lam.Erase.special` saturates the case before applying extra arguments; this
does not justify reordering effectful over-application arguments of wrappers.

The inspected consumer also has a `Check.checkCsimp` certificate path and a
`Build` priority for csimp before equation hints, even though its K1 parser
emits only equation hints. Parser behavior alone therefore does not establish
(d). Phase 1.5 consumer changes must explicitly refuse unchecked replacements
in a resource-bound context and validate executed equation selection; until
those changes are independently validated, the corresponding table entries
remain obligations. These observations are source inspection, not additional
resource-safety theorems or permission to rely on an ix verdict.

### Disabled scalar representation preparation

The optional written directive `scalar NAME` binds a separate explicit
representation assumption by address. It is **disabled in all shipped/pinned
profiles**. It does not follow from `shareable`, `crossing plain`, an inductive
shape, a familiar type name, or an apparent small literal. It permits copying
that scalar's payload across the ownership axis: a shared payload may satisfy
a unique result, and a unique payload can be used again. Usage (including zero,
linear and affine bounds), locality, and borrowing scopes retain their checks.
No usage crossing is added by `scalar`.

The necessary soundness condition is universal over the executed program:
every value of the named closed nominal type must have a resource-free,
non-owning representation that may be copied without sharing a heap owner,
reference-count obligation, capability, or mutable identity. This must also
hold at every generic call, closure capture, aggregate field, backend boxing,
and FFI boundary. A backend that boxes a payload must independently retain or
copy the box with ordinary ownership discipline; it cannot transfer the
checker's scalar ownership exemption to that box. Until that implementation
condition is established, such a type must not be listed. In particular,
bounded machine arithmetic alone is insufficient: boxed `UInt64`, arbitrary
`Nat`, `String`, and containers are not justified by their names or by a
particular unboxed execution.

The checker recognizes the assumption only on a reduced bare reference whose
declaration is a nominal type of a non-proposition sort. An application of a
type constructor and an abstract polymorphic type variable never inherit it.
The explicit profile assumption remains a trust condition, not a representation
proof. Shared enabled/disabled fixtures cover ownership copying, boxed
containers, polymorphic/applied types, captures, and unchanged usage/locality
refusals. The pinned-policy X09/L02/L03 refusals remain required.

Canonical encoding uses optional extension bit 5 (`32`), followed after the
linear-type list by a positive TagN length and a strictly increasing list of
32-byte addresses. An empty list emits neither bit nor data, preserving all
existing profile bytes. Duplicate, unordered, empty flagged, truncated, and
unknown-bit encodings are refused. Consumers that have not established the
representation condition must decline profiles with a nonempty scalar list.
