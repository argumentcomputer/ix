# Consistency model

`Ix.Theory` contains Ix's set-theoretic consistency model, its certified acceptance
interface, and certificate construction. Build it with `lake build IxTheory`;
run the selected regression tests, provenance check, and exact foundation
audit with `lake run check-theory`.

`Ix.Theory.Certified.accepted_has_model` constructs a model for accepted
declarations. `accepted_proof_sound` and `no_proof_of_False` give the corresponding
semantic and consistency results. These theorems assume a type `V` equipped
with `Ix.Theory.Model.SetTheory V`: set operations and laws together with a
countable tower of Grothendieck universes. The separate
[`Models/SetTheory`](../Models/SetTheory/README.md) package constructs this
structure on Mathlib's `ZFSet` from a strictly increasing countable sequence
of strongly inaccessible cardinals. Its `carneiro_implies_ix` theorem retains
that large-cardinal hypothesis explicitly and passes an axiom guard for
`propext`, `Classical.choice`, and `Quot.sound`. User-supplied logical axioms and
open frontiers retain their stated model hypotheses.

The [certified host adapters](certified-checking.md) connect authenticated
serialized Ixon to model admission. Separately, a production `checkEnvAnon`
[fragment](kernel-verification.md#production-environment-fragment) for
aliases, universe terms, instances of earlier constants, and a fragment of
closed dependent function bodies, including definitions with their own universe parameters,
extends every model of its source axioms under explicit execution witnesses.
Binder inference uses the declared type's separate formation check to turn
`Model.CheckingClaim` into semantic typing. The actual production validation
supplies source universe bounds; the scoped reading supplies term closure,
with bounds on auxiliary binder conditions checked separately. Model entries
retain the exact declared universe count and denote the checked body at every
universe instance. Application spines headed by locals
or admitted polymorphic constants derive their type's validity from the context
or dependency model, then check arguments and substitute the dependent result.
The synthesis rules additionally derive a uniform universe bound for every
generated type, allowing direct lambda applications and returned functions.
Bounds come from actual binder-domain and earlier declaration type checks.
For application, an inhabited dependent product bounds every fibre in a
Grothendieck universe; the proof regime retains the exact bound zero. The
resulting positive bounds can be larger than an independently inferred sort,
while preserving every binder's Prop condition. No additional codomain check
or semantic typing premise is required. Earlier executed type checks remain
usable after interface growth and universe instantiation.
Successful environment rows supply the axiom type-inference traces; public
declaration success supplies the corresponding definition traces.
For a source beta redex, the inference tree retains the lambda's checked
domain and supplies the argument's membership in it. This derives equality
and typing for the substituted result; denotational typing alone cannot
recover that domain after proof values have been identified. This extends to
the full original lambda prefix, with dependent arguments and any remaining
application suffix. The actual multi-argument structural-WHNF step reads the
result through simultaneous substitution and interned suffix rebuilding,
preserving intern coherence. The walk's bounds concern the original body and
argument trees. Substitution also preserves the model's typing, checking,
and equality judgments beneath any retained dependent parameters, updating
each later domain. Selected cheap-beta plans preserve the same meaning
when an actual source check is available.
Declaration admission includes declared types reduced through a lambda
prefix and a remaining suffix: the declaration's own executed type check
justifies conversion from that result to the original type. The environment
model and no-False theorems include this case. Recursive lambda inference
also supports changed cheap beta when the generated body type retains its
actual checking origin. The inference proof preserves checked lambda domains;
the raw reader derives the selected prefix and reduced expression. A syntactic
transport moves the original check through interface extension, local
weakening, and universe instantiation, and earlier local contexts come from
their executed domain checks. It now also carries codomain checks through
term substitution: the earlier function-type tree supplies the actual
codomain call, while the executed function and argument checks and hash
comparison establish membership in the substituted parameter's domain.
The mutual inference proof preserves this origin beneath remaining dependent
parameters. A variable-headed codomain now retains its actual argument checks
and local head type through earlier parameter substitutions. When a lambda
argument replaces that head, its own checked domains justify the newly
exposed prefix. Nested codomain origins are extracted from the executed
function-type tree. Later arguments transport the resulting reduction through
the remaining dependent parameters. A supplied lambda application also keeps
its already checked arguments: they precede the original codomain's arguments
in the combined spine, with both sets of dependent types preserved. The
selected beta prefix can consume arguments from both origins. The lambda
closes the reduced type using the actual final intern table. Each reduction
is bounded by the checked prefix of its selected origin.
Two successive prefixes now compose when the first lambda's body applies
its parameter and substitution exposes the supplied lambda. The body's
original argument checks remain available even if cheap beta changes its
inferred type. The first reduction retains typing at that current type;
the supplied lambda contributes the second prefix's domains and any initial
arguments. This supports the actual WHNF step on the intermediate term and
declaration admission through both reductions, without another inference
call on the intermediate term. Finite beta traces now compose any number of
retained prefixes, including generated functions and arguments, application
suffixes, and dependent substitutions. The result retains the original type
even when adjacent steps carry different types. A structural-WHNF trace
computes each raw substitution result and intern table and proves the actual
uncached loop under its bound, including the final unchanged iteration.
Declaration admission uses the same traces. The currently supported source
inference trees now construct complete beta typing derivations, retaining
lambda bodies and both application children. Dependent substitution rebuilds
these derivations, including under retained binders. Each generated result
therefore supplies the exact lambda domains and argument origins for every
later head-beta step. This also handles a lambda whose body's inferred type
changes by cheap beta. A finite operational WHNF path needs only raw execution,
reading, and representation resources; its semantic origins and declaration
conversion follow automatically from the original inference. Constructing
the initial inference and operational resources for arbitrary accepted
programs, the remaining reduction branches, and general conversion remain open.
Full-mode let inference now uses its original declared-type, value, and opened
body checks. The scoped reader interprets a let by value substitution, and the
actual opening, abstraction, and substitution walkers preserve that reading
beneath locals and binders. The successful value-type hash comparison supplies
the domain agreement needed to substitute both the body's typing derivation
and its inferred-type origin. This retains all subsequent beta origins, including
a lambda introduced by replacing the let variable. The actual final cheap-beta
choice determines the returned type. Declaration admission includes these let
bodies using the same validation and inference calls. The three child checks
remain in the existing recursive synthesis fragment; arbitrary recursive let
composition and automatic construction of its finite resources remain open.
Structural local-state preservation now covers the complete recursive checker
on both success and failure. The actual loader and initial state establish
coherent lookup and a bound on allocated identifiers. Recursive calls retain
that bound, and scope cleanup restores all incoming declarations and lookups.
The model reader transports through this observable restoration. Let inference
therefore derives its fresh identifier and intermediate contexts from execution,
using one initial invariant instead of separate freshness and context premises.
The same derived context transport now serves forall, lambda, and application
inference, including the Pi-exposure call before an argument check. Their
traces retain the initial structural invariant; binder and synthesis nodes
derive freshness instead of storing a separate proof. Retained beta origins
and inference-cache histories use that same transport. General construction
of these traces from accepted execution remains open.
This closes the structural local-state component; general semantic state,
reduction, conversion, and cache preservation remain separate obligations.
Safe definition admission also rejects circular justification in both Lean and
Rust, including `theorem loop : P := loop` with only `P : Prop` assumed. The
production dependency walk returns an order with a proved decreasing rank;
finite collision freedom ensures its memoized collector includes every syntax
reference. Successful validation exposes that order to the model-reference
proof. Constructing interpretations for all coordinated declarations remains
part of the full checker refinement. Safe source recursion is elaborated into
recursor applications and remains supported; the rejected cycles refer directly
to global declaration addresses. A cached block verdict additionally needs
provenance from a completed check of the same declarations. Replacing a checked
declaration in internal state while retaining its cached verdict bypasses a new
body check, so the general proof must establish immutable loading and cache
validity from the actual fresh-state execution.
Constant cache hits derive the same typing from concrete agreement with pure
universe substitution of a loaded declaration; sort hits use the canonical
successor sort. Sort and already-loaded constant inference preserve agreement
at their cache key and retain other entries. Structural preservation composes
through binder opening, interning, unrelated writes, and scope/policy cleanup,
including errors. It transports closed constant witnesses, and maintained
agreement constructs sort leaves. A finite operational trace now carries
preservation through recursive applications, dependent types, and full-mode
lambdas for keys absent from the recorded writes. It derives later constant
witnesses and sort leaves without repeated cache-hit observations. Frames allow
reuse of composite synthesis checks as well: a successful full call supplies
the exact cached result, and a later hit retains its original inference tree.
The same tree supplies the lambda domains, dependent codomain checks, and
body checks required by subsequent beta reductions. Those checks now survive
interface growth and insertion of locals, including shifts of captured variables
beneath dependent binders. Retained Pi checks preserve both their domain and
codomain checks. Full-cache priority permits either later checking policy and
requires no recursion fuel. Cache frames derive
reuse across supported recursive inference, including beta Pi exposure and
changed cheap-beta lambda bodies; public beta WHNF preserves all inference
entries. A concrete retained cache resource derives its result reading from
full inference and constructs the transported hit in the original synthesis
recursion. Initially populated full keys survive supported recursive calls by
cache priority, without a write-exclusion premise. An exact event fold now
reconstructs both complete inference maps from actual child and parent calls.
Histories begin empty and retain the producing call at every present key through
inference, policy changes, scopes, verified loading on both outcomes, and clearing.
The original rich synthesis tree supplies all full-publication checks; the older
checking-only wrappers need supplementary annotations for omitted child calls.
Finite collision data over the query and historical inputs recovers the original
source. Selection then derives its cached result reading and complete retained
check, including the original local context and later interface transport.
The raw execution history also covers full-mode lets, with all three child
calls before the parent publication. Their original let check and child cache
data derive both entire maps and the history. Retaining a let root in the typed
synthesis history still requires its integration into the recursive checking
datatype.
Arbitrary execution construction, compatibility with later contexts after scope
exit, and the other inference and conversion/cache paths remain open. Frames
allow new declarations while retaining old ones.
The actual verified loader preserves
inference caches on success and failure, including partial intern progress and
deduplicated faults. This covers standalone and mutual-block loading. Block
publication requires every prepared entry to agree with any old declaration at
its key, admitting fresh entries and exact repeats in a partially loaded block.
Recursive constant leaves use this result, so an earlier witness survives
inference that loads another dependency. Key coherence of the intern tables
is now derived through every production conversion form and the actual loader,
including errors. Conversion uses bounds computed from source syntax and
rejects exhausted cyclic sharing with coherent partial state. Constant inference
carries pre-call coherence through lookup, substitution, and cache publication.
For a fixed source, a finite check establishes disjoint ownership of projection
keys and separates them from standalones. Conversion follows this source key
inventory, and publication records each owning block. The invariant that loaded
projections have recorded blocks starts empty and survives actual lookup on
both outcomes and successful constant inference. Unrecorded blocks then have
fresh entries, discharging per-block overlap checks for this path. General
partially loaded states retain the pointwise compatibility interface. The source
check supplies address ownership, without establishing semantic admission.
`OwnedInferenceTrace` carries this ownership invariant and intern coherence
through successful applications, dependent functions, and full-mode lambdas.
One initial state resource supplies every recursive boundary and post-lookup
table; finite collision, construction, and size data remain explicit for the
actual substitution, opening, and closing walkers. The result preserves earlier
cache witnesses outside its computed writes and supplies the state resource
for a later constant call, including another block load.
Source-only conversion now predicts complete standalone declarations, with
finite inventories of the proposed intern nodes. Correspondence with actual
conversion is proved under collision freedom on the initial table and these
candidates, including errors. Agreement of loaded standalones with this source
catalog starts empty and survives lookup on both outcomes and successful
supported recursive inference. Source ownership protects these entries from
block publication. A static binding reads a predicted declaration's type in
an admitted model entry; actual constant lookup derives its type reading,
arity, and coherence. Thus this path needs no new post-load reading witness.
For a finite catalog of closed sorts and standalone constant instances,
execution histories now establish both inference partitions' agreement and
loaded-declaration coverage from empty caches. Recursive calls preserve these
entries even at written keys; finite collision domains separate other input
forms. Lookup errors, policy changes, binder scopes, and cache clearing retain
the invariant. Actual selection then constructs the constant and sort inference
interfaces, and constant typing follows from the source binding and history.
The static bindings still select already admitted entries. General declaration
admission, mutual-member interpretations, semantic cache invariants beyond this
catalog, finite collision/level resources, and automatic trace construction
remain obligations.
Full checker consistency
and compiler/backend refinement remain open.

`Ix.Theory.Named` retains the local name-indexed specification and proof
support needed by the existing kernel and compiler verification. It shares
`Ix.Theory.VLevel`; its expression calculus remains separate from the store
references and annotated semantics of the set model. The `IxTheory` build and
foundation import graph exclude this auxiliary development.

The foundation audit freezes 145 named roots, their types and dependencies,
the fields of the set-theory assumption, and the compiler-generated recursion
workers. It rejects proof holes and unapproved axioms, native implementations,
and mathematical imports from the checker, compiler, test harnesses, or older
metatheory. Its exact report is `Tests/Theory/certified-foundation.txt`.
The axiom checks read checked declaration types, bodies, and constructor fields
directly, including the full graph of every declaration in the mathematical
import boundary.

## Provenance and scope

The port contains 120 selected source modules and a certified umbrella, from
the Lean4Ix working tree on 2026-09-11,
based on commit `ab42e79e2a4e2615a3ca6ef983d510f374057a38`. The new model included
uncommitted files, so that revision alone is insufficient to identify the
input. `Tests/Theory/ImportManifest.lean` records each selected source path and
SHA-256. Namespace changes move `Lean4Ix` to `Ix.Theory` and flatten the former
`Lean4Ix.Theory` syntax helpers.

The import includes the exact dependencies of the certified interface and
certificate builders. The old full theory umbrella, generators, conjecture
frontier, and harness are excluded. Matching model tests live in `Tests/Theory`.
Tests that formerly invoked the old generators use frozen constructor and
recursor data extracted from their upstream compiled test fixtures.

The model's 20 con-leche foundation files derive from revision
`86cd20a65660d757cedc81561a44579099b565d0`. Their upstream and intermediate hashes,
ported content hashes, and notices are retained and checked. Imported license
and notice texts are under `Ix/Theory`; `PORTING.md` explains their scope.

The exact report records each root's checked type, axioms, and dependencies.
For example, `Modeled.CheckedCompanions.fixed_old` and
`Modeled.assignment_agrees` use `propext`, `Classical.choice`, and `Quot.sound`.
