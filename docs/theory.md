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
parameters. The lambda closes the reduced type using the actual final intern
table. Reduction remains bounded by the original checked lambda prefix.
Automatic origin construction for arbitrary generated types, general
reduction, and conversion remain open.
Safe definition admission also rejects circular justification in both Lean and
Rust, including `theorem loop : P := loop` with only `P : Prop` assumed. The
production dependency walk returns an order with a proved decreasing rank;
finite collision freedom ensures its memoized collector includes every syntax
reference. Successful validation exposes that order to the model-reference
proof. Constructing interpretations for all coordinated declarations remains
part of the full checker refinement.
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
new declarations while retaining old ones. The actual verified loader preserves
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
