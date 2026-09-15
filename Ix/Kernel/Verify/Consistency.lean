/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Level
import Ix.Kernel.Verify.Consistency.Expr
import Ix.Kernel.Verify.Consistency.Judgment
import Ix.Kernel.Verify.Consistency.Infer
import Ix.Kernel.Verify.Consistency.InstUniv
import Ix.Kernel.Verify.Consistency.Constant
import Ix.Kernel.Verify.Consistency.Atomic
import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Verify.Consistency.ScopedInstUniv
import Ix.Kernel.Verify.Consistency.ScopedConstant
import Ix.Kernel.Verify.Consistency.InferenceCache
import Ix.Kernel.Verify.Consistency.SortCache
import Ix.Kernel.Verify.Consistency.Literals
import Ix.Kernel.Verify.Consistency.Resolution
import Ix.Kernel.Verify.Consistency.Quotient
import Ix.Kernel.Verify.Consistency.ConstantCache
import Ix.Kernel.Verify.Consistency.LazyCache
import Ix.Kernel.Verify.Consistency.BlockCache
import Ix.Kernel.Verify.Consistency.IngressCoherence
import Ix.Kernel.Verify.Consistency.BlockOwnership
import Ix.Kernel.Verify.Consistency.SourceOwnershipCheck
import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Consistency.BinderOpening
import Ix.Kernel.Verify.Consistency.LetOpening
import Ix.Kernel.Verify.Consistency.LetInference
import Ix.Kernel.Verify.Consistency.LetSynthesis
import Ix.Kernel.Verify.Consistency.LetCache
import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.ApplicationWhnf
import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.Formation
import Ix.Kernel.Verify.Consistency.ContextInsertion
import Ix.Kernel.Verify.Consistency.ContextTransport
import Ix.Kernel.Verify.Consistency.SynthesisInference
import Ix.Kernel.Verify.Consistency.SynthesisCache
import Ix.Kernel.Verify.Consistency.SynthesisCacheHistory
import Ix.Kernel.Verify.Consistency.SynthesisCacheExecution
import Ix.Kernel.Verify.Consistency.BetaSubstitution
import Ix.Kernel.Verify.Consistency.Beta
import Ix.Kernel.Verify.Consistency.Simultaneous
import Ix.Kernel.Verify.Consistency.SpineReading
import Ix.Kernel.Verify.Consistency.CheapBetaReading
import Ix.Kernel.Verify.Consistency.BetaSpine
import Ix.Kernel.Verify.Consistency.BetaTrace
import Ix.Kernel.Verify.Consistency.BetaWhnf
import Ix.Kernel.Verify.Consistency.StructuralWhnfEntry
import Ix.Kernel.Verify.Consistency.LetWhnfPlan
import Ix.Kernel.Verify.Consistency.BetaWhnfPlan
import Ix.Kernel.Verify.Consistency.BetaHeadStepPlan
import Ix.Kernel.Verify.Consistency.BetaHeadConstruction
import Ix.Kernel.Verify.Consistency.BetaReannotation
import Ix.Kernel.Verify.Consistency.BetaHeadOrigin
import Ix.Kernel.Verify.Consistency.BetaCacheReannotation
import Ix.Kernel.Verify.Consistency.BetaCacheEvent
import Ix.Kernel.Verify.Consistency.BetaCachePublications
import Ix.Kernel.Verify.Consistency.BetaCacheHistory
import Ix.Kernel.Verify.Consistency.BetaHistorySource
import Ix.Kernel.Verify.Consistency.BetaHistoryInference
import Ix.Kernel.Verify.Consistency.BetaHistoryState
import Ix.Kernel.Verify.Consistency.InferenceWhnfHistory
import Ix.Kernel.Verify.Consistency.SynthesisCoherence
import Ix.Kernel.Verify.Consistency.SynthesisAppCongruence
import Ix.Kernel.Verify.Consistency.BetaPublicWhnf
import Ix.Kernel.Verify.Consistency.WhnfCacheFrame
import Ix.Kernel.Verify.Consistency.BetaTyping
import Ix.Kernel.Verify.Consistency.BetaInference
import Ix.Kernel.Verify.Consistency.BetaWhnfInference
import Ix.Kernel.Verify.Consistency.BetaSourceInference
import Ix.Kernel.Verify.Consistency.BetaExposureConstruction
import Ix.Kernel.Verify.Consistency.SortInference
import Ix.Kernel.Verify.Consistency.CheapBeta
import Ix.Kernel.Verify.Consistency.Validation
import Ix.Kernel.Verify.Consistency.RecursiveCache
import Ix.Kernel.Verify.Consistency.CacheExecution
import Ix.Kernel.Verify.Consistency.CacheHistory
import Ix.Kernel.Verify.Consistency.RecursiveState
import Ix.Kernel.Verify.Consistency.ConversionRecipe
import Ix.Kernel.Verify.Consistency.SourceAgreement
import Ix.Kernel.Verify.Consistency.SourceCache
import Ix.Kernel.Verify.Consistency.Production
import Ix.Kernel.Verify.Consistency.Dependencies
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.RunAssumptions
import Ix.Kernel.Verify.Consistency.Invariant
import Ix.Kernel.Verify.Consistency.Contracts
import Ix.Kernel.Verify.Consistency.DefEqMemo
import Ix.Kernel.Verify.Consistency.DefEqQuick
import Ix.Kernel.Verify.Consistency.DefEqTiers
import Ix.Kernel.Verify.Consistency.CheckedTyping
import Ix.Kernel.Verify.Consistency.WhnfGeneric
import Ix.Kernel.Verify.Consistency.WhnfLayers
import Ix.Kernel.Verify.Consistency.WhnfSteps
import Ix.Kernel.Verify.Consistency.DefEqReducing
import Ix.Kernel.Verify.Consistency.DefEqFinal
import Ix.Kernel.Verify.Consistency.DefEqLazyDelta
import Ix.Kernel.Verify.Consistency.Inductive.Shape
import Ix.Kernel.Verify.Consistency.Inductive.Block
import Ix.Kernel.Verify.Consistency.Inductive.Recursor
import Ix.Kernel.Verify.Consistency.Inductive.Formation
import Ix.Kernel.Verify.Consistency.Inductive.Admission
import Ix.Kernel.Verify.Consistency.Inductive.Run
import Ix.Kernel.Verify.Consistency.Audit

/-!
# Refinement into the set-theoretic consistency model

This library connects production kernel operations to `Ix.Theory`. Each
transport keeps its representation, arithmetic, and dependency assumptions
explicit. A production `checkEnvAnon` fragment preserves models of its
axiom set for aliases, universe terms, instances of earlier constants, and
closed function bodies built from sorts, locals,
polymorphic references, applications, dependent functions, full-mode lambdas, and lets
under the stated execution resources. Definitions may declare their own
universe parameters; model entries retain the exact arity and interpretations
at every instance.
Recursive forall, lambda, and let rules also expose sorts through the supported
public beta WHNF path, including hits at any of its three cache layers. Successful production calls
determine their raw child traces. Retained checks justify conversion from the
original inferred type to the exposed sort and supply the binder's level.
Source derivations and typed cache histories retain the original child check;
sort exposure leaves both inference-cache maps unchanged. General construction
of the finite representation and reduction resources remains open.
Safe definition admission now checks its reachable definition dependencies.
The actual traversal has proved root coverage and an order with a decreasing
natural-number rank. Finite collision freedom justifies complete reference
collection through syntax sharing, binders, and lets. Successful validation
exposes this order to the model-reference proof. Both production checkers
reject circular safe definitions; general body typing and model construction
for the ordered declarations remain separate obligations.
Constant inference supports arbitrary readable entry types, using the actual
universe-instantiation walker and explicit lookup and finite-support resources.
The returned type's scope and references justify declaration admission.
The binder case retains references to the preceding interface. Actual production
validation and the closed scoped reading derive source scope from finite
validation coverage and collision freedom. Auxiliary condition bounds remain
a separate syntax check. Declared-type inference from that same execution can
turn semantic checking into typing. Synthesis inference also derives formation
of its generated result type from actual binder-domain and earlier declaration
type checks. An inhabited product supplies a uniform codomain bound at an
application, preserving the exact Prop condition. Direct lambda applications
therefore synthesize full typing without an extra codomain inference call.
Earlier type checks remain reusable after interface growth and universe
instantiation. Source beta spines retain every original checked lambda
domain. Simultaneous substitution and the actual multi-argument WHNF step
preserve typing and denotation under finite walker resources, including the
remaining application suffix. The substitution bounds concern the original
body and arguments. Selected cheap-beta plans have the same typed meaning
when an actual source check is available. Definition admission can reuse its
executed declared-type inference to justify a beta-prefix conversion to the
value's inferred type. These paths are included in environment model
preservation. Recursive lambda inference also handles changed cheap beta
when the returned body type retains its actual checking origin. The proof
preserves checked lambda domains during the same inference recursion, reads
the selected prefix from the actual generated type, and transports the
original check through interface growth, local weakening, and universe
instantiation. Earlier local contexts are reconstructed from their executed
domain checks. Codomain origins are extracted from earlier function-type
trees, and actual function/argument calls justify term substitution through
them. The context relation updates later dependent parameters at any cutoff;
the original beta prefix is preserved by the same substitution. Variable-headed
codomains retain their actual argument checks and local types, extracted
through nested function-type calls. Substituting a lambda for that head now
uses the argument's own checked prefix to justify the newly exposed beta
steps. Earlier parameter substitutions update the retained head type and
argument checks; later arguments continue transporting the reduction.
The supplied argument may itself be a lambda application: its existing
argument checks are lifted beneath the retained parameters and joined to
the original codomain's checks in application order. The actual selected
prefix can consume arguments from both origins. These
origins are proved sound in the inference recursion and consumed by the
lambda case. Abstraction uses the reduced type and the reduction's final
intern table. A lambda body that applies its parameter also retains its
actual argument checks, even when cheap beta changes the body's inferred
type. Its first beta result supplies typing at the current type; substituting
the supplied lambda supplies the next checked prefix. Two successive
prefixes therefore compose without inference of the intermediate term.
Retained origins justify the actual multi-argument WHNF step, and declaration
admission includes this two-prefix conversion. Finite beta traces compose
any number of retained prefixes. An earlier result can supply a later lambda
or argument origin, and type transport preserves the original source type.
Application suffixes and dependent substitutions retain their checks.
The corresponding structural-WHNF trace computes each raw result and intern
table, then proves the actual uncached loop under its fuel bound. The same
traces justify definition conversion. Source inference now constructs a full
beta typing derivation retaining every lambda body, application child, and
checked function-type domain and codomain.
Dependent substitution rebuilds that derivation beneath retained binders,
so each generated result supplies the exact lambda domains for the next step.
Forward beta conversion preserves these domains when cheap beta changes a
lambda body's inferred type. Every finite head-beta path of the currently
supported inference fragment therefore derives all its semantic step origins
from the original check. The operational path contains only raw execution,
reading, and finite representation resources, and its automatic annotation
also supplies declaration admission. Public WHNF now computes the key states,
instrumentation, shared-fuel charge, and guarded cache insertions for these
beta paths ending at a sort, Pi, or lambda. Each of the three cache layers
may retain a prior executed result. Native reduction suppresses new writes
at the no-delta and outer layers; the structural layer still publishes.
Replay derives the next hit from that publication and preserves memoized
context keys. Successful beta calls now reconstruct their raw paths from
the original source reading and finite arithmetic and hash resources. The
actual run supplies the intermediate steps, iteration bound, cache choices,
fuel charge, and final state. Cached entries retain their producing executions.
Explicit-let substitution now composes with these beta steps in the same
trace and cache executions. It preserves the scoped reading and the original
annotated term, so later beta steps retain their existing typing derivation.
This also covers let-based Pi/sort exposure and declaration conversion.
Recursive application heads now use the same trace, with separate method
depth and loop bounds and actual full/cheap cache writes or retained hits.
Source reconstruction includes explicit-let heads returning lambdas, including
nested fresh and cached head calls. Retained producers are reannotated from
the current reading, even across different resolvers and local contexts,
while preserving the actual result, state, fuel, and iteration count. The
same reconstruction applies at all three cache layers, and publication
derives resources for later replay. The original typing derivation supplies
the head conversion while preserving every checked argument. Key frames
preserve all queries when a recursive call memoizes a different legacy context radius.
Complete WHNF histories now retain every actual publication and reconstruct
all five maps, including recursive head writes. Hits preserve the history;
native guards suppress the same upper writes as production. Binder/let
opening and scope cleanup retain entries from exited scopes. Loop exhaustion
keeps the completed prefix's publications, and clearing begins an empty
history. Finite collision data identifies the queried source among the
recorded inputs. The resulting provenance supplies all three cache layers'
origin resources, including public replay of zero-depth head producers.
Successful source reconstruction, Pi/sort exposure, and semantic public
reduction preserve the updated history for later calls. Verified standalone
and block loading preserve all five WHNF maps, every supported inference
node carries the complete WHNF history through its actual intermediate
states, and each returned state retains intern-table coherence.
Only an outer miss charges shared fuel. Pi exposure uses the
same complete cache-layer execution. Application inference
uses that exposure between argument checks and derives the type conversion
from a retained actual check of the function type. Dependent codomain
substitution and all later beta origins preserve those argument checks.
The original synthesis admission theorem includes this application case.
Constructing initial inference and operational resources for all accepted
programs, other WHNF branches, general semantic cache agreement, and conversion
remain open.
Full-mode let checks retain their original domain, value, and opened-body
synthesis checks. The scoped reader and actual opening, abstraction, and
substitution walkers interpret nested lets beneath locals and binders. Value
comparison identifies the declared domain; substitution preserves the complete
body checking derivation and inferred-type origin, including beta redexes
exposed by the value. The selected cheap-beta operation supplies the returned
type. Declaration admission consumes the same check and validation calls.
The original SynthesisInference datatype now includes this recursive let case,
so lets compose in its children and surrounding binders, applications, and
cache hits. Complete derivations retain function-type children after dependent
substitution exposes their constructor. Returned syntax readings are derived
before the synthesis semantic induction, without a context-formation premise.
The induction proves its own hereditary semantic invariant; source support and
reconstruction do not assume it, and the audit enforces that boundary.
Automatic construction of the initial execution and representation resources
remains open.
Local cache hits agree with the actual declaration type. Constant
hits agree with pure universe substitution of a loaded, admitted declaration;
sort hits return the canonical successor sort. Applications, foralls, lambdas,
and lets can reuse an earlier successful synthesis check. The cache node
retains its original inference tree, local reading, and execution, so lambda
domains and dependent codomain checks remain available to later beta proofs.
Successful full inference establishes the exact stored result; cache frames
derive its later selection under either checking policy, even with zero fuel.
The retained checks also cross interface growth and insertion of locals.
Complete derivations recover the lambda head, domain, body, and arguments
after lifting and substitution, preserving Pi codomain checks and hereditary
beta origins. A concrete full-cache resource derives its readings and
selection from the earlier call and remains usable in the original synthesis
recursion after actual binder opening and supported recursive inference.
Cold composite nodes still require misses in every eligible partition; full
mode leaves the inference-only partition unconstrained at a miss.
Applications use syntactic or supported beta Pi exposure, full argument checking,
hash comparison of the argument with the exposed domain, and arguments without
eager-reduction markers. Constant- and local-headed spines
can derive type validity from the admitted model or local context; their
arguments may be lambdas. The synthesis rules also allow lambdas and their
application results in function position, with derived formation bounds.
Polymorphic nodes use closed source readings, finite substitution resources,
and a pure prediction of the returned syntax with matching occurrence annotations.
Constant hits additionally check arity because they skip the runtime guard.
Concrete cache agreement is preserved by sort and already-loaded constant
inference. Cache frames compose through interning, key computation, binder
opening, unrelated writes, and scope/policy cleanup, including errors.
These frames transport closed constant witnesses; maintained agreement also
constructs sort leaves. A finite InferenceCacheTrace computes the keys written
by recursive applications, dependent functions, and full-mode lambdas, including
domain validation and outer cache writes. Successful inference preserves entries
outside that footprint, loaded declarations, and checking policy. This derives
later constant witnesses and sort leaves without new cache-hit observations.
The trace also covers beta Pi exposure and changed cheap-beta lambda bodies.
Public beta WHNF and Pi exposure preserve inference entries at every key;
their computed writes affect the WHNF caches. These frames also preserve the
earlier full composite checks. Every initially populated full key is outside
the writes by cache priority. An execution-ordered event fold reconstructs
both complete inference maps, including new entries. Histories start empty and
preserve the actual producing calls through inference, policy/scope changes,
verified loading on either outcome, and clearing. The original rich synthesis
trees supply their full-publication checks; older checking-only wrappers need
annotations for omitted child calls. Under finite query/history collision data,
selection recovers the original source and materializes its retained check in
its original context, including interface transport. Arbitrary execution and
resource construction, later context compatibility after scope exit, and
the other inference and conversion/cache paths remain open.
The operational cache trace includes full lets and their three child calls.
The original let check and child cache data derive the full event fold and raw
history, preserving initially populated full keys. The typed synthesis history
also retains let roots and descendants through their original recursive checks,
so later full-cache selection recovers those checks and their beta origins.
Frames allow declaration growth while retaining every old declaration. Verified
lazy loading derives such a frame on success and failure, including partial
conversion state and fault deduplication. Standalone and block preparation have
access only to intern tables; single-entry registration is fresh on an actual
lookup miss. Block publication requires each converted entry to agree with any
old declaration at its key. Fresh or partially loaded blocks meet this condition
through pointwise lookup checks; uniqueness among fresh keys is unnecessary.
Recursive constant leaves can use that loader and post-lookup walker resources,
so later closed witnesses survive inference that loads another dependency.
The production conversion loops have bounds derived from source syntax and
reject exhausted cyclic sharing while retaining partial intern state. Coherence
is proved through every conversion form and the actual loader on both outcomes.
Constant inference derives post-lookup coherence from its initial state and
returns coherence after substitution and cache publication, so the next call
can reuse it. Finite collision and level resources remain explicit.
For a fixed source, a finite header check establishes disjoint block ownership.
Actual conversion emits only the enumerated projection keys, and atomic
publication records their owner. The invariant that loaded projections have a
recorded block starts empty and survives lookup on both outcomes and successful
constant inference. It derives fresh entries for unrecorded blocks, so these
calls need no per-block overlap premise. Externally partially populated states
can still use the general compatibility resource.
An `OwnedInferenceTrace` now carries these ownership and coherence invariants
through recursive applications, dependent functions, and full-mode lambdas.
Its nodes contain finite walker data, while one initial state invariant supplies
every recursive boundary and post-lookup table. The resulting cache frame
transports earlier constant witnesses, supplies later sort coherence, and
returns the state resource for a subsequent constant that loads another block.
Source-only conversion recipes predict complete standalone declarations and
the finite intern candidates used to construct them. Under collision freedom
on the initial table and those candidates, actual conversion follows the
prediction on success and failure. Standalone source agreement starts empty,
survives verified lookup on both outcomes, and is preserved by supported
recursive inference. Source ownership protects its keys during block loads.
A static model binding reads the predicted type; actual constant lookup then
derives its type reading, arity, and coherence without post-load reading premises.
A finite catalog of closed sorts and source constant instances now establishes
both cache partitions' agreement and loaded-declaration coverage from the empty
state. Actual recursive inference preserves every catalog entry, including
writes at those keys. Finite input collision domains prevent other syntax
forms from writing them. Execution histories also include lookup errors,
policy changes, binder scopes, and cache clearing. Constant and sort leaves
derive their hit/miss interfaces from this invariant, and constant typing
follows from the source binding and history without fresh cache witnesses.
Model admission, mutual-member interpretations, general semantic cache
invariants, finite execution resources, and automatic trace construction remain
obligations.
One run-level record now collects the finite source check, hash verification,
and the collision and size resources over a run's finite syntax inventory. One
checker-state invariant bundles ownership, coherence, source and catalog
agreement, both cache histories, the local state and its reading, the
context's synthesis origin, and semantic agreement of the remaining reduction
memos. It holds at the driver's initial state, survives lookup on both
outcomes, key computation, binder and let opening, scope exit, cache clearing,
per-item reset, and policy changes, and sort and free-variable inference are
restated as its preservation. Re-expressing the other supported branches and
deriving the atomic run records from it remain open.
The soundness of reduction, conversion, and inference is stated as one mutual
contract per method table over that invariant, closed by induction on the
production method-table depth from the exhausted table and per-depth one-layer
obligations that remain open; the conversion hash path and sort inference are
instances.
Natural-number literals infer to the interned primitive `Nat` constant; a
static binding of that address to an admitted entry with a `natural` fact
types the literal in both cache partitions, through the synthesis, cache
trace, source-cache, and history recursions, and as invariant preservation.
Model references are derived from the source environment: the canonical map
`Ixon.Env.resolve` places standalones in their own one-member block and
projections at their block coordinates, agrees with the certified adapter, is
injective on standalone coordinates, enumerates exactly the driver's standalone
items under a finite materialization contract, derives both static bindings, and
restates the environment theorems with every reference at its canonical coordinate.
The non-reducing conversion tiers are proved under those contracts: positive
equivalence-manager and DefEq-cache answers certify chains of recorded
conversions, every memo update preserves the invariant, and the quick
structural tier composes universe equality and the common-local binder
comparison; the entry is assembled modulo the reducing tiers, the transport
of recorded chains to the caller's registration, the binder annotation
discipline, and hereditary typing of binder operands.
The WHNF bodies are proved against scope-generic reduction contracts over a
history-free reduction invariant with a checked (hereditary, canonical-atom)
typing premise: the five memo layers, the bounded loops, leaves, explicit and
local lets, multi-argument beta and head rebuilding after the recursive head
call, and delta unfolding through the unfold memo are closed by induction on
the method-table depth, and the projection, iota, literal, and quotient
reducers remain seams collected in one assumption record per depth.
discipline, and hereditary typing of binder operands. The reducing tiers after
the quick probe, from the eager `Bool.true` shortcut through the cheap passes,
proof irrelevance, the lazy-delta loop, and the final WHNF tier, are proved
modulo the reducer seams, which discharges that reducing-tail obligation.
The four canonical quotient constants are admitted through the guard sequence of
`checkQuot`: the canonical kernel types read as the certified quotient description, and
a fragment containing all four extends every model of an initial interface that
realizes the equality family, publishing the certified quotient entries and equations.
General checker soundness remains outside this fragment.
Singleton non-indexed inductive blocks are admitted through the certified
`Ordinary` witness: the stored family, constructors, and one-member recursor
block read to a certified shape by a decidable check, the retained closed type
checks of the block and recursor passes supply every formation fact, and the
remaining certified conditions (field universe bounds, later recursive
domains, singleton-proposition large elimination, and rule typing) are
collected in one seam record.
-/
