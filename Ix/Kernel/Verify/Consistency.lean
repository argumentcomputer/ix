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
import Ix.Kernel.Verify.Consistency.ConstantCache
import Ix.Kernel.Verify.Consistency.LazyCache
import Ix.Kernel.Verify.Consistency.BlockCache
import Ix.Kernel.Verify.Consistency.IngressCoherence
import Ix.Kernel.Verify.Consistency.BlockOwnership
import Ix.Kernel.Verify.Consistency.SourceOwnershipCheck
import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Consistency.BinderOpening
import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.Formation
import Ix.Kernel.Verify.Consistency.SynthesisInference
import Ix.Kernel.Verify.Consistency.BetaSubstitution
import Ix.Kernel.Verify.Consistency.Beta
import Ix.Kernel.Verify.Consistency.Simultaneous
import Ix.Kernel.Verify.Consistency.SpineReading
import Ix.Kernel.Verify.Consistency.CheapBetaReading
import Ix.Kernel.Verify.Consistency.BetaSpine
import Ix.Kernel.Verify.Consistency.CheapBeta
import Ix.Kernel.Verify.Consistency.Validation
import Ix.Kernel.Verify.Consistency.RecursiveCache
import Ix.Kernel.Verify.Consistency.RecursiveState
import Ix.Kernel.Verify.Consistency.ConversionRecipe
import Ix.Kernel.Verify.Consistency.SourceAgreement
import Ix.Kernel.Verify.Consistency.SourceCache
import Ix.Kernel.Verify.Consistency.Production
import Ix.Kernel.Verify.Consistency.Dependencies
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.Audit

/-!
# Refinement into the set-theoretic consistency model

This library connects production kernel operations to `Ix.Theory`. Each
transport keeps its representation, arithmetic, and dependency assumptions
explicit. A production `checkEnvAnon` fragment preserves models of its
axiom set for aliases, universe terms, instances of earlier constants, and
closed function bodies built from sorts, locals,
polymorphic references, applications, dependent functions, and full-mode lambdas
under the stated execution resources. Definitions may declare their own
universe parameters; model entries retain the exact arity and interpretations
at every instance.
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
intern table. Automatic origin construction for arbitrary generated types
and general reduction remains open.
Local cache hits agree with the actual declaration type. Constant
hits agree with pure universe substitution of a loaded, admitted declaration;
sort hits return the canonical successor sort. Application, forall, and lambda
nodes retain misses in every eligible cache partition. Full mode leaves the
inference-only partition unconstrained at a miss.
Applications use syntactic Pi exposure, full argument checking, hash conversion,
and arguments without eager-reduction markers. Constant- and local-headed spines
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
General checker soundness remains outside this fragment.
-/
