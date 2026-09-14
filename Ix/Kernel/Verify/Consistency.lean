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
import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Consistency.BinderOpening
import Ix.Kernel.Verify.Consistency.LocalOpening
import Ix.Kernel.Verify.Consistency.LocalSubstitution
import Ix.Kernel.Verify.Consistency.LetInference
import Ix.Kernel.Verify.Consistency.Application
import Ix.Kernel.Verify.Consistency.BinderInference
import Ix.Kernel.Verify.Consistency.RecursiveCache
import Ix.Kernel.Verify.Consistency.CacheInvariant
import Ix.Kernel.Verify.Consistency.CacheLifecycle
import Ix.Kernel.Verify.Consistency.InternInvariant
import Ix.Kernel.Verify.Consistency.StringExpansion
import Ix.Kernel.Verify.Consistency.DefinitionOrder
import Ix.Kernel.Verify.Consistency.Production
import Ix.Kernel.Verify.Consistency.Environment
import Ix.Kernel.Verify.Consistency.Audit

/-!
# Refinement into the set-theoretic consistency model

This library connects production kernel operations to `Ix.Theory`. Each
transport keeps its representation, arithmetic, and dependency assumptions
explicit. A production `checkEnvAnon` fragment preserves models of its
axiom set for monomorphic aliases, closed sorts, monomorphic specializations of
polymorphic constants, and closed function bodies built from sorts, locals,
polymorphic references, applications, dependent functions, and full-mode lambdas
under the stated execution resources.
Constant inference supports arbitrary readable entry types, using the actual
universe-instantiation walker and explicit lookup and finite-support resources.
The returned type's scope and references justify declaration admission.
The binder case also requires explicit syntactic scope and references to the
preceding interface. Its separate declared-type inference turns semantic checking
into typing. Local cache hits agree with the actual declaration type. Constant
hits agree with pure universe substitution of a loaded, admitted declaration;
sort hits return the canonical successor sort. Application, forall, and lambda
nodes retain misses in every eligible cache partition. Full mode leaves the
inference-only partition unconstrained at a miss.
Applications use syntactic Pi exposure, full argument checking, hash conversion,
and arguments without eager-reduction markers. Constant- and local-headed spines
derive type validity from the admitted model or local context; their arguments may be lambdas.
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
Initial agreement, finite execution resources, trace construction, lazy loading,
and preservation for keys inside the footprint remain explicit obligations.

The general reading now includes lets and strings. Binder opening, abstraction,
term substitution and universe substitution cover their nested occurrences.
String expansion follows the actual production intern sequence and preserves
the reading and table coherence under one finite allocation-pool condition.
The complete inference-cache invariant gives a fact for every entry in both
partitions. Writes, hits, initialization, clearing, scope/policy cleanup and
error isolation preserve these facts. Its parameterized entry meaning and
uncached-body preservation contract remain to be instantiated by the general
mutual semantic proof. General checker soundness remains outside this fragment.

Value-aware local readings additionally record a let's stored value in the
same model context. Successful production opening preserves these readings,
local lookup completeness, the allocation-counter bound and intern coherence;
let-bound free-variable reduction preserves the model value. Regular binders
lift the earlier readings into the extended model context. The scoped reader
is recovered by mapping every local to its variable index. Actual abstraction
followed by substitution closes a let body's inferred type with the same
reading and preserves intern coherence; its residual abstraction is derived
from the body reading. The let value's typing, cheap beta and general
reduction and inference, legacy local frames and the semantic cache invariant
remain obligations of the mutual execution proof.
Successful let inference yields its full operational trace in both policies,
including computed sort exposure and conversion. This trace transports the
recursive body's typing to the original let and its substituted type before
the final cheap-beta pass.

The safe-definition guard excludes self-reference for both modes and arbitrary
universe arities. Successful definition-block execution computes an order of
all loaded safe members and implies a well-founded internal dependency relation.
External dependency admission and the meaning of cached block successes remain
obligations of the general environment proof.
-/
