# Ix.Tc context-digest collision boundary

Snapshot: 2026-07-31. This note records a proof boundary for the K1/K2 cache
soundness argument.

## Two distinct collision obligations

Run-scoped expression collision freedom controls addresses of expressions in
the finite `RunSupport`. Schematically, it lets a proof recover the supported
expression represented by an expression-address component:

```text
e, e' in S and e.addr = e'.addr  ->  e and e' are the same source
```

The context component of an inference, DefEq, or open-WHNF key is different.
`ctxAddrForLbr` emits a composite Blake3 digest for a local-context suffix.
Injectivity of every expression-address ingredient does not establish
injectivity of the digest that combines those ingredients:

```text
ctxDigest(lbr, Delta) = ctxDigest(lbr, Delta')  -/->  Delta = Delta'
```

The outer hash can collide on two different sequences even when all of their
individual expression addresses are distinct and collision-free. Moreover, a
fixed-width digest cannot be globally injective over an unbounded context
domain. Cryptographic collision resistance is not mathematical injectivity.

The requested `lbr` is also a semantic input and must not be erased from the
representation relation. In particular, production `ctxAddrForLbr 0` emits
`emptyCtxAddr` regardless of the surrounding concrete context. If a relation
forgets which `lbr` was requested, that one digest can spuriously represent
arbitrary-radius suffixes without requiring a Blake3 collision at all. The
current `WhnfContextKeys.Represents` relation therefore retains `lbr`: WHNF
and inference use the source expression's `lbr`, and DefEq uses the maximum of
its two operands' `lbr` values.

## Equivalence-root cache probes

DefEq's union-find second chance replaces each original expression address by
a component representative and probes the ordinary DefEq cache with those
root addresses. A representative retains the comparison's requested radius,
but the expression named by that representative can have a smaller intrinsic
`lbr`. Consequently, reusing the original context digest for the root pair is
not justified merely because both roots remain in the same union-find scope:

```text
max(a.lbr, b.lbr) = r  does not imply
max(root(a).lbr, root(b).lbr) = r
```

`EqKey` therefore stores both values separately: `lbr` is the requested
context-suffix radius and `exprLbr` is the intrinsic radius of the expression
address. `EqKey.rootCacheScopeMatches` permits a root-derived probe only when
both representatives retain the exact context digest and requested radius,
and `max rootA.exprLbr rootB.exprLbr` reconstructs that radius. The Rust
kernel mirrors this as `EqKey::root_cache_scope_matches`.

The formal acceptance proof does not interpret a root address by itself.
Each verified union-find path supplies a supported endpoint expression and
its intrinsic-radius equality; the guarded cache entry supplies equality of
the two endpoints; the result composes original-left to left-root, root pair,
and right-root back to original-right. A failed guard simply disables the
optimization and continues through the ordinary DefEq path.

## Consequence for cache soundness

A cache value written while the ghost context is `Delta` can be read by an
execution represented by `Delta'` when both executions emit the same context
digest. `RunSupport.CollisionFree` alone does not justify transporting the
cached typing, WHNF, or definitional-equality judgment between those contexts.

The current formalization keeps this obligation visible in
`KernelSuffixModel.whnfTransport`, `inferTransport`, `defEqTransport`, and
`isPropTransport`.
`operationalWhnfContextKeys` proves that represented keys came from real,
reconciled `ctxAddrForLbr` executions with the same requested `lbr`; it
deliberately does not claim that an equal emitted digest makes their contexts
equal.

The finite construction is now explicit in the proof API:

- `ContextDigestSpec` names the normalized input and a state-validity
  predicate for context-id/memo coherence, exposes concrete current-context
  memo validity, requires validity preservation, and requires every real
  `ctxAddrForLbr` execution from a valid state to return its digest;
- `ContextDigestScope` stores a constructive finite input list and keeps run
  capture separate from composite-digest collision freedom;
- `ContextSuffixSemantics` states that equal normalized inputs preserve the
  four semantic judgment families (WHNF, inference, DefEq, and the auxiliary
  proposition classifier); and
- `ScopedKernelSuffixModel.finiteOperational` composes those facts into the
  joint WHNF/inference/DefEq/proposition-classifier model for captured states.

The existing `KernelSuffixModel` quantifies over every reconciled checker
state, which is stronger than a finite run claim. Converting the scoped model
to that universal interface therefore requires an explicit proof that every
such state is captured. A finite execution trace cannot discharge that proof
by itself; downstream method closure must retain the state-domain index or
establish a genuinely global specification.

The `ContextDigestSpec.execution` premise includes memo hits and requires
`ContextDigestSpec.StateValid` for the pre-state. This is
load-bearing: a successful lookup in `ctxAddrCache` is not evidence that the
cached address is the digest of the current normalized suffix. Concrete K2
must define that validity predicate from execution history or a strengthened
state invariant. The interface now requires both `memoValid` and `preserves`,
so an implementation cannot label an initial state valid while leaving later
memoized calls outside the proof domain.

Production now exposes the pure calculation as
`TcM.ctxAddrForLbrUncached`. The exact fast-path, cache-hit, and cache-miss
equations prove immediate replay stability and preservation of
`TcM.ContextAddrMemoValid`. This closes the operational memo-mutation part of
K2; it does not yet prove that the pure hash input is the chosen semantic
normalization of the reconciled `KVLCtx`.

## Required K2 discharge

Instantiating the finite construction for production must:

1. define the finite set of `(lbr, serialized relevant suffix)` composite
   context-digest inputs reachable during the verified run;
2. connect `ctxAddrForLbrUncached` to that normalized semantic input and prove
   the non-memo portion of `ContextDigestSpec.StateValid`;
3. prove that every represented production key execution lies in that set;
4. consume an explicit collision-freedom hypothesis for the composite digest
   on that set, yielding the required context or suffix equivalence; and
5. prove declaratively that this equivalence preserves `WhnfMeaning`,
   `InferMeaning`, `DefEqMeaning`, and `IsPropMeaning`, thereby constructing
   the four `KernelSuffixModel` transports.

Review rule: a proof that transports semantics across different requested
`lbr` values, or derives same-context-digest semantic transport from
expression-address collision freedom alone, is unsound. The radius index and
both collision layers must remain separately named in theorem statements and
trust reports.
