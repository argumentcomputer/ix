# Ix.Tc context-digest collision boundary

Snapshot: 2026-07-28. This note records a proof boundary for the K1/K2 cache
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

## Consequence for cache soundness

A cache value written while the ghost context is `Delta` can be read by an
execution represented by `Delta'` when both executions emit the same context
digest. `RunSupport.CollisionFree` alone does not justify transporting the
cached typing, WHNF, or definitional-equality judgment between those contexts.

The current formalization keeps this obligation visible in
`KernelSuffixModel.whnfTransport`, `inferTransport`, and `defEqTransport`.
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
  three semantic judgment families; and
- `ScopedKernelSuffixModel.finiteOperational` composes those facts into the
  joint WHNF/inference/DefEq model for captured states.

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
   `InferMeaning`, and `DefEqMeaning`, thereby constructing the three
   `KernelSuffixModel` transports.

Review rule: a proof that transports semantics across different requested
`lbr` values, or derives same-context-digest semantic transport from
expression-address collision freedom alone, is unsound. The radius index and
both collision layers must remain separately named in theorem statements and
trust reports.
