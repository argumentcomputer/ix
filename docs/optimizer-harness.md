# IxIR₁ optimizer harness

Status: scalar constructor-fetch forwarding joined the default O1 bundle on
2026-08-30. The checked HPT consumers propagate facts through complete stored
function bodies, prune impossible alternatives, collapse a certified detailed
unary case to one checked `fetch`, forward certified scalar fields after
allocation or successful reuse, and fuse adjacent PAP/application pairs. All
three consumers share one logical declaration rewrite and one content-address
rebuild.

The implementation is `Compilatrix/IxIR1/Optimizer.lean`, with compiler-facing
entry points `Pipeline.Artifact.optimizeWithProducedHPT` and
`optimizeWithCachedHPT`.

## Policy and fallback

`Optimizer.Policy` carries harness version 3, case-simplifier version 3,
fetch-forwarding version 1, and PAP-fusion version 1. The three passes have
independent enable bits and are enabled by default. The shared deterministic
bounds cover input instructions, canonical code bytes, and checked-certificate
bytes. The harness is disabled only when all three pass bits are false.

Fetch forwarding recognizes an `alloc` or `reuse` immediately followed by a
fetch of any field from its result. The selected constructor argument must be
HPT-proven scalar. The pass retains both binders and replaces the fetch with
`pure` of the source atom lifted across the constructor-result binder, so fuel,
stores, numeric locations, and cost counters are preserved exactly. Heap-valued
and out-of-range fields fail closed.

PAP fusion recognizes adjacent `papp`/`apply` binders and classifies their
combined arguments as under-, exactly-, or over-saturated. It retains both
binder slots, lowers supplied operands across the retired PAP slot, and rejects
the rewrite unless the continuation cannot mention that slot. Captures must be
HPT-proven scalar: IxIR₁ no longer carries function-parameter ownership modes,
so the local checker cannot soundly classify an arbitrary heap capture as
shared.

Every inferred-optimization failure is fail-soft. An unsupported version,
disabled pass, exhausted optimizer budget, or rejected content-address rebuild
returns the original graph and records a typed skip reason. These conditions
cannot reject an otherwise accepted compiler artifact. HPT production and
checking retain their own separately versioned structural limits.

## Observations

One `Observation` scans all stored function bodies plus the main and reports:

- artifact, mutual-block, function, and extern counts;
- `ret`, `letOp`, `case`, and alternative counts;
- alloc, reuse, free, RC increment/decrement, unique-drop, and fetch counts;
- direct call, self call, PAP allocation, dynamic apply, and extern-call
  counts;
- canonical code bytes; and
- stored ordinary/mutual artifact bytes.

`instructions` counts each `ret`, `letOp`, and `case` node once. These are
static compiler observations. Dynamic allocation, reclamation, RC, and live
heap counters remain in the IxIR₁ evaluator/cost model. Machine-dependent
wall time is deliberately absent from addressed reports.

## Identities and reports

The input and output graph roots use
`compilatrix/ixir1/optimizer-graph/1\0`. The preimage commits to artifact kind
and order, stable ABI address and declaration payload, ordinary declaration
address and payload, symbolic mutual-block payload, and exact main bytes.

Checked HPT certificate identity is the digest of its canonical cache-store
spelling; its exact framed byte count is reported separately. A pass report
contains the complete policy, typed disposition, input/output/certificate
roots, certificate size, before/after observations, case-pruning counters,
total forwarded fetches, total fused PAPs, under/exact/over fusion counters,
and a rebuild diagnostic only on fallback. Report schema 4 uses
`compilatrix/ixir1/optimizer-report/4\0`; pass behavior is versioned separately
inside the encoded policy.

This makes equality of reports executable byte equality rather than equality
of human-formatted text.

## Regression boundary

The compiled tests pin six properties:

1. two independent runs over the same checked input produce identical output
   roots, report bytes, and report addresses;
2. a non-degenerate whole-program case rewrite removes one impossible
   alternative through an intervening alias binding, eliminates the remaining
   unary case, materializes one checked fetch, shrinks canonical code bytes,
   readdresses the changed caller, rewrites the main edge, and preserves
   pipeline producer-to-target provenance;
3. disabled and one-below instruction-budget policies select the exact input
   root; and
4. after HPT is recomputed on the transformed root, the default shrinking pass
   reports `unchanged` and reproduces that root; and
5. the default PAP pass fuses under-, exact-, and over-saturation in one graph,
   reports each class, rejects non-scalar captures and binder-sensitive shapes,
   preserves the scalar result with an empty live heap, and reaches a fixed
   point after HPT recomputation; and
6. the default fetch pass forwards one allocation projection and one successful
   reuse projection, checks the lifted variable form, rejects heap-valued and
   out-of-range sources, preserves the exact result and all heap counters, and
   reaches a fixed point after HPT recomputation.

The production Ixon→IxIR₁ integration fixture separately exercises default
report generation and the disable path on compiler-emitted code. Default-pass
semantic authority comes from the checked whole-program history-refinement and
exact readdressing theorems documented in
[HPT certificates](hpt-certificates.md). `fusePair?_refines` proves each local
PAP decision; `FetchForward.runCode_forwardHead?_eq` proves literal evaluator
equality for each accepted fetch decision; and
`runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle` lifts the composed
decisions through main, stored declarations, recursive self calls, direct
calls, PAP application, and the final one-rebuild path.

## Next extension

Each remaining O1 consumer must add a versioned control, pass-attributed
counters, a canonical report entry, a fail-soft path, a whole-program theorem,
and a fixed-point regression. Known-shape destruction, rooted reachability,
and exact-case collapse beyond the checked unary form remain active work.
