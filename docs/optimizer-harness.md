# IxIR₁ optimizer harness

Status: O0 delivered 2026-08-30 for the current shrinking bundle. Its checked
HPT consumer now prunes impossible call-result alternatives and, as the first
O1 slice, collapses a certified detailed unary case to one checked `fetch`.
Future consumers extend this harness; they do not introduce parallel policy
or reporting paths.

The implementation is `Compilatrix/IxIR1/Optimizer.lean`, with compiler-facing
entry points `Pipeline.Artifact.optimizeWithProducedHPT` and
`optimizeWithCachedHPT`.

## Policy and fallback

`Optimizer.Policy` carries an independent harness version and case-simplifier
pass version. Pass version 2 covers pruning plus exact unary collapse. The pass
has an explicit enable bit and deterministic bounds on input instructions,
canonical code bytes, and checked-certificate bytes.

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
roots, certificate size, before/after observations, removed-alternative count,
collapsed-case count, materialized-fetch count, and a rebuild diagnostic only
on fallback. Its version-2 canonical spelling uses
`compilatrix/ixir1/optimizer-report/2\0` and has its own content address.

This makes equality of reports executable byte equality rather than equality
of human-formatted text.

## Regression boundary

The compiled tests pin four properties:

1. two independent runs over the same checked input produce identical output
   roots, report bytes, and report addresses;
2. a non-degenerate whole-program case rewrite removes one impossible
   alternative, eliminates the remaining unary case, materializes one checked
   fetch, shrinks canonical code bytes, readdresses the changed caller,
   rewrites the main edge, and preserves pipeline producer-to-target
   provenance;
3. disabled and one-below instruction-budget policies select the exact input
   root; and
4. after HPT is recomputed on the transformed root, the shrinking pass reports
   `unchanged` and reproduces that root.

The production Ixon→IxIR₁ integration fixture separately exercises report
generation and the disable path on compiler-emitted code. Semantic authority
still comes from the checked case-simplification and readdressing theorems documented
in [HPT certificates](hpt-certificates.md); the harness adds no trusted
optimizer.

## Next extension

Each remaining O1 consumer must add a versioned control, pass-attributed
counters, a canonical report entry, a fail-soft path, and a fixed-point
regression. General fact propagation and exact-case collapse beyond the
checked immediate unary form, PAP/apply fusion, fetch forwarding, known-shape
destruction, and rooted reachability remain active work.
