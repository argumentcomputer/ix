# IxIR₁ optimizer harness

Status: checked scalar and exact-leaf destruction joined the default O1 bundle
on 2026-08-30. The checked HPT consumers propagate facts through complete
stored function bodies, prune impossible alternatives, collapse a certified
detailed unary case to one checked `fetch`, forward certified scalar fields
after allocation or successful reuse, specialize certified destructor sites,
and fuse adjacent PAP/application pairs. Rooted reachability then filters the
rewritten old-keyed graph before all five consumers share one content-address
rebuild.

The implementation is `Compilatrix/IxIR1/Optimizer.lean`, with compiler-facing
entry points `Pipeline.Artifact.optimizeWithProducedHPT` and
`optimizeWithCachedHPT`.

## Policy and fallback

`Optimizer.Policy` carries harness version 5, case-simplifier version 3,
fetch-forwarding version 1, destruction version 1, PAP-fusion version 1, and
reachability version 1. The five passes have independent enable bits and are
enabled by default.
Reachability additionally carries an ordered list of exported declaration
roots. The shared deterministic bounds cover input instructions, canonical
code bytes, and checked-certificate bytes. The harness is disabled only when
all five pass bits are false.

Fetch forwarding recognizes an `alloc` or `reuse` immediately followed by a
fetch of any field from its result. The selected constructor argument must be
HPT-proven scalar. The pass retains both binders and replaces the fetch with
`pure` of the source atom lifted across the constructor-result binder, so fuel,
stores, numeric locations, and cost counters are preserved exactly. Heap-valued
and out-of-range fields fail closed.

Destruction removes a `drop` or `dropU` of an HPT-proven scalar by replacing
it with `pure erased`. It also replaces `dropU` with shallow `free` when HPT
proves one exact constructor with a complete all-scalar field vector. The
rewrite preserves the result binder and the root free, while avoiding generic
tag dispatch and the recursive field walk. Shared constructor roots,
heap-valued fields, identity-only facts, multiple shapes, widened facts, and
unresolved operands stay on the generic path. The successful-run theorem is
one-way because the specialized shallow free can succeed with less fuel than
the generic deep destructor.

PAP fusion recognizes adjacent `papp`/`apply` binders and classifies their
combined arguments as under-, exactly-, or over-saturated. It retains both
binder slots, lowers supplied operands across the retired PAP slot, and rejects
the rewrite unless the continuation cannot mention that slot. Captures must be
HPT-proven scalar: IxIR₁ no longer carries function-parameter ownership modes,
so the local checker cannot soundly classify an arbitrary heap capture as
shared.

Reachability hashes the exact ordered rewritten declaration rows, exact main,
and exact configured roots into a checked certificate. Its retained list must
be in input-key order, contain every exported root, and be closed under every
direct `call` and `papp` edge in main and retained declarations. `callSelf`
remains within its retained owner. Version 1 treats a reachable dynamic
`apply` as open-world and accepts only the complete declaration set; an
unreachable apply does not pin an otherwise dead component. A producer/checker
disagreement or nonexistent configured root retains the complete input graph.

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
total forwarded fetches, scalar drops elided, unique leaf drops specialized,
total fused PAPs, under/exact/over fusion counters, removed declarations, and
a rebuild diagnostic only on fallback. Report schema 6 uses
`compilatrix/ixir1/optimizer-report/6\0`; pass behavior is
versioned separately inside the encoded policy.

This makes equality of reports executable byte equality rather than equality
of human-formatted text.

## Regression boundary

The compiled tests pin nine properties:

1. two independent runs over the same checked input produce identical output
   roots, report bytes, and report addresses;
2. a non-degenerate whole-program case rewrite removes one impossible
   alternative through an intervening alias binding, eliminates the remaining
   unary case, materializes one checked fetch, shrinks canonical code bytes,
   readdresses the changed caller, rewrites the main edge, and preserves
   pipeline producer-to-target provenance;
3. disabled and one-below instruction-budget policies select the exact input
   root;
4. after HPT is recomputed on the transformed root, the default shrinking pass
   reports `unchanged` and reproduces that root;
5. the default PAP pass fuses under-, exact-, and over-saturation in one graph,
   reports each class, rejects non-scalar captures and binder-sensitive shapes,
   preserves the scalar result with an empty live heap, and reaches a fixed
   point after HPT recomputation;
6. the default fetch pass forwards one allocation projection and one successful
   reuse projection, checks the lifted variable form, rejects heap-valued and
   out-of-range sources, preserves the exact result and all heap counters, and
   reaches a fixed point after HPT recomputation;
7. the destruction pass elides one scalar drop and specializes one exact
   all-scalar unique leaf, replaces the generic deep drop with shallow free,
   preserves the exact scalar result and allocation/free/live observations,
   rejects every conservative fact boundary, and reaches an unchanged second
   run, while an unsupported destruction version selects the input graph;
8. a direct-call closure removes a dead two-function SCC, a PAP root retains
   its target, and an explicit exported root retains the whole SCC; and
9. stale input identity, substituted roots, and a canonical but non-closed
   retained set fail closed, while reachable dynamic apply retains the whole
   graph and both the filtered and rebuilt programs return the same result.

The production Ixon→IxIR₁ integration fixtures separately exercise default
report generation and the disable path on compiler-emitted code. A
constructor-only main also emits six stored functions, five of which have no
runtime path from main; the default pass reports and removes those five while
preserving the exact constructor result. Default-pass semantic authority comes
from the checked whole-program history-refinement and
exact readdressing theorems documented in
[HPT certificates](hpt-certificates.md). `fusePair?_refines` proves each local
PAP decision; `FetchForward.runCode_forwardHead?_eq` proves literal evaluator
equality for each accepted fetch decision;
`Destroy.runOp_specialize?_success` proves arbitrary-fuel successful-run
refinement for each accepted destructor decision; and
`runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle` lifts the composed
decisions through main, stored declarations, recursive self calls, direct
calls, PAP application, and the final one-rebuild path.

## Staged extension boundary

The scalar and exact-leaf cases are the complete destruction slice for the
current IxIR₁ instruction set. Recursive expansion is not merely a code-size
question: inline `fetch`/`free` expansion reduces the fuel available to the
continuation, while moving that expansion into a content-addressed helper adds
call/invoke fuel at the generic destructor's minimum successful boundary.
`HPTDestroy.recursiveExpansionFuelBoundary` executes both counterexamples.
A shared-root specialization additionally needs an explicit RC-zero branch,
which IxIR₁ does not expose as code.

Recursive unique destruction and the known-shape shared zero branch therefore
resume with the fuel-neutral consuming-destructure/reset operation in the
IxIR₂ final-RC path (or an equivalently primitive operation with the same
semantic contract). Exact-case collapse beyond the checked unary form remains
the next extension that fits the current IxIR₁ contract.
