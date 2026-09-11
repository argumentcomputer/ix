# IxIR₁ optimizer harness

The default O1 bundle applies five checked shrinking passes to the complete
IxIR₁ graph: case simplification, scalar fetch forwarding, destructor
specialization, PAP/application fusion, and rooted reachability. Accepted
rewrites share one content-address rebuild.

[`Optimizer.lean`](../Compilatrix/IxIR1/Optimizer.lean) implements the harness;
[`OptimizerReclamation.lean`](../Compilatrix/IxIR1/OptimizerReclamation.lean)
transports release, and [`PipelineSound.lean`](../Compilatrix/PipelineSound.lean)
projects the result onto the validated artifact. Entry points are
`Pipeline.Artifact.optimizeWithProducedHPT` and `optimizeWithCachedHPT`.

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

## Validated semantic attachment

`Optimizer.Outcome.RunRefines` exposes the selected execution relation for
both the literal skip branch and a successful content-address rebuild.
Direct-production and persistent-cache wrappers turn one successful source
run into a selected target run. They also preserve full-result reclamation:
evaluator determinism identifies every successful selected run with the
forwarded witness, heap-history isomorphism transports shared or unique deep
release, and the checked rebuild transports the released heap through its
final address map.

`ValidatedCompilation` instantiates that authority for the artifact returned
by `optimizeWithProducedHPT`. Its public endpoints state forward simulation,
target progress, all-fuel memory-error exclusion, and reclamation directly on
the selected artifact's declaration environment and main, not merely on an
internal optimizer outcome. The persistent-cache path has the same generic
successful-run and reclamation theorems and does not duplicate the pipeline
projection.

The selected artifact also exposes `frees ≤ allocs`, the evaluator's general
fresh-store balance. Heap-history refinement intentionally omits counters, and
successful PAP fusion or destruction may change allocations or frees, so the
pre-optimization no-reuse and ownership-amortized four-counter contracts are
not claimed through this interface without a separate syntactic or cost
preservation proof.

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

| Check | Required observation |
| --- | --- |
| Determinism | Independent runs produce identical roots, report bytes, and report addresses. |
| Whole-program case rewriting | Propagate through an alias, remove impossible alternatives, replace a certified unary case with fetch, and preserve producer/target provenance through readdressing. |
| Fallback | Disabled, unsupported-version, or exhausted-budget policies retain the exact input root. |
| Normalization | Recompute HPT on the output; a second shrinking run is unchanged. |
| PAP fusion | Cover under/exact/over saturation; reject non-scalar captures and live retired binders. |
| Fetch/destruction | Exercise allocation and reuse projections, scalar drops and unique leaves; preserve their stated results/counters and reject conservative fact boundaries. |
| Reachability | Exercise dead SCCs, PAP/exported roots, reachable dynamic apply, stale identities, substituted roots, and non-closed retained sets. |

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
semantic contract). That contract is now frozen in the
[IxIR₂ v0 specification](ixir2-spec.md): consuming/reset is one CFG transition,
credits are affine and exact-layout, and the shared decision is an explicit
optional-credit branch. Exact-case collapse beyond the checked unary form
remains the next extension that fits the current IxIR₁ contract.

## Downstream checked transformations

IxIR₂ and native transformations have separate validators, identities, and
semantic/cost contracts. The O1 history relation does not certify them.

| Transformation | Contract and evidence |
| --- | --- |
| Dynamic shared reuse | [IxIR₂ lowering and reuse](ixir2-spec.md#ixir₁ixir₂-lowering): checked last use/layout, physical live-heap simulation, and literal baseline fallback |
| Logical/physical credits | [General refinement](credit-refinement.md): both policies, all instruction forms, prefix resources, and reclamation under explicit root ownership |
| Source recursion recovery | [Closed eager folds](source-recursion.md): recognized source replacement and selected source/resource composition |
| Reservations across calls | [Source maps](source-call-reuse.md): v1 suspended credits, complete release, and allocation/free/RC/peak comparison |
| Static unique reuse | [Unique reversal](source-unique-reuse.md): consuming emission and separately validated baseline/selected targets |
| Borrowing | [Closed certificates](source-borrow.md) and [structural runtime functions](source-borrow-runtime.md), with owned PAP wrappers and lender lifetimes |
| Native selection | [Closed unique](source-native-unique.md), [runtime unique](source-native-runtime.md), [upstream](source-native-upstream.md), and [runtime scalar](source-native-scalar.md) contracts |
| Native counter folding | [Checked rewrite and measurements](performance/counter-fold-2026-09-10/README.md), with the original baseline independently selectable |

The [simulation guide](simulation-strategy.md) explains composition; the
[roadmap](roadmap.md) owns extensions and activation gates. Keep pass-attributed
counters separate from [native timing](performance/README.md).
