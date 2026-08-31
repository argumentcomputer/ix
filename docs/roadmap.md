# Compilatr.ix roadmap

Last reviewed 2026-08-31. This is the canonical source for priorities,
milestone state, and activation gates. It is intentionally forward-looking:
completed implementation detail belongs in the source tree, focused documents,
and version history—not in the live queue.

Local files under `plans/` explain designs and decisions. They do not override
this roadmap.

## Mission

Build a self-hosting certified toolchain from Ixon to native and zk targets.
Native and zk code generation must refine the same Ixon operational semantics,
with:

- an independently checkable compilation path;
- explicit ownership, cost, and runtime models;
- content-addressed compiler artifacts and certificates;
- a shrinking trusted-extern ledger;
- statement-faithful certificates at the eventual source boundary.

The principal end-to-end theorem is forward semantic preservation from
validated Ixon evaluation to emitted machine execution. Error/divergence
reflection, source-statement faithfulness, and resource/capability guarantees
are separate named obligations.

## Naming

- **Compilatr.ix** is the project and product name.
- **Compilatrix** is the Lean namespace and source-directory name.
- **ix** owns the surrounding object ecosystem and production checker line.
- **Ixon** is the content-addressed input language.
- **lean4ix** is the public kernel-theory and checker-verification anchor.

Legacy project names must not appear in active plans.

## Delivered baseline

The following foundation is present and should not be expanded into a second
status ledger here:

- Reproducible Lean/Lake/Nix builds, CI configuration, licensing, an axiom
  fence, and a validated trusted-extern ledger.
- Ixon v2 mode-bearing syntax, strict resource-bounded codecs, canonical
  sharing, checked content addressing, and bounded catalog ingress.
  See [wire format](ixon-v2-wire.md),
  [canonical sharing](canonical-sharing.md),
  [sharing policy](sharing-policy.md), and
  [catalog ingress](catalog-ingress.md).
- A validated, content-addressed erasure path to IxIR₀ with a theorem-backed
  fragment covering ordinary definitions, recursors, mutual blocks,
  projections, quotients, and configured opaque definitions. Erasure and the
  unvalidated engineering path retain scalar-only extern support; the
  certified compiler boundary rejects extern declarations explicitly.
- Mode-directed lowering to the explicit-store IxIR₁, with executable
  ownership checks, leak-freedom fixtures, cost counters, mutual-block
  addressing, and a proof-facing validated compilation record that retains
  the scoped erasure and both address-pass witnesses used by the current
  formal simulation spine. Function declarations now carry an address-
  committed owner-sensitive PAP-entry policy: direct known calls retain mixed
  affine/unique boundaries, while dynamic saturation is admitted only for
  declarations with homogeneous shared contracts.
- A bounded HPT post-fixpoint checker, durable content-addressed summaries,
  recursive constructor-field facts, and the first semantics-preserving
  whole-program fact consumer: owner-sensitive propagation through stored
  function bodies, impossible-alternative pruning, and checked detailed-unary
  exact-case collapse. The same one-rebuild boundary now includes exact scalar
  fetch forwarding after allocation/reuse, scalar-drop elimination,
  exact-all-scalar unique-leaf destruction, checked PAP/application fusion,
  and checked rooted declaration reachability with exported roots and a
  conservative dynamic-apply fallback. It runs behind a versioned fail-soft
  optimizer policy with canonical before/after reports, pass-attributed
  counters, and deterministic fixed-point regressions. The directly produced
  selected artifact is now attached to the validated semantic interface with
  artifact-facing forward simulation, target progress, all-fuel memory-error
  exclusion, full-result reclamation, and the evaluator-universal
  allocation/free law.
  Executable exact-fuel counterexamples close the IxIR₁ destruction boundary:
  recursive inline expansion steals continuation fuel, helper expansion adds
  call-entry fuel, and shared specialization lacks an explicit RC-zero branch.
  Recursive/shared known-shape destruction is therefore staged with the
  fuel-neutral consuming-destructure/reset path in IxIR₂.
  Shared evaluator proof families now expose one foundational traversal per
  recursive judgment: owner-sensitive deep-release safety and termination are
  paired behind common cores, and arbitrary fuel increases use one generic
  successor-stability lift across Ixon, IxIR₀, and IxIR₁.
  The certified extern boundary is closed mechanically on both the addressed
  IxIR₀ input and emitted IxIR₁ artifact environment; its semantic, progress,
  safety, reclamation, and cost endpoints carry no caller-supplied extern
  contract.
  See [HPT certificates](hpt-certificates.md) and the
  [optimizer harness](optimizer-harness.md).
- The frozen IxIR₂ v0 in-memory syntax and a bounded executable validator for
  block-local ordinals, explicit joins, owner/borrow flow, addressed call
  signatures, world-keyed constructor schemas, exact-layout affine credits,
  combined constructor/Nat dispatch, and the closed extern boundary. Positive
  fixtures cover ordinary and loop edges, direct borrowed calls, required and
  optional credit paths, joins, discard, and tail-self transfer; negative
  fixtures pin duplication, leaks, use-after-consume, lender lifetime, layout
  and optionality mismatches, malformed control flow, dynamic borrowed entry,
  externs, and resource exhaustion.
- IxIR₂ logical and physical small-step execution with independent control and
  heap-traversal budgets, executable calls/PAPs/CFG transfer, explicit physical
  reservations, hot/cold reset, reuse and discard observations, a credit-local
  heap-relation interface, proved local counter algebra, and non-degenerate
  intermediate and terminal executable witnesses.
- The standalone structured IxIR₁→IxIR₂ baseline lowerer for the no-`reuse`
  subset. Owner-keyed erased-information sidecars feed producer-derived SSA
  blocks, conservative join parameters, constructor/Nat dispatch, tail
  transfers, target-coordinate leaf facts, traces, and an exact validator
  equation. Differential Nat/constructor runs plus axiom-fenced scalar/vector
  operand resolution, environment extension, and the first `pure`/`move`
  small-step case establish the active simulation seam.
- Deterministic mode/counter fixtures, a generated well-moded corpus, and a
  bounded production-Std contact.
  See [counter evidence](thesis-counter-evidence.md),
  [well-moded generation](well-moded-generator.md), and
  [corpus contact](corpus-contact.md).

The current pipeline-output boundary is IxIR₁. IxIR₂ syntax, validation,
logical/physical execution, and a standalone structured baseline translator
are implemented, but the validated pipeline does not yet emit IxIR₂, paired
reuse, native instructions, or a self-hosted binary.

## Known boundaries carried forward

These are active scope constraints, not hidden qualifications:

- The main semantic results currently prove the forward successful-run
  direction. Error/divergence reflection is deferred until the execution
  semantics and native boundary stabilize.
- Erasure adequacy is not yet connected to lean4ix's kernel theory.
- The current validated fragment remains narrower than all of Lean/Ixon;
  unsupported features fail closed at validation.
- IxIR₁ runtime and unvalidated compilation support only scalar extern
  arguments/results. Validator-gated compilation rejects all extern
  declarations on its exact source and target graphs; reopening that boundary
  requires an explicit consume/borrow/retain ABI.
- The lowerer emits conservative RC operations and no reuse. Borrow inference,
  RC coalescing, and reset/reuse belong to the optimized IxIR₂ path.
- HPT parameters currently begin at `top`; summaries are context-independent.
- Large-corpus ingestion is bounded/in-memory. Streaming and distributed cache
  maintenance are scaling work, not blockers for the native wedge.
- Native BLAKE3 and durable-sync operations remain ledgered assumptions.
- The first x86 wedge may use a local emitted-subset semantics. Until it is
  connected to an independently maintained x86 model, that semantics remains
  an explicit ISA-specification assumption in the ledger.
- Threads, floats, source locality, and a zk cost model have explicit wake
  conditions below.

## Operating rules

Statuses used below:

- **active** — work is in flight and appears in the immediate queue;
- **next** — specified and unblocked when its named predecessor exits;
- **deferred** — dormant until its wake condition is met;
- **blocked** — requires an external decision or dependency change.

Roadmap hygiene:

1. Keep completed work in the delivered baseline or a focused evidence
   document; do not append implementation diaries to the queue.
2. Give every active item one concrete exit condition.
3. Record a dependency or risk change when reordering work.
4. A theorem-backed exit requires a non-degenerate executable witness and an
   axiom-fence entry.
5. An inferred optimization may fail closed to the unoptimized path; it must
   not reject an otherwise valid program.
6. Use exact artifact roots and pinned revisions in code/fixtures, not prose
   duplicated here.

## M2b — close the verified IxIR₁ middle end

This milestone is complete.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| Whole-pass value/ownership/progress simulation | delivered | Every validator-accepted current-fragment main has a composed IxIR₀→IxIR₁ forward simulation, no reachable memory error, and the existing reclamation/cost results without fixture-specific assumptions. |
| Proof-structure consolidation | delivered | Shared recursive judgments have one foundational traversal each; public theorems depend on those cores without duplicating the induction. Stop recording individual consolidation cuts in this roadmap. |
| HPT consumer tranche O1 | delivered | Checked case pruning/collapse, scalar fetch forwarding, scalar and exact-all-scalar unique-leaf destruction, PAP/application fusion, and rooted reachability compose through one owner-sensitive traversal and one rebuild, with arbitrary-fuel proofs, fail-soft policy/reporting, and fixed-point regressions. Recursive/shared destruction is assigned to the IxIR₂ consuming-destructure rows below because ordinary IxIR₁ expansion cannot preserve the same-fuel contract. |
| IxIR₁ extern ownership ABI | delivered | The validator-gated pipeline rejects externs on the exact addressed IxIR₀ input and emitted IxIR₁ graph, retains lookup-level certificates for both, and synthesizes the now-vacuous semantic/progress contracts internally. Runtime and unvalidated compilation remain scalar-only. |
| Address reproducibility | next | Two independent full compilations of the same validated root produce the same addressed IxIR₀/IxIR₁ graph and certificate identities. |
| HPT/cache scaling | deferred | Wake when bounded Std/corpus work demonstrates that directory enumeration, sharding, garbage collection, or cross-store scheduling is the bottleneck. |

`ValidatedCompilation.semanticForwardSimulation` is now the concise semantic
spine: validator-derived member scope and coverage plus both address-pass
equations are carried by the compilation result. The owner-sensitive
`CompilerContracts` layer has landed: declaration rewriting preserves
`papSafe`, the mutual seal requires all-shared ownership only for dynamically
enterable declarations, and a mixed unique/direct-call model proves that this
is strictly weaker than the former global premise. Initial SCC content
addressing now also certifies exact-source transport from the literal raw
declaration list, so this attachment need not admit synthetic final-key
aliases merely to prove declaration coverage. The concrete whole-pass trace
now derives source declaration layout and owner-sensitive PAP safety, and
partitions every raw function as either a selected source callable or a final
generated declaration. Addressed erasure and exact target addressing now
certify row selection too, so each validated compilation record exposes
source layout, PAP safety, and raw function coverage without caller premises.
Whole-program lowering now also carries exact operational provenance for every
generated constructor wrapper and lifted function through the full lowering
cluster. That provenance replays each generated body against the mutually
smaller source/application contracts, while same-address source declarations
are recovered from their concrete `lowerDecl` traces. One evaluator-fuel
induction therefore seals every source, generated, and dynamic-application
ownership contract, and each validated record exposes the resulting
`exactCompilerContracts` theorem for its literal raw target context. The
semantic endpoint now consumes that theorem through the certified exact-source
target-address transport and records the rebuild renaming relating raw and
emitted heaps; callers no longer supply target declaration, representation, or
ownership premises. The same interface exposes certified target progress and
all-fuel memory-error exclusion for each successful validated source main,
unconditional full-result reclamation, the current no-reuse/allocation-free
counter law, and the ownership-amortized four-counter budget whenever the
ordinary source execution has a call-aware profile. The retained source and
target extern scans prove that neither evaluator environment resolves an
extern, so these endpoints no longer ask callers for extern value or progress
contracts.

The directly produced O1 selection now composes that spine through the
optimizer's allocation-history refinement and exact final rebuild. The
artifact returned by `optimizeWithProducedHPT` therefore exposes forward
simulation, target progress, all-fuel memory-error exclusion, and full-result
reclamation on its own declaration environment and main. Its applicable
counter contract is the evaluator-universal `frees ≤ allocs` law. The
pre-optimization `reuses = 0` and ownership-amortized four-counter contracts
are not transported through an optimizer relation that intentionally forgets
counters and admits allocation-changing PAP/destruction rewrites.

M2b is complete. The detailed optimizer design is in
`plans/whole-program-optimization.md`.

## M2c — optimized native wedge

This is the current milestone. Its semantic interface is the stable M2b
boundary above. The normative syntax, ownership-flow, credit semantics,
validation obligations, and simulation interface are frozen in the
[IxIR₂ v0 specification](ixir2-spec.md).

| Deliverable | State | Exit condition |
| --- | --- | --- |
| IxIR₂ syntax and validation | delivered | The frozen v0 in-memory syntax, world-keyed schemas, bounded ownership/borrow/credit validator, stable rejection classes, proof-facing acceptance predicate, and positive/negative executable fixtures land together. |
| IxIR₂ logical/physical semantics | delivered | Executable semantics separate control from heap-traversal budgets, model logical frees versus physical reservations/reuse, cover calls/PAPs and CFG transfer, expose a credit-local heap relation, prove the local counter algebra, and validate intermediate and terminal equations on non-degenerate credit paths. Whole-machine refinement composes in the lowering tranche. |
| IxIR₂ CFG and join points | active | The validator-gated executable lowerer, generated trace, explicit parameters, constructor/Nat dispatch, tail calls, differential witnesses, theorem interface, operand-vector/environment lemmas, and first instruction step are delivered. Complete the remaining instruction/block induction and attach its sidecars to the validated pipeline artifact. |
| Direct-recursion recovery | next | Recognized recursor images validate to direct loops; unrecognized terms retain the literal correct fallback. |
| Static unique reuse | next | Fuel-neutral consuming unique destructure specializes recursive known shapes, produces affine reuse credits, and compiler-emitted list reversal reaches the FIP counter target. |
| Dynamic shared reset/reuse | next | A checked RC-zero branch specializes known shared shapes; ordinary all-shared code reuses RC=1 nodes on the hot path and allocates correctly on the cold path. |
| Borrowed parameter ABI and RC coalescing | next | Read-only call chains remove call-boundary RC traffic under a checked interprocedural borrow artifact. |
| x86-64 semantics and emitter | next | A typed System V subset, executable local semantics, encoder, minimal ELF object writer, and native differential co-simulation run one compiled program with the provisional ISA-specification trust entry exposed. |
| x86 reference-semantics bridge | deferred | Wake when Sail's Lean backend can reproducibly import the needed x86-from-ACL2 slice; before substantially expanding v0, prove per-form decode/execution equivalence between encoded bytes, the local model, and that reference. |
| Register-allocation validator | next | An untrusted allocator emits a coloring/spill certificate accepted by a verified checker over the machine CFG. |
| End-to-end native FIP witness | next | A validated Ixon program compiles to x86-64, runs natively, returns the checked result, and satisfies its memory/capability counters. |

The x86-64 boundary and staged encoder obligations are specified in
`plans/isa.md`. Reset/reuse, borrows, HPT consumers, and pass ordering are
specified in `plans/whole-program-optimization.md`.

## M2d — specialization and representation

This milestone may overlap late M2c work once IxIR₂ and the representation
boundary are stable.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| IxIR₀ˢ specialization | next | Stable, budgeted variants eliminate one higher-order/PAP path without nondeterminism or adversarial code growth. |
| Arity/dead-parameter optimization | next | Checked liveness removes unused parameters and flattens one saturated call family end to end. |
| Created-by and layout certificates | next | Producer/consumer groups validate independently of HPT and preserve semantic constructor identity. |
| Field deletion and unboxing | next | One closed layout drops dead storage and one scalar record/address-key path is unboxed with semantic readback. |
| Open-boundary representation policy | next | Exported/extern values retain a conservative ABI or carry an explicit versioned representation contract. |

## M3 — theory bridge and self-hosting

| Deliverable | State | Exit condition |
| --- | --- | --- |
| lean4ix theory bridge | next | IxIR₀ erasure adequacy is stated and proved against the pinned public lean4ix theory interface. |
| Mode conservativity | next | The `many/shared` fragment is proved conservative and Uses/Owned add no new definitional equality. |
| Bootstrap reproducibility | next | The upstream Gen-0 seed and generated compiler artifacts have a documented reproducibility/attestation procedure. |
| Compile Compilatr.ix with itself | deferred | Wake after M2c plus the required runtime subset. |
| Diverse double compilation | deferred | Wake after the first self-hosted compiler can rebuild a byte/address-comparable successor. |

The theory home remains public lean4ix plus ix's checker-verification line.
There is no local kernel-theory vendoring plan.

## M4 — frontend and statement faithfulness

M4 stays behind the backend spine unless an upstream integration need makes it
critical sooner.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| Address-equality frontend oracle | next | Upstream elaboration and the candidate frontend produce identical complete Ixon environments for a bounded corpus. |
| Vendored upstream frontend | deferred | Wake after M3 or a concrete compatibility need; retain parser/macro/elaborator behavior while replacing the backend target. |
| Mode surface syntax and inference | deferred | Start with explicit annotations; add inference only after the addressed contract and diagnostics are stable. |
| Statement faithfulness | deferred | A verified printer/round-trip relation ties human-readable statements to the certified Ixon address. |
| Reflection/TCB policy | deferred | Decide before proof-by-evaluation makes the compiler part of the logical soundness boundary. |

## Runtime and zk tracks

Runtime work follows actual emitted-code needs:

1. allocation, memcpy-class operations, RC, reset/reuse, and the syscall
   substrate required by the native wedge;
2. verified bignums and fixed-width arithmetic support;
3. threads/tasks and atomic RC;
4. floats and specialized numeric kernels.

Every persistent native boundary appears in
[the trusted-extern ledger](trusted-extern-ledger.md) with a retirement
condition. Seed-only upstream Lean/C++ components disappear from the execution
path after self-hosting; they are bootstrap provenance, not target-runtime
dependencies.

The zk backend shares IxIR₂ and semantic/cost observations with native code.
Its cost model wakes when the IxIR₂ operation set is stable and can be reviewed
against Aiur's current constraint costs. Native and zk may use different
representations, but both must refine the same semantic and resource contracts.

## Deferred design axes

| Axis | Wake condition |
| --- | --- |
| Regions/locality | After borrow and reset/reuse measurements expose a remaining nonescaping-allocation cost; require a checked IR prototype before an Ixon hash roll. |
| Usage polymorphism | When mode-polymorphic recursors or generic functions such as `map` block real corpus compilation. |
| Modal inductives/layouts | With M2d specialization and a stable representation identity. |
| Capability ladder | As native witnesses can certify rc-free → heap-free → alloc-free → panic-free. |
| Freeze/duplication representation | When a real unique→shared corpus path is needed or before header/layout choices become irreversible. |
| Threads/atomic RC | Before the N-thread Ix.Tc parity benchmark. |
| Floats | When a selected corpus or runtime surface requires IEEE behavior. |
| Error/divergence reflection | After the native operational semantics and failure boundary stabilize. |
| Region/source locality bit | Only after the IR prototype demonstrates native or zk benefit beyond reuse and borrowing. |

## External dependencies to monitor

- **ix/Ixon:** keep parity fixtures pinned to the selected upstream revision;
  upstream strict-ingress deltas when the format contract is ready.
- **lean4ix:** track the public theory/checker interface used by M3; bridge
  rather than vendor.
- **Aiur:** align the shared-middle cost model before freezing zk operation
  tariffs.
- **Toolchain:** advance the Lean/lean4-nix pin deliberately with parity and
  full-check evidence.

External movement may change a wake condition; it does not silently change
this repository's completion claims.

## Immediate queue

1. **Finish and attach structured IxIR₁→IxIR₂ lowering.** Prove the
   instruction/block-compositional control simulation over the generated
   trace, then derive the owner-keyed sidecars from the validated pipeline
   artifact and expose the checked IxIR₂ result there.
2. **Build the x86-64 v0 semantic skeleton.** Keep selection and encoding
   separate; prove fragment containment through the typed instruction AST.
3. **Run the first compiler-emitted reuse benchmark.** Unique list reversal is
   the gate from hand-written reuse semantics to an optimizing compiler.
4. **Prove address reproducibility.** Run two independent full compilations of
   one validated root and compare the addressed IxIR₀/IxIR₁ graphs and
   certificate identities.

Do not retain completed items in this list. Move durable evidence to the
relevant focused document and replace the queue entry with its successor.
