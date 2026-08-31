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
  projections, quotients, configured opaque definitions, and externs.
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
  counters, and deterministic fixed-point regressions.
  Executable exact-fuel counterexamples close the IxIR₁ destruction boundary:
  recursive inline expansion steals continuation fuel, helper expansion adds
  call-entry fuel, and shared specialization lacks an explicit RC-zero branch.
  Recursive/shared known-shape destruction is therefore staged with the
  fuel-neutral consuming-destructure/reset path in IxIR₂.
  See [HPT certificates](hpt-certificates.md) and the
  [optimizer harness](optimizer-harness.md).
- Deterministic mode/counter fixtures, a generated well-moded corpus, and a
  bounded production-Std contact.
  See [counter evidence](thesis-counter-evidence.md),
  [well-moded generation](well-moded-generator.md), and
  [corpus contact](corpus-contact.md).

The current implementation boundary is IxIR₁. No compiler path yet emits
paired reuse, IxIR₂, native instructions, or a self-hosted binary.

## Known boundaries carried forward

These are active scope constraints, not hidden qualifications:

- The main semantic results currently prove the forward successful-run
  direction. Error/divergence reflection is deferred until the execution
  semantics and native boundary stabilize.
- Erasure adequacy is not yet connected to lean4ix's kernel theory.
- The current validated fragment remains narrower than all of Lean/Ixon;
  unsupported features fail closed at validation.
- IxIR₁ externs are scalar-only at the trusted boundary; heap-argument
  ownership needs an explicit ABI contract.
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

This is the current milestone.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| Whole-pass value/ownership/progress simulation | active | Every validator-accepted current-fragment main has a composed IxIR₀→IxIR₁ forward simulation, no reachable memory error, and the existing reclamation/cost results without fixture-specific assumptions. |
| Proof-structure consolidation | active | Shared recursive judgments have one foundational traversal each; public theorems depend on those cores without duplicating the induction. Stop recording individual consolidation cuts in this roadmap. |
| HPT consumer tranche O1 | delivered | Checked case pruning/collapse, scalar fetch forwarding, scalar and exact-all-scalar unique-leaf destruction, PAP/application fusion, and rooted reachability compose through one owner-sensitive traversal and one rebuild, with arbitrary-fuel proofs, fail-soft policy/reporting, and fixed-point regressions. Recursive/shared destruction is assigned to the IxIR₂ consuming-destructure rows below because ordinary IxIR₁ expansion cannot preserve the same-fuel contract. |
| IxIR₁ extern ownership ABI | next | Heap-valued extern arguments/results have explicit consume/borrow/retain contracts or remain rejected by the validated fragment. |
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
The remaining attachment work is to prove semantic provenance for every
generated function, seal the resulting compiler contracts, and project them
to the memory-safety, reclamation, and cost corollaries.

M2b exits when that ownership premise is discharged for every accepted main
and the first useful certified whole-program optimization bundle is attached
to the same interface. The detailed optimizer design is in
`plans/whole-program-optimization.md`.

## M2c — optimized native wedge

M2c begins after the M2b semantic interface is stable. Design work that does
not perturb that interface may start earlier.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| IxIR₂ CFG and join points | next | Structured IxIR₁ lowers to validated blocks with explicit parameters, tail calls, and a compositional simulation theorem. |
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

1. **Finish the M2b mixed-mode pipeline attachment.** Derive the landed
   owner-sensitive PAP and declaration-coverage premises from every validated
   compilation record, then attach the memory-safety and existing
   reclamation/cost corollaries to the pipeline semantic endpoint.
2. **Specify IxIR₂ before implementing it.** Freeze block parameters,
   terminators, ownership flow, consuming unique destructure, and affine reuse
   credits together with the simulation statement. Include the fuel-neutral
   recursive unique destructor and shared RC-zero branch required beyond the
   delivered IxIR₁ leaf specialization.
3. **Build the x86-64 v0 semantic skeleton.** Keep selection and encoding
   separate; prove fragment containment through the typed instruction AST.
4. **Run the first compiler-emitted reuse benchmark.** Unique list reversal is
   the gate from hand-written reuse semantics to an optimizing compiler.

Do not retain completed items in this list. Move durable evidence to the
relevant focused document and replace the queue entry with its successor.
