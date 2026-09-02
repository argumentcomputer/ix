# Compilatr.ix roadmap

Last reviewed 2026-09-07 against the current working tree. This is the
canonical source for priorities, milestone state, and activation gates.
The [development plan](development-plan.md) records the code review evidence,
bounded work packages, and acceptance criteria behind this queue. Local
`plans/` files explain design alternatives and do not override it.

## Mission

Build a self-hosting certified toolchain from Ixon to native and zk targets,
with an independently checkable compilation path, explicit ownership and
resource models, content-addressed artifacts, and a shrinking trusted-extern
ledger. Native and zk targets refine the same Ixon operational semantics.

The principal theorem is successful-run forward semantic preservation from
validated Ixon evaluation to emitted machine execution. Error/divergence
reflection, source-statement faithfulness, and resource/capability guarantees
are separate named obligations.

## Naming

- **Compilatr.ix** is the project and product name.
- **Compilatrix** is the Lean namespace and source-directory name.
- **ix** owns the surrounding object ecosystem and production checker line.
- **Ixon** is the content-addressed input language.
- **lean4ix** is the public kernel-theory and checker-verification anchor.

## Review direction

Prioritize complete compiler entry points over additional optimization
breadth. The baseline IxIR₁→logical-IxIR₂ induction and physical-baseline→reuse
whole-main theorem are assembled. N1 now connects baseline interpretations and
selects the actual compiler output of a synthetic Ixon scalar, with a composed
typed-x86 theorem and native checks. C1 adds bounded accepted-source coverage
and comparisons of complete compiler artifacts. D1 recovers a direct loop
from an eager synthetic Ixon list fold with hot/cold reuse observations.
D2 composes successful source evaluation through the actual selected physical
program, with original owned IxIR₁ execution on outer fallback. R2 adds terminal
allocation balance and complete shared-result reclamation. R3 proves comparative
allocation/free laws for actual shared-main baseline and selected executions.
R4 adds RC and peak-live bounds, including intermediate selected states and
complete release. R5 adds a separately versioned policy for credits suspended
across non-tail direct calls, with a checked source-map specialization and the
same resource and cost guarantees. Static unique reuse now compiles a checked
source-list reversal with consuming ownership, exact no-RC costs, and complete
reclamation. Native heap selection is next; these gates do not establish
ordinary Std compilation or self-hosting.

## Delivered baseline

| Boundary | Evidence and scope |
| --- | --- |
| Build and trust discipline | Lean/Lake/Nix builds, CI, the [axiom fence](../Compilatrix/Fence.lean), and [trusted-extern ledger](trusted-extern-ledger.md). Local review checks passed; see the development plan for the exact check surface. |
| Ixon ingress and identity | Strict bounded v2 codecs, canonical sharing, checked content addressing, and bounded catalogs. The [Std contact](corpus-contact.md) succeeds at ingress and deliberately pins a downstream `freezeNeeded` rejection. |
| Validated Ixon→IxIR₁ | Checked addressed erasure to IxIR₀, mode-directed explicit-store lowering, and artifact-facing forward simulation, progress, memory-error exclusion, reclamation, and scoped cost results. Genuine source sharing/oracle obligations remain explicit. See [simulation strategy](simulation-strategy.md) and [lowering restrictions](lowering-restrictions.md). |
| IxIR₁ optimization | Bounded HPT production/checking and durable summaries; checked case simplification, scalar fetch forwarding, scalar/leaf destruction, PAP fusion, and rooted reachability through one rebuild. The selected artifact has its own semantic and reclamation endpoints; its universal counter law is `frees ≤ allocs`. See [optimizer harness](optimizer-harness.md). |
| Baseline IxIR₂ | Frozen in-memory syntax, bounded ownership/borrow/credit validation, executable logical and physical semantics, and checked structured lowering. The attached whole-main theorem preserves successful IxIR₁ execution; the checked absence of credit operations transports its exact result and budgets to physical execution. See [IxIR₂ specification](ixir2-spec.md). |
| Dynamic reuse | Checked insertion and whole-main preservation from successful physical baseline execution to the exact optimizer output, with compiler progress derived internally. Production selection retains a checked baseline on target rejection. D2 supplies source-facing physical composition; R2 adds terminal allocation balance and complete shared-result reclamation. R3/R4 prove allocation/free laws and RC/peak bounds for the shared-main compiler domain, with separate counter invariants and all intermediate states covered. |
| Source recursion recovery | D1's checked immediate-list schema derives a direct accumulator recursor from actual Ixon erasure. D2 derives execution of the actual selected physical IxIR₂ or original owned IxIR₁ on outer fallback; R2/R3/R4 add shared reclamation and comparative allocation/free/RC/peak laws without new source premises. Eight source cases check terminal/reclaimed balances and comparative laws, with 25 rejection/fallback checks. See [source recursion](source-recursion.md). |
| Reuse across calls | R5's explicit v1 policy suspends caller-owned reservations through direct `call`/`callSelf`, preserving v0 behavior. A checked closed Nat-map specialization produces actual compiler input; its source theorem includes selected execution, fallback, reclamation, and allocation/free/RC/peak laws. Nine maps, 35 policy/rejection checks, and complete fresh-process artifacts exercise hot, cold, and mixed ownership. See [source call reuse](source-call-reuse.md). |
| Static unique reuse | Checked recursor-mode identities and closed-source reversal specialization produce consuming IxIR₁ and a validated IxIR₂ translation. The source theorem covers arbitrary accepted finite Nat lists, actual selected/fallback execution, exact no-RC allocation/reuse/peak costs, every reservation prefix, and full reclamation. Seven cases and 43 boundary checks have complete fresh-process artifacts. See [source unique reuse](source-unique-reuse.md). |
| Native scalar path | Typed local x86-64 semantics, exact graph recognition, actual-selector and source-facing refinement theorems, E0 encoding, and ELF emission. A synthetic Ixon scalar passes the validated compiler and native checks with its real addressed IxIR₁ provenance; earlier hand-written fixtures remain useful substrate checks. |

The default production compilation result remains IxIR₁.
`IxIR2.Pipeline.compileValidated` supplies a separate checked baseline
attachment. `X86.ValidatedScalar.compile` supplies the bounded source-to-native
scalar endpoint; general source graphs still need wider selection and runtime
support.

`Recursion.compileValidated` is the optional source-recovery endpoint. It
retains the original validated compilation and, when recovery succeeds, the
exact generated ownership, CFG, and reuse artifacts.

`CallReuse.compileValidated` selects the v1 pass on an ordinary checked
attachment. `CallReuse.compileMap` adds the optional checked closed-map
specialization and retains the original validated source on outer fallback.

`UniqueReuse.compile` checks an explicit closed Ixon entry under the opt-in
`recursor-modes/1` policy. It retains consuming IxIR₁ when target translation
fails and a checked IxIR₂ baseline when optional static reuse fails.

## Known boundaries

- The accepted fragment is narrower than Lean/Ixon; unsupported constructs
  fail closed. Erasure adequacy is not yet connected to lean4ix.
- Certified compilation rejects externs on its exact source and emitted
  graphs. Runtime/unvalidated scalar extern support is not an ownership ABI.
- The bounded unique reversal endpoint handles consuming destructuring and
  recursor worlds for its checked source schema. General unique recursors,
  partial or escaping unique rule applications, and unique native heap
  selection remain outside that endpoint.
- Baseline lowering emits conservative RC and no reuse. Shared and bounded
  static unique reuse are separately selected passes; borrow inference and
  RC coalescing remain future work.
- Baseline interpretation independence is proved for checked programs without
  credit operations. General logical/physical credit refinement remains open.
- IxIR₂ has no canonical codec or independent content address. Initial native
  integration may use the implemented IxIR₁-root-plus-policy provenance;
  persistent IxIR₂ identities require the codec gate below.
- HPT summaries are context-independent and parameters start at `top`.
  The bounded corpus does not establish broad source acceptance or scale.
- Recursion recovery currently checks closed Nat-list entries with known
  immediate-tail minor functions. General `brecOn`, open entries, mutual or
  nested recursion, and well-founded erasure remain outside that schema.
- Native BLAKE3 and durable sync remain ledgered interfaces. The local x86
  semantics, E0 encoder, and ELF writer remain specification assumptions.
  Native differential checks do not retire them.

## Operating rules

- **delivered** means the named, scoped boundary has code and evidence.
- **active** means work is in flight and appears in the immediate queue.
- **next** means specified work follows its named predecessor or gate.
- **deferred** means dormant until its wake condition is met.
- **blocked** means an external decision or dependency change is required.

Keep one observable exit per work package. A theorem-backed exit needs an
axiom-fence entry and a non-degenerate executable witness at the claimed
input boundary. Record semantic, resource, and native-byte guarantees
separately. Optional optimizer failure must retain the last checked artifact;
invalid source remains an error. Put detailed theorem evidence in focused
documents and keep completed proof steps out of the immediate queue.

## M2b — verified IxIR₁ middle end

The scoped semantic milestone is complete. Compiler reproducibility is a
cross-pipeline gate in M2c, rather than unfinished work inside this milestone.

| Deliverable | State | Completed boundary |
| --- | --- | --- |
| Whole-pass simulation and ownership | delivered | The validated artifact exposes forward simulation, progress, memory-error exclusion, full-result reclamation, and the stated baseline cost contracts. |
| Proof-structure consolidation | delivered | Shared recursive judgments use common foundational traversals and public projections. |
| HPT consumer tranche O1 | delivered | The five checked consumers compose through one owner-sensitive traversal and exact rebuild, with fail-soft policy and fixed-point regressions. |
| Certified extern closure | delivered | Source/target scans close the current certified boundary; reopening heap-valued externs requires an explicit ownership ABI. |

Recursive/shared destruction stays in IxIR₂: IxIR₁ recursive inline/helper
expansion breaks the same-fuel contract, and shared specialization requires an
explicit RC-zero branch. HPT/cache scaling wakes only when measured bounded
corpus work identifies cache scheduling or storage as the bottleneck.

## M2c — source-driven optimized native execution

This is the current milestone. The [IxIR₂ specification](ixir2-spec.md)
fixes the in-memory contract; the [development plan](development-plan.md)
defines the immediate proof and integration cuts.

| Deliverable | State | Exit condition or delivered scope |
| --- | --- | --- |
| IxIR₂ syntax, validation, and local semantics | delivered | Frozen v0 syntax, bounded validation, executable CFG/call/PAP/credit behavior, and local counter laws. This does not claim general logical/physical refinement. |
| Baseline CFG lowering and logical simulation | delivered | Exact checked attachment and canonical whole-main successful-run theorem, including calls, recursive application, constructor/Nat dispatch, and internally derived target ownership/provenance facts. |
| Dynamic shared reset/reuse composition | delivered | R1: `OptimizedAttachment.physicalMainSimulation` preserves successful physical baseline main runs without progress callbacks. Constructor macros, tail returns, recursive residual application, and checked production fallback compose internally. Source-facing and general resource claims retain their separate gates. |
| Baseline physical execution bridge | delivered | N1: `Attached.successfulPhysicalMainSimulation` composes logical lowering with exact interpretation transport for the checked baseline inventory. |
| Local x86 semantics, scalar selection, and E0 emission | delivered | Both exact scalar graphs refine the actual selected typed target. Seven deterministic objects pass independent decoding and native checks. |
| Validated source-to-native scalar path | delivered | N1: synthetic Ixon roots for zero, 42, and UInt64 max compile, select, emit, link, and run with real IxIR₁ provenance. `sourceScalarRefines` composes to the local ISA without Nat truncation; source sharing/oracle premises remain explicit. |
| Accepted-source coverage and address reproducibility | delivered | C1: 13 Ixon cases cover accepted direct calls, constructor/Nat dispatch, PAP/application, three native scalar exits, and exact negative boundaries. Two fresh processes produce identical complete canonical IxIR₀/IxIR₁ graphs, maps, HPT certificate/cache records, IxIR₂ diagnostics, and object bytes. The production failure is preserved in a closed 17-constant dependency slice. See [source coverage](source-coverage.md). |
| Direct-recursion recovery | delivered | D1's first schema checks an eager immediate-tail list fold and derives a direct loop from synthetic Ixon. Forward simulation reaches selected IxIR₀; eight source cases retain the established hot/cold reuse observations and complete fresh-process artifact comparison. D2 extends the rejection/fallback matrix to 25 cases. General recognition remains future work. |
| Recovered source-to-physical composition | delivered | D2: `Compilation.sourceRefinesSelected` derives actual selected physical IxIR₂ execution after recovery and original owned IxIR₁ execution on outer fallback. Common lowering and HPT/CFG attachments supply all intermediate runs and compiler invariants; seven new fences retain the existing axiom basis. |
| Selected terminal resources | delivered | R2: `Compilation.sourceRefinesSelectedWithResources` adds shared-result reclamation to the same source premises and value relation. Actual physical execution gives `live + frees = allocs` at halt and complete release gives `live = 0`, `allocs = frees`. Both selection branches and literal fallback are covered; nine new fences retain the existing trust basis. |
| Comparative allocation and free laws | delivered | R3: `Compilation.sourceRefinesSelectedWithAllocationLaws` compares the actual recovered physical baseline and selected result. For shared mains, `baseline.allocs = selected.allocs + selected.reuses` and the corresponding free equation hold at halt and after complete release. Both selection branches and independent sufficient fuel are covered; twelve new fences preserve the trust basis and R2's endpoint. |
| RC and peak-live bounds | delivered | R4: `Compilation.sourceRefinesSelectedWithCostLaws` proves `selected.rcops ≤ baseline.rcops` and `selected.peakLiveNodes ≤ baseline.peakLiveNodes` for actual shared-main executions and complete release. Every selected prefix is bounded by the actual baseline counters. Both selection branches and independent sufficient fuel are covered without new source premises; seventeen new fences preserve the trust basis and R3's endpoint. |
| Credits across non-tail calls | delivered | R5: explicit v1 validation/execution suspends unique caller-owned reservations through `call`/`callSelf`; v0 retains its rejection. The actual compiler-selected shared pass has composed source, reclamation, allocation/free, RC/peak, and all-prefix guarantees. Nine closed source maps exercise hot/cold/mixed reuse, with 35 policy/fallback checks and seven independent artifact-corruption regressions. |
| Static unique reuse | delivered | `UniqueReuse.Compilation.sourceRefinesWithCostLaws` composes checked source erasure, canonical recursor worlds, consuming IxIR₁, and validated IxIR₂ selection. For `n` cons cells, physical reversal uses `n + 2` allocations, `n` reuses, zero RC, and peak `n + 2`, followed by complete release. All physical prefixes have unique reservations and exact allocation accounting; checked fallbacks and independent budgets are covered. Seven source cases, 43 boundary checks, twelve independent corruption regressions, and 24 theorem fences retain the existing trust basis. |
| Borrowed ABI and RC coalescing | next | After reuse ownership requirements stabilize, a checked interprocedural artifact removes RC traffic from a read-only direct-call chain. |
| General credit refinement | next | Relate logical and physical execution for the full credit language beyond the current compiler-selected rewrite trace. Preserve the explicit credit/ownership domain and keep native heap selection separate. |
| IxIR₂ codec and content addressing | next | Strict bounded decoding, canonical encoding, roundtrip/canonicality, and exact versioned preimages before independent IxIR₂ persistence/cache identity or self-hosted reproducibility. |
| Register-allocation validator | next | When the selected machine CFG needs allocation/spills, check interference, call preservation, edge transfers, and spill layout; the scalar leaf need not wait for a general allocator. |
| End-to-end native FIP witness | next | After physical reuse composition and heap/runtime selection, a validated Ixon program runs natively with the checked result and justified memory/capability observations. |
| x86 reference-semantics bridge | deferred | Wake with a pinned reproducible reference-model slice; prove per-form byte decode/execution agreement before retiring the local ISA assumption or substantially expanding v0. |

`plans/isa.md` owns the staged ISA/encoder design;
`plans/whole-program-optimization.md` owns reset/reuse, borrow, and pass-order
choices. A scalar source-to-native exit does not complete the native FIP row.

## M2d — specialization and representation

Activate this tranche once accepted-source measurements identify the needed
transformations and the relevant artifact boundary is stable. The narrow
recursion-recovery experiment in D1 may use IxIR₀ specialization machinery
without activating this entire milestone.

| Deliverable | State | Exit condition |
| --- | --- | --- |
| IxIR₀ˢ specialization | next | Budgeted deterministic variants eliminate one measured higher-order/PAP path without adversarial code growth. |
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

The first scalar native path needs its ABI and object/link boundary. Further
runtime work follows actual emitted-code needs:

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
Its cost model wakes when a named Aiur integration supplies a pinned
operation/cost contract and a representative executable comparison. The v0
syntax freeze alone does not establish that contract. Native and zk may use
different representations, but both must refine the same semantic and
resource contracts.

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

1. **Native heap selection for unique reversal.**
   Define the bounded heap/runtime ABI and select the actual validated unique
   reversal artifact into typed machine operations. Connect those operations
   to the existing source, ownership, and resource proofs, then emit and run a
   source-produced native witness with complete reclamation and measured
   allocation/reuse counts. Preserve scalar selection, all source fallbacks,
   and the artifact/trust gates. General credit refinement, broader unique
   compilation, and an independent IxIR₂ wire identity retain separate gates.

The [development plan](development-plan.md) defines the evidence that closes
these items. Replace each completed queue entry with its successor; keep
proof histories in focused implementation documents.
