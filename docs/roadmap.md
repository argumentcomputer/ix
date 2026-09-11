# Compilatr.ix roadmap

Reviewed 2026-09-11. This page owns priorities, delivery state, acceptance
criteria, and activation gates. [Compiler design](compiler-design.md) explains
the decisions; [development and validation](development-plan.md) explains how
to land a change. The [documentation guide](README.md) indexes the contracts
and evidence.

## Mission and direction

Build a self-hosting certified toolchain from Ixon to native and zk targets,
with explicit ownership/resources, content-addressed artifacts, checked
optimization, and a shrinking trusted boundary.

The validated compiler reaches IxIR₁, with checked IxIR₂ and native attachments
for selected source families. Native instruction/stream/object certification,
upstream computations, runtime reversal, scalar functions, and the first
performance experiments are delivered at the scopes listed below. A bounded
physical scalar CFG fragment is delivered; broader runtime/source support
remains open.

The core claim is successful-run forward preservation under the stated source,
ownership, and environment premises. Reference ISA agreement, system linking,
finite resources, observable effects, executable-compiler correctness, and
statement faithfulness retain their separate obligations.

## Current milestone: M2c

The order below sets the next source/native deliverables. Conditional gates
can proceed independently when their prerequisites are available.

| Package | State | Activation and observable exit |
| --- | --- | --- |
| [N3: compositional native lowering](#n3-compositional-native-lowering) | physical scalar source and static capture slices delivered | Runtime source application, one static Word capture, closure reclamation, Nat peeling, branches/joins, direct calls, source-to-ELF contracts, and finite stack sufficiency. Allocating calls, runtime/heap captures, and broader recursion remain extensions. |
| [PERF3: optimization and compiler scaling](#performance-measurement) | first paired optimization delivered; scaling next | The [checked counter fold](performance/counter-fold-2026-09-10/README.md) has source-to-object preservation, full-matrix paired measurements and retained replay, with the byte-identical baseline selectable. Broader scaling experiments retain their own gates. |
| [F1: finite heap and stack](#f1-finite-heap-and-stack) | active for scalar stack; heap extension next | N3 proves sufficient finite stack for nonrecursive scalar calls. General occupied-heap capacity and allocating calls remain open. |
| [I2: canonical IxIR₂ identity](#i2-canonical-ir-identity) | next | Before independent IxIR₂ persistence, cache keys, or self-hosted intermediate-root comparison. Land the strict codec and exact versioned preimages. |
| [I3: modular source certification](#i3-modular-source-certification) | deferred | Wake before increasing the default 512 certificate-candidate limit or attempting the compiler's full source closure. Compose independently checked units and reuse unaffected evidence after a dependency edit. |
| [A1: allocation and spill validation](#a1-allocation-and-spill-validation) | deferred | Wake when an actual selected CFG needs general allocation, moves, or spills. Validate value flow through the allocated program, including calls and joins. |

**State meanings:** delivered is a scoped boundary backed by code and
evidence; active is work in flight; next follows its named predecessor or
gate; deferred waits for its wake condition; blocked needs an external
decision or dependency change. Completing a package moves its compact
evidence into the delivered baseline and replaces it with its successor.

### E1/E2: encoded instructions and objects

[E1 local instruction laws](x86-encoded-instructions.md) and
[E2 certified streams/objects](x86-stream-objects.md) are delivered. The next
reference bridge is **S1**, a reproducible Lean adapter, then **S2**, execution
agreement for the emitted fragment. [S0](x86-reference-model.md) pins and maps
the candidate model. ISA faithfulness and system linker/loader behavior remain
explicit until their corresponding obligations are discharged.

### C3: upstream source progression

Delivered: checked equal-erased-block reuse, three unchanged
[computational native entries](source-native-upstream.md), and
[retained measurements](performance/native-reverse-2026-09-09/README.md#c3-unchanged-upstream-computations)
for the original two entries. `captureClosed` now reaches certified ELF with
exact static Nat capture transport and complete baseline reclamation. Addition
and the Std slice reach recorded source-certificate failures. Further source progression must
retain original bytes/writer pins, exact stage failures, source agreement,
reclamation, fresh artifacts, and affected negative neighbors. N3/PERF2 govern
broader native computation.

### N3: compositional native lowering

The [first scalar source slice](source-native-scalar.md) delivers two runtime
Nat arguments, exact arithmetic with overflow fallback, branches/joins, direct
helpers, finite stack sufficiency, and universal source-to-ELF contracts.
It consumes checked erased source. The subsequent
[physical scalar CFG slice](source-native-physical-scalar.md) delivers
compositional selection and simulation of actual physical IxIR₂: moves,
scalar ownership operations, Nat peeling, jumps/joins, and nonrecursive
direct calls. Its universal source theorem derives the actual closure
application and physical invocation from successful runtime Ixon application,
then reaches ELF execution with a sufficient finite stack and exact Nat
result. The exported closure is fully reclaimed before the scalar body runs.
Seven unary/binary source exports, four separate CFG shapes, 133
source/application/object runs, 76 additional stream runs, and 1,162 linked
native calls exercise this boundary.

The [captured export extension](source-native-captured-scalar.md) adds one
static exact Word capture and one runtime Word argument. A checked closed
initializer identifies the actual PAP, and a checked unary wrapper binds its
capture before calling the selected binary physical function. The universal
source-to-ELF theorem derives application and exact reclamation, including
dead initializer slots. Nine source exports, 171 source/application/object
runs, 135 artifact corruptions, and 1,494 linked native calls cover captures
zero, seven, and the maximum Word across projection, branches, and helpers.
Allocating calls, runtime/heap captures, general occupied heaps, and broader
recursion remain separate. C3 also admits the unchanged closed captured
computation under its supplied-state translation-validation contract.

Acceptance retained for extensions beyond the delivered scalar fragment:

- Declare the admitted instructions, signatures, representations, and control
  flow. Compile runtime scalar arguments, branches, joins, and direct calls;
  prove successful-run preservation for every accepted CFG in that fragment.
- Compose value/register correspondence, block-edge transfers, caller/callee
  frames, and ownership where present. Exercise multiple function/CFG shapes
  through the actual source compiler and selector. F1 covers sufficient stack
  and heap capacity; A1 covers required allocation, moves, and spills.
- Bind the theorem to the actual selected artifact and extend E1/E2 coverage
  to its emitted forms and objects. Keep the reference-ISA and linker/loader
  obligations explicit, and preserve checked rejection/fallback boundaries.

**Nat/Word arithmetic contract:** each extension must specify
the source operations, word widths/signedness, representations, and admitted
input, intermediate, and result ranges. Prove that each emitted operation
implements its source arithmetic on that domain. Arithmetic witnesses
must use runtime operands and test zero, maximum values, conversions,
underflow, and two individually representable operands whose sum overflows.
State and check the entry rejection or runtime fallback contract for values
outside the fast path; exact Nat preservation cannot silently become wrapping
Word arithmetic. A later accepted input requiring unbounded results activates
the bignum extension: small/boxed transitions, limb operations, ownership,
reclamation, and occupied-space costs need their own proofs and runtime ABI.

### F1: finite heap and stack

R4/R5 bound peak live nodes, but a reserved slot still occupies storage.
`live + frees + presentCredits = allocs` does not by itself bound occupied
bytes, allocator overhead, fragmentation, or stack demand. CakeML's space
semantics provides the useful pattern: state resource requirements and relate
sufficient capacity to execution without resource failure.
See [Do You Have Space for Dessert?](https://cakeml.org/oopsla20.pdf).

Acceptance:

- Define occupied storage as live objects plus reservations under a versioned
  layout-size model. Track allocator capacity/overhead and stack demand
  separately from evaluator fuel and from peak-live counters.
- Derive the existing arena requirement `80 + 32 * (n + 2)` bytes from its
  descriptor and cell layout, then prove adequacy for the selected broader
  family. Specify insufficient-capacity behavior separately.
- Include a reservation suspended while a callee allocates, so omitting
  reserved storage is observable. Account for call frames, saved values,
  spills, and any allocator metadata used by that family.
- Preserve the existing peak-live results at their stated scope. A general
  allocator must separately explain freed-slot reuse and fragmentation
  before these bounds become general physical-space claims.

### I2: canonical IR identity

Until this gate closes, native provenance uses the actual IxIR₁ root plus
lowering/pass/native policy versions. Diagnostic JSON and inherited
declaration keys are not independently addressed IxIR₂ bodies.

Acceptance:

- Strict bounded decoding, canonical encoding, roundtrip on the declared
  representable domain, and global accepted-byte canonicality.
- Exact versioned preimages covering signatures, capabilities, schemas,
  layouts, dependencies, policies, block order, instructions, and terminators.
  Canonical block renumbering is a separate checked pass.
- Canonicality, malformed-input, resource-limit, mutation, and fresh-process
  artifact checks before advertising an IxIR₂ wire version or using its
  roots for independent persistence/cache identity.

### I3: modular source certification

The [current certificate policy](resource-budgets.md#certificate-scaling-decision)
checks one bounded source union. The next scaling boundary is reusable checked
units following dependency/SCC boundaries, with recursive groups kept intact.

Acceptance:

- Bind imports/exports and certificate keys to exact source/dependency roots,
  modes/schemas, sharing/checker policies, and required semantic/oracle premises.
  Check each unit's evidence independently and prove that composition supplies
  the closed program's source-preservation result without new trust assumptions.
- Compile at least two units, change one dependency, and reuse unaffected
  evidence while rechecking the dependent cone. Compare with monolithic
  compilation at the declared semantic and artifact layer; reject stale or
  incompatible interfaces and malformed evidence.
- Bound per-unit and aggregate work, measure checking cost and certificate
  size, and demonstrate a larger accepted closure assembled from bounded
  units before increasing the monolithic defaults. Independent IxIR₂ evidence
  persistence requires I2; native linking retains its separate ABI obligation.

### A1: allocation and spill validation

Keep allocation heuristics outside the soundness boundary. CompCert's
validation checks value correspondence through spilling and moves in
addition to assignment constraints; that is the intended strength here.
See [Validating Register Allocation and Spilling](https://xavierleroy.org/publi/validation-regalloc.pdf)
and [CompCert Allocation](https://compcert.org/doc/html/compcert.backend.Allocation.html).

Acceptance is a simulation of the actual allocated CFG, covering operand and
two-address constraints, interference, caller-clobbered and callee-saved
registers, stack-slot separation/alignment, parallel moves, block-edge
transfers, and the unique placement of credit values. Exercise at least a
spill across a call and a join. A coloring check alone does not close it.

## Performance measurement

[PERF1](performance/native-reverse-2026-09-09/README.md) is delivered for
runtime reversal against Lean 4, CakeML, CompCert, GCC, and Clang, with scoped
C3 measurements. The [counter-fold experiment](performance/counter-fold-2026-09-10/README.md)
delivers the first PERF3 optimization pair. Both retain raw data, correctness,
artifact replay, and analysis. [Benchmark design](benchmark-plan.md) owns the
comparison rules; the [implemented protocol](../benchmarks/protocol.md) owns
commands and exact sampling details.

| Package | State | Activation and observable exit |
| --- | --- | --- |
| PERF2: broader native workloads | deferred; admit families as source/native support lands | Cover at least three computational families: an unchanged upstream program, runtime arithmetic/control, and heap traversal. Extend beyond 64 elements only with the required ABI/selector and F1 contracts. Add OCaml; report support gaps and a fixed common comparison subset. |
| PERF3: optimization and compiler scaling | first pair delivered; scaling next | Measure compile/check time, evidence/artifact growth, cache/dependency edits under fixed analysis choices, and paired checked optimizations. Both artifacts must select. Retain neutral/adverse, short-list, and fallback cases; use results to activate M2d/I3 work. |

Correctness and runner smoke tests belong in ordinary CI. Timing regression
thresholds require history on a controlled host; the first shared-host runs
do not establish that history. A speedup is not a delivery requirement.

## Acceptance testing and compiler explanation

These tracks accompany source/native delivery and reuse the existing
generators, reports, and artifact checkers.

| Package | State | Activation and observable exit |
| --- | --- | --- |
| [Q1: generated integration tests](#q1-generated-integration-tests) | next; alongside upstream and ownership extensions | Generate declaration graphs and cross-stage interactions, with replay and shrinking that preserve the property under test. |
| [T1: compiler explanation](#t1-compiler-explanation) | next; use delivered C3 artifacts | An `explain ROOT` CLI reports the last accepted stage, exact rejection, provenance, optimization decisions, and resource charges from actual compiler artifacts. |

### Q1: generated integration tests

Extend the [seeded well-moded generator](well-moded-generator.md) beyond mains
in a fixed declaration environment. Generate bounded declaration/dependency
graphs, repeated erased blocks, sharing and alias patterns, suspended credits,
and supported pass combinations. [Csmith](https://github.com/csmith-project/csmith)
is a reference for systematic generated compiler testing.

Acceptance includes deterministic seeds, replay, and shrinking that retain
the relevant validity assumptions or exact expected rejection. Compare source
and target observations, ownership/reclamation, resource charges, and complete
artifacts at the boundaries exercised. Generate cache operation sequences,
including replacement after indexing, and turn minimized failures into fixed
regressions. Preserve C3's checked repeated-block reuse cases. The
[reviewed cache-read gap](review-2026-09-09.md#2-p2--a-stale-cache-index-undercharges-the-payload-actually-loaded)
remains a target: enforce the selected-read cap before payload allocation,
including changed lengths and record counts. Record generator fragment coverage
separately from universal theorem claims.

### T1: compiler explanation

Start with a CLI over retained reports and provenance maps. For an input root,
show source origin, accepted stages, the first blocking checker/selector with
its exact diagnostic, and address relationships through emitted artifacts.
Explain optional pass selection/fallback with its evidence and resource/growth
charges. Report measured compile/check cost separately from deterministic
artifact data, and provide a replayable case or command.

Acceptance covers an accepted upstream input, an optional fallback, and a
resource or source rejection, with output checked against the actual reports.
Readable names and source locations are optional diagnostic sidecars; they do
not change canonical identities or authorize acceptance. CakeML's
[IR exploration facility](https://cakeml.org/projects.html) motivates exposing
the intermediate stages before building a richer interface.

## M2d: measured specialization and representation

Activate each row from an accepted-source measurement and a concrete checked
proposal. The [counter fold](performance/counter-fold-2026-09-10/README.md)
provides one measured native option with a selectable baseline; general
proposal checking, specialization, field deletion, and unboxing remain gated.
The current measurements do not justify increasing source-certificate budgets.

| Order or dependency | Acceptance criterion |
| --- | --- |
| Interprocedural liveness | Extend block-local last-use checking to bounded function/SCC call/return summaries. Remove one dead scalar parameter across a complete direct-call family while preserving eager evaluation and ownership effects not proved removable. |
| Budgeted IxIR₀ˢ specialization | Eliminate one measured higher-order/PAP path using canonical variant keys and deterministic per-function/SCC/global growth caps. Keep a generic fallback; test adversarial recursion and stable output order. |
| Created-by after liveness | Check allocation lineage separately from possible constructor tags, including reuse, calls, PAPs, cases, and joins. Cover every producer and consumer in each proposed representation group. |
| Field deletion after both analyses | Remove one internal dead field at all producers/consumers; an open-boundary twin keeps its public layout. Preserve semantic constructor identity, eager effects, and destruction of omitted fields. Use a relation that may retain erased source information as ghost data. |
| Unboxing/flattening after field deletion | Demonstrate one scalar-record or address-key improvement with separate exact-Word, layout, alignment, ownership, and ABI obligations. Choose IxIR₂ representation operations versus a small following IR when this concrete consumer requires the decision. |
| [Proof-producing scalar peepholes](#proof-producing-scalar-peepholes), after stable scalar semantics and native measurements | Accept bounded external rewrite proposals only with Lean-checked proofs and side conditions; demonstrate one native improvement while bounding search, checking cost, and code growth. |

GRIN's distinction between semantic liveness, created-by groups, and shape
analysis motivates this order. A target-only decoder cannot reconstruct
arbitrary deleted payloads; the representation theorem must express the
observations actually preserved.
See [A Modern Look at GRIN, §§5–6](https://cyber.bibl.u-szeged.hu/index.php/actcybern/article/view/4101/4018).

Inlining/specialization remains an eager-language proof here: PureCake's lazy
equivalences do not license dropping eager evaluation or duplicating unique
captures. Its verified transformations motivate a bounded, measured policy.
See [Verified Inlining and Specialisation for PureCake](https://cakeml.org/esop24-inlining.pdf).

Record checker cost, certificate/artifact size, code growth, dynamic heap/RC
counts, and native measurements with every optimization claim. Broader case
hoisting, contification, arity raising, CSE, and PAP devirtualization activate
only from a measured consumer; heap forwarding needs alias/lifetime evidence
and devirtualization needs captured-payload evidence.

### Proof-producing scalar peepholes

Wake when a measured accepted native program exposes a scalar rewrite worth
searching for. Keep the proposal search outside the trust boundary; a small
Lean checker must establish refinement in Compilatrix's actual semantics,
including word/range, flag, and failure side conditions. Rejection or budget
exhaustion retains the checked input artifact. Memory, ownership, and credit
rewrites require their own additional contracts before admission.

Acceptance requires one measured native improvement, exact input/output and
proof provenance, invalid-evidence regressions, and deterministic bounds on
search work, proof/checker cost, and code growth. Record runtime distributions
and code size alongside compilation cost. [Alive2](https://github.com/AliveToolkit/alive2)
provides translation-validation ideas; its bounded LLVM checks do not supply
the required Compilatrix theorem.

## Runtime effects and whole-program behavior

Runtime implementation follows selected programs: allocation/reservation,
RC/drop and memory movement first, then required arithmetic/bignums and I/O;
threads/atomics and floats have separate gates. The
[trust ledger](trusted-extern-ledger.md) records each surviving opaque
implementation. Compiler-host hashing and durable sync do not already define
a target-language effect ABI.

| Gate | State | Acceptance criterion |
| --- | --- | --- |
| Observable extern contract | deferred; before certified externs reopen | Start with one byte-buffer operation. Specify ownership/retention, modified memory and frames, emitted event, return/error behavior, and the oracle/environment relation; compose source→IR→target trace preservation. Keep the linked implementation obligation explicit. |
| Behavior strengthening | deferred; begins with the first effectful endpoint | Define the observation vocabulary and prove successful-run trace preservation first. Distinguish source errors, resource failure, compiler rejection, and runner fuel exhaustion. Divergence/reactive behavior and error reflection require later explicit theorems. |
| Linking | deferred; reusable native units or separately shipped runtime | Bind imports/exports to signatures, ownership, layouts, symbol resolution, and compatible environments. Prove linking preserves the corresponding source/target behavior. Content-addressed dependencies and tested ELF pairs alone do not establish this. |

The effect boundary follows the separation between an FFI oracle and its
external implementation in [CakeML's I/O verification](https://cakeml.org/vstte18.pdf).
The behavior and linking gates draw on
[CompCert Behaviors](https://compcert.org/doc/html/compcert.common.Behaviors.html)
and its [separate compilation theorem](https://compcert.org/doc/html/compcert.driver.Compiler.html#separate_transf_c_program_correct).
Clocked functional semantics can support divergence reasoning, but one
fuel-exhausted run is not evidence of divergence; see
[Functional Big-step Semantics](https://cakeml.org/esop16.pdf).

## M3: executable certification and self-hosting

| Package | State | Acceptance criterion |
| --- | --- | --- |
| X1: small executable checker | next after a suitable accepted native family | Compile a pure bounded certificate/codec checker. Connect its source specification and actual source representation to the generated implementation's acceptance result; quantify over admitted inputs and name byte/ISA/loader dependencies. Fence the theorem and compare independent runs, including rejection cases. |
| Theory bridge | next with a pinned public interface | Prove erasure adequacy against public lean4ix and ix's checker-verification interface. Bridge to that theory rather than vendor a local replacement. |
| Mode conservativity | next with the theory bridge | Prove the `many/shared` fragment conservative and that Uses/Owned add no definitional-equality rules. Operational compiler preservation alone does not establish this. |
| [Seed and artifact reproducibility](#reproducible-optimization-and-artifacts) | next before self-hosting | Specify the Gen-0 toolchain, attestation and runtime closure, exact comparison layer, and analysis-choice policy. Compare artifacts across cold/warm caches and supported scheduling orders under that policy. Independent IxIR₂ roots require I2. |
| Full compiler executable and Gen 1 | deferred until source/runtime closure is accepted | Extend X1 to the actual compiler, cover every required recursion form, and compile its closure natively. The resulting compiler must rebuild a successor within a stated practical budget and retain the same checked boundaries. |
| Gen 2 and diverse double compilation | deferred until Gen 1 rebuilds | Compare a self-built successor at the declared byte/address layer, then document an independently seeded comparison. Keep reproducibility, seed provenance, and executable correctness as separate claims. |

CakeML's bootstrap and binary extraction connect logical compiler functions,
their program representations, and generated machine code. X1 adopts that
obligation with a smaller first witness; it is not closed by deterministic
reports or diverse compilation alone. See
[The Verified CakeML Compiler Backend, §11](https://cakeml.org/jfp19.pdf) and
[Binary Code Extraction to Reduce the TCB](https://cakeml.org/itp18-short.pdf).

### Reproducible optimization and artifacts

The [HPT cache contract](hpt-certificates.md#cache-and-summary-identities)
permits different sound post-fixpoints for one query; their summary identities
and enabled optimizations may differ. Define a reproducible mode that either
commits the accepted analysis roots as build inputs or reproduces a specified
deterministic analysis. Pin compiler/checker/producer versions, resource and
logical scheduling policies, target/runtime inputs, and the artifact layer
being compared. The attestation binds source, compiler, certificate/analysis,
and output roots together with the Gen-0 toolchain and runtime dependency
closure.

Acceptance compares complete artifacts from cold and warm caches and from
supported serial, reordered, and parallel execution under that fixed policy.
Exercise stale, corrupt, and valid-but-differently-precise cache records.
Missing committed evidence must be reconstructed with the committed choice or
fail explicitly; alternative analysis roots define different build inputs.
Separately establish semantic preservation for successful compilation with any
admitted cache contents, even when valid analysis choices produce different
code. Emit host timings and cache statistics as separate diagnostics; compare
every byte of the artifacts declared deterministic.

## M4 and other conditional tracks

M4 remains behind the backend spine unless a concrete upstream integration
need makes it necessary sooner.

| Track | Wake condition and first exit |
| --- | --- |
| Frontend/address oracle | A frontend integration need or M3 readiness. Compare complete Ixon environments from upstream and candidate elaboration; then retarget pinned upstream parser/macro/elaborator code. |
| Surface modes and inference | Addressed contracts and diagnostics are stable. Start with explicit annotations; inference is a separate extension. |
| Statement faithfulness | Before certifying what a user reads. A verified printer/round-trip relation connects displayed statements to certified Ixon addresses. |
| Reflection/TCB policy | Before proof-by-evaluation puts compiler execution in the logical soundness boundary. State the additional trust/theorem obligations explicitly. |
| zk/Aiur | A named integration supplies a pinned operation/cost contract and representative executable comparison. Refine the shared semantic/resource observations with target-specific representation and tariffs. |
| Regions/locality | Borrow and reuse measurements expose residual nonescaping-allocation cost. First check an IR prototype, including escape/tail-call/credit safety; require native or zk benefit before an Ixon locality hash roll. |
| Usage polymorphism and mixed field worlds | A real recursor/generic-function or unique-spine/shared-leaf path requires it. Check instantiation and child-world destruction; do not silently generalize the current homogeneous schemas. |
| Freeze/clone representation | C2 or another real path needs unique→shared publication, or a header/layout decision requires it. Decide deep conversion/copy/steal behavior and prove ownership, progress, reclamation, and cost. |
| Capability certificates | Native consumers need compositional rc-free, heap-free, alloc-free, or panic-free guarantees. Define each predicate and resource domain explicitly. |
| Threads/atomic RC | Before an N-thread Ix.Tc comparison. Specify memory ordering, task ownership, and the concurrency relation to the target ISA. |
| Floats | An accepted source/runtime surface requires IEEE behavior. Specify arithmetic and exceptional outcomes before emission. |
| RV64 | A usable reference model, consumer, deployment target, or mature shared backend justifies a second ISA. Reuse the middle-end semantics and allocation contract. |

Track ix/Ixon writer compatibility, lean4ix's public interface, Aiur's cost
contract, and Lean/toolchain pins with reproducible fixtures. External movement
may wake a package; it does not change completion claims by itself.

## Delivered baseline and continuing limits

M2b is complete at its stated semantic boundary. These records link to the
current contracts; detailed proofs, fixture counts, build logs, and measurements
belong in those references.

| Boundary | Delivered scope and continuing limit |
| --- | --- |
| Ingress and identity | Strict [Ixon codecs/sharing](ixon-v2-wire.md), bounded [catalog ingress](catalog-ingress.md), and cycle-safe [IxIR₀/IxIR₁ addressing](ixir-content-addressing.md). The full Std catalog retains a downstream rejection. |
| Validated source and O1 | [Source preservation](simulation-strategy.md), owned IxIR₁, checked [HPT](hpt-certificates.md), and five [shrinking consumers](optimizer-harness.md). Source sharing/oracle premises remain explicit; the optimized universal counter law is `frees ≤ allocs`. |
| Baseline IxIR₂ and R1–R4 | [Checked CFG lowering](ixir2-spec.md), physical baseline transport, selected shared reuse, fallback, reclamation, allocation/free comparison, and RC/peak-live bounds in the accepted compiler domain. |
| C1/N1 | [Bounded coverage](source-coverage.md) and synthetic exact-Word scalar native entries, with complete fresh-process artifacts. |
| C2/C3 | Three [unchanged computations](source-native-upstream.md), including a static Nat capture, reach certified ELF with full baseline reclamation; the original two retain performance measurements. General source/recursor support remains bounded. |
| D1/D2/R5 | [Closed fold recovery](source-recursion.md) and [shared maps across calls](source-call-reuse.md), including source/resource laws and v1 suspended reservations. General nested/mutual recursion remains open. |
| Static unique reuse | [Consuming list reversal](source-unique-reuse.md) for every accepted finite Nat list, with checked fallback, zero RC, reuse, and complete release. |
| Native unique reversal | [Closed native lists](source-native-unique.md) of at most 64 exact Words. Production emission is certified; the family's original source interface ends at typed execution. |
| N2 | [Runtime list reversal](source-native-runtime.md): one object pair, caller-built unique lists of at most 64 Words, entry validation, source-to-object preservation, and full release. |
| N3 scalar slices | [Runtime scalar functions](source-native-scalar.md) with exact arithmetic and overflow behavior; [physical scalar CFGs](source-native-physical-scalar.md) and [static captured exports](source-native-captured-scalar.md) with ordinary source application, exact closure reclamation, branches/joins, direct helpers, and finite-stack source-to-ELF proofs. |
| E1/E2 | [Local instructions](x86-encoded-instructions.md) and [complete streams/ELF](x86-stream-objects.md), including calls, returns, provenance, entry selection, and checked PC32 relocation. Reference ISA, external bodies, and system loading remain explicit. |
| R6 | [General credit refinement](credit-refinement.md) for both policies and every instruction, including prefixes and independent successful budgets. Complete reclamation requires explicit logical root ownership. |
| B1/B2 | [Closed borrowed-call certificates](source-borrow.md) and [structural runtime borrowing](source-borrow-runtime.md), with lender preservation, two fewer RC operations, full reclamation, and unchanged peak. Recursive SCCs and native shared borrowing remain open. |
| PERF1/PERF3 | [Native comparisons](performance/native-reverse-2026-09-09/README.md) and [checked counter folding](performance/counter-fold-2026-09-10/README.md), with full retained data and independent artifact/check/analysis replay. Broader workloads and scaling remain next. |

The [compiler entry-point table](compiler-design.md#compiler-entry-points)
identifies the checked APIs. `Pipeline.compileValidated` supplies source
certification; the broader `Pipeline.compile` does not.

### C2: upstream executable acceptance

Current source coverage and the subsequent C3 transitions are recorded in
[source coverage](source-coverage.md). The dated [2026-09-09 review](review-2026-09-09.md)
preserves the earlier rejection diagnosis.

### R6: general credit refinement

The [credit-refinement contract](credit-refinement.md) owns the public API,
ownership premises, counter laws, and regression evidence.
