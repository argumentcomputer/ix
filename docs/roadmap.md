# Compilatr.ix roadmap

Reviewed 2026-09-10 against the working tree. This is the single source for
priorities, delivery state, acceptance criteria, and activation gates.
[Compiler design](compiler-design.md) explains the enduring decisions;
[development and validation](development-plan.md) explains how to land and
check a change. Focused specifications record implemented contracts.

## Mission and direction

Build a self-hosting certified toolchain from Ixon to native and zk targets,
with explicit ownership and resource models, content-addressed artifacts,
independently checked optimization, and a shrinking trusted boundary.
Compilatr.ix is the project name; Compilatrix is its Lean namespace.

Three unchanged upstream closure programs compile through checked baseline
IxIR₂ with source agreement and complete reclamation. The bounded native heap
endpoint now compiles one parameterized reversal function and runs the same
emitted code on caller-built runtime lists. Checked borrowed calls now reduce
RC operations from 5 to 3 across eighteen closed source chains, with equal
results, complete reclamation, and unchanged peak live heap use. Local E1
instruction proofs now compose through certified complete streams and ELF
objects, including the parameterized source-to-object endpoint. Open shared tag-readers now select
before runtime arguments arrive, with structural source/function/continuation
proofs, exact lender-state preservation, two fewer RC operations, complete
reclamation, and unchanged peak for every admitted owned heap. The broader
Std catalog and upstream recursors retain the specific boundaries recorded below.
Two unchanged upstream computations now reach certified native objects with
successor instructions and direct calls. The first six-implementation reversal
reference and their C3 measurements have complete retained samples, compiler
and memory diagnostics, and independently reproduced artifacts and analysis.

The principal compiler claim is successful-run forward preservation to
machine execution. Existing source theorems retain their explicit sharing,
oracle, and accepted-fragment premises. The N2 endpoint reaches actual
certified object text; older native source interfaces retain their typed
local x86 endpoint. ISA faithfulness and system linker/loader behavior remain
ledgered separately. Finite space, observable effects, error/divergence
reflection, executable-compiler correctness, and statement faithfulness each
need their own theorem.

## Current milestone: M2c

The order below sets the next source/native deliverables. Conditional gates
can proceed independently when their prerequisites are available.

| Package | State | Activation and observable exit |
| --- | --- | --- |
| [N3: compositional native lowering](#n3-compositional-native-lowering) | active; first scalar source slice delivered | Runtime arguments, exact arithmetic, branches/joins, helper calls, universal contracts and complete ELF execution are delivered at checked erased source. General physical IxIR₂ selection remains next. |
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

E0 supplies tested encoding and ELF emission. [E1 is delivered](x86-encoded-instructions.md)
for every emitted form, consuming actual encoder bytes with independent
decoding and local execution proofs. [E2 is delivered](x86-stream-objects.md)
for certified production streams and objects, including the N2 source-to-object
endpoint. CakeML's multi-target work motivates connecting
instruction encoding, intermediate PCs, and machine execution explicitly.
See [Verified Compilation of CakeML to Multiple Machine-Code Targets](https://cakeml.org/cpp17.pdf).

**E1 acceptance:** specify an independent decoder for the emitted forms.
Start with a load/store/branch slice used by the native heap witness. Prove
encode/decode and execution agreement, including operand widths, effective
addresses, signed displacement/immediate checks, instruction lengths, flags,
and modeled failure conditions. Extend the result to every emitted form.
Encoder self-consistency or matching `objdump` output alone is insufficient.

**E2 delivered scope:** kernel-proved translation validation supplies
instruction-boundary integrity, actual text fetch/decode, and injective
symbolic-PC/byte-address correspondence. Complete streams compose internal
calls under concrete stack/data-access conditions. Independent ELF parsing
supplies text, symbols, provenance, relocation and entry interpretation;
checked PC32 application connects named CALL destinations. The N2 source
endpoint consumes actual emitted object execution for every admitted runtime
input. Unchecked APIs, reference-ISA agreement, external procedure bodies and
system linker/loader behavior retain the boundaries recorded in the ledger.

The reference bridge is a separate sequence: **S0** pins a reference model
and maps/tests the local subset; **S1** provides a reproducible Lean adapter;
**S2** proves emitted-fragment execution agreement. Before substantial ISA
growth, record S0 readiness and a concrete route to S1/S2. Local E1 proofs
can begin before an external generator is usable. The local ISA assumption
remains until reference agreement is proved.

The [recorded S0 readiness decision](x86-reference-model.md) pins the Sail
x86 snapshot and maps every emitted form. Reference execution comparison and
the Lean adapter remain pending; the document gives the concrete S1/S2 route.

### C3: upstream source progression

C2's accepted closures and the [reviewed rejection boundaries](review-2026-09-09.md)
provide the starting corpus. Keep the writer pin, original bytes, roots, and
complete source closure attached to every stage result.

**Delivered:** checked equal-erased-block reuse advances addition and the Std
slice to their recorded source-certificate failures. Unchanged `applyClosed`
and `letClosed` pass source agreement, complete physical reclamation,
[structural native selection and certified object execution](source-native-upstream.md).
Their [retained reference](performance/native-reverse-2026-09-09/README.md#c3-unchanged-upstream-computations)
records compile/check costs, IR/HPT and code growth, physical/native counters,
30 blocks of native call timings, and independent replay. Captured closures
keep their checked physical fallback; broader source and N3 acceptance remain
separate. The [measurement decision](performance/native-reverse-2026-09-09/README.md#follow-up-decision)
sets the next optimization and runtime/recursion gates.

Acceptance:

- First, permit checked reuse of exactly equal erased IxIR₀ blocks and member
  identities. Preserve complete producer maps, lookup/semantic audits, and
  protected namespaces; conflicting preimages still reject. Advance pinned
  `addClosed` and the 17-constant Std slice beyond readdressing and record the
  next boundary separately from eventual source acceptance.
- Name one unchanged upstream computational entry and its current failing
  stage. Carry it through validated erasure, checked physical execution, and
  actual native selection, extending the required source and N3 fragments.
  Require source agreement, ownership/reclamation, complete fresh artifacts,
  checked fallbacks, and the affected negative neighbors at each claimed exit.
- Record compile/check cost, certificate/artifact and code growth, runtime
  counters, and native measurements for named accepted inputs. Use this
  measurement gate to activate M2d and further recursion/runtime extensions.

### N3: compositional native lowering

The [first scalar source slice](source-native-scalar.md) delivers two runtime
Nat arguments, exact arithmetic with explicit overflow fallback, immutable
lets, branches/joins, direct helpers, and reusable contracts for every
accepted function. Finite stack sufficiency and complete ELF execution are
proved. Five synthetic source families pass full source compilation and native
gates. This attachment consumes checked erased source; runtime selection and
simulation of general physical IxIR₂ CFGs remain open.

C3's [closed Nat call selector](source-native-upstream.md) provides structural
known-closure specialization and explicit execution certificates. It does not
close the runtime-argument, branch/join, or general call-contract criteria below.

The current scalar selector and native reversal endpoints recognize exact
graphs or source families. Extend selection to a bounded physical IxIR₂
fragment whose accepted functions compose from reusable instruction, block,
and call contracts. [CompCert instruction selection](https://compcert.org/doc/html/compcert.backend.Selection.html)
provides a structural-pass reference.

Acceptance:

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

**Nat/Word arithmetic contract:** before enabling runtime arithmetic, specify
the source operations, word widths/signedness, representations, and admitted
input, intermediate, and result ranges. Prove that each emitted operation
implements its source arithmetic on that domain. The first arithmetic witness
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

The [benchmark plan](benchmark-plan.md) specifies workload admission, comparison
groups, timing/lifetime boundaries, statistics, compiler/cache measurements,
result bundles, and regression policy. The [first full reference](performance/native-reverse-2026-09-09/README.md)
delivers PERF1 for N2's E2-certified runtime reversal: all six implementations,
38 rows, 30 paired blocks across three sessions, 20,520 reversal samples, and
180 additional C3 call samples. Its 0–64-element unique-list domain and exact
Word payloads remain explicit. Independent source/environment replay rebuilt
identical objects and executables, reran full correctness, and regenerated the
analysis byte for byte; the digest-addressed archive also passed extraction
and relocated analysis.

| Package | State | Activation and observable exit |
| --- | --- | --- |
| PERF1: first native benchmark suite | delivered; 2026-09-10 | The linked x86_64 Linux reference includes all five comparison toolchains, entry and lifecycle distributions, memory/code size, compiler/checker costs, uncertainty, complete raw samples, and independent artifact/correctness/analysis replay. |
| PERF2: broader native workloads | deferred; admit families as C3/N3/runtime support lands | Cover at least three computational families including one unchanged upstream program, runtime arithmetic/control, and heap traversal. Extend input sizes beyond N2 only with the required ABI/selector and F1 contracts. Add OCaml, publish support gaps and per-family results, and keep a fixed common comparison subset. |
| PERF3: optimization and compiler scaling | first paired optimization delivered; broader scaling next | The [counter-fold reference](performance/counter-fold-2026-09-10/README.md) delivers one checked rewrite, 38 paired comparisons, code/fixture-checking costs and exact replay. Extend to compiler scaling, evidence/artifact growth and cache/dependency-edit behavior under fixed analysis choices. Require both artifacts to select and retain short-list/adverse and fallback cases. |

PERF1 acceptance:

- Pin source/toolchain/runtime/build inputs and implement the manifest, build
  adapters, independent correctness checker, timing runner, and report generator.
  Check every length 0–64, exact payload boundaries, consuming ownership,
  actual emitted objects, and the affected ABI/rejection/reclamation cases.
- Keep the current validation and counter costs in the main Compilatrix result.
  Preserve Lean's opportunity to reuse exclusive inputs. Report language/runtime
  results separately from the C comparison with matched arena behavior, and
  account for allocation and tracing-GC work in lifecycle measurements.
- Collect paired randomized blocks using the plan's timer, lifetime, and host
  controls. Publish distributions, uncertainty, missing/failed rows, memory and
  code size, and a complete replayable result bundle. Require independent
  reproduction of the artifacts/checks and analysis from retained samples.

Early subsets can produce useful numbers before all adapters are ready; PERF1
closes only with all five named comparison toolchains. A speedup is not an
acceptance condition. Correctness and runner smoke tests belong in ordinary CI;
timing regressions use a recorded dedicated host and measured noise thresholds.
The first run used a shared host with three session clusters. Its intervals
describe that run; no dedicated regression threshold is set until controlled
independent history is available.

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
regressions. The [review's repeated-block and cache-read findings](review-2026-09-09.md)
are first regression targets: the cache cap must hold before payload allocation,
including changed lengths and record counts. Correct those boundaries as the
regressions land. Record generator fragment coverage separately from universal
theorem claims.

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

Each row activates separately from an accepted-source measurement and a
concrete checked proposal. The [PERF1/C3 decision](performance/native-reverse-2026-09-09/README.md#follow-up-decision)
identified runtime reversal's entry-time gap against the matched arena C kernels
as the first PERF3 target. The [counter-fold experiment](performance/counter-fold-2026-09-10/README.md)
now proves and measures cancellation of four adjacent reservation/live counter
changes: twelve fewer instructions per cell, 84 fewer code bytes, and length-64
primary paired speedups of 1.3621 for entry and 1.1829 for lifecycle. The full
matrix and unchanged baseline are retained. This is one explicit native option;
the general external-proposal checker and broader scalar rewrites keep the
acceptance criterion below.

General PAP specialization, field deletion and unboxing remain deferred. The
two closed C3 entries already use no native heap, and this experiment has no
generic-versus-specialized native pair. Runtime scalar arguments and direct
calls need N3's exact-Nat/Word and call contracts; broader recursion also needs
its missing source certificates and F1. The measured reversal fixture checking
cost does not justify increasing I3's source-certificate budgets.

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

M2b is complete at its stated semantic boundary. The following M2c foundations
remain delivered; the forward queue extends them rather than reopening them.

| Boundary | Evidence and limit |
| --- | --- |
| Build, ingress, and identity | [Fence](../Compilatrix/Fence.lean), [trust ledger](trusted-extern-ledger.md), strict [Ixon wire/sharing](ixon-v2-wire.md), [catalog ingress](catalog-ingress.md), and canonical [IxIR₀/IxIR₁ identities](ixir-content-addressing.md). The real Std contact currently establishes ingress and a downstream rejection. |
| Validated Ixon→IxIR₁ and M2b optimization | [Simulation strategy](simulation-strategy.md), [restrictions](lowering-restrictions.md), [HPT](hpt-certificates.md), and the five-consumer [optimizer harness](optimizer-harness.md). Source sharing/oracle premises remain explicit. The optimized universal counter law is `frees ≤ allocs`; HPT parameters start at `top`. |
| Baseline IxIR₂ and R1–R4 | [IxIR₂ specification](ixir2-spec.md), [physical bridge](../Compilatrix/IxIR2/PipelinePhysical.lean), and [reuse simulation](../Compilatrix/IxIR2/ReuseLiveSim.lean). Whole-main lowering, credit-free interpretation transport, selected shared reuse, checked fallback, reclamation, comparative allocation/free laws, and RC/peak-live bounds are assembled for the checked compiler domain. |
| C1 and N1 | [Source coverage](source-coverage.md) retains the original bounded Ixon inputs, full fresh-process artifact comparison, and three source-to-native scalar cases. Native selection recognizes exact graphs and exact Word values; these native cases are synthetic. |
| C2: upstream executable acceptance | [Source coverage](source-coverage.md#c2-fresh-closure-classification) now includes three unchanged upstream closure programs accepted through checked baseline IxIR₂, two upstream negative neighbors, and the reviewed original Std transition. The 18-case gate checks source results, complete artifacts, and reclamation. Native selection and broader Std/recursor acceptance remain separate exits. |
| D1/D2 and R5 | [Source recursion](source-recursion.md) covers eight closed eager-list folds with selected physical execution and source/resource/cost composition. [Source call reuse](source-call-reuse.md) covers nine maps with v1 reservations across non-tail calls. General `brecOn`, open entries, mutual/nested recursion, and well-founded erasure retain separate gates. |
| Static unique reuse | [Source unique reuse](source-unique-reuse.md) covers arbitrary accepted finite Nat lists in the closed reversal schema. For `n` cons cells: `n + 2` allocations, `n` reuses, zero RC, peak `n + 2`, and full release, with actual selection and checked fallback. |
| Bounded native FIP witness | [Native unique reversal](source-native-unique.md) connects the actual selected artifact to typed x86 byte-memory execution and eight linked main/release pairs. Inputs are closed compile-time lists of at most 64 exact Words in a fresh arena. Owned results, costs, saved registers, and release are covered. E2 certifies production emission and supplies the generic object bridge; this family's existing source interface still ends at typed execution. |
| N2: native runtime input | [Parameterized reversal](source-native-runtime.md) compiles once and emits one object pair for caller-built lists of up to 64 exact Words. Eight inputs and 203 malformed calls run in one linked process. The source/physical/native relation states input ownership, capacity, permissions, alignment, frames, result agreement, and complete release. |
| E1: emitted instructions | [Local byte execution](x86-encoded-instructions.md) proves all emitted forms, lengths, widths, addresses, flags, memory faults and local control patches through an independent decoder. Twelve axiom fences and a compiled gate cover 31,921 instruction cases, 2,000 branches and all eight runtime main/release inputs. E2 supplies complete streams and ELF interpretation; reference ISA agreement remains separate. |
| E2: streams and objects | [Certified object execution](x86-stream-objects.md) composes complete text, injective byte PCs, nested/reused return slots, independent ELF text/entry/symbol/provenance interpretation and checked PC32 relocation. All production emitters return certificates; the actual N2 source endpoint reaches object bytes for every admitted runtime input. Twenty-three fences, the corruption/execution gate and all existing native gates retain the logical/hash basis. ISA, external bodies and system linker/loader behavior remain explicit. |
| C3: upstream source progression | [Two unchanged upstream computations](source-native-upstream.md) reach source agreement, complete physical reclamation and certified computational ELF execution; six new fences preserve the logical/hash basis. Exact erased-block reuse advances addition and Std to recorded certificate failures. The [reference](performance/native-reverse-2026-09-09/README.md#c3-unchanged-upstream-computations) retains compiler/checker, evidence/code, counter and native call measurements. Runtime arguments, broader recursion and general stack sufficiency remain separate. |
| PERF1: first native benchmark suite | [Full reversal reference](performance/native-reverse-2026-09-09/README.md) compares Compilatrix, Lean, CakeML, CompCert, GCC and Clang in 30 paired blocks, with all 38 rows, memory/GC and code diagnostics, uncertainty and a digest-addressed raw archive. Independent source/environment rebuild, full correctness and byte-identical analysis passed; premeasurement gates passed 805 Lake jobs, 17 compiled commands and 19 x86_64 Linux Nix checks. Shared-host results do not set a dedicated regression threshold. |
| PERF3: first checked optimization experiment | [Reserve/reuse counter folding](performance/counter-fold-2026-09-10/README.md) preserves final general-purpose registers and arena words, every native instruction prefix's safety, and the selected source-to-object contract. It removes twelve instructions per cell and 84 code bytes, with 1.3621× entry and 1.1829× lifecycle paired speedups at length 64 on the recorded host. Both complete correctness matrices, 30 paired blocks/6,840 samples, 813 Lake jobs and 19 Nix checks passed; source/artifact/correctness/analysis replay is exact. The baseline remains the default, and broader compiler scaling and general peephole search remain separate. |
| R6: general credit refinement | [Full credit contract](credit-refinement.md) covers successful execution of the same checked program under both policies, the full instruction language, every physical prefix, and independent successful budgets. Logical root ownership supplies physical ownership and complete shared/unique reclamation. No optimizer trace, per-step callback, or new axiom is required. |
| B1: borrowed calls and RC | [Checked borrowed source calls](source-borrow.md) infer unary shared variants, preserve owned PAP wrappers, and validate every changed body/call site. Eighteen closed source chains execute 5→3 RC operations with equal results, full reclamation, and peak two. These finite source/target execution certificates retain their closed scope. |
| B2: borrowing with runtime arguments | [Structural runtime borrowing](source-borrow-runtime.md) selects accepted open shared tag-readers before arguments arrive. Derived source/function/continuation proofs cover every admitted owned heap, preserve lender state through borrowed prefixes, and establish full reclamation with two fewer RC operations and unchanged peak. Nine source functions serve 144 direct/PAP comparisons; owned wrappers add one control transition. Recursive SCCs and native shared borrowing retain separate boundaries. |

The default production result remains IxIR₁. The
[design reference](compiler-design.md#compiler-entry-points) identifies the
checked IxIR₂, borrowing, recovery, call-reuse, unique-reuse, and native attachments.
Use the validated API for a certified claim; the broader `Pipeline.compile`
does not supply erasure certification.

### E2: certified streams and objects

Delivered through [complete-stream and actual-object execution](x86-stream-objects.md).
Production emission validates every decoded instruction, canonical offset,
branch/call target and relocation, then independently parses and validates
the actual ELF bytes. Successful results carry kernel proofs. This discharges
the certified-output boundary without claiming encoder/writer completeness
for unchecked APIs.

Internal calls preserve a concrete relation between symbolic continuation
tokens and physical stack return addresses. Released slots retain their byte
differences until ordinary stores overwrite them. Complete call traces state
alignment, permissions, active-frame protection and safe data reads explicitly.
The N2 source endpoint reaches parsed object text for every admitted runtime
list, with physical returns, exact provenance, the reversed owned graph,
matching source/resource observations and complete release. It retains the
existing source premises and an initial readable caller slot outside the arena.

Twenty-three axiom fences retain ordinary logical axioms and the existing
indexed-source BLAKE3 boundary. The new gate covers 14 complete streams,
50 branch objects, 15 stream corruptions, 1,010 malformed/truncated objects,
10 relocation cases, six stack contracts, a physical caller-slot fault, and
all eight actual runtime object inputs. Existing artifact bytes and identities
pass their unchanged goldens and linked-native checks.

The 2026-09-09 delivery passed the 760-job local build, all fifteen compiled
regression gates and all seventeen Nix checks on x86_64 Linux. Reference ISA
agreement, external procedure bodies and system linker/loader behavior remain
explicit. Broader compositional selection and finite space retain their N3
and F1 gates. The subsequent [PERF1 reference](performance/native-reverse-2026-09-09/README.md)
delivers the first performance measurements; broader families and paired
optimization/compiler scaling retain their PERF2/PERF3 gates.

### B1: borrowed calls and RC

Delivered for the [closed shared tag-reader family](source-borrow.md), with
both constructor branches and zero through eight acyclic forwarding
functions. Bounded inference reconstructs and checks every affected body,
call site, block capability, and owned entry wrapper. Conservative root
retains/releases disappear only after that rewrite passes validation;
projected-field retains stay intact. Root escape, invalid local tail-lender
lifetimes, and later take/reset requirements reject a candidate.

The optional source attachment derives exact Ixon and physical execution
certificates, scalar result agreement, complete reclamation, strict RC
improvement, and nonincreasing peak live heap nodes. All eighteen source
cases execute 5 baseline RC operations and 3 selected RC operations, with
three allocations/frees and peak two. Wrappers add three control transitions
and increase stored code; the complete costs and inference work are reported.
B2 below supplies a structural open-input proof for this family. Recursive
SCCs remain outside both packages. The family is not selected by the current
native backend, so no native RC measurement is claimed.

The independent gate compares complete fresh artifacts, reconstructs the
caller/callee rewrite, and replays every physical heap/control transition
with a separate interpreter. Twelve boundary negatives, one field-retain
preservation guard, three source fallbacks, and thirteen artifact corruptions
pin the scope. Ten axiom fences preserve the existing logical/hash basis.
The 2026-09-08 delivery passed the 654-job local build, all twelve compiled
regression gates, and all fourteen Nix checks on x86_64 Linux.

### B2: borrowing with runtime arguments

Delivered for the [open shared tag-reader family](source-borrow-runtime.md).
The ordinary validated source compiler produces the baseline; structural
recognition certifies its actual erased source graph, every inferred parameter
summary, affected caller/callee body, and owned PAP wrapper. Selection takes
neither runtime arguments nor replay fuel and requires no missing-simulation
callback. Optional failure retains the complete checked baseline.

Reusable function/continuation proofs derive actual executions for every
admitted heap. Every borrowed prefix preserves the exact caller store,
including aliases and the ownership/view facts needed for later take/reset.
The owned-entry contract requires one external shared root owning the whole
allocation-ordered heap, balanced allocation accounting, and a valid saved
peak. Payload descendants have no size bound in the theorem. Root ownership
constructs release fuel, both runs fully reclaim the input, and borrowing
removes exactly two executed RC operations without changing the peak. The
source composition retains the existing sharing/oracle, argument-relation,
and successful-application premises.

Nine source functions with zero through eight acyclic forwarding calls serve
72 runtime inputs and 144 direct/PAP comparisons. Direct RC counts range from
3→1 to 35→33. Owned wrappers add one control transition; the full declaration,
block, instruction, and heap-work costs are reported. Nine aliased lenders,
a positive borrow-then-reset caller, eight structural/lifetime guards, all
twelve B1 negatives, and four source fallback policies exercise the boundary.
The independent gate compares all ten files from fresh processes, rebuilds
every rewrite and runtime heap/control prefix, and rejects twenty corrupted
artifacts. Fifteen axiom fences retain the existing logical/hash basis.

The 2026-09-08 delivery passed the 686-job local build, all thirteen compiled
regression gates, and all fifteen Nix checks on x86_64 Linux. The actual scalar
native selector rejects both artifacts at `missingConstructorSchema`; no
native RC or latency improvement is claimed. A later accepted family needing
recursive SCCs, mixed/multiple parameters, effects, or native shared borrowing
must extend the structural, lifetime, and resource contracts at that boundary.
Peak live nodes do not discharge F1's occupied-byte or stack-capacity gate.

### N2: native runtime input

Delivered for the [canonical parameterized unique-list reversal](source-native-runtime.md).
The compiler certifies the source function and selects the actual checked
physical IxIR₂ export. One native reversal/release pair serves all runtime
inputs; its source, graph, and versioned ABI/policy identities contain no input
payloads. The source-argument relation retains explicit sharing/oracle and
successful-application premises and connects the admitted input to preserved
caller state, the reversed owned result, matching costs, and full release.

The bounded ABI admits at most 64 exact Word payloads in an arena of at most
66 cells. The caller constructs the input; reversal performs one accumulator
allocation and `n` reuses with zero RC operations. Length and capacity rejection
have exported-entry proofs with exactly unchanged memory. Other malformed
headers and links are covered by read-only guard composition and the rejection
matrix. General open heaps, shared native RC, larger inputs, and additional
source shapes remain separate extensions.

The independent gate compares complete artifacts from two fresh processes,
reconstructs canonical preimages, decodes the single object pair, and links it
once for eight runtime inputs, complete reclamation, and 203 malformed calls.
Six adapter/selection negatives and 17 artifact/observation corruptions are
checked separately. Sixteen axiom fences retain the existing logical and
addressed-source hash boundaries. The 2026-09-08 delivery passed the 632-job
local build, every compiled regression gate, and all 13 Nix checks on x86_64
Linux. E2 now composes the source theorem through certified object text for
every admitted runtime input, including physical returns and parsed
provenance. Reference-ISA agreement and system linker/loader assumptions
remain active.

### C2: upstream executable acceptance

Delivered for the [pinned upstream closure family](../fixtures/ixon-upstream/README.md):
fresh arguments, shared captures, and let-bound closures produce Nat 3, 2,
and 4 through the actual checked baseline IxIR₂. The writer revision,
original bytes, roots, complete closures, and independent upstream kernel
checks are recorded. A second clean upstream project reproduced all five
exports and manifests; fresh Compilatrix processes compare all retained graphs,
address maps, HPT records, stage observations, and complete reclamation.

The diagnosis found that the usage checker classified fresh reusable lambdas
as unique even when their captures and results were shared. The corrected
classification uses the existing shared PAP representation. The actual checker
inversion and two axiom fences establish its parameter, result, and capture
conditions without introducing freeze or unique callable values.

All original Std bytes remain pinned. Its 17-constant slice now passes usage
and raw erasure, then reaches an IxIR₀ reserved-identity collision before
erasure certification. Upstream `Nat.add` reaches the same boundary;
explicit `Nat.rec` fails erasure coverage. The full 54-constant contact retains
a later usage rejection. The accepted closure entries use baseline policy;
the scalar native selector reports `missingConstructorSchema`.

Generalize recursion recovery when evidence identifies the next entry/minor
shape. Well-founded erasure and recovery of an already-erased recursor image
remain different obligations. The [coverage record](source-coverage.md) and
[restriction ledger](lowering-restrictions.md) state the exact scope.

### R6: general credit refinement

Delivered for `call-local/0` and `suspended-direct-calls/1` through the
[public checked-program API](../Compilatrix/IxIR2/CreditRefinement.lean).
Allocation history relates live heaps and saved registers; every present
physical credit owns a distinct empty slot across active and suspended frames.
The full allocation/free/RC and peak-live laws hold through branches, loops,
applications, and nested calls. Complete reclamation states logical
`RootOwnership` explicitly rather than deriving it from validator acceptance.

The [regression gate](credit-refinement.md#regression-and-trust-boundary)
checks 25 accepted program/policy combinations, including multiple credits,
reordered back edges, mixed shared/unique reuse, hot/cold reset, both discard
paths, nested calls, and borrowed parameters. Ten axiom fences retain only the existing
logical axioms. The 2026-09-08 delivery passed the 592-job local build, all
compiled regression gates, and all 12 Nix checks on x86_64 Linux. Existing
source and native endpoints passed their gates unchanged.

The [validation guide](development-plan.md) lists the reproducible check
surface; the [R6 record](credit-refinement.md) gives the exact domain and API.
