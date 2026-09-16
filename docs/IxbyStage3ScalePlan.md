# Path to proving the full Stage 2 guest execution

[CSLib](IxbyStage2CSLib.md) is the preferred workload, with the separately
pinned [Init guest](IxbyStage2GuestConfig.md) retained as a fallback. The
CSLib image was recompiled with its native keys and entrypoints; it accepts
the real proof and rejects a changed claim and trailing proof bytes. Both
workloads fit the original 16-billion-step and 16 MiB proof limits.

| Reference execution | Program bytes | Input bytes | Transitions | Wall seconds | Peak RSS, KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| Init, original pinned guest | 1,002,355 | 9,611,120 | 5,372,353,187 | 710.70 | 1,209,236 |
| CSLib, recompiled guest | 1,016,587 | 4,813,238 | 2,268,502,805 | 300.89 | 548,096 |

The CPU box supplied the reference measurements on 2026-09-15. These are
reference execution, not Flock proving costs or compiler/native refinement
certificates. The target remains a generic, image-independent proving setup
and a proof of the exact approved binary/input/output relation. No complete
Stage 3 proof of either workload has been generated.

A subsequent [complete reference observer run](../flock-stage3/profile/README.md)
matched the same CSLib output and transition count in 345.94 seconds, with
627,068 KiB maximum RSS. It observed 73 locals, 647 continuations, 65-bit
Nats, byte arrays through 4,813,182 bytes, nine constructor fields and three
PAP captures. Its opcode census covers all executed blocks; value maxima
cover inspected operands/locals/returns/applications. These are measurements
for execution-class design, not constrained execution or proving estimates.

## Completed foundations

The entries below record individual component milestones. Their integration
into a complete original-format proof is described in entries 22–24 and the
current-status section below.

1. [Strict functional intake](IxbyFunctionalIntake.md): canonical
   IXBF/IXFI/IXFO, full typed syntax, arbitrary-precision metadata, whole-image
   and value admission, exact byte preservation, explicit static census, and
   independent reference/real-Init regression tests. It is not a constrained
   decoder or a trusted admission oracle.
2. [Wide global fuel component](IxbyFlockWideFuel.md): exact 64-bit
   consumed/remaining accounting, conservation and exhaustion constraints,
   poisoned-padding tests, and real isolated-verifier Flock component proofs.
   It does not yet upgrade the old u32 Exec profile or implement segmentation.
3. [Constrained codec components](IxbyFunctionalCodec.md): exact original-wire
   header metadata, 4,096-bit natural payloads and checked ByteArray ranges.
   Fresh-process Flock proofs bind decoded fuel/byte-array limits to their
   consumers, including the retained Init prefix and I/O ranges. These are
   completed components of gate 1 below, not whole-image circuit admission.
4. [Constrained records and reference checks](IxbyFunctionalRecords.md):
   original constructor/function/block records, transport/value/operand/operation
   prefixes, exact/partial arities, full constructor identities and successor
   frames. Original-source differentials cover every Init block, and isolated
   Flock proofs connect decoded records directly to their consumers. These
   records do not themselves prove grammar or source/registry authentication.
5. [Constrained grammar control](IxbyFunctionalGrammar.md): complete program
   and preorder-forest transitions, exact context/counter continuity, required
   decoder kinds/bounds, payload extents and terminal EOF. Independent original
   source differentials cover the corpus and Init; small complete decoder/state
   chains verify in isolation and reject recomputed state substitutions. Generic
   whole-file dispatch and source authentication are supplied by subsequent
   components below; registry admission and remaining semantic checks are
   still required.
6. [Constrained scalar payloads](IxbyFunctionalScalars.md): checked length/
   cursor packing, the header's exact Nat-bit limit and streaming strict UTF-8.
   Actual decoder/grammar chains bind these consumers, including UTF-8 state
   across chunk boundaries, and reject same-endpoint internal substitutions.
   Source authentication and generic dispatch are supplied by the following
   layers; this scalar component does not establish those links alone.
7. [Authenticated original-byte reads](IxbyFunctionalSource.md): constrained
   chunk selection and BLAKE3 paths bind windows to the original file digest,
   exact offset and length. A separate final-chunk path prevents false length
   claims. The existing header decoder consumes those actual window wires.
   The following dispatcher reuses one authenticated buffer in a small-file
   class. Component 15 adds larger-file shared chunk use; full registry
   admission remains required. The raw digest is not the Exec commitment chain.
8. [State-selected whole-grammar dispatch](IxbyFunctionalDispatch.md): all
   decoder choices, bounds, source requests and cursor advances derive from
   carried state, including intermediate UTF-8 steps. An explicit 1 KiB,
   32-step class proves complete source-bound grammars while hashing one
   shared buffer once. The following layer adds bounded declaration/header
   registries; component 15 adds larger-file authentication. The raw-file/Exec
   commitment bridge remains unfinished.
9. [Source-bound declaration/header registries](IxbyFunctionalRegistry.md):
   state-derived immutable insertion of constructors, functions and owned
   block headers, exact coverage, full constructor uniqueness, entry-frame
   equality and constrained typed reads. Eight small-file proofs and seven
   recomputed wiring rejections connect these records to original bytes.
   Subsequent components add instruction/reference semantics and bounded
   transport values. Scalable registry access and full-image admission remain
   unfinished.
10. [Source-bound instruction/reference checks](IxbyFunctionalReferences.md):
    complete event coverage with final-registry reads, forward/self/tail calls,
    exact/partial arities, owned successor frames and duplicate alternatives.
    Twenty-four small-file proofs and nine recomputed wiring rejections cover
    all instruction/operation forms. The following components add transport
    values and typed executable bodies. Scalable access and the raw-file/Exec
    commitment bridge remain unfinished.
11. [Source-bound typed input/output values](IxbyFunctionalValues.md):
    actual dispatcher events and the checked program registry produce scalar,
    constructor and PAP records with exact payloads/ranges. Completion derives
    parentage, child order, depth and subtree spans; constrained reads consume
    the actual finished arena. Thirty-two proofs in separate Input/Output
    classes and ten recomputed wiring rejections cover bounded forests.
    The following authenticated value component adds record-sized reads;
    complete original artifact admission remains unfinished.
12. [Source-bound typed executable bodies](IxbyFunctionalBodies.md): actual
    checked Program events produce complete owned function/block records,
    ordered operands, scalar payloads, operations, references, projection fields,
    successors and alternatives. Completion checks exact coverage, source spans
    and canonical fields; constrained reads consume the actual finished bank.
    Thirty-six proofs and fifteen recomputed wiring rejections cover the
    component. This completes bounded body materialization. The following
    component adds authenticated code reads; execution consumers and the
    raw-file/Exec commitment bridge remain unfinished.
13. [Authenticated typed code access](IxbyFunctionalCode.md): actual completed
    Program records and the original digest form a constrained BLAKE3 image.
    Typed reads consume authenticated chunks and reuse their handles across
    records, with full root/index binding and no whole-bank input per read.
    Forty-one proofs and eleven recomputed wiring rejections cover the
    original-byte-to-code-digest-to-typed-read chain.
    Sealing remains bounded by the existing loader. Component 15 adds source
    streaming; full semantic admission and execution/memory consumers remain
    unfinished.
14. [Authenticated typed transport values](IxbyFunctionalValueAccess.md):
    the actual completed arena, original transport digest and code digest
    form a constrained BLAKE3 image. The seal connects the arena's program
    registry and context to the code's actual registry. Node/child/root reads
    use reusable chunk handles; untrusted locators are checked against the
    source-derived parent and ordinal. Forty-four honest proofs and nineteen
    recomputed wiring rejections in the joint Input/Output classes cover
    original bytes, code/value seals and typed reads. Full-image admission and
    authentication for execution allocations, locals and continuations remain
    unfinished.
15. [Streaming original-file grammar proofs](IxbyFunctionalStreaming.md):
    bounded batches share authenticated source chunks and preserve all grammar
    and UTF-8 state. The complete original CSLib Program has 1,217 verified
    Flock batch proofs; Input and Output each have one. A fresh process checks
    all three, deriving transport context from the verified Program. The
    Unaggregated Program chain is 492,388,476 bytes; component 16 compresses it.
    Full semantic registry/body/value materialization and execution remain.
16. [Complete native recursive Flock aggregation](IxbyFlockRecursion.md): all
    1,217 retained CSLib Program batches produce one 360,907-byte proof bundle.
    Mixed Boolean/element child verification, complete boundary continuity,
    exact coverage and inherited-claim folds are constrained. The root checks
    genuine Start/Done/EOF and all 98 approved fixed-table families. The full
    server aggregation took 35 minutes and 54,413,188 KiB peak process RSS.
17. [Authenticated cells and batched memory](IxbyFlockMemory.md): full-u64
    addressing, old/new root continuity, exact immutable allocation/read
    bounds, and a fixed whole-record permutation with ordered read/write
    auditing. Fresh-process component proofs reject recomputed path, counter,
    routing and value substitutions. A 512-access depth-40 batch proved in
    417 ms after setup. Execution consumers and full-state integration remain.
18. [Paged frame and code consumers](IxbyFlockPagedExecution.md): frame,
    continuation, tail-call, over-application and copy transitions derive
    actual memory addresses and bind 64-bit fuel. Fresh mixed component proofs
    reject recomputed target, depth, value, caller and fuel substitutions.
    Read-only code/operand/declaration consumers constrain full-width indices;
    the native packed original CSLib image fits these consumers. Source-to-code
    admission and full instruction/value/initialization integration remain.
19. [Ordered instruction batches](IxbyFlockPagedExecution.md): actual code and
    operand reads produce numeric, control, call and return actions; complete
    state records form one exact execution chain, sharing their clocks with
    authenticated memory. A fresh 399,571-byte proof covers 20 physical steps,
    seven logical transitions and final halt. All 57 changed expected words
    and eight locally valid recomputed instruction/clock attacks reject.
    Full original source/input admission,
    output serialization and execution aggregation remain.
20. [Immutable object execution](IxbyFlockPagedExecution.md#immutable-objects-and-application):
    constructor fields, projection, cases, closures and partial/exact/excess/tail
    application now use actual code, immutable allocations and authenticated
    argument copies. A fresh 378,755-byte proof covers 144 microsteps and 37
    logical transitions and rejects nine recomputed object/clock substitutions.
    The native batch runner checks fixed operation/cell quotas before each step;
    15-batch tests preserve pending copies, fuel, the final state and memory root.
21. [Byte instructions and BLAKE3](IxbyFlockPagedExecution.md#byte-instructions-and-streaming-blake3):
    all ten byte-related primitives use authenticated, arbitrarily aligned
    memory ranges, immutable outputs and the original byte limit. Two fresh
    378,755-byte proofs cover conversion/copy/equality and an unaligned
    multi-chunk hash, rejecting 11 recomputed byte/hash substitutions. A
    25-batch hash resumes pending chunk/tree operations with the same digest.
    Full source/input admission, output binding and execution aggregation remain.

22. [Complete paged admission and endpoint binding](IxbyFlockPagedAdmission.md):
    original-byte banks, code materialization, semantic references, full
    constructor-ID uniqueness, typed input and initialization, exact Bytes
    output and artifact commitments have production proof APIs. All 1,227
    original code batches, 994 reference batches, 146 constructor IDs and
    5,695 commitment-bridge batches pass their actual circuits. A fixed IXFP
    descriptor binds original limits and fuel; the endpoint circuit links all
    283 component facts and derives the final digest `S`.
23. [Complete recursive execution](IxbyFlockRecursion.md#complete-paged-execution-aggregation):
    eleven component chains and the endpoint proof now close into one proof
    whose verifier checks every fresh and inherited fixed-table claim. A
    34-byte Bytes identity execution produces a 499,347-byte root; a separate
    CLI execution returning 1,025 bytes produces a 503,683-byte root. Both
    verify independently from the approved setup, expected digest and root
    proof alone. Genuine but incompatible children reject. The CLI implements
    original-artifact commitments, streamed proving, checked reuse, aggregation,
    setup census and final verification. An independently checked countdown
    fixture executes 83 reference transitions across three execution batches
    and produces a 502,515-byte complete root; a budget of 82 fails.
24. [Native advice and larger execution batches](IxbyFlockPagedExecution.md#larger-shared-execution-batch):
    direct native advice is checked against the unchanged Boolean plans in
    tests, and actual proof generation retains all circuit constraints. The
    fixed Shared class has 688 microstep slots, 256 authenticated cells and
    `M=31`. An original-CSLib segment of 118 microsteps and 32 logical steps
    proves in 5.933 seconds, produces 498,939 bytes and verifies freshly.
    Recomputed state-clock and memory-clock attacks reject. A separate native
    prefix generates 150,607 microsteps in 8.172 seconds without proving.
25. [CPU server execution throughput](IxbyFlockPagedExecution.md#cpu-server-throughput-and-cost-breakdown):
    148 actual proof samples pass across two prefix windows, with independent
    local reception of server proofs. Eight workers reach 31.631–33.166
    logical steps per second; sixteen reach 34.767 with 276.663 GiB peak RSS.
    The table census attributes 78.6% of dense field data to switching
    networks and finds a 58.5-fold padded working domain. These measurements
    establish the need to reduce per-instruction proving cost before a full run.
26. [Boolean routing and larger batches](IxbyFlockPagedExecution.md#boolean-routing-and-the-1024-fetch-class):
    three separate classes preserve exact whole-record routing while enabling
    support-aware witness generation. `shared-1024` provides 1,024 Fetch slots
    and 8,128 microstep slots. The first sixteen CSLib batches average 1,057
    logical steps per proof, versus 37 in the previous Shared sample. Leaf
    throughput reaches 292.245 logical steps/second with eight workers,
    8.4 times the previous best short sample. The larger leaves also compose
    through two recursive levels with fresh
    verification and rejection of repeated, reversed and skipped segments.
    The complete 83-step countdown fits one execution leaf and produces a
    502,979-byte root accepted from only the approved setup, expected digest
    and root proof. A dirty-buffer regression covers the padding bug found
    while composing large execution and small commitment proofs.

## Current integration and next measurements

The complete original-format proof path is implemented and has genuine
small-workload proofs. The original CSLib program has a complete grammar
aggregate and conditional execution-segment proofs. **The complete
2,268,502,805-step CSLib execution has not been proved.** Server measurements
show a substantial improvement from the original Shared layout, but do not
yet establish a practical full-run budget. The 1,024-Fetch class reduces the
quota-based floor from 61 million to 1.91 million execution leaves against
the recorded reference profile. At its measured leaf size this still implies
at least 1.17 TB before recursive nodes; other instruction and memory quotas
can require additional leaves. Short-window rates are not complete-run
measurements and exclude native replay, admission, output and aggregation.

The current paged path streams bounded execution segments over depth-40
authenticated memory and accepts original artifacts up to 16 MiB. Its physical
numeric representation is Nat128; the original observed maximum is 65 bits.
These are separate, explicit factories from the retained 64-step legacy Exec
classes. The original binary, functional limits, input and canonical output
remain bound by admission, initialization, finalization and commitments.

1. **Further reduce ordering and instruction-family costs.** Boolean routing
   and the 1,024-Fetch class are implemented and measured. The exact switching
   networks still occupy 81.2% of the larger class's useful field data. A
   smaller consistency argument and workload-specific classes remain the next
   targets. ByteStart/ByteFinish or Resume quotas already end some measured
   batches before their Fetch quota fills. Preserve complete state, memory
   and fuel checks, and compare time and peak memory per logical step,
   including recursive costs. The measured windows do not cover the full
   byte/hash workload.
2. **Long-run operation.** The CLI retains and verifies bounded proof files;
   it currently generates and proves leaves sequentially. `--resume`
   regenerates native state from the beginning before checking cached leaves.
   The bounded benchmark demonstrates shared-setup parallel workers, but the
   CLI still needs a bounded pipeline and native state checkpoints. Their
   implementation must preserve the existing complete state, memory-root and
   global-fuel checks. These operational changes do not remove the measured
   per-instruction proving cost.
3. **Full pinned benchmark.** Generate all original CSLib component proofs,
   aggregate their exact counts, and verify the root in a fresh process against
   the [independently computed original-artifact digest](../flock-stage3/profile/cslib-paged-statement-v0.json). Record setup
   identities, table geometry, wall time, memory, storage and proof bytes.
   Exercise changed artifact, boundary, memory, budget and proof inputs. Keep
   the separately pinned Init artifacts distinct if using the fallback.

Native constraint-to-reference refinement remains a separate correctness
obligation. The native Flock execution proof does not supply that formal
refinement. Terminal FFLONK compression is also a separate later task.
