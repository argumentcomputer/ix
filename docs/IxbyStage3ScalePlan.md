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

On 2026-09-15 the CPU box is available for testing. These measurements are
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

## Next implementation gates

The [paged admission implementation](IxbyFlockPagedAdmission.md) now adds
original-byte-bank proofs and source-bound packed-code writes to the
foundations above. Three joint parser/code/memory proofs verify in fresh
processes, and all 1,227 original CSLib code batches pass their actual
circuits with the exact packed memory root. Complete semantic reference walks
and full constructor-ID uniqueness now have fresh component proofs; all 994
original reference batches and all 146 IDs pass their actual circuits. Input
materialization now has fresh proofs and produces the exact original initial
memory root, state and parameters. Bytes output and the exact domain-separated
artifact commitment bridge now have fresh component proofs; all 5,695 original
bridge circuits pass. Recursive composition must consume the initialization,
finalization and all linked endpoints, bind the approved original-wire profile
and final statement digest, and cover the full execution proof run.

1. **Constrained binary correspondence.** Define the approved native
   IXBF/IXFI/IXFO execution class and its identities. Constrain canonical
   admission and the actual decoded code/input, or supply an explicit checked
   correspondence for a different representation. A host transcode, renamed
   header, or matching example output cannot establish this bridge. Preserve
   binding to the original image, limits, primitive meanings and result ABI.
   Codec, body/value-record, complete grammar-control, checked payload packing,
   guest Nat-limit, UTF-8 and generic state-selected dispatch are implemented,
   with complete source-bound grammar, declaration/header-registry and
   instruction/reference, typed transport-value and executable-body proofs for
   explicit small-file classes. Authenticated typed code and transport-value
   reads now reuse chunk handles. Complete original-file grammar proofs now
   span the full CSLib Program/Input/Output with shared source chunks. Next
   is their complete recursive composition with the scalable semantic
   admission, execution consumers and artifact commitment bridge.
   Full-Init row differentials and small-file proofs do not close those obligations.
2. **Streaming witness and measurements.** Produce bounded execution batches
   while recording actual opcode frequencies, stack depth, allocations, byte
   traffic, and Nat widths. Keep the untrusted witness generator separate from
   verification. Do not materialize billions of execution steps just to profile
   it. The complete reference control/block census and observed maxima are
   retained in the profiling report above. Bounded execution-memory witness
   generation and full allocation/byte-traffic measurements remain. Static
   limits and native runtime are not prover-cost estimates.
3. **Scalable code and memory authentication.** Replace capacity-wide selector
   scans and full-bank replication with a reviewed access construction for
   code, locals/continuations, and immutable constructor/PAP/byte/Nat records.
   Bounded typed-code and transport-value seals and reusable authenticated
   reads are implemented; full-image sealing, execution allocations and
   local/continuation memory consumers remain required. Authenticated mutable
   cells, immutable allocation and an exact batched memory log are now proved
   independently; connect the actual execution addresses/values and complete
   machine boundaries to these components.
   Record identity, allocation order, field access and repeated reads must be
   constrained. Benchmark code-authentication and representative memory traces
   before choosing capacities or allocating a full circuit. Any new argument
   or backend identity must be explicit; do not bypass admission guards.
4. **Complete bounded execution segments.** Bind each boundary to the same
   program, input and budget, including control/frame state, continuations,
   all relevant arena commitments and allocation counters, and global fuel.
   Enforce an authentic initial state, exact adjacent-state equality, ordered
   coverage without skips/restarts, and a genuine final halt/output. The new
   fuel ledger must consume actual control wires, not prover-selected kinds.
   A local segment allowance must not reset the global semantic budget.
5. **Sound composition.** Verify the complete segment chain; if one aggregate
   Stage 3 proof is required, implement and review its composition relation.
   The [complete parser aggregate](IxbyFlockRecursion.md) now constrains mixed
   child verification, all parser boundaries and inherited-claim folds across
   the full 1,217-batch tree. Adapt this machinery to the complete execution
   segment statement once that relation is implemented and measured.
   A concatenated list of endpoint hashes or an unchecked state-continuity
   claim is not an aggregate execution proof. Version the wider profile and
   proof envelope explicitly, retaining rejection of old/different setups.
6. **Full pinned benchmark.** Regenerate the witness from the pinned CSLib
   image and input, prove within an explicitly admitted resource envelope, and
   verify in a fresh process against the externally expected Exec statement.
   Record setup identities, raw/padded table geometry, witness/proof/verify
   time, peak memory and complete proof bytes. Require negatives for changed
   image, input, claim, memory access, boundary, budget and proof bytes.
   Retain the original Init artifacts and configuration as a fallback; do not
   interchange the two guests' key pins.

The current native factories cap execution at 64 steps, functions at four,
locals at 16, and program/I/O buffers at 512 bytes. Both full guest images
have 681 functions and 73 locals in their largest frame, with the artifact
sizes shown above. Raising constants alone does not address the current
unrolled execution and memory construction. The next measurable milestone is
a representative CSLib execution segment, including authenticated memory,
proved and verified independently before estimating the full proving run.

Source/image/ABI reflection and native constraint-to-reference refinement
remain separate correctness obligations. Experimental proof acceptance does
not close them. Stage 4 terminal compression is a later, distinct task and is
not required merely to produce a native Stage 3 proof.

No paid tier, hardware, storage, SRS, protocol security setting or existing
resource cap is increased by this plan. Admit and measure each new component
before any full-workload proving attempt on the available CPU box.
