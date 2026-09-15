# Local path to proving the real Init execution

The unchanged Stage 2 IXBF binary accepted the retained Init proof in
5,372,353,187 reference transitions, with 710.70 seconds wall time and
1,209,236 KiB maximum RSS. The original 16-billion-step and 16 MiB proof limits
were sufficient. The CPU box has been powered off; this phase is local work.

This runtime result is not a Flock proof or a compiler/native refinement
certificate. The target remains a generic, image-independent proving setup
and a proof of the exact approved binary/input/output relation.

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
   class. Larger-file shared chunk use and registry admission remain required;
   the raw digest is not the Exec commitment chain.
8. [State-selected whole-grammar dispatch](IxbyFunctionalDispatch.md): all
   decoder choices, bounds, source requests and cursor advances derive from
   carried state, including intermediate UTF-8 steps. An explicit 1 KiB,
   32-step class proves complete source-bound grammars while hashing one
   shared buffer once. The following layer adds bounded declaration/header
   registries; larger-file authentication and the raw-file/Exec commitment
   bridge remain unfinished.
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
    Scalable access and complete original artifact admission remain unfinished.
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
    Sealing remains bounded by the existing loader. Full-image admission,
    original-source streaming and execution/memory consumers remain unfinished.

## Next implementation gates

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
   explicit small-file classes. Authenticated typed code reads now reuse chunk
   handles. Next are streaming full-image admission, execution consumers and
   the Exec commitment bridge.
   Full-Init row differentials and small-file proofs do not close those obligations.
2. **Streaming witness and measurements.** Produce bounded execution batches
   while recording actual opcode frequencies, stack depth, allocations, byte
   traffic, and Nat widths. Keep the untrusted witness generator separate from
   verification. Do not materialize a five-billion-step trace just to profile
   it. Static limits and native runtime are not prover-cost estimates.
3. **Scalable code and memory authentication.** Replace capacity-wide selector
   scans and full-bank replication with a reviewed access construction for
   code, locals/continuations, and immutable constructor/PAP/byte/Nat records.
   The bounded typed-code seal and reusable authenticated reads are implemented;
   full-image sealing and execution/value-memory consumers remain required.
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
   A concatenated list of endpoint hashes or an unchecked state-continuity
   claim is not an aggregate execution proof. Version the wider profile and
   proof envelope explicitly, retaining rejection of old/different setups.
6. **Full pinned benchmark.** Regenerate the witness from the unchanged Init
   artifacts, prove within an explicitly admitted resource envelope, and
   verify in a fresh process against the externally expected Exec statement.
   Record setup identities, raw/padded table geometry, witness/proof/verify
   time, peak memory and complete proof bytes. Require negatives for changed
   image, input, claim, memory access, boundary, budget and proof bytes.

The current native factories cap execution at 64 steps, functions at four,
locals at 16, and program/I/O buffers at 512 bytes. Init's image has 681
functions, 73 locals in its largest frame, 1,002,355 program bytes and
9,611,120 input bytes. Raising constants alone does not address the current
unrolled execution and memory construction.

Source/image/ABI reflection and native constraint-to-reference refinement
remain separate correctness obligations. Experimental proof acceptance does
not close them. Stage 4 terminal compression is a later, distinct task and is
not required merely to produce a native Stage 3 proof.

No paid tier, hardware, storage, SRS, protocol security setting or existing
resource cap is increased by this plan. Admit and measure each new component
locally before any full-workload proving attempt.
