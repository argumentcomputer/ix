# Aiur verifier soundness repairs

Aiur's verifier must reject a false result even when a prover supplies trace
rows directly, without running the interpreter. The regressions in
`crates/aiur/src/synthesis/tests/` exercise four supplied-trace failures and
a native Merkle commitment-binding defect.

| Failure | Required invariant | Regression |
| --- | --- | --- |
| An inactive function row supplied a public proof of `3 * 5 = 16`. | Function and memory rows satisfy `multiplicity * (1 - selector) = 0`. | [Inactive rows](../crates/aiur/src/synthesis/tests/acceptance.rs) |
| Self-recursive and mutually recursive rows balanced their own calls without a finite execution. | Calls advance a checked component order, increase a bounded rank, or satisfy a checked unit-counter relation that excludes short self-recursive cycles. | [Self recursion](../crates/aiur/src/synthesis/tests/acceptance.rs), [call ordering](../crates/aiur/src/synthesis/tests/call_order.rs) |
| An empty return at rank seven supplied a public claim with output seven because lookup messages are zero-padded. | Public claims and constrained calls agree with the function's input and output arities; yields agree with their continuation. | [Message shapes](../crates/aiur/src/synthesis/tests/lookup_shapes.rs) |
| An inactive branch's store arguments changed a live call's lookup channel and supplied output seven for a program returning one. | Ungated arguments require a single function with terminal control and one selector. Branching circuits retain argument gates. | [Empty branches](../crates/aiur/src/synthesis/tests/branchless.rs) |
| A large native Merkle cap omitted a shorter matrix: changing its values preserved the commitment, and altered openings verified. | The cap retains the injection layer of every committed matrix. | [Merkle cap coverage](../crates/aiur/src/synthesis/tests/mmcs.rs) |

## Call ranks and witness generation

The general Aiur layout gives each function row six little-endian rank bytes. A constrained call adds
six bytes for `callee_rank - caller_rank - 1` and requests the derived rank
`caller_rank + 1 + gap` in its lookup. The callee's return binds this rank
without a separate callee-rank column or equality constraint. Three byte-pair
lookups range-check each six-byte value. Ranks and gaps are below `2^48`, so
the derived rank is below `2^49`, below the Goldilocks characteristic. The
call lookup therefore cannot wrap around the field to permit a cycle.

Ranked function query maps share a completion counter. Reversing completion
order assigns a ranked root rank zero and gives each constrained callee in
the same component a larger rank.
Promoting an earlier advice query refreshes its completion time after its
children are promoted. Shared callees retain a consistent rank. Witness
workers accumulate their byte-range queries locally; the prover merges those
counts before constructing the binary byte-table trace.

## Checked IxVM component ordering

IxVM enables a compiler pass that computes strongly connected components of
its constrained call graph after lowering and deduplication. An independent
checker validates every constrained bytecode edge: it must advance the static
component order, stay within a component whose endpoints both retain
dynamic ranks, or be a self-edge certified by the unit-counter checker below. It also checks the assignment's size and order bounds. The
native system constructor repeats these checks over branches, defaults and
shared continuations before constructing the AIR and verification key.
The certificate is part of the fixed program, not advice from the prover.

The resulting layouts use these rank witnesses:

| Location | Additional columns | Additional byte-pair lookups |
| --- | ---: | ---: |
| Acyclic or certified counter row | 0; return rank is zero | 0 |
| Other recursive function row | 6 rank bytes | 3 |
| Call to a function without ranks | 0; requested rank is zero | 0 |
| Call across components to a ranked function | 1 callee-rank field | 0 |
| Call within a ranked recursive component | 6 gap bytes | 3 |

A boundary call must still bind its ranked callee's rank through the return
lookup. Replacing it with a constant would break that binding. Within a ranked
recursive component, the bounded rank and gap retain the original strict ordering.
The Lean theorem `CallComponent.wellFounded_calls` in
[the compiler pass](../Ix/Aiur/Compiler/CallOrder.lean) proves that the bounded
static order and bounded dynamic ranks together give a well-founded call
relation. Its premises still rely on activity, exact lookup balance and the
byte-range constraints; it is not a complete AIR extraction theorem.

The compiler recomputes function and shared-continuation layouts before
grouping. In a mixed circuit, acyclic operations reuse recursive members'
rank columns and lookup slots, so rank-range queries are gated only by ranked
members. General Aiur programs retain the dynamic layout unless explicitly
enabled through `Source.Toplevel.componentRanks`.

Function maps without ranks omit completion timestamps and counter updates:
their return rank is always zero. This saves eight retained bytes per query
without changing the relative completion order inside recursive components.
The RAM estimate counts only stored timestamps. Generic Aiur systems without
a component certificate retain timestamps for every function; recursive
ranked components still refresh timestamps after advice promotion. Regenerating the
IxVM, aggregation and recursive-verifier execution sources produces identical
files because instructions and function indices are preserved.

## Checked existing counters

IxVM also enables `Source.Toplevel.counterRanks`. The compiler may omit ranks
from a singleton recursive component when its actual lowered bytecode has one
of two relations on a fixed input or output column:

- Every constrained self-call shifts the chosen input by exactly one field
  unit, in the same direction on every branch.
- Every path with recursion contains at most one constrained self-call and
  returns the chosen output of that call shifted by exactly one field unit,
  with a common direction on all paths.

The [Lean checker](../Ix/Aiur/Compiler/UnitCounter.lean) follows constants,
addition and subtraction by constants, and multiplication by one or between
two constants. Other outputs are unknown. Loads, advice, source types and
function names supply no arithmetic assumptions. It checks every explicit
branch and default. Shared continuations and analysis beyond 256 nested blocks
retain their ranks. Mutual recursion still requires ranks. The
[native constructor](../crates/aiur/src/unit_counter.rs) independently checks
the relation from the bytecode before constructing constraints; an invalid
unranked self-edge is rejected.

Every provider cycle stays within one static component. An unranked recursive
cycle therefore consists entirely of rows of one certified function, using
the same column and direction. A simple cycle of length `m` would imply
`m = 0` modulo the field characteristic. The existing verifier bound on all
lookup slots of all active trace rows gives `0 < m < p`, excluding that cycle.
The Lean cycle lemmas prove this modular argument for the actual Goldilocks
addition and subtraction operations, including wraparound. They assume the
per-edge relation; they do not establish a complete checker-to-AIR extraction
theorem. That interface is covered by independent bytecode checks and supplied
witness regressions.

The pass removes ranks from 68 of the 389 previously ranked constrained
functions in the measured production program. All 83 kernel fixtures retain
their execution outputs and query counts, while their summed unpadded FFT
model falls 2.34%; `Vector.append` falls 2.41% and the separate shard fixture
3.47%. The original function partition is retained. No instruction or function
index changes. Unsupported recursive components retain the existing rank layout.

[Counter regressions](../crates/aiur/src/synthesis/tests/call_order.rs) verify
input counters with sharing and advice promotion, and output counters over
memory lists. They also supply cycles whose local polynomial constraints all
hold and show that the closing lookup fails in both directions, across field
wrap, and with singleton or grouped circuits. The
[checker tests](../crates/aiur/src/unit_counter_tests.rs) cover malformed
indices, zero or mixed steps, unconstrained progress, nonlinear expressions,
multiple recursive outputs, mutual cycles and the analysis-depth limit.

## Function regrouping measurements

The existing partition retains 185 function circuits. Candidate splits and
transfers were evaluated from actual native shapes on all 83 kernel fixtures,
the shard pipeline and seven additional full-closure checks. They were not
retained after proof-size and proving-time comparisons. Twelve extra circuits
saved about 0.44% raw FFT work but grew all four measured proofs about 5–6%.
A two-transfer alternative kept the circuit count fixed and saved only 0.08%
padded work; its four median proving times were 2–9% higher than counters alone,
with overlapping ranges. That small model benefit did not justify changing
the partition.

The retained counter optimization was measured separately in a 36-proof,
three-variant comparison. Across four fixed full-closure claims, its median
process RSS falls 1.7–3.1% and proof sizes fall 1.6–1.7%. Proving-time changes
are mixed, with overlapping sample ranges; these measurements do not establish
a general proving-speed improvement. Every before/counter/experimental proof
verifies. The rejected partition leaves all production grouping data unchanged.

## Lookup grouping

After compiling the constraints, synthesis chooses lookup groups using their
actual polynomial degrees and the configured PCS quotient-degree limit. A
larger group commits fewer stage-2 accumulator columns but can require more
quotient chunks. The deterministic selector accepts a change only if its FFT
cost is no larger than the previous layout at every integer row height,
including height one. Integer comparisons cover the small-height cases and
the slope of the cost for larger heights. This guarantee concerns the FFT
model; higher quotient degrees can increase constraint-evaluation work.

Grouping retains every lookup message, multiplicity, selector gate and rank
check. The consumer bound counts logical lookup slots, independently of the
number of accumulator groups. Derived circuit metadata is updated before
transcript construction and key serialization. The key codec and recursive
verifier already support the selected group sizes and quotient degrees.
Native tests cover the degree limit, key round-trips and altered claims;
recursive-verifier tests exercise quotient degrees two and four together.

Relative to the component-rank layout, modeled FFT work falls on all 83 kernel
fixtures by a median 4.44%: `Nat.add_comm` improves 6.22%, `Vector.append`
9.11%, and the shard pipeline 9.40%. Fixed byte-table rows and main columns
stay unchanged. For the small unary byte table, the same selector chooses
more accumulators at a lower quotient degree because that costs less FFT work.

## Consolidated byte lookups

Byte AND and OR share the XOR table; byte comparison shares the subtraction
low-byte table. The caller keeps one output auxiliary and one lookup slot.
For input bytes `a`, `b` and the claimed output `z`, the requested table result
is:

- AND: `a + b - 2*z`, on the XOR channel.
- OR: `2*z - a - b`, on the XOR channel.
- Less-than: `a - b + 256*z`, on the subtraction channel.

The table binds both inputs to bytes and fixes their XOR or modular difference.
Each affine equation therefore determines the original operation's result
uniquely in Goldilocks: its output coefficient is nonzero (`2` or `256`). This
also forces the comparison result to zero or one without another constraint.
Selectors continue to gate each request. Native and generated execution merge
AND/OR multiplicities into XOR and comparison multiplicities into subtraction.

The binary table retains all 65,536 input pairs. Its main width falls from ten
to seven, stage-two width from ten to eight, and preprocessed width from fourteen
to eleven, with quotient degree two. Surviving channel identifiers are unchanged;
the three removed identifiers remain reserved. Fixed-table activity/height
validation and the lookup-consumer bound remain enforced.

[The native regressions](../crates/aiur/src/synthesis/tests/byte_consolidation.rs)
check every byte pair against the compiled lookup expressions in singleton and
grouped circuits, wrong field outputs, inactive selectors, and both execution
paths' accumulated table multiplicities. Supplied proofs with forged outputs
or non-byte inputs satisfy the local constraints and fail lookup verification.
Honest proofs exercise mixed original/shared channels and verifying-key codec
roundtrips. The table and caller AIR expressions change, so systems, keys and
stored proofs must be rebuilt together.

The measured production program preserves every function/memory shape and all
execution counts across the 83 kernels and the shard. Each proof saves 26,214,400 FFT units. The
83-kernel sum falls 2.06% with raw heights and 1.47% after power-of-two padding;
the median individual raw reduction is 10.91%. All 24 matched full-closure
proofs verify. Proof sizes fall 0.067–0.140%; observed median proving times
fall 0.38–2.91% with overlapping ranges, and process RSS changes are small and
mixed. These timings do not establish a general speed or memory improvement.

## Structural bounds

System construction validates constrained-call arities, continuation yields,
canonical function-index and memory-width domains, circuit membership and
control counts. A circuit must reserve at least as many selectors as its
return/yield leaves, including yields consumed by a continuation.
Each constrained function's return arity is summarized once and reused at
every call site. Public-entry shapes are retained with the immutable program
so verifying a claim's shape takes constant time. Summaries include early
returns from nested continuations and reject inconsistent return arities.

Before checking proof openings, the public verifier validates the claim's
channel, entry visibility and arity. It also requires fixed byte tables to be
active at their exact preprocessed heights, and bounds the total number of
lookup consumers below the field characteristic. The bound includes the
public claim and every slot of each active trace row. Malformed metadata,
integer overflow and a bound reaching the characteristic are rejected.

These additional guards make the counting and byte-range assumptions explicit;
the fixed-table and global-count regressions do not claim another demonstrated
false-result acceptance. See [metadata bounds](../crates/aiur/src/synthesis/tests/lookup_budget.rs)
and [fixed tables](../crates/aiur/src/synthesis/tests/byte_shapes.rs).

## Native Merkle cap coverage

The native binary MMCS injects shorter matrices while walking from the
tallest matrix's leaves toward the root. A cap can stop that walk before a
shorter matrix is included. For an eight-row and a two-row matrix, cap
heights two and above omit the shorter matrix; changing that matrix leaves
the commitment unchanged and altered single and multiple openings verify.

Aiur rejects this geometry before checking openings. With trace log-degrees
`d`, LDE log-blowup `b`, and configured cap height `c`, it requires
`min(c, b + max(d)) <= b + d_i` for every active matrix. The implementation
avoids addition overflow and accounts for the native cap's height clamping.
Fixed-table activity makes the preprocessed matrices part of this check too.

Cap heights at most `b`, including the default root cap, satisfy the condition
without scanning degrees. Larger caps require a linear metadata check. No
AIR, trace width, FFT cost or proof encoding changes. Unsafe configurations
are rejected; the recursive verifier already requires cap height zero.

## Limb addition

The checked successor uses eight byte additions and an eight-byte input key.
Adding two limbs with carry one uses sixteen byte additions in one helper.
In each byte column the two overflow bits are mutually exclusive, so their
sum is still a bit; the [carry tests](../Tests/Ix/IxVM/CarryAdd.lean) include
the corresponding natural-number identity. A zero carry uses the existing
limb adder directly. The list adder accepts only carry zero or one, including
when either list is empty.

Every input and result byte remains checked by a byte-add lookup. The tests
compare against independent integer addition through all byte carry boundaries,
exercise asymmetric/empty tails and invalid carry values, and prove and verify
maximal overflow and both dispatch branches. The radix-2^16 multiplier is
unchanged by this addition optimization.

## Limb multiplication

Schoolbook multiplication streams later product rows into the accumulator,
removing the temporary product and shifted lists. Multiplication carry and
addition carry remain separate. Empty tails retain the existing row builder
and adder, so the result preserves exact list shape, including interior and
trailing zero limbs. The first product row uses the linear row builder.

The shifted accumulator prefix still passes through checked addition with
zero. Loaded fields are not assumed to satisfy byte bounds merely because
of their source type. When adding the incoming product carry overflows, a
checked successor increments the high product limb and explicitly rejects
another overflow. The radix-2^16 multiplier and byte lookup constraints are
unchanged. The entry wrapper stays narrow because its circuit also contains
frequently executed byte and expression helpers.

The [fusion tests](../Tests/Ix/IxVM/FusedMul.lean) prove exact producer/consumer
list equality for abstract arithmetic steps and compare the implementation
with independent natural-number results, boundary cases and the previous
composition. They also verify proofs and reject invalid addition carries.
The list theorem does not prove the Aiur compiler or its arithmetic gadgets.
Scaling tests include repeated operands, where memoization of the previous
product rows can make fusion's wider circuits slightly more expensive even
when it retains fewer queries.

## Substitution regressions

Simultaneous substitution keeps the full substitution list in its memo keys.
Its length determines how many binders are removed; higher indices lower by
that count, and binder depth prevents capture.

The [substitution tests](../Tests/Ix/IxVM/SubstProjection.lean) compare exact
results with an independent natural-number de Bruijn model and a frozen
walker across binders, lets, projections, capture, index lowering and lists
with unused tails. Representative claims also prove and verify. The model
retains the sufficient-prefix theorem for future experiments; production
does not project its substitution keys. That theorem does not certify the
Aiur compiler.

## Host memory and byte advice

`split_u32` obtains its four low bytes from the native field-to-bytes hint.
The production caller still range-checks every byte and reconstructs the
original field element. Both the reconstruction and its maximum value are
below the field modulus, so inputs at least `2^32` fail instead of truncating.
Zero still normalizes to an empty limb list. Removing repeated subtraction
avoids retaining a growing tree of unconstrained queries; the byte checks
and constrained arithmetic are unchanged. [Byte-hint regressions](../Tests/Ix/IxVM/ByteHints.lean)
cover boundary values, incorrect advice and native prove/verify cases.

Query keys and cached function outputs use segmented, per-column byte, u32 or
full-field storage. Widths come from actual canonical field values. A wider
value widens only the active segment; completed segments keep their original
layout. Every lookup still hashes canonical values and compares the complete
decoded key, so hash collisions and alternative field representations cannot
alias distinct keys. Insertion indices, multiplicities and completion
timestamps retain their existing meaning. A memory row's sole output is
its insertion index; that pointer is reconstructed instead of stored.
Insertion checks the pointer and output width before mutating the record.
Logical field counts still include the pointer; encoded payload estimates
exclude its removed storage.

Query completion and memory interning reuse a canonical key hash between
lookup and insertion. Exact key comparison remains mandatory, including
during collisions and table growth. Ordinary inserts encode field slices
directly with checked, fixed-size byte/u32/field writes; the general decoded
view is used when copying a segment during widening. Packed-key comparison
reads canonical integers directly, and array/slice copies choose the decoder
once per row while retaining their shape checks.

The interpreter, generated executors and witness builders decode these
values into their existing field representations. Cache hits decode directly
into stack arrays. The storage encoding adds no trace columns or constraints
and does not change the AIR or verification key. The Rust query-view API does
change, so regenerate all three executors and rebuild them together.
[Storage regressions](../crates/aiur/src/querymap/tests.rs) compare full-width
and packed rows, segment-boundary widening, forced collisions through table
growth, implicit pointer validation, hint promotion, function and memory
traces, and stage-two lookup witnesses.

Record memory estimates count the actual encoded key/output payload, plus
hashes, multiplicities, table-index estimates and retained completion times.
They exclude layout/allocation overhead and temporary coexistence of old and
new active segments during widening; they remain estimates rather than
process RSS bounds.

Function witness construction stores a member index and query index per
active row, sharing function metadata across the member's rows. On a 64-bit
host this reduces per-row metadata from 72 to 16 bytes. Counting active
multiplicities before allocation also avoids geometric vector growth and
metadata for advice-only entries. Row order, selector offsets, multiplicities
and rank bindings are preserved, including advice promotion.

The prover RAM model sums all member-function queries before splitting a
grouped circuit's height. It uses the configured extension-field dimension
for lookup messages and quotient storage, independent of accumulator grouping,
and includes lookup row writers at padded heights plus function metadata.
The [RAM and witness regressions](../crates/aiur/src/synthesis/tests/peak.rs)
cover reordered groups, advice-only entries, shard sizing and extension storage.
The historical RSS calibration remains an estimate requiring recalibration
against the current prover; these corrections do not establish an absolute
process-memory bound.

## Compatibility and validation

The activity, call-order and branch-gating repairs change affected AIR
expressions and verification keys. Rebuild proving systems and keys, and
regenerate stored proofs against the repaired systems. Public claim encoding
is preserved: its omitted rank is zero under lookup padding. Component
specialization also changes the IxVM AIR and key, and extends the internal
Lean/Rust bytecode representation; rebuild both sides of the FFI together.
Counter specialization changes rank columns, call lookups and verification
keys while preserving the existing bytecode representation. Lookup retuning
changes affected stage-2 layouts, quotient degrees and keys,
so it also requires rebuilding systems and regenerating proofs. Byte-table
consolidation changes the caller lookup expressions, fixed table and keys,
while keeping the existing bytecode operations and function layouts.
The byte-advice, carry and multiplication changes alter IxVM
function indices; regenerate its executor and matching systems from the
updated Lean sources. Packed query views also change the internal Rust API
used by all three executors: regenerate and rebuild all three, even though
packing alone leaves the AIR and keys unchanged.

The native regressions cover supplied false witnesses as well as honest
execution, finite recursion, shared callees, advice promotion and grouped
circuits. Component tests also reject forged assignments and displaced
boundary ranks, check the component producer against an independent
reachability oracle on all 512 three-vertex graphs, and run the existing
Aiur proving corpus with component and counter layouts. Run them with:

```sh
cargo test --locked --release -p aiur --features parallel
cargo clippy --locked --release -p aiur --all-targets --features parallel -- -D warnings
lake exe ix codegen --check
lake test -- ixvm-subst-projection ixvm-fused-mul ixvm-carry-add aiur-cross aiur-cost aiur-prove aiur-components ixvm-byte-hints recursive-verifier ix-aggr
lake test -- --ignored ixvm
```

These repairs and regression tests address the defects above. They do not
establish complete compiler preservation or cryptographic soundness.
