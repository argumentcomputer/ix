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

The general Aiur layout gives each function row three little-endian u16
rank limbs. A constrained call adds three limbs for
`callee_rank - caller_rank - 1` and requests `caller_rank + 1 + gap` in its
lookup. The callee's return binds this rank without a separate callee-rank
column or equality constraint. Three scalar u16 lookups range-check each
48-bit value. Ranks and gaps are below `2^48`, so
the derived rank is below `2^49`, below the Goldilocks characteristic. The
call lookup therefore cannot wrap around the field to permit a cycle.

Ranked function query maps share a completion counter. Reversing completion
order assigns a ranked root rank zero and gives each constrained callee in
the same component a larger rank.
Promoting an earlier advice query refreshes its completion time after its
children are promoted. Shared callees retain a consistent rank. Witness
workers accumulate their scalar u16 range queries locally; the prover merges
those counts before constructing the binary byte-table trace.

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

| Location | Additional columns | Additional scalar u16 lookups |
| --- | ---: | ---: |
| Acyclic or certified counter row | 0; return rank is zero | 0 |
| Other recursive function row | 3 u16 rank limbs | 3 |
| Call to a function without ranks | 0; requested rank is zero | 0 |
| Call across components to a ranked function | 1 callee-rank field | 0 |
| Call within a ranked recursive component | 3 u16 gap limbs | 3 |

A boundary call must still bind its ranked callee's rank through the return
lookup. Replacing it with a constant would break that binding. Within a ranked
recursive component, the bounded rank and gap retain the original strict ordering.
The Lean theorem `CallComponent.wellFounded_calls` in
[the compiler pass](../Ix/Aiur/Compiler/CallOrder.lean) proves that the bounded
static order and bounded dynamic ranks together give a well-founded call
relation. Its premises still rely on activity, exact lookup balance and the
rank-limb range constraints; it is not a complete AIR extraction theorem.

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
ranked components still refresh timestamps after advice promotion. Timestamp
omission alone preserves instructions and function indices and requires no
generated-source changes.

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

At `ec8432ee`, the pass removes ranks from 68 of the 389 previously ranked
constrained functions in the measured production program. All 83 kernel
fixtures retain their execution outputs and query counts, while their summed unpadded FFT
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

At `ec8432ee`, the partition retains 185 function circuits. Candidate splits
and transfers were evaluated from actual native shapes on all 83 kernel fixtures,
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

The binary table retains all 65,536 input pairs. At the consolidation step,
its main width falls from ten to seven, stage-two width from ten to eight,
and preprocessed width from fourteen to eleven, with quotient degree two. Surviving channel identifiers are unchanged;
the three removed identifiers remain reserved. Fixed-table activity/height
validation and the lookup-consumer bound remain enforced. The u16 rank
encoding below subsequently adds one main column, making the current width eight.

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

## Bounded BLAKE3 byte reader

`blake3_read_block` separates byte traversal from block compression. Every
caller supplies an empty reverse accumulator and index zero. The reader
returns the remaining stream, accumulator and length after 64 bytes or end
of input. Its only recursive edge increments the index by one, which both
counter checkers verify in the bytecode. The existing field-cycle and
lookup-consumer arguments allow its row ranks and gap lookups to be omitted.

The per-byte circuit has three inputs, 15 main columns and eight stage-two
columns, versus seven inputs, 29 main and 20 stage-two columns in the old
loop; quotient degree stays two. The outer loop carries chunk/digest/tree
state once per block; the block driver and its recursive block helper retain
ranks. It passes the old last-byte index to full-block compression and the
consumed-byte count to
partial finalization. Padding and chunk/root flags are preserved. Hashing
and deserialization continue to use the same materialized byte stream.

Production adds one singleton reader circuit (185 → 186), with 758 constrained
functions and 321 still ranked. All existing function query counts remain
unchanged except the block driver; memory trace heights are unchanged.
Across all 83 measured kernels, summed FFT work falls 4.80% raw / 4.66% padded;
the shard falls 7.24% / 9.29%. All measured fixtures improve in both models.

[The reader regressions](../Tests/Ix/IxVM/Blake3Reader.lean) compare block/chunk
boundaries against Rust BLAKE3, including padded bytes, exact remainders and
wrong content digests. Twelve proofs and 184 assertions pass with ordinary
reader ranks and checked counters; the existing hash and full IxVM suites
also pass. All 24 matched full-closure benchmark proofs verify. Vector's
median proving time falls 4.86% and process peak RSS 3.18%; large multiplication
proves 3.12% faster. Nat and wide multiplication have 1.78–2.29% median proving
regressions with overlapping ranges. Proof sizes grow 0.042–0.233%, and the
three smaller workloads use 0.58–0.70% more median process peak RSS. These
measurements do not establish a universal proving-speed or memory improvement.

## Three u16 rank limbs

The 48-bit rank and gap encoding uses three scalar limbs instead of six
bytes. The packing equation is `lo + 2^16*mid + 2^32*hi`; every limb is
range-checked below `2^16`. This preserves the existing no-wrap and strict
call-order argument. Static component and unit-counter checks, selector
gates, public rank zero, and advice-promotion ordering are preserved.

The existing binary byte table supplies scalar `256*i + j` on a distinct
channel (15), with one additional multiplicity column. The original
byte-pair channel (11) still bounds both `i` and `j` separately. Distinct
channels are necessary: lookup zero padding must not identify a request
for two bytes `(256, 0)` with the valid scalar u16 value `256`.
Preprocessed columns and fixed table heights are unchanged.

All 321 ranked functions and 131 of 186 function circuits narrow; function
indices and all measured execution counts are preserved. Stage-two widths
and quotient degrees are unchanged. `Bytes2` uses eight main and eight
stage-two columns, at quotient degree two. Its extra main column costs
5,242,880 FFT units per proof at blowup four. This fixed penalty makes
41 of 83 raw costs regress by up to 5.06%, while 42 improve. The aggregate
falls 6.48% raw / 6.82% padded, and original-main aggregate raw overhead
falls from 17.57% to 9.96%. Padded costs improve for 49 fixtures and regress
for 34. The shard improves 5.07% raw / 4.56% padded.

All 30 matched proofs verify. Vector proves 4.90% faster with 10.07% lower
process peak RSS; proof sizes shrink 5.28–7.11% on all five claims. Smaller
timings are mixed: Nat is 1.04% slower, `nat_mul_big` 5.38% slower, and wide
multiplication nearly flat. Small process peaks are nearly unchanged;
sampled prove-window peaks vary more. These are workload-specific results.

[The rank regressions](../crates/aiur/src/synthesis/tests/call_order.rs)
exhaust all 65,536 scalar values against every rank/gap position, reject
forged values in each limb and cross-channel byte-pair substitutions, and
verify supplied ranks through `2^48-1` in both partitions and decoded keys.
They also prove ordinary u32 byte packing with and without ranks. Existing
cycle, mixed-group, byte-operation, recursive-verifier and full IxVM suites
pass. The code keeps the bytecode schema and generated instruction sources;
the new layouts and keys require matching rebuilt systems and proofs.

## Unrolled BLAKE3 compression

`blake3_compress` inlines seven fixed rounds and the final digest fold into
one acyclic row. It accepts 128 state bytes without a stage counter. The
shared round helper performs the same eight mixes and message permutation;
each permutation reads a saved old message. The final permutation only
rewires words that the digest does not consume.

The compiled function has no constrained callees. Component validation
therefore checks its acyclic position without a unit-counter argument.
The bounded reader keeps its checked counter, and the recursive block
driver/helper keep their ranks. Byte arithmetic, range checks, lookup
messages, activity/selector gates and arity/cap/consumer bounds are preserved.
The existing branchless rule applies to this one terminal, single-selector
function; its predicate and degree limits are unchanged.

The compression shape changes from 533 main / 194 stage-two columns to
2,738 / 690, at the same quotient degree four. Its unique rows fall exactly
eightfold on all 84 measured fixtures; all other function/memory counts
and shapes are unchanged. Across 83 kernels the FFT sum falls 9.99% raw /
10.38% padded, with every fixture improving. The shard falls 15.79% / 17.14%.
The resulting kernel raw sum is 1.03% below the fixed original-main baseline.

The tradeoff is larger proofs and slower verification. In an 80-proof,
four-layout comparison, full unrolling gives Vector a 5.25% lower proving
median and 4.36% lower process peak RSS, while proofs grow 19.93–34.40% across
the five claims and verification medians rise 16.07–21.54%. The host was busy;
small timing differences are uncertain. An earlier separate 30-proof run
also observes Vector improvements (5.00% proving, 3.53% process RSS).
Small process peaks are nearly unchanged and sampled peaks are mixed.
Two-round rows save 3.38% raw / 3.50% padded FFT work with 4.15–7.23% larger
proofs; four-round rows save 5.51% / 5.69% with 12.40–21.27% larger proofs.
Full unrolling is selected for its FFT and large-workload proving gains.

[The compression regressions](../Tests/Ix/IxVM/Blake3Rounds.lean) compare
thirteen word states against independent wrapping-UInt32 arithmetic and
source/native execution with counter specialization enabled and disabled.
Eight new proofs verify, and the compiled-callee check establishes acyclicity
directly. Rust BLAKE3 boundary digests, reader proofs, generated-code parity,
recursive verification, aggregation and the complete IxVM suite pass.
This is source/implementation validation, not a complete AIR extraction theorem.

## Two u16 limbs for u32 comparison

`U32LessThan` uses two scalar u16 limbs for each of `a`, `b` and the witness
`c`, replacing twelve byte columns with six limb columns. Six range queries
use the existing scalar channel; the fixed table and lookup counts do not
grow. Recomposition bounds both inputs below `2^32`. Two boolean carries
establish `a + c + 1 = b + carry * 2^32`, with `0 <= c < 2^32`, so the result
`1 - carry` is exactly `a < b`, including equality and u32 endpoints. These
integer sums are below the Goldilocks characteristic. Selector gates and
the separate byte-pair channel are preserved.

Execution records all six scalar multiplicities once. Witness construction
writes the six corresponding messages, while rank ranges remain separately
collected. Advice promotion records the queries only when the call becomes
constrained. Native and generated execution retain checked u32 conversion.

Auxiliary maxima shrink in 60 functions and main widths in 12 circuits.
Function indices, component assignments, ranks, all function/memory counts,
stage-two widths, quotient degrees and fixed table shapes are unchanged on
all 84 fixtures. The 83-kernel sum falls 0.32% raw / 0.34% padded, and the
shard falls 0.26% / 0.31%. Every fixture improves in both models. The combined
raw kernel sum is 1.34% below original main and 40.95% below the initial repair.

All 40 matched proofs verify and shrink 0.25–0.51%. The first matrix observes
Vector proving 4.81% slower. A separate eight-pair Vector follow-up verifies
all 16 proofs and measures 0.63% faster median proving with overlapping
ranges, nearly equal process peaks and 0.37% fewer median whole-process
instructions; every pair improves in instruction count. These windows do
not establish a stable proving-speed gain;
the change is retained for FFT and proof-size savings with all bounds intact.

[The comparison regressions](../crates/aiur/src/synthesis/tests/u32_compare.rs)
exhaust all 65,536 scalar values in all six lookup positions and both
partitions. Boundary combinations cover grouped/singleton and ranked/acyclic
layouts, decoded verification keys, wrong public results and input bounds.
Directly supplied witnesses that satisfy every local polynomial but forge
a limb range are rejected by lookup verification. Advice-promotion proofs
check that exactly six scalar multiplicities are recorded. Full Lean,
native, IxVM, recursive-verifier and generated-executor checks pass.
The new AIR and messages require matching rebuilt systems, keys and proofs.

## Separate Let rows in expression lowering

`expr_lower_walk` calls a five-input helper for the three recursive children
of a `Let`. The same recursive operations and final store remain, with the
cutoff incremented only under the body. The lowering precondition is
unchanged. The helper stays in the ranked recursive component; both compiler
and native component checks validate the resulting call graph.

The common walk narrows from 34 main / 18 stage-two columns to 30 / 14 at
quotient degree four. A new 23 / 18-column helper uses quotient degree two.
Across 83 kernels it adds 2,212 rows while 544,630 existing walk rows narrow.
All existing function/memory query counts are preserved. There are now 187
function circuits and 322 ranked functions among 759 constrained functions.
Kernel FFT work falls 0.38% raw / 0.39% padded: 80 fixtures improve, three
are unchanged and none regress. The shard falls 0.20% in both models.

All 40 matched proofs verify. Proving medians range from −3.94% to +1.03%,
with overlapping ranges; no stable speed gain is established. Vector's
proof grows 0.23%, while four smaller proof sizes shrink 0.016–0.119%.
Process peak changes stay within 0.21%. A separate 16-run Vector execution
follow-up has effectively unchanged instruction counts and a 1.78% higher
execution median with overlapping ranges. The change is retained for its
FFT saving with these measured tradeoffs.

[Substitution regressions](../Tests/Ix/IxVM/SubstProjection.lean) now include
two proofs that lower whole and nested Lets against an independent Nat-indexed
binding model, including nonzero surrounding depth and retained local
variables. All 10,866 primary, 845 IxVM and both 98-test native suites pass,
including the supplied-trace, recursive-verifier and component regressions.
The additional function shifts internal indices and changes the key;
all three executors and matching systems, keys and proofs must be rebuilt.

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
Three-u16 rank encoding changes function/table layouts, lookup arguments and
keys while preserving the bytecode schema and generated instructions; rebuild
the Lean/Rust systems together and regenerate proofs for their new keys.
Unrolled compression preserves public hashes, claims, function indices and the
instruction schema, but changes its private input arity, layout and keys.
Use the three regenerated executors and rebuild matching systems and proofs.
The byte-advice, carry, multiplication and BLAKE3 reader changes alter
function indices. The reader also changes function layouts; regenerate all
three executors and rebuild matching systems, keys and proofs from the
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
lake test -- ixvm-blake3-reader aiur-hashes ixvm-subst-projection ixvm-fused-mul ixvm-carry-add aiur-cross aiur-cost aiur-prove aiur-components ixvm-byte-hints recursive-verifier ix-aggr
lake test -- --ignored ixvm
```

These repairs and regression tests address the defects above. They do not
establish complete compiler preservation or cryptographic soundness.
