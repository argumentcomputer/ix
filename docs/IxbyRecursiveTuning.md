# Faster recursive fixed-table evaluation

The recursive prover now computes Flock's circuit-structure table marginals
by walking live cells and summing constant planes directly. The previous
evaluator scanned the whole padded eight-plane rectangle for every marginal.
This is an exact native evaluation change: circuit constraints, transcript
messages, approved setups and table claims retain their existing meanings.

## The same execution and the same proofs

Both runs consume the same three `cslib-2048` leaf proofs for physical clocks
**0–20,000**, covering **4,598 logical steps** of the runtime-v2 CSLib image.
They measure every recursive join: one pair of execution leaves, followed
by that recursive node joined with the third leaf.

| Cached work | Original evaluator | Optimized evaluator |
| --- | ---: | ---: |
| Leaf-pair join, including verification | 159.25 s | 19.61 s |
| Recursive-node/leaf join, including verification | 141.01 s | 17.00 s |
| All joins | 300.26 s | 36.61 s |
| Unchanged leaf witness/proof/verification measurement | 87.61 s | 87.61 s |
| Leaves plus every join | 387.87 s | 124.22 s |

The matched join total improves **8.20x**. Combining it with the earlier,
unchanged leaf measurement improves the cached total **3.12x**, from
6.46 to 2.07 minutes. Leaf proofs and timings are reused explicitly; the
experiment reruns aggregation. It does not remeasure leaf production.

Both recursive proofs and statements are **byte-identical** across evaluators
and to the prior [batch-tuning run](IxbyCslibTuning.md). The final 404,083-byte
root retains SHA256
`740e4e4ed6e444f162ce959c8e98c6aeeae3bf1f1a20864be87c435f1a5251bf`.
Its complete 57-word public statement, source parameters, clocks, fuel and
memory roots are unchanged.

Both runs use the same instrumented binary, one proof worker and two Rayon
threads on the Ryzen 9 7950X3D host. Large proof jobs run sequentially with an
84 GiB memory cap and swap disabled. Ordinary tests and Clippy overlapped
optimized setup compilation. These are bounded measurements from one matched
run per evaluator; they do not forecast a full CSLib proof.

Cached totals exclude setup, source admission, complete-run closing and I/O.
Including setup and fresh reception, tree process wall time falls from
**613.89 to 366.44 seconds** (10.23 to 6.11 minutes, **1.68x**). Peak memory is
34.49 and 34.55 GiB respectively, with no swap. The faster evaluator does not
reduce the large proof's memory footprint.

A fresh receiver clears its environment, recompiles the
approved setup and uses the optimized production evaluator in both runs.
The reference switch controls the producer's folds and in-process node
verification. Each fresh receiver rejects all 114 tested public-word
mutations, truncation and trailing bytes.

## Where the time went

The initial profiler separated child transcript hashing, statement binding,
wiring, Boolean/element algebra, commitment openings, fixed-table folds,
Flock proving and final table checks. It found that native fixed-table
evaluation dominated the previous recursive timing.

| Selected work across both joins | Original evaluator | Optimized evaluator |
| --- | ---: | ---: |
| Native fixed-table fold witnesses | 234.98 s | 6.06 s |
| Final fixed-table checks | 35.62 s | 1.00 s |
| Flock proof kernels | 16.59 s | 16.69 s |
| Flock witness preparation | 1.49 s | 1.51 s |

The final matched run attributes approximately **231 seconds** to the three
structure-table folds, versus **1.7 seconds** with the new evaluator. Boolean
matrix and jagged-layout folds use their existing evaluators. The native
Flock proof kernels also retain their prior implementation.

The checked report includes exclusive per-join phase timings and nested
per-family details. Nested phases must not be added to their parent timings.
`PCS_TRACE` also records Flock's commitment, Boolean/element proof, wiring
and opening kernels, including phases that run concurrently.

### Circuit work stays measurable

| Constraint phase, leaf-pair join | BLAKE3 compressions |
| --- | ---: |
| Child transcripts | 11,254 |
| Child public-vector digests | 23,956 |
| Child commitment-opening authentication | 21,700 |
| Fixed-table fold transcript | 34,924 |
| Total | 91,834 |

The first node also retains 2,201,133 arithmetic operations and 44,198 packing
rows; the second retains 66,042 compressions, 1,637,169 arithmetic operations
and 40,445 packing rows. Both use 17 row variables and 32 dense variables.
These are constraint counts, not CPU shares. The optimization accelerates
evaluation of the approved tables without shrinking the recursive circuit.

## Why the faster evaluator is equivalent

The pinned Flock structure table has eight planes:

| Plane | Entry |
| --- | --- |
| 0 | Live cell's identity address |
| 1 | Live-cell indicator |
| 2 | Live cell's wired address |
| 3–4 | Element-table affine constants, independent of row |
| 5 | Boolean-table constant-pin live prefix |
| 6–7 | Zero |

A marginal is a weighted sum along either the rows or the columns. The
[implementation](../flock-stage4/recursive/src/structure.rs) computes both
directions using those exact entries:

- Walk only each cell slot's live row prefix and combine the three address
  planes in one pass.
- Sum the row-independent affine constants once. These constants apply
  across the full row domain, including unused invocation rows.
- Use prefix sums for live indicators, constant pins and identity addresses.
- Retain the declared dimensions and zero padding of every plane.

For an aligned slot base `s * R` and row `r`, the address is `(s * R) | r`.
Their bit ranges do not overlap, so its field encoding equals the sum of the
two encodings in GF(2^128). This permits a prefix sum for the identity plane.
Field addition is exact XOR, so parallel summation changes no values.

The optimized evaluator implements the same `FoldMatrix` interface consumed
by the existing prover and root checks. Its dimensions come from the pinned
reference matrix; it reads the approved circuit's actual live counts, wire
permutation, element constants and Boolean pins. No witness values determine
which rows are live or which entries belong to the fixed table.

## Validation and reproduction

Differential tests compare both complete marginal vectors against the pinned
Flock implementation for Boolean-only, element-only and mixed circuits.
They cover every plane, zero/full/partial invocation counts, nontrivial wire
permutations, public padding, affine constants on both sides, arbitrary
128-bit weights, basis weights and a 512-row case crossing the parallel
chunk boundary. A modified matrix-claim value is rejected.

All five ordinary recursion tests and strict Clippy pass. The real tree runs
add both recursive proofs, unchanged setup identities, byte-for-byte receipt
comparisons and fresh-root mutation/framing checks. Large ignored tests
remain opt-in; this does not claim that the full CSLib execution was proved.

The [machine-readable report](../flock-stage3/profile/cslib-runtime-v2-recursion.json)
checks the original leaf receipts, every join, public boundaries and setup
identities. [Logs, retained proofs and commands](../flock-stage3/profile/recursive-tuning-v0/README.md)
support reproducing the comparison from the same test binary. The reference
evaluator switch is test-only; production uses the optimized evaluator.

## What to optimize next

With these joins, unchanged leaf production accounts for about **71%** of the
cached segment total. Reducing execution rows and improving useful work per
leaf now have a larger share of the measured opportunity. The complete native
profile identifies Fetch/Resolve/Resume as 64.55% of physical rows.

Within recursion, Flock proving and child-advice generation now deserve more
attention. The public-vector digest alone accounts for 26.1% of the first
node's hash constraints; most child public words are fixed setup data.
Specializing those fixed parts is a concrete next circuit experiment. Cheaper
state/memory routing remains the larger architectural opportunity. These
candidates still require their own equal-work proof measurements.
