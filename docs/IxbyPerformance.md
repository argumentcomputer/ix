# IxBy performance priorities for runtime-v2 CSLib

The compiler's new CSLib verifier is [copied into IxBy](../flock-stage4/fixtures/cslib-runtime-v2/README.md):
**1,005,374 program bytes, 672 functions, and 360,337,913 logical transitions**
to the exact expected output. It uses the runtime-v2 array, byte-builder, and
unboxed numeric primitives. This document ranks further optimization
opportunities; their speedups have not been measured.

The [complete reference census](../flock-stage3/profile/cslib-runtime-v2-reference.json),
[exclusive function costs](../flock-stage3/profile/cslib-runtime-v2-costs.json),
and [new native prefix counts](../flock-stage3/profile/cslib-runtime-v2-physical.json)
pin the actual exported bytes. The import checks SHA256 and BLAKE3 against the
compiler record, checks all 672 function counts, and independently reproduces
the original profile and P/B/I/O/S commitments. The complete observation came
from the compiler's chunked reference interpreter. The new local measurements
cover only two short native windows; a complete CSLib Flock proof is still open.

## Scale and the optimization target

The [batch experiment](IxbyBatchTuning.md#longer-executions-and-join-costs)
models the complete 73,731-step synthetic arithmetic fixture at **21.57 logical
steps/s** with arithmetic 4K leaves, one worker, two threads, and cached setups.
Applying that rate to 360,337,913 steps gives **193 days**. This is a scale
illustration, not a CSLib prediction: its instruction mix differs, higher
recursive levels are modeled, and admission, closing, setup, and I/O are excluded.

| Illustrative completion target | Required aggregate logical steps/s | Multiple of that model |
| --- | ---: | ---: |
| Seven days | 596 | 27.6x |
| One day | 4,171 | 193.4x |

The useful objective is elapsed time and memory for a **fixed execution plus
its aggregation**, with all proof components included. Logical transitions,
physical microsteps, circuit words, and wall time measure different costs.

For `B` leaves, the current binary tree has `B - 1` joins. A useful first model is:

```text
time = setup + admission + native_replay + B * leaf_cost
       + floor(B/2) * raw_leaf_join_cost
       + (B - 1 - floor(B/2)) * recursive_join_cost + closing + I/O
```

Leaf cost includes witness generation, proving, and verification. Use measured
costs at the relevant tree levels. The current 4K arithmetic
anchor spends **70.7%** of modeled online time in joins: about 52.69 seconds per
leaf, 155.19 seconds per raw-leaf pair, and 113.43 seconds for the measured
recursive pair. Even eliminating leaf cost entirely would improve this
particular fixed-batch model by only 1.41x. Fitting more work into each leaf
also reduces joins and therefore has a different payoff.

## What the new program spends transitions on

The compiler's own before/after comparison is 2,033,412,182 to 360,337,913:
**82.28% fewer transitions**, a ratio of 5.64 to 1. The older IxBy census
of 2,268,502,805 belongs to a different earlier image and is not that comparison's
baseline. The old `natural`, array-tree, byte-rope, and nibble-conversion costs
should not be presented as future runtime-v2 savings.

These groups contain disjoint function names. Counts include each function's
own instructions, with callee instructions charged to the callee. They include
necessary work and are **not estimates of removable transitions**.

| Current functions | Exclusive Eval transitions | Share of all transitions |
| --- | ---: | ---: |
| `Array.getInternal`, `Array.size`, `Array.push` | 70,343,426 | 19.52% |
| Array extract/append and runtime list/array conversion helpers | 38,129,061 | 10.58% |
| Selected byte/field wire-codec and runtime byte helpers | 44,878,539 | 12.45% |
| Nat power, shift-right, and log2 loops | 15,206,592 | 4.22% |
| `Goldilocks.mul` wrapper | 3,226,245 | 0.90% |

Separately, 56,489,266 transitions (15.68%) are Return/Apply control steps,
which the observer does not attribute to functions. There are 54,202,575
ordinary call operations, 20,862,427 tail calls, 22,543,217 constructions, and
37,512,228 constructor cases. These opcode counts overlap the function groups;
do not add them as independent savings.

## Fresh physical evidence: retuning is necessary

The existing count-only harness executed the copied program through 200,000
physical microsteps, covering its first 48,599 logical transitions. It evaluated
all seven relevant named classes in two adjacent windows. The table reports
average logical transitions per complete leaf, excluding the partial tail.

| Class | Microsteps 0–100,000 | Microsteps 100,000–200,000 |
| --- | ---: | ---: |
| `shared-linked-1024` | 1,069 | 1,184 |
| `arithmetic-768` | 22 | 23 |
| `arithmetic-3072` | 162 | 178 |
| `arithmetic-4096` | 221 | 243 |
| `arrays-768` | 27 | 27 |
| `builders-768` | 26 | 27 |
| `mixed-3072` | 745 | 1,586 |

In the second window every arithmetic 4K leaf stops on `StoreCopy`; every
mixed 3K leaf stops on `ByteRead`. The first window also contains array/builder
bursts. These are early windows, **not a representative full-run sample or
proof timings**. In particular, neither window reaches a BLAKE3 microstep.
The old arithmetic geometry cannot be used to forecast the new CSLib run.

## Ranked opportunities

### 1. Fit physical quotas to the new program, across execution phases

Increase the copy/byte quotas that currently force short leaves. Collect
windows from decoding, key validation, MMCS hashing, and FRI arithmetic before
selecting a class. Optimize the maximum and distribution of short leaves as
well as average occupancy. Keep every family able to make progress.

Sweep 3K/4K and then larger useful batches while tracking all three switching
networks and commitment padding. A bigger fetch quota alone does not help when
copying fills first. Measure leaf plus join cost for the same work. Later,
allow a small verifier-selected set of classes within one chain, with each
child's setup identity bound into recursion; current executions use one class.

**First check:** full-phase occupancy census, then a bounded genuine proof tree
for the best two candidates. This is the nearest implementation opportunity.

### 2. Replace expensive switching networks with cheaper consistency arguments

State, memory-ordering, and tree-authentication routing occupy **68–74% of dense
leaf circuit words** in the tuned layouts; arithmetic 4K is 72.2%. These are
data shares, not measured CPU shares. Current Benes networks use
`N * (2 log2(N) - 1) / 2` switches apiece.

Investigate committed multiset/permutation arguments and separate read-only
lookup checks for immutable code and data. The target is substantially less
work per memory/state event. Memory chronology, read-after-write values,
authenticated roots, multiplicities, and cross-leaf consistency must remain
checked. Challenge-dependent claims need commitments before their challenges.
Flock uses a characteristic-two field, so field compatibility and soundness
must be part of the design.

[Twist and Shout](https://eprint.iacr.org/2025/105) study separate read/write
and read-only memory checks; [Lasso](https://eprint.iacr.org/2023/1216) studies
multilinear lookup arguments. These are candidate design references, not
measured IxBy speedups or drop-in replacements.

**First check:** a soundness design and exact cost census for one replacement,
including recursive verification. This is a major architectural opportunity.

### 3. Make recursive aggregation cheaper

Profile the recursive verifier replay by table and wall time: transcript
hashing, commitment openings, shared matrix claims, and statement handling.
Reduce duplicated work where the approved child setups share structure. Keep
compiled setups reusable across nodes and measure their memory footprint.

Compare binary joins with four/eight-child joins. Fewer nodes alone is
insufficient: a node must check more children and can cross a padding boundary.
Folding or a different accumulation protocol is a larger research option,
requiring an explicit integration and soundness design.

**First check:** actual equal-work trees at several depths, including mixed
leaf/node joins and cached-setup memory. Join cost is already the largest
measured term in the long-run model.

### 4. Fuse interpreter microsteps and keep temporary values off the memory log

`Fetch`, `Resolve`, and `Resume` account for **73.1% of the first 200,000 native
microsteps**. Today an operand can be read into scratch memory and then read
again by its consumer; entering a function copies resolved arguments cell by
cell. Caller locals already stay in their existing bank across a call.

Try common operand/consumer combinations, checked straight-line blocks, and
direct argument transfer. Keep temporary values in circuit wires when their
lifetime allows it. Authenticate the consumed instructions and preserve exact
fuel, errors, branch behavior, and boundary state. This can reduce physical
work while keeping the original program and its logical transition count.

**First check:** count removed microsteps, memory events, and tree parents on
real windows, then prove the replacement against the existing path.

### 5. Inline and specialize small compiler runtime wrappers

`Array.getInternal` and `Array.size` alone account for **61.2 million Eval
transitions (17.0%)**. The former calls the latter, compares the index, branches,
dispatches the array representation, invokes an existing native primitive,
and returns. `Array.push` still dispatches and constructs a wrapper.

Expose the known representation at call sites, inline small wrappers, and
remove redundant checks where source reasoning or the native operation already
establishes the exact required behavior. Extend this to tiny arithmetic and
constructor helpers. Balance inlining against program size and admission cost.

**First check:** a new compiler image and full reference census, with unchanged
expected output and explicit new commitments. This is the clearest remaining
compiler-side target; native array operations themselves already exist.

### 6. Avoid array/list materialization and use bulk collection operations

The selected extract/append/conversion helpers account for **38.1 million
Eval transitions (10.6%)**. `toList` alone executes 17.7 million and constructs
one list node for each element visited. Fuse consumers with array traversal;
use views or bulk operations where source semantics permit them.

Native persistent operations should also be measured for bytes/cells copied,
path depth, sharing, and authenticated parents. Larger branching factors,
chunked traversal, and bulk append/extract are candidates. Preserve aliases
and immutable-update behavior.

### 7. Specialize wire decoding and byte assembly

The selected wire/runtime helpers account for **44.9 million Eval transitions
(12.5%)**. The run invokes builder append 2.59 million times, freeze 976,357
times, and byte slicing 1.72 million times. Measure chunk lengths and total
bytes traversed/copied; operation counts do not reveal their physical cost.

Fuse fixed-width reads/writes and their cursor/bounds work, batch field-array
codecs, and keep slices/builders alive across consumers to avoid repeated
materialization. Builder append/freeze and zero-copy slices are already present.
Preserve canonical encodings, truncation handling, and exact final bytes.

### 8. Lower arithmetic loops and retain useful scalar types

Nat power/shift/log loops account for **15.2 million Eval transitions (4.2%)**.
Recognize constant shifts, powers of two, and bounded arithmetic idioms. A native
replacement needs the exact Nat overflow, subtraction, division, and fuel
contract of its chosen compilation strategy. Observed Nats reach 65 bits;
observed maxima alone do not justify narrowing the program's declared limits.

`Goldilocks.mul` converts both Nat inputs to Field, multiplies, converts back,
and returns. Keep Field values through arithmetic regions where correspondence
permits. Extension-field multiplication is **already** native, with 2.77 million
calls; consider batches of existing field operations or a checked FRI arithmetic
kernel only after measuring its constrained cost and surrounding memory traffic.

### 9. Reduce constructor allocation and immutable-data authentication

The 22.5 million constructions and 37.5 million constructor cases justify
examining representation specialization, elimination of intermediate pairs
and success wrappers, and sharing of constants. These overlap the wrapper and
collection targets above. Separate immutable code/object reads from mutable
frame memory if a cheaper argument preserves the full binding to source bytes
and boundary roots. Measure allocation and live heap growth over the full run.

### 10. Optimize prover kernels and schedule the whole pipeline

Profile witness generation, field arithmetic, commitments/hashing, allocation,
and memory bandwidth independently. Vectorization, buffer reuse, and fewer
copies are candidates; accelerator work should follow a measured hot kernel.
Run leaves and ready joins concurrently with shared cached setups where
possible, and determine the best worker/thread split for available memory.
The measured 4K leaf process peaks at 45.1 GiB and its tree process at 34.4 GiB,
so worker counts cannot be chosen from CPU count alone.

Stream execution witnesses and aggregation, retaining a logarithmic frontier
of completed subtrees plus restart checkpoints. At a hypothetical 4,096 logical
steps per leaf this run already needs roughly 88,000 leaves and as many joins.
Keeping every witness, setup, and proof resident will not scale. Include
admission and output/closing work in the final benchmark.

## Suggested order of work

1. Extend physical profiling across the complete new workload; attribute rows,
   memory traffic, allocation, hash blocks, and batch stops to phases/functions.
2. Retune two candidate geometries and measure equal-work leaf-plus-join trees.
   Start small wrapper/codec compiler experiments against the complete census.
3. Prototype one cheaper routing/memory argument and profile recursive replay.
   These address the largest current proof costs.
4. Revisit larger batches, block fusion, and worker scaling after those costs
   change. Require measured end-to-end improvement at each step.

Reproduction commands and imported evidence are in the
[profile directory](../flock-stage3/profile/cslib-runtime-v2/README.md).
