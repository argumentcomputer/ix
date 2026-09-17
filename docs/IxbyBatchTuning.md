# Paged execution batch tuning

Including recursive joins changes the preferred arithmetic batch size.
Among the tested classes, 4K leads the model for long runs with cached setups,
while 3K offers lower startup cost and memory use.

This experiment measures physical proof batches for the semantics-2 runtime.
The IXBF/IXFI/IXFO formats, 58 primitives, and execution statement are unchanged.
The [compiler handoff](CompilatrixRuntimeV2Handoff.md) remains the language
contract. Batch selection is a separate verifier setup decision.

The compiler's actual runtime-v2 CSLib export is now available. The
[new physical samples and optimization priorities](IxbyPerformance.md)
measure that image separately. The retained CSLib measurements below remain
the earlier header-migrated image; their historical results are unchanged.

The [measurement record](../flock-stage3/profile/execution-batch-tuning-v0.json)
contains the full sweep, held-out census, native batch boundaries, proof
receipts, setup identities, and timing model. Its
[`batch_tuning.py`](../flock-stage3/profile/batch_tuning.py) assembler checks
successful test logs, matches workload hashes, and checks proof statements
against the measured boundaries.

## What a fetch quota means

A fetch quota bounds one execution leaf. It does not limit the complete run.
An execution can span many leaves and recursive aggregation joins their exact
machine states and memory roots.

An instruction can need several physical microsteps: operand resolution,
arithmetic, frame movement, tree traversal, or byte copying. Each family has
its own quota. Distinct memory cells and shared-tree parents impose additional
bounds. A batch stops before any of these bounds would be exceeded; the next
batch resumes the suspended instruction.

The measurements distinguish fetched instructions from **logical steps**,
the semantic fuel charges. Frame transitions can charge fuel without fetching
another instruction. Neither number is the total number of physical microsteps.

## Padding boundaries

The count pass uses the same emitter as the prover. It includes three exact
switching networks:

| Network | Number of lanes |
| --- | --- |
| State continuity | Next power of two of `microstep_slots + 1` |
| Memory ordering | Next power of two of `access_slots + 2 * cells` |
| Shared-tree authentication | Next power of two of `2 * parents + 1` |

With `N` lanes, a network has `(2 log2(N) - 1) * N / 2` switches. Crossing a
power-of-two boundary can therefore cost much more than the added useful work.

The semantics-2 collections increased the original `shared-linked-1024`
class to 10,432 microstep slots and 29,248 memory-access slots. Its state network
has 16,384 lanes; memory ordering has 65,536 because `29,248 + 2 * 2,048 = 33,344`.
Its 1,024 fetch slots often remain partly unused when another family fills first.

The census also caught a capacity error: the three existing large 1K classes
need a row exponent of 16 after the collection extension. They previously
declared 15, causing compilation to reject them. `Shared1024`,
`SharedPacked1024`, and `SharedLinked1024` now use 16 and transcript version 3.
An ordinary test counts the exact emission of every named class and checks its
declared capacity. The other preexisting classes retain their setup identities.

## Selected geometries

All six added classes use shared memory authentication and exact packed state
linking. Every one of the 31 microstep families has a positive quota. A workload
outside the intended mix can still make progress, but may need many short leaves.

| CLI class | Fetch slots | Microstep slots | Cells | Parents | State lanes | Memory lanes | Tree lanes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `shared-linked-1024` | 1,024 | 10,432 | 2,048 | 8,191 | 16,384 | 65,536 | 16,384 |
| `arithmetic-768` | 768 | 3,351 | 512 | 1,023 | 4,096 | 16,384 | 2,048 |
| `arithmetic-3072` | 3,072 | 13,401 | 1,536 | 3,071 | 16,384 | 65,536 | 8,192 |
| `arithmetic-4096` | 4,096 | 17,868 | 2,048 | 4,095 | 32,768 | 65,536 | 8,192 |
| `arrays-768` | 768 | 8,186 | 2,048 | 4,095 | 8,192 | 32,768 | 8,192 |
| `builders-768` | 768 | 5,119 | 1,024 | 2,047 | 8,192 | 16,384 | 4,096 |
| `mixed-3072` | 3,072 | 14,878 | 1,536 | 6,143 | 16,384 | 65,536 | 16,384 |

The exact quotas are fixed in
[`tuning.rs`](../flock-stage3/host/src/ixby/paged_exec/tuning.rs).
They are not inferred from proof bytes. A verifier selects a named class before
reading a proof; the class domain, matrices, wiring, and public layout bind its
physical setup. A complete execution currently selects one class for its entire
execution chain. Automatic switching between classes is not implemented.

The 4K arithmetic prototype crosses the state-routing boundary that the 3K
class avoids. Its unpadded circuit data is 96,097,553 field words, versus
62,053,577 for 3K. The number of committed words rounds to 134,217,728 and
67,108,864 respectively. These counts motivate measuring proof generation and
aggregation together instead of selecting the largest fetch quota.

Routing remains the largest leaf cost after quota tuning. The switching
tables account for 45,540,352 of the baseline's 61,691,832 dense field words
(73.8%), 42,444,544 of 62,053,577 for arithmetic 3K (68.4%), and 69,379,328 of
96,097,553 for arithmetic 4K (72.2%). These are circuit-data shares, not measured
fractions of elapsed time.

## Workloads and scope

The independent
[`paged-execution-batch-sweep.py`](../flock-stage4/fixtures/paged-execution-batch-sweep.py)
generator creates three loops:

- Arithmetic: 16 unboxed Nat additions per iteration, followed by a tail call.
- Arrays: update and read a persistent 64-element array.
- Builders: append two 63-byte chunks and freeze the 126-byte result.

Each loop eventually returns its original 63-byte input. Expected IXFO bytes
are constructed independently of the runtime. All three small fixtures were
checked by Lean's reference byte executor. The large fixtures use 4,096 loop
iterations and exact fuel budgets.

The fourth workload is a native trace prefix from the retained CSLib export,
with its three format headers migrated to semantics 2. This is not a fresh
Compilatrix export using the new array and builder ABI. Its results do not
measure a complete CSLib proof or establish the speedup of compiler integration.

The initial census covers 100,000 microsteps per workload. It sweeps fetch
quotas of 768, 1,024, 3,072, and 4,096 with different memory bounds. All four
workloads are evaluated against 145 distinct candidate geometries, including
poorly matched ones.
Partial final batches are excluded from occupancy averages.

The held-out window starts at microstep 100,000 and covers up to the next
100,000 microsteps. The array and builder fixtures halt within that window.
The arithmetic classes retain about 765, 3,069, and 4,094 logical steps per
complete leaf; arrays retain 764 and builders 744. On the retained prefix,
the baseline averages 1,233 and `mixed-3072` averages 3,509 logical steps per
leaf. Different instruction families fill first there, so the exact mix
still needs to be measured again after compiler integration.

Leaf proofs establish conditional execution segments. The recursive benchmark
joins four adjacent leaves through three actual recursive proofs and verifies
the result in a fresh process. Source admission and the complete-run closing
relation are outside this benchmark. The separate
[runtime-v2 fixture](CompilatrixRuntimeV2Handoff.md#validation-and-reproduction) covers a complete
original-format execution.

## Leaf measurements

Each row measures three adjacent genuine leaf proofs with one worker and two
threads. The worker rate includes witness generation, proving, verification,
and saving the proof files; it excludes native replay and setup. Every proof
verified. Peak memory covers the entire process, including setup. These are
short samples on one machine, not confidence intervals or complete-run rates.
Runs were sequential on an AMD Ryzen 9 7950X3D, with an 84 GiB memory cap,
swap disabled for the process group, and no CPU affinity pinning.
The release binaries used Rust 1.98.1 and the repository's
`-Ctarget-cpu=native` configuration.

| Workload | Class | Logical steps/leaf | Worker steps/s | Setup seconds | Peak GiB | Proof bytes |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Arithmetic | baseline 1K | 432.3 | 14.11 | 124.59 | 31.82 | 624,091 |
| Arithmetic | `arithmetic-768` | 766.0 | 81.27 | 19.76 | 10.42 | 571,587 |
| Arithmetic | `arithmetic-3072` | 3,070.0 | 77.87 | 138.91 | 31.69 | 627,995 |
| Arithmetic | `arithmetic-4096` | 4,095.3 | 75.24 | 431.76 | 45.06 | 603,411 |
| Arrays | baseline 1K | 146.0 | 4.32 | 138.76 | 31.86 | 624,091 |
| Arrays | `arrays-768` | 764.0 | 40.54 | 47.14 | 17.64 | 607,451 |
| Builders | baseline 1K | 192.3 | 5.56 | 134.36 | 31.87 | 624,091 |
| Builders | `builders-768` | 744.7 | 56.22 | 41.04 | 13.26 | 539,875 |
| Retained prefix | baseline 1K | 1,201.3 | 35.82 | 135.58 | 31.98 | 624,091 |
| Retained prefix | `mixed-3072` | 2,413.3 | 70.32 | 138.07 | 32.58 | 631,899 |

Here baseline 1K means `shared-linked-1024` with its corrected semantics-2
capacity. The named classes improve useful occupancy over that baseline.
Among the arithmetic classes, however, the smallest class has the highest
leaf-only rate. This does not establish the best class for a long execution.

The retained prefix also illustrates the distinction between fetches and
logical steps: control transitions can charge fuel without a fetch. Its mixed
class fills numeric or projection quotas before reaching 3,072 fetches.
The result describes this retained prefix, not a new compiler export.
The fourth mixed leaf, collected for recursion, contains only 196 fetches and
219 logical steps: it fills the 24-projection quota. It still takes 32.42
worker seconds to produce and verify. Local bursts can therefore produce
short leaves even when the average quota balance fits the trace well.

## Recursive measurements

Each tree joins four consecutive execution leaves with two joins of raw leaf
proofs and one join of the resulting recursive proofs. Join times include
both proving and verification, as in the current CLI. A fresh receiver
reconstructs the selected setup and accepts the root using only the expected
57-word statement and root proof. It rejects two changes to each public word,
truncation, and trailing data. The prover also rejects repeated, reversed,
and skipped valid child segments.

The fourth leaf was collected in a separate process with the same producer
binary. The record includes both leaf setup receipts; online timings exclude
those setups.

The online rate combines all four leaf timings with all three join timings.
It excludes setup, native replay, filesystem work, negative checks, and the
separate fresh receiver. It remains a rate for a conditional four-leaf tree.
The baseline and arithmetic rows use the arithmetic fixture; the mixed row
uses the retained prefix.

| Class | Logical steps | Mean raw-leaf join seconds | Recursive join seconds | Leaf + join seconds | Online steps/s | Root bytes | Peak tree-process GiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline 1K | 1,729 | 153.96 | 113.33 | 544.15 | 3.18 | 421,363 | 33.04 |
| `arithmetic-768` | 3,060 | 49.05 | 63.29 | 197.56 | 15.49 | 421,267 | 24.74 |
| `arithmetic-3072` | 12,276 | 154.36 | 113.13 | 571.75 | 21.47 | 421,363 | 32.98 |
| `arithmetic-4096` | 16,380 | 155.19 | 113.43 | 634.57 | 25.81 | 421,395 | 34.44 |
| `mixed-3072` | 7,459 | 155.25 | 116.50 | 562.19 | 13.27 | 421,363 | 33.14 |

## Longer executions and join costs

A smaller leaf can be faster to prove while making a complete execution
slower. With `B` leaves, a binary aggregation tree needs exactly `B - 1` joins.
The benchmark therefore measures both a join of two raw leaves and a join of
two recursive proofs. Comparing four leaves of each class alone is still
insufficient: those trees cover different amounts of useful execution.

For a common execution, the report counts the exact leaves produced by each
quota set, including the partly occupied final leaf. It checks the counted
boundaries against the actual leaf proofs. The complete arithmetic fixture
has 73,731 logical steps. Its native execution and leaf counts are measured;
its full proof tree is modeled from the smaller proof samples.

| Complete native execution | Class | Logical steps | Leaves | Joins |
| --- | --- | ---: | ---: | ---: |
| Arithmetic | baseline 1K | 73,731 | 171 | 170 |
| Arithmetic | `arithmetic-768` | 73,731 | 97 | 96 |
| Arithmetic | `arithmetic-3072` | 73,731 | 25 | 24 |
| Arithmetic | `arithmetic-4096` | 73,731 | 19 | 18 |
| Arrays | baseline 1K | 16,387 | 112 | 111 |
| Arrays | `arrays-768` | 16,387 | 22 | 21 |
| Builders | baseline 1K | 24,579 | 128 | 127 |
| Builders | `builders-768` | 24,579 | 34 | 33 |

For the arithmetic fixture, 4K cuts the join count by 25% relative to 3K and
by 81.25% relative to 768. Those savings must be weighed against leaf time,
the cost of each class's recursive verifier, setup, and resident memory.

For the CLI's tree layout, `floor(B / 2)` joins pair raw leaves; every other
join has at least one recursive child. The model uses:

```text
first_level_joins = floor(B / 2)
other_joins = B - 1 - first_level_joins
online_time = B * mean_leaf_time
            + first_level_joins * mean_leaf_pair_join_time
            + other_joins * recursive_join_time
```

Leaf time includes witness generation, proving, and verification. Join time
includes producing and verifying the recursive proof. The four-leaf join is
only a proxy for higher levels and mixed leaf/node joins. Sensitivity cases
multiply that proxy by two and four; these are assumptions, not measurements
or bounds on all future trees.

The online comparison assumes cached setups. Cold setup time is reported
separately: the 4K arithmetic class has a substantially larger initial setup
cost. The current CLI also compiles the raw leaf setup again in its separate
aggregation phase; the record reports that setup subtotal explicitly.
Larger trees also require recursive setups above the four-leaf level,
which this experiment does not time. Native execution, admission, and the
complete-run closing relation are outside the modeled proof time.

For the same 73,731-step arithmetic fixture, the resulting estimates are:

| Class | Cached online minutes, 1x upper joins | 2x upper joins | 4x upper joins | Measured setup subtotal, minutes |
| --- | ---: | ---: | ---: | ---: |
| baseline 1K | 466.22 | 626.77 | 947.87 | 4.41 |
| `arithmetic-768` | 104.49 | 155.12 | 256.38 | 0.89 |
| `arithmetic-3072` | 69.11 | 91.74 | 136.99 | 4.68 |
| `arithmetic-4096` | 56.98 | 73.99 | 108.02 | 14.28 |

The setup subtotal covers the separate leaf and aggregation phases through
four leaves. It excludes the additional setups needed by the complete tree,
so adding it to the online estimate does not give a complete cold-run time.

Among the tested classes, **4K is the best candidate for long arithmetic runs
with cached setups**. Its raw-leaf and recursive joins cost about the same as 3K's,
and its smaller join count outweighs slower leaf generation. Its projected
online time is about 18% lower than 3K's and 45% lower than 768's in the 1x
case. That ordering persists in the two sensitivity cases.

**3K offers a cheaper startup and lower peak leaf memory.** Its measured setup
subtotal is about one-third of 4K's, and its leaf process peaks at 31.69 GiB
versus 45.06 GiB. Adding the measured setup subtotals makes the 3K and 4K
estimates much closer for this fixture; short samples and unmeasured upper
setups do not establish a cold-run winner. The 768 class offers the lowest
startup and leaf memory, but its many joins make it slower in this long-run
model. Selecting it from leaf-only throughput would miss that trade-off.

## Validation

All 35 execution leaf proofs and 15 recursive proofs verified. Fresh receivers
accepted all five recursive roots and rejected 114 public-word mutations,
truncation, and trailing data for each root. Each prover also rejected three
invalid child pairs. The two remaining new classes, arrays and builders,
passed fresh leaf receivers.

All 28 measured independent-fixture leaf boundaries match the complete native
census. Every leaf run's program and input hashes match the initial, refined,
and held-out census workloads. The 45 affected ordinary tests, both workspace
Clippy checks with warnings denied, and both formatting checks passed.

## Reproduction

Generate the fixtures:

```sh
python3 flock-stage4/fixtures/paged-execution-batch-sweep.py --out /tmp/batch-fixtures
```

Run the proof-free sweep from `flock-stage3`:

```sh
IXBY_QUOTA_FIXTURES=/tmp/batch-fixtures \
IXBY_QUOTA_FETCH=768,1024,3072,4096 \
cargo test --locked --release -p ixby-flock --lib \
  ixby::paged_exec::quota_tests::physical_batch_quota_sweep \
  -- --ignored --exact --nocapture --test-threads=1
```

`IXBY_QUOTA_RETAINED` optionally adds a directory containing `program.ixby` and
`input.ixbi`. To measure the selected classes on the next trace window, set
`IXBY_QUOTA_SKIP_MICROSTEPS=100000` and `IXBY_QUOTA_NAMED_ONLY=1`.

Measure four actual leaves, with a new output directory:

```sh
IXBY_PAGED_PROGRAM=/tmp/batch-fixtures/arithmetic/program.ixby \
IXBY_PAGED_INPUT=/tmp/batch-fixtures/arithmetic/input.ixbi \
IXBY_PAGED_NATIVE_CLASS=arithmetic-4096 \
IXBY_PROOF_BATCHES=4 IXBY_PROOF_WORKERS=1 IXBY_PROOF_THREADS=2 \
IXBY_PROOF_OUT=/tmp/arithmetic-4096-proofs RAYON_NUM_THREADS=2 MALLOC_ARENA_MAX=2 \
cargo test --locked --release -p ixby-flock --lib \
  ixby::paged_exec::benchmark_tests::original_execution_proof_throughput \
  -- --ignored --exact --nocapture --test-threads=1
```

From `flock-stage4`, aggregate those leaves. Create an empty output directory
for the three recursive proofs first:

```sh
IXBY_EXECUTION_CHAIN_CLASS=arithmetic-4096 \
IXBY_LARGE_EXECUTION_PROOFS=/tmp/arithmetic-4096-proofs \
IXBY_LARGE_EXECUTION_CHAIN_OUT=/tmp/arithmetic-4096-chain \
RAYON_NUM_THREADS=2 MALLOC_ARENA_MAX=2 \
cargo test --locked --release -p ix-flock-recursion --lib \
  execution_tree::tests::large_execution::execution_batch_shape_chain_proves_fresh \
  -- --ignored --exact --nocapture --test-threads=1
```

From `flock-stage3`, count the leaves needed for each complete independent
fixture, without constructing its proofs:

```sh
IXBY_QUOTA_FIXTURES=/tmp/batch-fixtures \
cargo test --locked --release -p ixby-flock --lib \
  ixby::paged_exec::quota_tests::physical_batch_complete_counts \
  -- --ignored --exact --nocapture --test-threads=1
```

Build before timing. Record setup, native replay, witness, proof, verification,
and maximum resident memory separately. Use the same thread count for each
comparison and a memory limit with swapping disabled; a fetch quota alone
does not predict peak memory.
