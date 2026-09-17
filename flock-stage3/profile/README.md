# Reference execution profiling

## Current runtime-v2 CSLib workload

The [recursive evaluator comparison](cslib-runtime-v2-recursion.json) records
both same-proof trees, phase/family timings and unchanged setup identities.
It reduces the two measured joins from 300.26 to 36.61 seconds; see the
[results](../../docs/IxbyRecursiveTuning.md) and
[reproduction bundle](recursive-tuning-v0/README.md).

The [complete native census](cslib-runtime-v2-native.json) covers
1,703,268,652 physical steps and matches every compiler block count, fuel and
expected output. The [batch/proof comparison](cslib-runtime-v2-tuning.json)
and [reproduction bundle](cslib-tuning-v0/README.md) record the selected
`cslib-2048` class, 341 capture replays, and actual equal-work recursive trees.

The [new compiler export and retained evidence](cslib-runtime-v2/README.md)
cover **360,337,913 logical transitions** with exact expected output.
The [reference summary](cslib-runtime-v2-reference.json),
[function costs](cslib-runtime-v2-costs.json), and
[two new physical windows](cslib-runtime-v2-physical.json) bind the copied
runtime-v2 program and input. See the [current priorities](../../docs/IxbyPerformance.md)
for the remaining opportunities, including recursive joins. The two-prefix
record is retained as the initial measurement before full profiling.

## Historical reference image and observer

`ExecutionProfile.lean` observes the unchanged reference `Ix.Ixby.step`.
It validates the initial state and checks the exact expected output when the
guest halts. It records block and control counts, frame/continuation sizes,
and scalar/object maxima at inspected operands, locals, returns and
applications. These maxima do not certify all values reachable in the heap.

The retained [CSLib summary](cslib-reference.json) covers all 2,268,502,805
transitions and matches the pinned expected output. Profiling took 345.94
seconds and 627,068 KiB maximum RSS. It observed 73 locals, 647 continuations,
65-bit Nats, byte arrays through 4,813,182 bytes and constructors with nine
fields. This is native execution evidence, not a Flock proof or a proving
time estimate.

The observer builds against the already built `ixby-exec` target in the pinned
Compilatrix checkout from [the workload record](../../docs/IxbyStage2CSLib.md).
It reuses that target's recorded compiler arguments and libraries, replacing
only the executable's main module. The output directory must be new.

```sh
python3 flock-stage3/profile/build.py --compilatrix /path/to/compilatrix \
  --lean-root /path/to/matching/lean --out /path/to/new-build
# --lld /absolute/path/to/ld.lld can select the linker when needed.
/path/to/new-build/execution-profile \
  /path/to/cslib.ixby /path/to/cslib.ixbi /path/to/expected.ixbo \
  /path/to/new-report.json 16000000000
python3 flock-stage3/profile/summarize.py \
  /path/to/new-report.json /path/to/new-summary.json
```

A smaller final step cap produces a prefix report with `completed=false`.
Full reports include all 6,763 instruction descriptions and block counts;
the summary weights their opcode names by the observed visit counts.

The [function cost record](cslib-runtime-costs-v0.json) joins those observations
to the compiler's function inventory, checking both against the pinned image.
Eleven helpers for array traversal, byte ropes, numeric conversion and number
unboxing account for 56.0% of all reference transitions. These are exclusive
instruction counts, not measured optimization gains. See
[IxBy performance priorities](../../docs/IxbyPerformance.md) for the new image's
remaining costs. `function_costs.py` retains the historical groups by default;
`--groups` selects an explicit group file for a different compiler image.

## Native Flock execution segment

The separate [Shared execution measurement](cslib-shared-execution-v0.json)
records a genuine proof of 118 original-CSLib microsteps and 32 logical steps,
including fresh verification and recomputed clock rejections. It also records
a longer native advice prefix whose accelerated calculations are compared
with their Boolean plans. See the [class, timings and reproduction command](../../docs/IxbyFlockPagedExecution.md#larger-shared-execution-batch).
These measurements cover a conditional segment and advice generation; the
complete CSLib execution remains unproved.

The [original-artifact expectation](cslib-paged-statement-v0.json) pins the
184-byte IXFP descriptor, the three artifact hashes and independently computed
32-byte statement for a future complete CSLib proof. Computing this statement
does not prove the execution.

The [CPU server throughput record](cslib-server-proof-throughput-v0.json)
contains 148 verified proof samples across two prefix windows, worker scaling,
fresh local reception, and the exact table-cost census. The best short sample
reaches 34.767 logical steps per second; full CSLib proving is not practical
with that original layout. Switching networks occupy 78.6% of the dense witness, and
the padded working domain is 58.5 times the useful field data. See the
[measured costs and reproduction commands](../../docs/IxbyFlockPagedExecution.md#cpu-server-throughput-and-cost-breakdown).

The [larger execution record](cslib-large-execution-v0.json) records the separate
Boolean-routing classes and `shared-1024`, which has 1,024 Fetch slots. It
contains 96 verified proof samples, with the final larger-class run reaching
292.245 logical steps/second and averaging 1,057 logical steps per proof. It
retains actual per-family row usage, server throughput and memory measurements,
the table census, fresh leaf verification and a genuine two-level recursive
CSLib execution chain. It also records the partial-padding failure found in a
complete small proof and its dirty-buffer regression. The separate
[complete countdown record](../../flock-stage4/census/paged-execution-countdown-1024-v0.json)
records successful full proving and fresh verification with the final class.
Complete original CSLib execution remains unproved.

The [packed execution record](cslib-packed-execution-v0.json) measures exact
bit packing around the existing Boolean routing networks. It records 72
verified benchmark proofs, a controlled 24.1% throughput improvement and
27.1% lower peak memory at eight workers, and a 415.918-step/second sample
with sixteen workers. The record includes the exact packing masks, 26.4%
smaller useful witness, fresh leaf receivers, two recursive levels and their
114 public-word rejections. The
[packed countdown record](../../flock-stage4/census/paged-execution-countdown-packed-v0.json)
records the complete small fixture separately. These measurements do not
establish a complete CSLib proving rate.

The [linked execution record](cslib-linked-execution-v0.json) replaces the
state sorting audit with exact after/before record matching and checked clock
progress. It records 72 verified server proofs, a paired 31.6% higher worker
rate and 24.9% lower peak RSS, and 25.3% fewer useful witness words. Larger
commitment query openings increase the execution leaf to 607,299 bytes.
The record distinguishes the server executable's slow setup from the final
construction fix measured locally. The
[linked countdown record](../../flock-stage4/census/paged-execution-countdown-linked-v0.json)
records a complete 510,115-byte root accepted in a fresh process. The execution
record also includes two recursive levels over three genuine CSLib leaves,
fresh verification and 114 public-word mutation rejections. Full CSLib
execution remains unproved.
