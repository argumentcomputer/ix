# Reference execution profiling

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
