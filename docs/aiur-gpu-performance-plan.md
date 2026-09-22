# GPU proving performance plan

2026-09-16. Written after the typed seed schema and the removal of the
handwritten BLAKE3 provider on `sb/aiur-trace-sharding-gpu`. This ranks
what to do next to make one join prove faster and the pipeline of joins
keep the GPU busy. Every estimate below is derived from the one measured
join and is marked as such; the first item is to re-measure.

## Where the time goes

FLT aggregate slot 19, one join, one RTX PRO 6000, eight CPU cores, from the
[paired replay](../bench/aiur-trace-replay-2026-09-16/README.md). Host phases
are unions of overlapping spans and do not add.

| Phase | Seconds | Share of proving |
| --- | ---: | ---: |
| Execution and planning (before proving) | 24.5 | |
| Proving, both rounds | 23.5 | 100% |
| Stage-one commit | 12.3 | 52% |
| Lookup construction | 4.1 | 17% |
| Quotient | 2.3 | 10% |
| FRI and opening | 2.3 | 10% |
| Host witness work inside proving, union | 8.4 | |
| BLAKE3 seed preparation, union | 2.3 to 2.8 | |
| Device seed callbacks, union | 1.2 | |
| Peak device memory | 64.5 GiB of 96 | |

The earlier kernel profile of a representative claim, before packed seeds,
had kernels active for 56% of proving, with the largest idle stretch inside
stage-one commit. Round two regenerates stage one (`Retention::Regenerate`),
so every host trace that is not generated from seeds is built twice.

Three facts bound what trace generation alone can do:

- The [schema inventory](../bench/aiur-trace-schema-2026-09-16/README.md)
  says that outside BLAKE3 and the klimbs family, a typed seed is still 55 to
  58% of the row it replaces, so generation saves upload bytes but not the
  host pass that resolves record keys.
- Seed preparation runs one thread per circuit; the BLAKE3 circuit's rows
  are packed serially while the other seven cores idle.
- Execution takes as long as proving. In a pipeline of joins, execution of
  the next join is the supply that has to hide behind the GPU.

## Ranked work

Gains are per join against the table above, are estimates, and are not
additive. Each item names the measurement that accepts or rejects it.

### 1. Re-measure the join with the current tree

Run the paired replay as generated against CPU traces on the FLT cache with
the typed schema, and capture a kernel-busy timeline per phase (CUPTI or
`nsys`, not only host spans). Attribute stage-one commit into host witness
for uncovered circuits, seed preparation, transfer, device LDE and Merkle,
and any height groups hashed on the host. Everything below assumes this
breakdown; the 12.3 s stage-one number is the least understood and the
largest.

Cost: a bench host with the FLT cache, half a day. Gate: same proof digest
and trace plan as the recorded pair.

### 2. Parallel seed preparation

`BoundCudaProgram::prepare` packs rows serially. Split each member run into
row chunks, pack chunks on the Rayon pool into per-chunk typed buffers with
per-row fit flags, then concatenate; if any row in the run failed its guard,
re-encode the run full width from the typed bytes and repack only the
failing rows, keeping the whole-run codec rule. Proof bytes are unchanged
because seed content is unchanged.

Estimate: BLAKE3 preparation from 2.3 to 2.8 s toward 0.4 s on eight cores;
the wall-time gain is whatever share of that sits on the critical path of
stage-one commit, which item 1 tells. Cost: one to two days, no protocol
change. Gate: `seed_preparation` span in the replay, the guard-fallback and
widening tests, and identical proof bytes.

### 3. Keep wide height groups on the device

multi-stark `b6629c2` hashes any Merkle height group wider than 32 KiB per
row on the host. If item 1 shows host hashing inside stage-one commit for
the FLT join, implement a multi-block BLAKE3 leaf hash on the device that
consumes a leaf row in 32 KiB pieces, and remove the host path for those
groups. Estimate: unknown until measured; if present it is serial host work
inside the largest phase. Cost: two to three days in `cuda/kernels.cu` and
`mmcs.rs`, with the existing wide-group regression test as the oracle.

### 4. Fewer, larger pieces

The join proved six pieces at `AIUR_MAX_PIECE_LOG_HEIGHT=24` with 31 GiB of
device headroom. Quotient, FRI, transcript and stage-two costs are largely
per piece; raising the shard cell budget until admission is tight trades
that fixed cost for larger LDEs. Estimate: 5 to 10% of proving if the
per-piece fixed cost is what the six-piece split suggests. Cost: a sweep of
`AIUR_TRACE_SHARD_MAX_CELLS` under the new lookup admission, one day. Gate:
`MULTI_STARK_CUDA_MEMORY_LOG` shows no spills, and proving time per row.

### 5. Weighted coverage expansion

Fill `real_rows` per circuit from the FLT record, rank circuits by rows
times (canonical minus typed bytes) and by rows times retained host
arithmetic, and extend `traceBundle` to the top of that ranking. The static
inventory already points at the BLAKE3 neighbours and the klimbs family. Then
add grouped spans and the memory and byte-table primitives so round two
rebuilds nothing on the host.

Estimate: bounded by the share of the 8.4 s host witness union that is not
already hidden behind device work, and by round two's rebuild of uncovered
traces; item 1 measures both. Cost: the handoff's steps 4 to 6, one to two
weeks. Gate: the exact-cell parity harness against the bytecode oracle on the
real record, nvcc registers and spills for the wide writers, and the paired
replay.

### 6. Device kernels

The per-kernel profile puts 44 to 49% of kernel time in the NTT passes, 20
to 22% in BLAKE3 Merkle hashing, 13% in the interpreted quotient evaluator
and 5 to 7% in an uncoalesced opening kernel, with 8 to 10% of proving spent
in copies while no kernel runs. The
[GPU kernel plan](aiur-gpu-kernel-plan.md) ranks that work: a fused
shared-memory NTT, full-lane leaf hashing, compiled and coalesced
evaluators, coalesced reduced openings, copy-kernel overlap, round-boundary
pipeline fill, the FRI host gap, and two proofs per device.

### 7. Lookup construction

At 4.1 s this is the largest device-side phase after stage one. Profile the
graph kernel's occupancy and the per-job synchronization in
`accelerated_lookup_commit`; candidates are batching the inverse passes
across jobs, raising `LOOKUP_ROWS_PER_CHUNK` where admission allows, and
running independent jobs on separate streams. Estimate: unknown until
profiled. Cost: two to four days.

### 8. Execution supply

Execution and planning equal proving time. This is the pipeline's limiter
once proving improves, and it is a separate track already designed in the
[distributed execution recommendations](aiur-gpu-performance-recommendations.md):
prefetch the next join's execution during proving, and partition execution by
ownership so several cores execute one claim. Estimate: in steady state most
of the 24.5 s per join hides behind the GPU. Cost: weeks.

### Deferred

- Coalesced stores in the generated kernels. One thread writes one 533-word
  row; device callbacks total 1.2 s, so this only matters once coverage is
  wide. Measure memory throughput first.
- Tree caching across rounds. Measured already: no end-to-end gain and 17 GiB
  more peak memory.

## Sequence

1. Item 1, the measurement, on the bench host.
2. Item 2 in parallel with 1; it needs no measurement to be correct.
3. Items 3 and 4 as item 1 directs.
4. Item 5, then the kernel plan's items and 7, each gated by a paired
   replay and the CUPTI kernel-family profile.
5. Item 8 as its own track.

Judge every step by lower proof wall time and fewer exposed idle gaps, with
identical proof bytes; never by a phase's span duration alone, since the
phases overlap.
