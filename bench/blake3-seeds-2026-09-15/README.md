# Packed BLAKE3 seeds — 2026-09-15

## Result

The implementation uses 176-byte seeds and bounded pinned staging. On the same
cached Mathlib join, proving without CUPTI took **24.756 s versus 27.177 s**, an
**8.9% reduction**. With CUPTI, the reduction was 9.5%. Every replay verified
natively and reproduced the original proof with identical trace-piece boundaries.

Packing accounts for most of the improvement. A packed, pageable variant also
performed well. Pinned staging saved about 0.06 s in the seed writer in both
comparisons, but its separate effect on proof wall time is smaller than the
variation between these runs. These are single replays per configuration and
collector setting, not a measured speedup of the full 78-shard run.

## Measurements

All runs used physical GPU 3, 24 CPU cores (72–95), the same cached join 33,
and seven trace pieces. `profile` runs include CUPTI; `control` runs retain
the Rust timing spans but omit CUPTI.

| Measurement | Original, pageable | Packed, pageable | Packed, pinned |
|---|---:|---:|---:|
| Proving, control | 27.177 s | 25.180 s | 24.756 s |
| Proving, profile | 27.726 s | 24.900 s | 25.106 s |
| Replay including preparation and verification, control | 58.301 s | 55.730 s | 55.216 s |
| Seed bytes per real row | 1,296 | 176 | 176 |
| Seed uploads, profile | 25.815 GiB | 3.506 GiB | 3.506 GiB |
| Seed DMA time, profile | 2.720 s | 0.336 s | 0.073 s |
| Seed writer, including upload and synchronization, profile | 3.799 s | 1.390 s | 1.329 s |
| Seed writer, control | 3.806 s | 1.387 s | 1.324 s |
| Seed preparation, both rounds, profile | 6.614 s | 2.841 s | 2.791 s |
| All H→D traffic, profile | 68.195 GiB | 45.886 GiB | 45.886 GiB |
| Stage-one commitments, both rounds, profile | 14.891 s | 12.921 s | 13.232 s |
| Lookup construction and commitment, profile | 5.684 s | 4.904 s | 4.773 s |
| Peak RSS, control | 28.562 GiB | 26.686 GiB | 26.817 GiB |
| Peak live device allocations, profile | 63.676 GiB | 63.676 GiB | 63.676 GiB |

Seed traffic fell **86.4%** and all H→D traffic fell **32.7%**. The 334 seed
transfers in each profiled run had exactly the expected `176 / 1296` byte ratio.
The three uploads per source—two commitments and lookup regeneration—remain.

The pinned path's host copy and other work outside CUDA API calls occupied about
0.36 s inside the seed-writer spans. Host work and synchronization prevent the
additional 0.26 s DMA saving from reaching writer time in full. The complete writer improves
by only 0.062 s with CUPTI and 0.063 s without it. The proof-wall comparison
between the two packed paths changes direction with the collector setting;
do not attribute a reliable proof-wall gain to pinning alone.

Seed preparation is pipelined with proving. Its 3.8 s reduction does not add
directly to the wall-time saving. The execution record remains **14,003,112,192
bytes**; packing does not reduce the record pool's reservations. The expanded
traces and LDEs are unchanged, explaining the unchanged peak device allocation.

## Implementation and correctness

- [Rust seed layout and scalar writer](../../crates/aiur/src/gpu_trace/mod.rs):
  64-bit canonical multiplicity, one stage byte, 128 input bytes, 32 recorded
  output bytes, and seven initialized padding bytes. Bounds are checked before
  narrowing, and unsupported values still use the reference builder.
- [CUDA generator and upload](../../crates/aiur/cuda/blake3_trace.cu): matching
  compile-time size, alignment, and offset assertions. Four lazily allocated
  portable pinned slots are shared across devices; each holds 65,537 seeds.
  The maximum is **44 MiB plus 704 bytes per process**. A lease remains held
  until stream completion, including when a launch fails.
- The main trace, field encodings, lookup ordering, and proof format are unchanged.
  Host-byte accounting uses the actual packed seed size.
- [Seven focused tests](tests.log) passed, covering bytecode/scalar/CUDA parity
  for all eight stages, large canonical multiplicities, invalid byte bounds,
  maximum-size tiles, padding and wrapped halos, failure cleanup, and eight
  concurrent callers across four GPUs. The tests took under two seconds after
  building their target on four CPU cores.

All six replays produced:

```text
12beead9b79adc380e89315c871294470a76d7e9d574cce5e76b791e887697e2
```

[compare.py](compare.py) checks the exact seven boundary lines, seed row counts,
execution-record size, proof address, device/CPU settings, successful exits,
and expected transfer-byte ratio. All CUPTI captures had zero dropped or invalid
records. GPU contention guards observed no foreign process on the selected GPU.

## Reproduction and artifacts

The baseline is the frozen, instrumented build from
`target/prover-profile-build`, described in the
[earlier investigation](../prover-profile-2026-09-15/README.md). The packed build
uses the same frozen sources with only the three GPU seed files changed;
multi-stark and the compiled Lean objects are unchanged. The source delta is
[seeds.patch](seeds.patch). Build commands, hashes, flags, and CPU affinity are
in [build.json](build.json) and [tests-build.json](tests-build.json).

`build.py tests` builds only the Aiur test target; `build.py ffi` builds the Rust
FFI target and relinks the saved Lean objects. Both are restricted to four CPU
cores. `build.py pageable` creates the comparison variant by replacing only the
CUDA object in a copy of the packed FFI archive; the Rust code is identical.

```bash
python3 bench/prover-profile-2026-09-15/run.py join 33 \
  --label packed-profile --device 3 \
  --binary target/blake3-seeds-build/ix-packed \
  --output-root bench/blake3-seeds-2026-09-15
python3 bench/prover-profile-2026-09-15/analyze.py \
  bench/blake3-seeds-2026-09-15/packed-profile
python3 bench/blake3-seeds-2026-09-15/compare.py
```

Use a fresh label when repeating a run. Omit `--binary` for the baseline; use
`ix-packed-pageable` for the packed pageable variant. Add `--no-cupti` for a
control. The runner fixes the 1.5-billion-cell piece cap, disables tree retention,
and passes `--no-write`. It reads the original Mathlib aggregate cache.

Each run directory contains command/environment metadata, stdout/stderr, and
GPU samples. Profile directories also contain analysis summaries. Raw JSONL
captures and generated timelines remain locally available but are gitignored.
[comparison.json](comparison.json) contains the checked measurements.
