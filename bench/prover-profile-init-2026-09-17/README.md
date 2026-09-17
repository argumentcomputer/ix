# CUPTI profile of an Init claim and join on the current tree, 2026-09-17

One RTX PRO 6000, 24 CPU cores (`taskset -c 8-31`), CUDA 13.3, the
collector and analyzer of `bench/prover-profile-2026-09-15`, binary
`4714bb2a…` built from ix `5beba0d4` plus the packing sub-spans (this
commit) against multi-stark `c26dbba`, `AIUR_GPU_TRACE=generated`, trace-only
lookups, 1.5e9 cells per piece, device-resident seeds on. Claim 1 of the
four-shard Init partition (11 pieces) and join slot 5 replayed from the
lanes run's cache (8 pieces, proof `6aaff856…`). `profile.sh` is the runner,
`idle.py` attributes kernel-idle time inside a phase to the host spans
active then. The raw `cuda.jsonl` and `spans.jsonl` are not checked in
(873k and 282k CUPTI records, zero dropped); `analysis.json` holds the
analyzer's output, `spans.txt` the span unions, `idle.txt` the attribution.

## Where the time goes

| | claim 1 | join 5 |
| --- | ---: | ---: |
| Execution before proving | 98.5 s | 29.2 s |
| Proof, both rounds | 44.9 s | 24.0 s |
| Kernel busy, union | 28.7 s, 64% | 16.6 s, 69% |
| No kernel running | 16.2 s | 7.5 s |
| Stage-one commit, union / no kernel | 23.4 / 9.9 s | 12.7 / 4.3 s |
| Lookup construction, union / no kernel | 8.2 / 1.9 s | 5.2 / 1.2 s |
| Quotient, union / no kernel | 6.8 / 0.1 s | 2.8 / 0.0 s |
| FRI and opening, union / no kernel | 5.7 / 3.5 s | 2.3 / 0.9 s |
| Host witness, union | 12.4 s | 3.9 s |
| Seed packing: filter / pack / widen / concatenate | 1.3 / 6.6 / 0 / 2.2 s | 0.1 / 2.0 / 0 / 0.5 s |
| Device callbacks, union / no kernel | 4.7 / 3.7 s | 1.4 / 0.6 s |
| Host-to-device bytes / copy-only time | 89 GiB / 2.7 s | 42 GiB / 1.1 s |
| Peak live device memory | 63.6 GiB | 54.2 GiB |

Kernel families, share of kernel-busy time:

| Family | claim 1 | join 5 |
| --- | ---: | ---: |
| NTT, radix-8 stages | 28.8% (6,283 launches) | 35.1% (2,277) |
| NTT, radix-2 stages | 16.7% (9,252) | 7.9% (4,299) |
| BLAKE3 leaf rows, short rows and digest pairs | 21.6% | 21.9% |
| `evaluate_quotient` | 13.2% | 13.5% |
| `accumulate_reduced_opening` | 5.0% | 7.4% |
| `lookup_messages_graph` | 4.3% | 4.4% |
| `gather_resident_lde_group` | 2.3% | 2.4% |
| Generated row writers | 0.5% | 0.6% |

## What the idle time is

Claim 1, 16.2 s with no kernel:

- 9.9 s inside stage-one commit. 6.4 s of it has the next shard's host
  witness active (CPU-built circuits 5.2 s, packing 3.6 s, concatenation
  1.2 s, live filter 0.9 s), 3.5 s has a device callback active, and 2.8 s
  has neither: the commit's own uploads, `cudaHostRegister` (0.8 s over
  124 calls) and hashing.
- 3.5 s inside FRI and opening, 8% of the proof. Spans added to the
  streamed opening path (`claim1e/phases.txt`, multi-stark `fed36dc`) place
  3.21 s of it in the preparation step, all pure host time, 0.29 s per
  shard: `pcs.rs` builds the full coset of the largest LDE height on the
  host, 2^26 elements per shard, bit-reverses it, converts it and uploads it
  for the denominators. That vector depends only on the height, so a
  per-height cache on the host and the device removes it. The rest of the
  phase is small: query grind 0.15 s at 20 bits, queries 0.19 s, the 256
  round commitments 1.94 s of union with 0.01 s idle, interpolation 0.34 s,
  input openings 0.02 s. `apis.py` confirms the gap is host compute, not
  waits: 3.05 s of the idle has no CUDA API call active.
- 9.9 s inside stage-one commit, of which `apis.py` puts 7.8 s in host
  compute and 2.0 s in CUDA waits, mostly stream synchronization. Per
  source, host-built traces spend 5.8 s of their 9.0 s of span time with an
  idle device and generated sources 3.9 s of 9.8 s (`claim1b/narrow.txt`),
  so the staged synchronous upload of host traces is the larger commit-side
  target.
- 1.9 s inside lookup construction. The lookup-phase callbacks total
  1.01 s of union on the claim and 0.68 s on the join (`split.py` of the
  seed-cache bench), of which 0.2 s coincides with an idle device; the
  rest of the idle time is per-job admission and synchronization.

Join 5, 7.5 s with no kernel: 4.3 s in stage-one commit (2.0 s with no
witness or packing active), 1.2 s in lookup construction, 0.9 s in FRI.

## Reading it

- **Per transform shape** (`claim1b/shapes.txt`, `join5b/shapes.txt`,
  kernels attributed by time to the innermost active LDE span): on the
  claim, radix-2 time is 4.3 s of narrow transforms, of which 1.8 s are
  width-2 quotient codewords, 1.2 s lookup LDEs of width 2 to 6 and 1.4 s
  main traces of width 6 and 7, against 0.5 s of residue stages of wide
  transforms; on the join 0.8 s narrow against 0.5 s residues.
- **NTT is the largest single family, 43 to 47% of kernel time**, with
  BLAKE3 hashing at 22%; halving both would shorten either proof by
  roughly 22%, if the saved kernel time is on the critical path. On the
  claim a third of the NTT time is radix-2 stages, 9,252 launches; that
  kernel serves the narrow-width fallback and the residue stages of wide
  transforms, and the width-2 codewords already end in a fused tail, so the
  launches must be split by width and height before the narrow transform
  is sized as a project.
- **Kernels are busy 64 to 69% of the proof**, against 56 to 58% in the
  September 15 profiles; those were Mathlib units, so the difference is
  not attributable to the seed work alone, whose controlled effect is the
  5.9 s of 256.5 s in `bench/aiur-seed-cache-2026-09-17`. The remaining
  idle time is the commit's host side, FRI's host side, and lookup
  admission, in that order. A host span active during an idle stretch
  identifies a candidate, not a cause.
- **Packing's fixed parts are a quarter of it**: filter plus concatenate
  are 3.5 of the claim's 9.3 s of packing union. Packing straight into the
  span and filtering per chunk removes them without changing the seeds.
- Execution is 2.2x the claim proof and 1.2x the join proof on 24 cores,
  the same ratios the lanes runs show.

## Reproducing on this host

The fixtures, the lanes cache with the four Init shard proofs and the two
joins, the scripts and the control binary live in `~/benchdata/init-gpu`
(`init.ixe`, `init-4.ixes`, `lanes-cache/`, `ix-control`, `run.sh`,
`profile.sh`, `compare.py`, `split.py`, `idle.py`, `shapes.py`, `narrow.py`,
`apis.py`, `env.sh`). `profile.sh <binary> <label> claim 1` and
`profile.sh <binary> <label> join 5 $(cat lanes-cache/shard-proofs/*)`
replay the two units with CUPTI; `shapes.py <dir>` attributes kernel time
per transform shape and `narrow.py <dir> shapes.py` splits radix-2 time and
reports the commit and FRI sub-phases.

Building `ix` here: source `env.sh`, which puts the Nix store's Lean 4.33.1
on the path, sets `LEAN_SYSROOT`, `IX_CUDA=1 IX_CUDA_TRACE_CODEGEN=1`,
`NVCC`, `MULTI_STARK_CUDA_ARCHS=120`, `RUSTUP_TOOLCHAIN=stable` (which is
1.98.1 here), `CLANG_PATH=/usr/lib/llvm-21/bin/clang` for bindgen, and
`CFLAGS=-std=gnu17` so gcc 15 does not redirect `strtol` to a C23 symbol
the Lean toolchain's libc lacks. To build against a local multi-stark,
append the `[patch]` table to the tracked `.cargo/config.toml` rather than
replacing it, since it carries `-Ctarget-cpu=native`, and restore it and
`Cargo.lock` afterwards. Lake's trace for the Rust archive covers ix's own
sources and lockfile, not a path-patched multi-stark, so after changing
multi-stark delete `.lake/build/lib/libix_ffi_*` and `.lake/build/bin/ix`
before `lake build ix`, or the old archive is relinked unchanged. The
sandbox hides the GPU; run anything that opens the device outside it.

sppark at `17278d7` compiles and links for sm_120 with CUDA 13.3:
`~/benchdata/init-gpu/sppark-smoke.cu` builds with
`nvcc -std=c++17 -O2 -arch=sm_120 -I<sppark> -DFEATURE_GOLDILOCKS smoke.cu
<sppark>/util/all_gpus.cpp` and round-trips a 2^20 transform through
`NTT::Base_dev_ptr` with no mismatches. The crate resolves as a git
dependency with the `cuda` feature and exports `DEP_SPPARK_ROOT`.
