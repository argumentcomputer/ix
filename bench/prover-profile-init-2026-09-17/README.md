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
- 3.5 s inside FRI and opening with no host span at all, 8% of the proof.
  The query proof of work is 0 bits on these proofs, so this is not the
  grind; sibling gathers and the opening's synchronous copies are the
  candidates, and a span around each is the next step.
- 1.9 s inside lookup construction, of which the callbacks are 0.2 s: the
  resident seeds have removed the callback cost, what is left is per-job
  admission and synchronization.

Join 5, 7.5 s with no kernel: 4.3 s in stage-one commit (2.0 s with no
witness or packing active), 1.2 s in lookup construction, 0.9 s in FRI.

## Reading it

- **NTT is the largest single family, 43 to 47% of kernel time**, and on
  the claim a third of it is radix-2 stages: the narrow-width fallback for
  matrices under eight columns and the width-2 codewords, 9,252 launches.
  A fused narrow transform is the cheapest kernel item and worth about 12%
  of the claim's kernel time on its own; the radix-8 fusion is the larger
  and harder half.
- **Kernels are busy 64 to 69% of the proof**, up from 56 to 58% in the
  September 15 profiles, after packed seeds, pipelined upload and resident
  seeds. The remaining idle time is the commit's host side, FRI's host
  side, and lookup admission, in that order.
- **Packing's fixed parts are a quarter of it**: filter plus concatenate
  are 3.5 of the claim's 9.3 s of packing union. Packing straight into the
  span and filtering per chunk removes them without changing the seeds.
- Execution is 2.2x the claim proof and 1.2x the join proof on 24 cores,
  the same ratios the lanes runs show.
