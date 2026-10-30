# Final proof measurements

These records describe the measured revisions and workload. The earlier BLS
comparison is retained in Git history at `ca8ed5b5`.

## Stock gnark comparison

On October 28, 2026, the same `2^24` Init circuit was measured on 32 logical
Xeon Platinum 8559C CPUs and one RTX PRO 6000 Blackwell GPU, with Go 1.26.8
and CUDA 13.3. Five proofs per mode after one warmup gave medians of 11.550 s
for stock gnark with CUDA, 11.671 s patched/unfused, and 11.439 s patched/fused.
All 18 proofs verified and rejected altered claims. Fusion saved 4 GiB of
transfers but only 0.96% versus stock gnark; stock gnark is now the supported
integration. The implementation was `cfc35206e`, matching `sb/bn254` at
`0a713fbf`; detailed reports and archive pins are in `target/quotient-benchmark/`
in the measurement worktree.

## Matched Init final measurements

Recorded in `a5ddac43`, using stock gnark `262cf453c107`. Measured on 2026-10-29 with Go 1.26.8, 32 logical CPUs and an RTX PRO 6000
Blackwell Server Edition. Both systems use exactly the same checked-in Init
verifier description and witness. Values are medians of three warm proofs in
separate processes at default parallelism; no other GPU compute process was
present when either CUDA run started.

| Backend | CPU proving | CUDA proving | Native proof | Ix envelope | Solidity payload |
| --- | ---: | ---: | ---: | ---: | ---: |
| Groth16 | 7.35 s | 2.61 s | 196 B | 236 B | 384 B |
| PLONK | 66.07 s | 11.59 s | 584 B | 624 B | 864 B |

Groth16 CUDA uses ICICLE with pinned key vectors; PLONK CUDA uses the existing
sppark adapter and retained bases. Proving includes gnark witness solving.
Opening the key/circuit takes about 27 seconds for Groth16 and 22 seconds for
PLONK, separately from the table. Earlier compression stages and witness export
are excluded. Groth16 uses development keys; PLONK reuses its pinned Ignition
cache. These are one-workload measurements, not predictions for every circuit.
Raw samples, file identities, opening times and peak process RSS are recorded
in `tools/plonk-wrapper/testdata/final-comparison.json` at `c6c6cb95`. The
actual Groth16 Init proof also passes
the Solidity adapter test, at 318,490 execution gas excluding transaction
intrinsic gas and calldata.
