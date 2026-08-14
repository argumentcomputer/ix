# Kernel cold-circuit grouping by layout shape (2026-08-14, post xor-split rebase)

Rebuilt from scratch after rebasing group-functions onto main @ 97aa19e8
(perf/virtual xor split #558) — the old groupings predated the fused
xor-rotation circuits and were discarded. Workloads: execute-only
`ix check --ixe InitStd.ixe` over String.split and Array.extract_append,
with the TEMP Sel/Aux/Lkp stats columns
(cold-groups/kstats2-{String.split,Array.extract_append}.txt; grouped runs
in kstats2-grouped-*.txt).

## Heuristic (same conservative rule as the pre-rebase baseline)
Cold = max FFT share < 0.5% across the two workloads (668 of 709 function
circuits). Cluster cold circuits by SHAPE PROXIMITY: a band admits a member
while max(aux) <= 1.6 * min(aux), max(lkp) <= max(2 * min(lkp), min + 4),
and summed selectors stay <= 40 (selectors sum under the merge rule; aux and
lookups merge by max, so shape mismatch is pure per-row waste).
verify_claim is excluded (entry functions cannot group).

## Result: 85 bands over 630 circuits
- circuits 730 -> 185, total committed width 33,331 -> 15,763 (-53%)
- measured FFT cost: String.split 4.951e10 -> 5.622e10 (+13.6%),
  Array.extract_append 1.352e11 -> 1.471e11 (+8.8%)
- hot circuits left ungrouped (top max-share): blake3_compress_inner_j,
  expr_inst_many_walk, expr_inst_many, blake3_compress_chunks, list_snoc.G,
  peel_beta, list_drop.Ptr.Expr, blake3_compress
- band membership: cold-groups/kernel-bands2.json; applied grouping:
  Ix/IxVM/ColdGroups.lean
