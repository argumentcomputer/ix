# sp1-gpu-zerocheck (vendored)

A verbatim copy of `sp1-gpu-zerocheck` 6.6.0 from crates.io (Succinct's sp1
monorepo, `crates/gpu/zerocheck`), applied through `[patch.crates-io]` in
the workspace `Cargo.toml`, with two changes in `src/prover.rs`:

- `build_chip_column_layouts` takes the preprocessed-padding column count
  from `TraceDenseData::prep_padding_col_count` instead of assuming exactly
  one padding column. The tracegen emits
  `ceil(padding / 2^max_log_row_count)` padding columns, which exceeds one
  whenever `max_log_row_count < log_stacking_height` — Aiur's default
  parameters (20 < 21) — shifting every main chip's column index so the
  zerocheck evaluated constraints on the wrong columns and the verifier
  rejected the proof with `ConstraintsCheckFailed(InconsistencyWithEval)`.
  SP1's own parameters (22 ≥ 21) never hit this.
- `SP1_GPU_ZEROCHECK_NO_COLUMN_TILE` forces every chunk onto the Sequential
  lowering (an A/B diagnostic switch; off by default).

Only built under `aiur-hypercube`'s `cuda` feature.
