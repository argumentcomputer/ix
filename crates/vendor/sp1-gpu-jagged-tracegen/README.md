# sp1-gpu-jagged-tracegen (vendored)

A verbatim copy of `sp1-gpu-jagged-tracegen` 6.6.0 from crates.io
(Succinct's sp1 monorepo, `crates/gpu/jagged-tracegen`), applied through
`[patch.crates-io]` in the workspace `Cargo.toml`, with one change:

- `MAX_COLS_PER_TRACE` raised from `1 << 14` to `1 << 20`. It bounds the
  total number of columns across all chips of a shard; Aiur's IxVM kernel
  machine exceeds the upstream bound, which sized the GPU prover's
  start-index buffer and made trace generation panic.

Only built under `aiur-hypercube`'s `cuda` feature.
