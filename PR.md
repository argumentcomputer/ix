# Make Rust panic recovery effective

## Summary

- Keep the workspace panic strategy at Rust's default `unwind` setting.
- Guard the aggregate `proveMultiStarkJoin` and `proveIxAggr` Lean FFI entrypoints.
- Make the Blake3, Sha256, and IxVM proving benchmarks fail on `Except.error`.

## Why

The workspace set `panic = "abort"` in dev and release, so a Rust or CUDA panic
terminated the process before any `catch_unwind` handler could return
`Except.error` to Lean. Removing those overrides makes the existing recovery
paths effective. Uncaught panics still abort at a non-unwinding `extern "C"`
boundary, so they cannot unwind into Lean.

Latest main also added two proving FFI entrypoints without the common panic
barrier. They invoke the same CPU/CUDA prover and need the same containment as
the other proving calls.

The three one-shot benchmarks used generic `bench`, which discards its result.
After panic recovery became reachable, that would report a caught proving
failure as a successful timing. `benchStepE` propagates the error instead.

## Validation

- `cargo check --release -p ix-ffi --features parallel`
- `cargo clippy --release -p ix-ffi --features parallel -- -D warnings`
- `cargo fmt --all -- --check`
- `lake env lean Benchmarks/Blake3.lean`
- `lake env lean Benchmarks/Sha256.lean`
- `lake env lean Benchmarks/IxVM.lean`

## Scope

CUDA initialization during `AiurSystem.build` remains outside these proving
guards because `build` is currently infallible on the Lean side.
