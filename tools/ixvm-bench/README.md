# IxVM bytecode comparison

This CPU-only harness loads `Benchmarks/IxVMCompare.lean` exports and the sibling
new Aiur repository's `Examples/IxVM/fixtures/nat-add-comm.json`. The source pin
is `91348190f091d53ab0838440eaeaf0cb36f2737f` (ixon-v4). Both normal Ix calls
and an explicitly constrained-call variant check the same transitive target.
The latter changes only source `CallMode.unconstrained` to `CallMode.normal`,
before compilation; native scalar/division hints and pointer fast paths remain.
All circuits are ungrouped. No generated execution or trace kernels are used.

```sh
lake build Ix.IxVM.Toplevel
lake env lean --run Benchmarks/IxVMCompare.lean /tmp/ixvm-current
RUSTFLAGS='-C target-cpu=native' CARGO_TARGET_DIR=tools/trie-bench/target \
  cargo build --release --locked --manifest-path tools/ixvm-bench/Cargo.toml
RAYON_NUM_THREADS=8 tools/trie-bench/target/release/ix-ixvm-bench \
  /tmp/ixvm-current-standard.json \
  ../aiur/Examples/IxVM/fixtures/nat-add-comm.json prove 1
```

Modes are `execute`, `witness`, `prove`, and `validate`; the final argument is the
sample count. Repeated modes discard two warmups. `validate` requires the
`-validation.json` export. Every witness/prove run serializes and verifies its
proof; statistics include all chips, per-function constrained/unconstrained row
counts, and the content addresses actually visited by the checker.

The complete comparison runner and saved report live in sibling Aiur under
`tools/bench/compare_ixvm.py` and `design/benchmarks/ixvm-20261013/`.
