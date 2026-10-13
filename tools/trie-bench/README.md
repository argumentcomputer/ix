# Persistent trie comparison

`Benchmarks/Trie.lean` implements the same nine-function program as new Aiur's
`Examples/Trie.lean`. It constructs a persistent binary trie, performs point
updates and current/snapshot reads, and returns a checksum and final tree sum.
There are no hints, custom tables, byte intrinsics or pointer comparisons.

The fixed runtime input is `[14, 4096, 17]`. Expected output is
`[7648480556796356527, 9841071873329795828]`, with 331,804 function queries and
102,413 memory cells. The independent array reference model and comparison
runner live in new Aiur's `tools/bench/` directory.

```sh
lake build Benchmarks.Trie
lake env lean --run Benchmarks/Trie.lean /tmp/ix-trie.json
RUSTFLAGS='-C target-cpu=native' cargo build --release --locked \
  --manifest-path tools/trie-bench/Cargo.toml
RAYON_NUM_THREADS=8 tools/trie-bench/target/release/ix-trie-bench \
  /tmp/ix-trie.json ../aiur/Examples/Trie/fixtures/fixed.json prove 1
```

The harness accepts `execute`, `witness` or `prove`, followed by a sample count.
Repeated modes discard two warmups. Each execution starts with a fresh record;
witness mode reuses an immutable record and includes shard planning/indexing.
Proving runs serialize, decode and verify the proof. JSON reports include each
ungrouped chip's stage 1/stage 2 columns, raw/padded rows, quotient degree, proof
size and timings. Execution and witness population both use the production CPU
bytecode interpreters. This standalone crate disables default CUDA features
and has no execution-codegen or trace-codegen build step.

Both systems use multi-stark `acfc370`, Goldilocks with quadratic extension,
log blowup 1, 64 FRI queries, binary folds, final polynomial length 1 and zero
proof-of-work. Ix's standard system includes its unused fixed Bytes1/Bytes2
chips; the comparison reports them explicitly. The `aiur/witness` span isolates
witness time inside the production proof API; the remaining proof time includes
planning and record disposal. New Aiur's corresponding report documents this
small difference in measurement boundaries.
