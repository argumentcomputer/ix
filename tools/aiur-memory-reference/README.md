# Optional Rust memory AIR reference

`Export.rs` calls the actual `aiur::memory::Memory::build` and serializes its
returned expression trees and lookup. It contains no replacement builder.
The required Compilatrix gate compares its frozen output with the Lean
builder for widths 0, 1, 2, 7, and 256. This is a fixture conformance check,
not a universal theorem about Rust or an IxVM verifying-key comparison.

The reference run uses Rust 1.98.1, ix revision
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`, and multi-stark revision
`9a90612286625b6cec59516532d4501677cf468c`. The relevant source SHA-256 values
observed in the clean reference checkout are:

| Source | SHA-256 |
| --- | --- |
| ix `crates/aiur/src/memory.rs` | `5762044cbed9d45a9f393459e7fbc71569bd8955ba408afa0f540dda08ce2c2a` |
| ix `crates/aiur/src/lib.rs` | `88d605423f79e310b73a643e122babae76a87407571edee7a1887faeb9a7f142` |
| multi-stark `src/expr.rs` | `09d491e5cef888975b21be9dcabd53f57b9d8c1c28204820fd74a5af2d1c2bb0` |

To regenerate, use a clean checkout at each revision and copy
`Cargo.toml.in` to `plans/aiur-memory-reference/Cargo.toml`. Replace the two
absolute paths with the exporter source and the pinned ix crate directory.
Run with Rust 1.98.1:

```sh
cargo run --manifest-path plans/aiur-memory-reference/Cargo.toml \
  > plans/aiur-memory-reference/expected.json
lake exe check-aiur --dump-memory-air plans/aiur-memory-reference/lean.json
```

Compare the parsed JSON with both `lean.json` and the committed
`fixtures/aiur-memory-air/expected.json`. JSON object ordering and whitespace
are immaterial. Constants are decimal strings; columns and widths are JSON
numbers. Expression arrays preserve every operator, argument order, current/
next column, transition mask, and signed lookup multiplicity. Unsupported
Rust expression forms cause the exporter to fail.

Regeneration is optional and keeps its dependency build outside production
and required CI. The required gate uses the frozen Rust artifact, exports the
Lean graph in a fresh process, compares the complete graph, and rejects eight
mutations. Review any fixture change against the pinned Rust source; never
regenerate the expected file from the Lean implementation.
