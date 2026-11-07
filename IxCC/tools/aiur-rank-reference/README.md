# Optional Rust rank AIR reference

`Export.rs` invokes the actual pinned `Toplevel::build_constraints`, after
claim-shape, component, and row-count admission. It exports complete graphs
for six two-function examples: legacy ordered ranks, component-ordered ranks,
boundary ranks, an unranked caller with a ranked callee, a zero-rank callee,
and a selector-gated ordered call. It also invokes the actual private
`Bytes2::preprocessed` and `Bytes2::lookups` through the pinned module tree.
No replacement constraint builder or byte-table generator is used.

Because the gadget API is private, the generated wrapper uses Rust
`include!` on the unchanged upstream `lib.rs`, then adds the exporter as a
sibling module. Rust resolves the original modules at their original paths.
The wrapper lives under `plans/`; no upstream file is copied or modified.
`Prepare.lean` checks the six relevant source digests before writing it.

The recorded run used Rust 1.98.1, ix
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`, and multi-stark
`9a90612286625b6cec59516532d4501677cf468c`. Use a clean checkout at that ix
revision. The source SHA-256 values are:

| Source | SHA-256 |
| --- | --- |
| ix `crates/aiur/src/lib.rs` | `88d605423f79e310b73a643e122babae76a87407571edee7a1887faeb9a7f142` |
| ix `crates/aiur/src/constraints.rs` | `f9c8d433e4c49987b21b8e33be0533eb1f2b6e8b75ab26d8ffaf2f7fe9889fa9` |
| ix `crates/aiur/src/gadgets.rs` | `bd755d8f39675004fdc5434e66344c4ed8849de9ad91a58f86e121b5a522baeb` |
| ix `crates/aiur/src/gadgets/bytes2.rs` | `f0fc58ec29c758b3b398977311efb6e3b1df8b01f6916e9ebd464a34ed8e866a` |
| ix `crates/aiur/src/call_order.rs` | `8660340043b03c728f72431f86f8d5244056363a71fb4f5fba1478deb7207c73` |
| ix `crates/aiur/src/bytecode.rs` | `f3b2ac1a00db49f964313010a63b39906a6b8c30f51b1e1087edf782be6d8cb6` |
| multi-stark `src/expr.rs` | `09d491e5cef888975b21be9dcabd53f57b9d8c1c28204820fd74a5af2d1c2bb0` |

From the IxCC root, with Rust 1.98.1 selected for both `cargo` and
`rustc`, prepare and run the optional producer:

```sh
lake env lean --run tools/aiur-rank-reference/Prepare.lean \
  /absolute/path/to/pinned/ix plans/aiur-rank-reference
cargo run --manifest-path plans/aiur-rank-reference/Cargo.toml \
  --target-dir plans/aiur-rank-reference/target -- plans/aiur-rank-reference/rust
lake exe check-aiur --dump-rank-air plans/aiur-rank-reference/lean
```

Compare the parsed `expected.json` objects and the exact `range-columns.bin`
bytes with each other and with the committed `fixtures/aiur-rank-air/` files.
The binary contains 65,536 row pairs, two canonical u8 values per row,
projected from columns zero and one of the actual 11-column fixed table.
Other preprocessed columns and other gadget lookups are outside this fixture.
Constants are decimal JSON strings; operator order, columns, selectors,
lookup order, argument order, and signs are all retained.

The recorded output digests are
`342de19aca878d3df0b9458ab6fcb8972e48abd2c8fdd9ac963f37f0dcb17414`
for `expected.json` and
`281f79f89f0121c31db2bea5d7151db246349b25f5901c114505c18bfaa50ba1`
for `range-columns.bin`. Required CI consumes these frozen Rust artifacts,
compares a fresh Lean process's outputs, and rejects 14 graph/table mutations.
Do not regenerate expected fixtures from the Lean model. The optional Rust
dependency build is outside production and required CI. These examples do
not prove the universal Rust compiler or bind the production IxVM to a key.
