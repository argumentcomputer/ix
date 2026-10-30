# Formal Aiur program libraries

The new programs use ordinary Aiur modules and the existing verified module
linker. Shared arithmetic and data structures live in `Aiur/Aiur/Library`;
IxVM and the recursive verifier compose them in their own Lean packages.
There are no new AST operations, native arithmetic primitives, or proof axioms.

| Library | Interface and implementation |
| --- | --- |
| `U8/Signature.lean`, `U8.lean` | `U8Signature` and its checked `UInt8` fixed-table implementation. Bytes and split parts are opaque. The interface exposes checked constructors and typed literals, not the backing tables. |
| `U32/Signature.lean`, `U32.lean` | `U32Signature` and `UInt32`, with opaque byte-array words and compact words. Advice supplies raw fields; byte lookups and carry equations check them. |
| `U32/Goldilocks.lean` | Explicit field selection, including the proved characteristic bound. The same U32 implementation works over any field whose natural cast is injective below `3 * 2^32`; another large prime does not require copied arithmetic. |
| `U64.lean` | Shared little-endian byte arithmetic and checked conversions, with its separate `2^56` field bound. |
| `List.lean` | Polymorphic lists, length, concatenation, lookup, take/drop, snoc, and reversal. No word-library dependency. |
| `List/Word.lean` | Checked depth and U64-indexed list operations, separated from the generic list library. |
| `Option.lean`, `Bytes.lean` | Shared option layout, byte streams, 32-byte addresses, and structural address equality. |
| `Blake3.lean` | Shared compression, hashing, address conversion, and digest packing. Uses the byte, word, and list libraries. |
| `Field/Goldilocks.lean` | Canonical field encoding, checked inverse advice, and quadratic extension arithmetic with nonresidue 7. This implementation is specifically selected for Goldilocks, unlike the bounded U32 implementation. |

Signatures check types, opacity, and provider conformance. They do not assert
that an arbitrary provider implements correct integer arithmetic: a replacement
still needs its own arithmetic argument and tests. Existing U32 arithmetic
lemmas remain in `U32/Correctness.lean`. A BN254 application can reuse bounded
word arithmetic after establishing the field bounds; it must choose a suitable
extension field separately instead of reusing the Goldilocks extension blindly.

Module parameters select providers statically. For example:

```text
module AddWords<W: U32Signature> {
    fn add(a: Field, b: Field) -> Field {
        let x = W::from_field(a);
        let y = W::from_field(b);
        W::compact_field(W::compact(W::add(x, y)))
    }
}
module Selected = AddWords::<UInt32>;
```

`U32Signature` shares its byte boundary with the selected `UInt8` provider.
The applications use that provider consistently. Hints cannot construct the
opaque types, even through an abstract module parameter. Host hint closures
and table accelerators remain registered in Rust; their channels, table names,
row indices, and constraints are unchanged by this refactor.

## Applications and source composition

`IxVM/IxVM/Program.sources` composes the root entrypoints with Ixon types and
serialization, ingress, conversion, address maps, and the kernel subsystems:
limbs, natural primitives, levels, substitution, weak-head reduction,
inference, definitional equality, canonical checks, checking, claims, and
evaluation. Those modules are in `IxVM/IxVM/Modules`.

`MultiStark/MultiStark/Program.sources` composes proof and system decoding,
transcript, hash adapters, Merkle verification, PCS, and the STARK verifier.
`Aggregate.sources` uses those same files and adds aggregation. There is one
copy of the verifier implementation. The separate root files retain the public
entrypoints `MultiStark::verify_multi_stark_proof` and `MultiStark::ix_aggr`.

The manifests are ordered lists of relative source paths. `Aiur.SourceBundle`
reads them outside the language frontend; the AST still contains only module
declarations. Both exporters and the CLI artifact cache consume the complete
bundle, so editing a dependency invalidates the cache. Shared Lean libraries
are linked into the exporter and covered by its binary digest.

`tools/ixvm/adapt.py` and `recursion.py` reproduce the application modules from
the pinned legacy sources and reviewed compatibility adapters. This is port
maintenance tooling, not Rust code generation. `modules.py` changes global
names and extracts shared bodies; it checks inverse renaming and exact helper
bodies. The ordinary frontend then checks every cross-module reference. The
`*.names.json` files map old port names to their new locations, including types
inside monomorphized names. Existing tuned groups use the relocated names.

## Compatibility checks

Legacy is the behavioral reference, with the previously reviewed adaptations:
no unconstrained pointer values, explicit raw hint channels, checked byte/word
construction, and structural equality where equality is required. Optional
pointer shortcuts stay removed. These adaptations have not been changed.
The port audit distinguishes lexical translation, semantic adaptations, and
library replacements; it is not a theorem of equivalence to legacy.

For the modularization itself, `tools/ixvm/check-refactor.py` compares complete
compiled exports against the pre-refactor artifacts. It permits only declared
name changes and no-op removal: empty bytecode guards and trace assignments of
each column to itself. Jump targets and hint instruction offsets are adjusted
for removed guards. All other instructions, enum layouts, fixed-table rows,
constraints, lookup messages, trace actions, and group layouts must match.
Direct `*`/`&` syntax replaces the legacy inline `load`/`store` wrappers, which
accounts for those no-ops disappearing.

The comparison against `44ea8742` passed for all three applications:

| Application | Bytecode functions | Function chips after deduplication | Ungrouped function columns, before = after | Tuned groups | Empty guards removed |
| --- | ---: | ---: | ---: | ---: | ---: |
| IxVM | 828 | 778 | 19,675 | 112 | 3,404 |
| Recursive verifier | 224 | 189 | 5,907 | 39 | 390 |
| Aggregation | 285 | 245 | 7,878 | 39 | 528 |

These column counts cover the function chips, before the host adds memory,
fixed-table, and lookup-protocol columns. Those inputs also compare exactly;
this refactor does not change circuit size or grouping. The checks and artifact
hashes are saved in [the comparison record](benchmarks/formal-aiur-modules/summary.json).
The pinned legacy program sources are unchanged between the pin and that
baseline. Distributed workers recognize both the relocated `check_owned`
callable and the old name used by cached artifacts.

From the repository root:

```sh
python3 tools/ixvm/adapt.py --check
python3 tools/ixvm/recursion.py --check
python3 tools/ixvm/audit.py --out .lake/port-audit
lake build ixvm/ixvm multiStark/stark-export aiur/library_tests aiur/u32_tests
lake env Aiur/.lake/build/bin/library_tests .lake/libraries.json
cargo run --release --locked -p aiur --features stark --example library_check -- .lake/libraries.json
tools/ixvm/check-formal.sh
```

The library regression also instantiates abstract byte/word clients, rejects
opaque hints and incomplete providers, and checks accelerated execution against
table execution and reference trace generation. The full integration gate
covers valid/invalid IxVM claims, the retained legacy bytecode entrypoint,
recursive proofs, aggregation, and production controllers.

Validation of this refactor passed 2,586 accelerated/table execution and
reference-trace comparisons, the Lean arithmetic/domain/opacity checks, two
dishonest-hint proof rejections, and U64/Blake3 proofs. Application proof checks,
resident/distributed controllers, and the three-workload CPU proof/key parity
gate passed. The first controller run exposed the renamed worker callable;
the controller gate passed after adding compatibility for both names. CUDA
runtime validation was not repeated on this machine, which has no GPU.
