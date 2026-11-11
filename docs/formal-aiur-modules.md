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

The library modules are written as Lean syntax, as the applications are (see
"Writing modules in Lean" below): `aiur_library% deps ⟦ … ⟧` checks a fragment
against the libraries it uses, `deps`, and keeps only the fragment, so linking
clients share each dependency once; `aiur_library% ⟦ … ⟧` checks a fragment
that uses no other module. The string forms (`aiur_library% deps "…"`,
`aiur% "…"`) remain, and the frontend tests exercise them.

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

The application modules are Lean files containing embedded Aiur syntax.
Lean parses and elaborates the syntax when the package is built.

`IxVM/IxVM/Source/*.lean` contain the authored Aiur modules. They define Ixon
types and serialization, ingress, conversion, address maps, and the kernel subsystems
(limbs, natural primitives, levels, substitution, weak-head reduction,
inference, definitional equality, checking, claims, and evaluation), and the
entrypoints in `IxVM.lean`. Each `aiur_module` contains named `def` declarations
written with `aiur_fn⟦ … ⟧`. Imported modules retain these declarations in Lean's
persistent environment metadata. `IxVM/Program.lean` resolves the selected modules
and shared Goldilocks libraries together, then emits each function once as a
transparent Lean definition, such as `IxVM.KernelWhnf.whnf`. `IxVM.program`
contains references to those definitions; `IxVM.source` adds the certified
static tables. Execution and refinement proofs use that same source. Import
`IxVM` to use it from another Lean project; no source files are read at runtime.

`KernelRoleSpec.lean` is the one rendered module: `lake exe ix codegen` writes
it from IxC's role specifications (`Ix/IxVM/RoleSpecGen.lean`), reading only the
specification digest's bytes. `lake exe ix codegen --check` checks freshness.
The `ixvm-source` test compares the public program, tables, and bytecode with
full native preparation of the declaration metadata.
`lake exe ixvm/ixvm-proof-gen --check` checks the derived lookup and mirror
proof scripts; the lookup lemma for the example is `IxVM.KernelWhnf.whnf.lookup`.

`MultiStark/MultiStark/Modules/*.lean` hold proof and system decoding,
transcript, hash adapters, Merkle verification, PCS, the STARK verifier, and
aggregation. `MultiStark.recursionSource` and `MultiStark.aggregateSource`
(`MultiStark/MultiStark/Program.lean`) compose them; there is one copy of the
verifier implementation. `Recursion.lean` and `Aggregate.lean` are the two
definitions of module `MultiStark`, with the public entrypoints
`MultiStark::verify_multi_stark_proof` and `MultiStark::ix_aggr`.

The program elaborator (or `#aiur_check` for quoted programs) checks the
modules against their libraries, so an ill-formed module fails the build. Each
program also has a digest, BLAKE3 of its composed module input’s `Repr` rendering
computed at build time (`IxVM.programDigest`,
`MultiStark.recursionDigest`, `MultiStark.aggregateDigest`). The exporters
print it (`ixvm digest`, `stark-export digest [--aggregate]`) and report it
when they export, and `ix` caches each exported artifact under BLAKE3 of the
exporter binary and that digest.

### Writing modules in Lean

The embedded block is the module language of the string frontend, parsed by
Lean. Only the lexical surface differs: comments are Lean comments, a block
label is written `@name` (`'name` in source text), a negated operand keeps its
space (`a - -b`, `a / -b`), and a member of a projection needs parentheses
(`(p.0).f`). Nested generic arguments close as in Rust (`List<List<Field>>`).
An `aiur⟦ … ⟧` block is not checked on its own, since it may use modules of
other blocks; `aiur_library%` blocks are checked against their dependencies.
Lean parses the block where it reads the file, so a syntax error is reported in
place; the parse keeps only the block's text, which the elaborator lowers. (The
parse of ambiguous alternatives shares subtrees, and linters that walk a
command's syntax as a tree would take minutes on it.) Compiling a module that
nests very deeply can need a larger `maxRecDepth`, as the long role matches of
`KernelRoleSpec.lean` do.

`lake exe aiur/aiur_embed` converts `.aiur` text, and checks that both forms
lower to the same program:

```sh
lake exe aiur/aiur_embed into MultiStark/MultiStark/Modules/StarkVerifier.lean StarkVerifier.aiur
lake exe aiur/aiur_embed new  FILE.lean SOURCE.aiur NAMESPACE NAME [DOC]
lake exe aiur/aiur_embed body SOURCE.aiur
```

`into` replaces the block of an existing file and keeps its header.

### Divergences from main

The port's intentional differences from main's IxVM semantics, formerly
encoded in the retired `tools/ixvm/adapt.py`, are in the modules, each marked
by a `-- Port divergence` comment:

- `RBTreeMap`: address-keyed maps compare all 32 address bytes
  (`canon_ord_cmp_g`, `canon_ord_then`, `canon_addr_cmp`, `canon_addr_chunk`;
  formerly `CANON_ADDR_CMP_HELPERS`), never prover-chosen ROM addresses.
- `KernelRoles`: role-indexed maps (`RoleMap`, `role_map_lookup_or_default`) are
  separate from address-keyed maps, and role contexts are compared by
  `role_ctx_limit` (formerly `ROLE_MAP_HELPERS`).
- `KernelSubst::ctx_close_cut`: a cut that runs out of context closes at 0
  (review item R7).
- `KernelDefEq`: `k_is_def_eq_core` runs the ordered tiers without pointer
  shortcuts; the variable arms in `k_is_def_eq_struct_safe` and
  `try_def_eq_app` (the BVar arms); the literal-tag progress guard in
  `k_is_def_eq_struct_go`.
- `IxByteStream::read_byte_stream` and `Ingress::load_constant_hint` read typed
  hints.
- `IxVMCompat` holds the former `Compatibility.aiur`: IO hints, ordinary long
  division (`ordinary_div_mod`, `divide_grow`), `stream_equal`,
  `default_binding_addr`, `check_owned`; and `audit_div` from `PortCases.aiur`,
  whose probes are `IxVM::check_port_cases`.

Smaller rewrites with the same aims (byte matches through `to_field`, address
comparisons through `address_eq`, `klimbs_eq` for limb equality, and
`constrain_eq!` for recomposed advice) are in the bodies, unmarked. The
recursive verifier's adaptations (typed hints for IO and arithmetic advice,
`StarkHash::digest_eq` by all digest bits, the aggregation byte matches) are
likewise in its modules.

## Refactor checks

The retired legacy IxVM, as ported, was the behavioral reference, with the
previously reviewed adaptations: no unconstrained pointer values, explicit raw
hint channels, checked byte/word construction, and structural equality where
equality is required. Optional pointer shortcuts stay removed. These
adaptations have not been changed.
The port audit (the retired `audit.py`) distinguished lexical translation,
semantic adaptations, and library replacements; it was not a theorem of
equivalence to legacy. The adaptations are listed under "Divergences from
main" above.

Moving the modules from `.aiur` text into Lean changed no program. Compared
with the string frontend's programs from the `.aiur` bundles, the elaborated
IxVM, recursion and aggregation programs are equal (`==`) and render identically
(`Repr`), and the exported artifacts (`ixvm export-claim-trace`,
`stark-export export-trace [--aggregate]`) are byte-identical. Moving the library
modules and their test clients from strings into Lean likewise left every
library program equal and identically rendered, and the `u32_tests` and
`library_tests` exports byte-identical.

For the modularization itself, a comparison tool, `formal-checks refactor`,
compared complete compiled exports against the pre-refactor artifacts. It
permitted only declared name changes and no-op removal: empty bytecode guards
and trace assignments of each column to itself. Jump targets and hint
instruction offsets were adjusted for removed guards. All other instructions,
enum layouts, fixed-table rows, constraints, lookup messages, trace actions,
and group layouts had to match. Direct `*`/`&` syntax replaced the legacy inline
`load`/`store` wrappers, which accounts for those no-ops disappearing. The tool
read JSON exports, so it was retired when the artifacts moved to Ixon
serialization; its record below stands.

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

From the repository root:

```sh
lake build ixvm/ixvm multiStark/stark-export aiur/library_tests aiur/u32_tests
lake env Aiur/.lake/build/bin/library_tests .lake/libraries.json
cargo run --release --locked -p aiur --features stark --example library_check -- .lake/libraries.json
tools/ixvm/check-formal.sh
```

The library regression also instantiates abstract byte/word clients, rejects
opaque hints and incomplete providers, and checks accelerated execution against
table execution and reference trace generation. The full integration gate
covers valid/invalid IxVM claims, recursive proofs, aggregation, and the
production controller.

Validation of this refactor passed 2,586 accelerated/table execution and
reference-trace comparisons, the Lean arithmetic/domain/opacity checks, two
dishonest-hint proof rejections, and U64/Blake3 proofs. Application proof
checks, the controller gate, and the three-workload CPU proof/key parity gate
passed. CUDA runtime validation was not repeated for this refactor; the
measuring machine had no GPU.
