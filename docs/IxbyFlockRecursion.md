# Native Flock aggregation for streaming grammar proofs

All **1,217 retained CSLib Program batches** now form one **360,907-byte**
native Flock proof bundle, including 53,168 bytes of folded root advice.
The separate expected statement is 1,008 bytes. The root verifier receives
these two files and externally expected source length/digest and batch count.
It compiles the approved setup without reading proofs or source bytes.

The claim is complete original Program grammar parsing, with genuine Start,
complete Done at EOF, and all intermediate parser states connected. Full
semantic program admission and execution of the CSLib verifier remain separate
work. See [streaming scope](IxbyFunctionalStreaming.md) and the
[execution plan](IxbyStage3ScalePlan.md).

## Complete aggregation relation

`GrammarTreeCompiler` admits an exact leaf count from 2 through 65,536. Each
node splits at the largest power of two strictly below its count. The complete
CSLib root joins 1,024 and 193 leaves; the latter joins 128 and 65, and 65 joins
64 and one. There are exactly 1,216 binary merges and no padding leaves.
Every real leaf must advance its parser cursor. The count and child classes
belong to setup and are checked before decoding a submitted root proof.

Each parent constrains both complete child Flock verifiers, including mixed
Boolean/element children at later levels. All three original-source words and
all 30 intermediate state words are equal across each join. Source metadata,
grammar counters, payload obligations and UTF-8 state therefore cannot change
at an internal boundary. Root verification additionally enforces zero Program
context at Start, complete Done and the exact externally expected file length.

Original-matrix, circuit and jagged-layout claims are grouped by approved fixed
table identity. Their values, points and weights are bound to actual child
verifier outputs and inherited public advice, then folded inside each parent.
Fresh fold challenges include the claims and approved identities. The final
verifier checks every folded family against its compiled table. Descriptors,
table identities and index mappings never come from proof bytes.

The root has 98 fixed-table families and 3,323 root-advice words. Its geometry
is 2,769,854 variables, 911,346 arithmetic operations, 28,409 packing rows and
29,481 BLAKE3 compressions. The row domain has 15 variables and the dense
commitment has 31. These are native GF(2^128)/BLAKE3 constraints; the Stage 4
workspace supplies the reusable verifier compiler, without invoking FFLONK.

### Full CSLib measurement

The Intel Xeon 6975P-C server used eight in-process workers, each with four
Rayon threads. A single setup was shared within each level, and proving graphs
were released between levels while approved verifier cores were retained.

| Measurement | Result |
| --- | ---: |
| Original retained Program chain | 492,388,476 bytes |
| Aggregate proof, including all root advice | 360,907 bytes |
| Expected statement | 1,008 bytes |
| Complete server aggregation and root check | 2,099.490 s |
| Process wall time | 2,102.80 s |
| Single-process maximum RSS, GNU time | 54,413,188 KiB |
| Final node proving, including advice | 41.237 s |
| Server root verification after setup | 12.352 s |
| Fresh local setup compilation | 80.389 s |
| Fresh local root verification after setup | 13.187 s |
| Fresh local process wall, including nine rejection checks | 96.23 s |
| Fresh local maximum RSS, GNU time | 31,355,436 KiB |

The process RSS includes every worker thread; it is not a sum of separate
worker peaks. The original leaf proving run is excluded from these times.
The local receiver ran outside the worktree with a cleared environment and
received no child proof or source-file path. Nine checks rejected changed
source/state words, setup/count header fields, root advice, damaged proof
bytes, truncation and trailing data. A separate five-real-batch test exercised
the uneven `4 + 1` tree and independent reception before the full run.
Proofs and statements are written with create-new files. An explicit resume
mode checks the source/count configuration and cryptographically verifies
each cached node under its freshly compiled approved class before reuse.

Pins:

- Root setup: `645e27b9c5a3abecced8df15349e5a6b6b811f3adbf3cceb6e2fd1e2e1da36df`.
- Proof SHA-256: `f4cbe2d0203bc57ed99d167ac8218271dca28007f9c93970dda0b560e7c9d163`.
- Expected statement SHA-256: `17765dc30db5e28967f5fc53bb0681e6551d3adcbb13fc02ddc9efe22f12f937`.
- Executed binary SHA-256: `1f5f6ffdf633f85c0dcc7f332a151b4dcd5aac7898e31e92061a29cd8d0fd9ab`.

The server binary used
`-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq,+vpclmulqdq,+aes`.
The remote artifacts are under `/tmp/ixby-grammar-tree.I7oyt8/`; the root,
statement, result, complete log and GNU timing were retrieved into
`/tmp/ixby-tree-full-result.dvcvCN/`. These are scratch artifacts.
The checked-in [measurement record](../flock-stage4/census/grammar-tree-cslib-v0.json)
retains the per-level geometry, timings and artifact hashes.

### Reproduce the complete tree

```sh
cargo build --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion --bin grammar-tree

# Compile the exact tree and report geometry without reading any proofs.
flock-stage4/target/release/grammar-tree census --batches 1217

# Prove every internal node; retain intermediate nodes for checked resumption.
flock-stage4/target/release/grammar-tree aggregate \
  --frames /path/to/program-frames --out /path/to/new-output \
  --batches 1217 --length 1016587 \
  --digest 96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05 \
  --workers 8 --threads 4

# Independent receiver: no original files, leaves or intermediate proofs.
env -i RAYON_NUM_THREADS=4 /absolute/path/to/grammar-tree verify \
  --proof /path/to/root.flock --statement /path/to/root.statement \
  --batches 1217 --length 1016587 \
  --digest 96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05 \
  --check-rejections
```

The complete-tree implementation is in
[tree.rs](../flock-stage4/recursive/src/tree.rs), with constrained folds in
[fold.rs](../flock-stage4/recursive/src/fold.rs) and the reproducible runner in
[grammar-tree.rs](../flock-stage4/recursive/src/bin/grammar-tree.rs).

## Earlier two-child prototype

The original pair experiment below retains its own setup and encoding. It
carried raw root claims and produced a 375,155-byte bundle. The complete tree
above uses mixed child verification, folded claims and an exact coverage
relation, so these historical proof sizes and setup identities differ.

### Pair relation and setup

The fixed child setup is the existing 32-step, source-depth-14, Nat-4096
grammar batch under Fast128. `CompiledGrammarBatch` owns its exact circuit,
public template, PCS parameters and transcript domain. Its strict `IXFSTB00`
verifier replaces the previous test-only verifier without changing the leaf
relation or proof encoding.

`compile_grammar_batch_replay` compiles every child verifier phase without
reading a source file, statement, proof or witness. Native recording of each
real child must match that complete topology. The native recursion backend
then constrains:

- Chained BLAKE3, fork/join links, challenge derivation and grinding predicates.
- The approved registry/count/circuit prefix and the hash of the actual child
  public vector, including every fixed public word.
- Boolean zerocheck/lincheck, Product-GKR wiring and gather recombination.
- Both ring switches, merged PCS, multipoint/Frobenius assist and Ligerito,
  including extension-field identities, query indices, caps and Merkle paths.
- All three source-identity words and all 30 intermediate parser-state words
  shared between the left and right children.

The 63 application outputs are the source length/digest, left initial state
and right final state. The circuit has exactly two child verifiers. Each
child proves a bounded batch; the parent does not claim an exact number of
active decoder steps or independently assert whole-file Start/Done.

Native GF(2^128) multiply/add equations occupy a fixed 64-operation element
table. A second element table constrains canonical Boolean bit decompositions
and their packed field words. BLAKE3 uses the existing Boolean compression
table. These are Flock-native constraints; no prime-field reinterpretation or
terminal KZG-FFLONK proof is involved.

The circuit graph fixes every variable, gate, constant, equality and public
position. Advice regeneration must reproduce that graph exactly. The root
verifier compiles the approved setup; proof headers cannot select a registry,
profile, circuit, transcript or public layout.

### Pair deferred root checks

Each child exports 70 original matrix claims, three circuit-structure claims
and three jagged-layout claims. Their values and weights are circuit wires
derived from the verifier above. Shared wires are published once, producing
3,582 root-advice words for both children.

The root verifier first verifies the parent Flock proof, then directly checks
all **152** claims against the approved child matrices, wiring and layout.
Root descriptors, table identities and index mappings belong to compiled setup;
the bundle supplies only field values. Changed values remain subject to both
the parent proof and the root checks.

This prototype carries the two children's raw claims. It does not fold them
into a constant-size accumulator across an arbitrary tree. A further merge
must verify mixed Boolean/element Flock children, bind inherited claims to
their public outputs, and constrain the folds. Merely running the native root
checks while generating advice would not satisfy that requirement.

### Measured first pair

The leaves are `program-000000.frame` and `program-000001.frame` from the
complete retained CSLib Program run. Each frame is 404,592 bytes, including
its 484-byte length/state wrapper; each child proof is 404,108 bytes.

| Item | Result |
| --- | ---: |
| Parent bundle, including root advice | 375,155 bytes |
| Root advice | 3,582 words / 57,312 bytes |
| Arithmetic equations | 666,730 |
| Packed arithmetic rows | 10,418 |
| Bit packing rows | 21,742 |
| BLAKE3 compressions | 17,874 |
| Variables / equality links | 1,646,480 / 139,565 |
| Fixed public words | 1,412 |
| Flock profile | Slim128, BLAKE3 |
| Row variables / dense variables | 15 / 30 |
| Batch logarithm / committed lanes | 6 / 60 |
| Local setup compilation | 17.769 s |
| Local `prove` call, including advice | 2.199 s |
| Fresh-process root verification after setup | 150.322 ms |
| Complete test, including both setup compilations and rejection checks | 43.40 s |
| Process maximum RSS reported by GNU time | 6,597,836 KiB |

The prover used 16 Rayon threads; the separate root verifier used four.
Setup compilation dominates this one-pair test and can be reused for further
pairs. The RSS figure is not a sum of simultaneously running process RSS.
Measurements do not predict the geometry or cost of later recursive levels.

The Intel Xeon 6975P-C server reproduced the **identical proof and expected
statement bytes** with 32 prover threads and a separate four-thread verifier.
Setup took 15.517 seconds, proving 2.033 seconds, and root verification after
setup 202.151 milliseconds. The complete test took 38.84 seconds, with
6,611,684 KiB maximum RSS reported by GNU time. Its artifacts were retrieved
into `/tmp/ixby-grammar-pair-server.p1mFFd/`; the remote run remains under
`/tmp/ixby-grammar-pair.p1mFFd/`.

The server binary used
`-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq,+vpclmulqdq,+aes`.
Its SHA-256 was
`0ef61ebbdd66facda7cf27eec15284f560cabbb993ffc3f2bb8612a361c7cb58`;
a copy is retained as `ixby-pair-tests-portable` beside the local artifacts.

Pins:

- Replay topology: `773034df2c4ddbf47fe15c434db30e9f0f617a9a839d383e4c284aeae8e540b6`.
- Parent setup: `823ec504e09ad4c6177cb61d576324c55fd0d0172902ecb3262665c33d09ca2a`.
- Parent proof SHA-256: `3b710b96eadcce82de1850405c556160e44441cd0b130b2cdfb3559fa4d78bd6`.
- Expected statement SHA-256: `0ee141d60600a0b652e0e9b57aca5023d7f9cf0a639619eb993c047de307ff79`.

Proof, expected statement, log and process timing are retained under
`/tmp/ixby-grammar-pair.qPthMC/`. They are scratch artifacts, not repository
fixtures. The original Program is 1,016,587 bytes with raw BLAKE3
`96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05`.

### Pair validation and entry points

The fresh receiver runs with a cleared environment and only the parent-bundle
and expected-statement paths. Changed source/state words, root advice,
damaged proof bytes, truncation and trailing bytes reject. Reusing the first
valid child as the second child rejects at the intermediate boundary. Separate
table checks reject wrong arithmetic outputs, non-Boolean decomposition words,
wrong packed words and nonzero unused rows.

Regression checks passed 268 ordinary Stage 3 tests and 267 tests in this
workspace, plus Clippy with warnings denied in both. The existing three-guest
Exec replay retained identical complete topologies. All three complete CSLib
grammar chains also passed the new production leaf verifier, with transport
context derived from the verified Program chain.

Implementation:

- [Fixed leaf verifier](../flock-stage3/host/src/ixby/ixbf_decode/stream/batch.rs).
- [Proof-free child replay](../flock-stage4/exec/src/batch_replay.rs).
- [Native parent constraints](../flock-stage4/recursive/src/pair.rs).
- [Parent proof and root verification](../flock-stage4/recursive/src/proof.rs).

The recursive crate is housed in the Stage 4 workspace to reuse its neutral
verifier compiler. Its output is a native Flock proof.

```sh
# Ordinary backend checks.
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion

# Retained two-child constraint replay and every direct root check.
IXBY_CSLIB_FRAME_DIR=/path/to/retained/program-frames RAYON_NUM_THREADS=4 \
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion retained_pair_native_constraints_and_roots \
  -- --ignored --nocapture

# One real parent proof plus a fresh root-verification process. Output paths
# must not exist; the test also writes pair.statement beside pair.flock.
IXBY_CSLIB_FRAME_DIR=/path/to/retained/program-frames \
IXBY_PAIR_PROOF_OUT=/path/to/new-output/pair.flock RAYON_NUM_THREADS=16 \
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion retained_pair_proves_one_flock_root \
  -- --ignored --nocapture
```
