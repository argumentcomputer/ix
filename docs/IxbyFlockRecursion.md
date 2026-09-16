# Native Flock aggregation for parsing and execution

An original-format identity program now has a **499,347-byte complete execution
proof**. A fresh receiver verifies the approved profile/class/tree and the
32-byte expected digest, with no program, input, output or child proofs.
See [complete execution aggregation](#complete-paged-execution-aggregation).

## Complete original CSLib grammar aggregation

All **1,217 retained CSLib Program batches** now form one **360,907-byte**
native Flock proof bundle, including 53,168 bytes of folded root advice.
The separate expected statement is 1,008 bytes. The root verifier receives
these two files and externally expected source length/digest and batch count.
It compiles the approved setup without reading proofs or source bytes.

The claim is complete original Program grammar parsing, with genuine Start,
complete Done at EOF, and all intermediate parser states connected. Full
semantic program admission and execution of the CSLib verifier remain separate
full-workload measurements. See [streaming scope](IxbyFunctionalStreaming.md) and the
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

## Complete paged execution aggregation

[`PagedTreeCompiler`](../flock-stage4/recursive/src/execution_tree/mod.rs)
composes genuine production proofs for all eleven
[paged components](IxbyFlockPagedAdmission.md) and the
[endpoint relation](IxbyFlockPagedExecution.md#complete-endpoint-binding).
The verifier receives an externally selected IXFP profile, execution class,
eleven exact component counts, expected `S`, and one strict `IXFPTR00` bundle.
The profile and every child setup are compiled before reading proof bytes.
The final application statement is exactly the two field words of `S`.

The relation has three operations:

- **Chain:** connect every shared field and every boundary field of adjacent
  batches of the same component. Each genuine batch must make progress. Code,
  input and execution boundaries include all parser, capture, machine, clock
  and memory-root words, including suspended operations.
- **Concatenate:** collect complete component-chain statements in the fixed
  eleven-component protocol order, preserving all 283 words.
- **Close:** verify the concatenation and endpoint proofs, equate all 283
  component words, and publish only the endpoint proof's `S`.

Every operation constrains both complete child Flock verifiers. Fresh and
inherited Boolean-matrix, circuit-structure and jagged-layout claims enter the
parent's constrained folds; final verification checks all actual fixed tables.
Boolean claims can share a fold only after resolving their original table and
hashing its complete sparse matrix, dimensions and variable count. Identical
matrices from different registries therefore share work without dropping any
claim. This reduces the measured closing node from 558 to 315 table families
and from dense domain `M=32` to `M=31`.

The new tree policy admits 1 through `2^31` batches per component, with exactly
one constructor-ID component. Binary component chains use the largest power
of two strictly below the count; ordered component concatenation uses the same
rule on its component range. Exact setup compilation still enforces the native
recursion geometry limits. This count policy is separate from the existing
grammar tree's 65,536-leaf policy. The grammar tree's 1,217-leaf circuit and
setup identity remain unchanged after extracting the shared accumulator code.

### Complete original-format proof measurement

The fixture independently encodes a 34-byte IXBF identity program, a 50-byte
IXFI input and a 49-byte IXFO output containing a 34-byte Bytes value. It proves
every component using the production APIs, verifies all saved proofs, and
checks the initial captured memory against the native image. An independent
hash implementation derives the expected original-artifact commitment.
Each component has one batch; the endpoint proof is the twelfth leaf.

| Local measurement, four Rayon threads | Result |
| --- | ---: |
| Final proof, including all root advice | 499,347 bytes |
| Externally expected statement | 32 bytes |
| Root-advice words | 10,001 |
| Closing node witness and proving | 46.392 s |
| Fresh receiver setup | 138.569 s |
| Fresh receiver verification after setup | 16.788 s |
| Complete test, including all leaf/node proofs and fresh receiver | 629.27 s |
| GNU time wall time | 632.61 s |
| GNU time maximum RSS | 68,963,992 KiB |

The RSS is the reported maximum for this invocation, not a sum of process
peaks. The parent releases its compiler and proving graphs before starting the
fresh receiver. The receiver runs with a cleared environment and gets only
`S` and the root proof on stdin; its approved setup is part of the fixture.

The closing node has 4,644,403 variables, 902,986 arithmetic operations,
50,388 packing rows, 42,819 BLAKE3 compressions, 16 row variables and dense
domain `M=31`. Its setup identity is
`c0e99ed53b2c69f09c6dff31ec235f1289dffc93efa8838de4c2f4c168829d54`.
The [measurement record](../flock-stage4/census/paged-execution-identity-v0.json)
retains artifact hashes and exact timings.

A second genuinely valid endpoint proof changes parser metadata while keeping
`S` unchanged. The closing circuit rejects it when paired with the original
component root, exercising the equality of facts that endpoint checks alone
do not interpret. The fresh receiver also rejects both halves of each changed
digest word, changed root advice, setup/count headers, damaged proof bytes,
truncation and trailing bytes.

A separate 5,121-byte source test proves three batches across two recursive
levels. It rejects individually valid leaf proofs with disconnected memory
roots and all eighteen low/high-bit changes to the nine root statement words.
Its final proof is 304,891 bytes; the test takes 37.95 seconds.

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage4/Cargo.toml -p ix-flock-recursion \
  --lib \
  execution_tree::tests::fixture::original_bytes_identity_proves_one_execution_digest \
  -- --ignored --exact --nocapture --test-threads=1

RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage4/Cargo.toml -p ix-flock-recursion \
  source_chain_links_all_boundaries_through_two_recursive_levels \
  -- --ignored --nocapture --test-threads=1
```

`IXBY_PAGED_EXECUTION_OUT` optionally selects a retained fixture directory.
Cached proofs are accepted only after checking the newly generated expected
statement and the current approved verifier. The measurements establish a
complete original-format execution proof for this small fixture. They do not
measure the 2.268-billion-step CSLib execution, larger execution batches, or
the additional Lean refinement from these native constraints to semantics.

### Original-artifact command-line workflow

[`paged-execution`](../flock-stage4/recursive/src/bin/paged-execution/main.rs)
streams leaf generation, retains proofs in bounded files, aggregates exact
component counts, and verifies one final root. Each original artifact is
limited to 16 MiB by the current source classes. The output argument supplies
the original canonical IXFO bytes; the proof binds these to the returned Bytes
value. The currently supported execution classes are `small`, `objects`,
`compact`, `bytes`, `shared-compact`, `shared`, `shared-compact-boolean`,
`shared-boolean` and `shared-1024`. The last three use Boolean routing and
separate approved setups; `shared-1024` has 1,024 Fetch slots. See the
[larger-class implementation and measurements](IxbyFlockPagedExecution.md#boolean-routing-and-the-1024-fetch-class).
The complete original CSLib execution remains unproved.

```sh
RUSTFLAGS='-C target-cpu=native' cargo build --release --locked \
  --manifest-path flock-stage4/Cargo.toml -p ix-flock-recursion \
  --bin paged-execution

# Extract the explicit functional descriptor; every output path must be new.
flock-stage4/target/release/paged-execution profile \
  --program /path/to/original.ixby --out /path/to/profile.ixfp

# Independently compute the expected digest from the original byte strings.
flock-stage4/target/release/paged-execution statement \
  --profile /path/to/profile.ixfp --program /path/to/original.ixby \
  --input /path/to/original.ixbi --output /path/to/original.ixbo \
  --out /path/to/expected.statement

# Prove leaves and the complete root; use a new run directory.
flock-stage4/target/release/paged-execution prove \
  --profile /path/to/profile.ixfp --class shared-compact \
  --program /path/to/original.ixby --input /path/to/original.ixbi \
  --output /path/to/original.ixbo --out /path/to/run --threads 4

# Repeat the same prove command with --resume to check and reuse saved proofs.
# leaves.json records the eleven component counts. The caller supplies the
# approved counts explicitly to verification and aggregation.
env -i /absolute/path/to/paged-execution verify \
  --profile /path/to/profile.ixfp --class shared-compact \
  --counts N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10 \
  --statement /path/to/expected.statement --proof /path/to/run/root.flock \
  --threads 4
```

The `leaves` command uses the same arguments as `prove` and stops after saving
all checked leaf proofs, the endpoint proof and component counts. `aggregate`
takes `--profile`, `--class`, `--counts`, `--statement`, `--dir` and `--threads`
to finish such a directory. `census` takes the profile, class and counts to
compile the complete tree without reading proof bytes. Exact final setup is
preflighted before any recursive proving begins.

Resumption checks the original file hashes, profile and class. It regenerates
native state to obtain each leaf's expected statement and verifies every saved
leaf before reuse; it does not yet restore native execution from a checkpoint.
Every retained intermediate is verified under the freshly compiled approved
node. A retained complete root can be verified directly without reopening its
children. Sharded proof directories avoid placing every batch in one directory.
Atomic file writes leave incomplete pairs recoverable; complete but invalid
cached proofs cause an error.

A separate CLI fixture returns 1,025 bytes and exercises two output batches
and two batches in each Input/Output commitment bridge. Its approved counts
are `[1,1,1,1,1,1,1,2,1,2,2]`, including fourteen component leaves plus the
endpoint proof. The CLI produces a **503,683-byte** proof in 601.319 seconds.
An independent CLI receiver verifies it in 20.105 seconds after 147.553 seconds
of setup, using a separately computed expected digest. Checked leaf resumption
also passes. This is a second small-workload measurement, not a full CSLib run.
See the [CLI measurement record](../flock-stage4/census/paged-execution-cli-v0.json).

With `--class shared`, the same 1,025-byte fixture produces a **503,875-byte**
root in 643.673 seconds. A fresh CLI verifier accepts it in 21.636 seconds
after 149.079 seconds of setup. Its input directory contains only the approved
profile, independently computed expected digest and root proof. Peak process
RSS is 88,764,532 KiB for the complete proving command and 65,067,824 KiB for
the fresh verifier. See the [Shared CLI measurement](../flock-stage4/census/paged-execution-shared-cli-v0.json).

### Execution spanning several batches

The [countdown fixture](../flock-stage4/fixtures/paged-execution-countdown.py)
takes a Bytes value and the natural 40. It repeatedly cases on the natural
and tail-calls itself with its predecessor, then returns the original Bytes.
The independent reference interpreter takes exactly **83 transitions**,
including the final return-to-halt transition, and produces the expected
49-byte output. A fuel budget of 82 fails in both the reference interpreter
and the CLI prover; the generator's `--fuel 82` option reproduces that case.

The Shared class produces three genuine execution proofs. Their full state,
memory and fuel boundaries join across two recursive levels:

| Batch | Microstep interval | Consumed fuel interval |
| --- | --- | --- |
| 0 | 0–144 | 0–32 |
| 1 | 144–288 | 32–64 |
| 2 | 288–367 | 64–83 |

All thirteen component proofs and the endpoint proof produce one
**502,515-byte complete root** in 715.895 seconds. A fresh CLI receiver
accepts it in 22.616 seconds after 147.775 seconds of setup, with only the
approved profile, expected digest and root proof in its input directory.
This is a complete small execution spanning multiple execution batches;
the original CSLib execution remains unproved.

A separate check first verifies each genuine execution leaf, then rejects
repeated, reversed and skipped segment pairs at the recursive constraints.
Both retained execution levels verify, and all 57 expected words reject
independent low- and high-half mutations. This test takes 98.32 seconds.
See the [complete countdown measurement](../flock-stage4/census/paged-execution-countdown-v0.json)
for artifact pins, setup identity, proof timings and peak memory.

The same pinned countdown also passes with `shared-1024`: one execution leaf
covers microsteps 0–367 and fuel 0–83, and all eleven component counts are one.
Its complete **502,979-byte root** verifies in a fresh process from only the
approved profile, expected digest and root proof. The
[larger-class countdown record](../flock-stage4/census/paged-execution-countdown-1024-v0.json)
records 715.7 seconds for complete proving on the CPU server, 170.9 seconds
for fresh setup and 23.3 seconds for verification. A separate genuine CSLib
chain exercises multiple larger execution leaves and two recursive levels;
see the [larger execution checks](IxbyFlockPagedExecution.md#boolean-routing-and-the-1024-fetch-class).

To reproduce after building the CLI above, choose two new directories:

```sh
countdown_files=/path/to/new-countdown-files
countdown_proofs=/path/to/new-countdown-proofs
paged_cli=flock-stage4/target/release/paged-execution
python3 flock-stage4/fixtures/paged-execution-countdown.py --out "$countdown_files"
"$paged_cli" profile --program "$countdown_files/program.ixby" \
  --out "$countdown_files/profile.ixfp"
"$paged_cli" statement --profile "$countdown_files/profile.ixfp" \
  --program "$countdown_files/program.ixby" --input "$countdown_files/input.ixbi" \
  --output "$countdown_files/output.ixbo" --out "$countdown_files/expected.statement"
"$paged_cli" prove --profile "$countdown_files/profile.ixfp" --class shared \
  --program "$countdown_files/program.ixby" --input "$countdown_files/input.ixbi" \
  --output "$countdown_files/output.ixbo" --out "$countdown_proofs" --threads 4
"$paged_cli" verify --profile "$countdown_files/profile.ixfp" --class shared \
  --counts 1,1,1,1,1,1,3,1,1,1,1 --statement "$countdown_files/expected.statement" \
  --proof "$countdown_proofs/root.flock" --threads 4
IXBY_COUNTDOWN_PROOFS="$countdown_proofs" RUSTFLAGS='-C target-cpu=native' \
  RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage4/Cargo.toml -p ix-flock-recursion \
  execution_chain_rejects_repeated_reversed_and_skipped_valid_segments \
  -- --ignored --nocapture --test-threads=1
```

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
