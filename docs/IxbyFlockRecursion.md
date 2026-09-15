# First native Flock merge for streaming grammar proofs

The first two retained CSLib Program batches now have one independently
verified Flock proof. The proof bundle is **375,155 bytes**, including
57,312 bytes of deferred root values. The verifier receives the expected
source identity and outer parser states, this bundle, and its compiled setup.
It receives no child proofs or original source bytes.

This completes the first two-batch merge experiment. The complete 1,217-batch
Program chain has not been aggregated. Repeated recursion, accumulator folding,
tree coverage/padding, and whole-file Start/Done checks remain to be implemented.
The underlying claim is grammar parsing; it does not establish execution of
the CSLib verifier. See [streaming scope](IxbyFunctionalStreaming.md) and the
[execution plan](IxbyStage3ScalePlan.md).

## Relation and setup

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

## Deferred root checks

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

## Measured first pair

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

## Validation and entry points

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
