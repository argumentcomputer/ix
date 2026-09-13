# Experimental IxBy / Flock native workspace

This independent workspace starts the generic IxBy execution backend. Its
current implementation connects canonical byte admission, a fixed-capacity
scalar/control interpreter, BLAKE3/Exec commitments, and direct Flock proofs,
alongside labelled native gadget regressions. The native constraint-to-reference
refinement, broader crypto guest profile, and compiled Stage 2 verifier remain
unfinished. See [the direct scalar execution boundary](../docs/IxbyFlockScalar.md).
It is excluded from the root Cargo workspace and has no `aiur`, `multi-stark`,
or `ix-terminal` dependency. Test-only Plonky3 field crates provide arithmetic
differential oracles at the same revision used by the original tests.

Flock is pinned to `b310f35f35f68095537150a1c8c0a43caca9a29e`; no experimental
m37 patch/profile is enabled. `IMPORT-PROVENANCE.json` records the donor HEAD
and each working-source hash, including the uncommitted sizing changes.
Visibility/import/formatting adaptations are separate from the original
table/witness identities. The source worktree was not modified.

## What is imported

- Shared Boolean R1CS builder, initialized witness generation, F128 equality,
  canonical Goldilocks/add/multiply/extension gates, lane repacking, and byte
  windows; count/emit parity and bounded assertion-group wiring regressions.
- Generic BLAKE3 compression and byte/word/parameter packing extracted from
  the old statement-binding file, without its Stage 2 relation or decoder.
- Arithmetic and Merkle conformance proof/verification/strict artifact codecs.
  Their historical configuration identity lives under `conformance/config`;
  it is not the new generic execution protocol identity. These artifact types
  must never be accepted as Exec proofs through fallback decoding.

Ordinary tests include direct P3 differentials, noncanonical field elements,
wrong quotient/result/direction bits, all byte-window offsets, dummy-row zero
initialization (including the BLAKE3 constant pin), and circuit/schema drift.
New BLAKE3 regressions compare the compression gate with native hashes at
single-block boundaries and reject tampered R1CS output bits.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace
cargo fmt --manifest-path flock-stage3/Cargo.toml --all -- --check
cargo clippy --release --locked --manifest-path flock-stage3/Cargo.toml --workspace --all-targets -- -D warnings
```

The current ordinary suite passed 88 tests. The two imported conformance proofs
are opt-in and also passed locally on 2026-09-12, including their serialized
round trips and malicious operand/path/root/proof mutations:

| Label | Flock proof bundle bytes | Scope |
| --- | ---: | --- |
| Goldilocks arithmetic conformance | 129,251 | Base/extension arithmetic gadget circuit |
| BLAKE3 Merkle conformance | 108,171 | Four-level authentication-path gadget circuit |

These byte counts exclude the conformance artifact's public operands and
framing. They are neither generic Exec proof sizes nor terminal FFLONK sizes.
Tests ran with four Rayon workers, a 32 GiB virtual-address limit, and a
300-second timeout per test; this is a bounded regression, not peak-RSS or
production capacity evidence.

```sh
RAYON_NUM_THREADS=8 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace conformance:: -- --ignored --test-threads=1
```

The native `ixby::exec::compile_exec_profile` now mirrors the proof-free input
boundary in `Ix/Ixby/Flock/Contract.lean`, with a distinct Exec domain and a
fixed public template containing only two varying statement-digest limbs.
Guest code, branch outcomes, private input, Stage 2 keys and witness geometry
do not determine its setup. The Lean compiler instance and native refinement
remain to be supplied. See `docs/IxbyExec.md` for the theorem boundary.

The direct execution regression proved 39 changed programs/inputs covering
scalar values, both branch outcomes, recursion depths and all 20 enabled
scalar opcodes under one setup. Each complete proof was 296,091 bytes. Fresh
verification consumed only approved setup, the expected 32-byte full statement
digest and proof; recomputed, locally valid advice for substituted program/input
bytes rejected at the wiring check. These are small native Stage 3 executions,
not completed formal M3 refinement, a certified Stage 2 guest, or Stage 4 proofs.

## Generic interpreter access component

`host/src/ixby/access.rs` implements setup-capacity-only selector-based reads
for banks of 1–32 F128 words. Full 32-bit indices and live lengths are
constrained; selectors are computed from those bits, never supplied as
untrusted one-hot advice. Disabled reads require a zero index and return zero.
All cells outside the live prefix must be zero. The wiring wrapper pins every
validity residual to a verifier-owned zero word. Payload type/bytecode
admission and complete machine transitions remain separate, unfinished work.

The count-only emitter now retains instance-specific setup parameters and
does not materialize bank tables while counting. Count/emit tests compare
counts, I/O schemas, and exact A/B matrices. Constraint tests cover every
index/live length for representative capacities through 32, high index and
control bits, all padding-bit mutations, and every forged output bit.

An opt-in conformance test proves three distinct access patterns under the
same fixed setup, each with a 107,763-byte Flock bundle. Its verifier rebuilds
only setup and consumes externally expected public words, without evaluating
the gate. It rejects changed public words, changed proof bytes, truncation,
trailing bytes, and the old arithmetic-conformance transcript domain.
These are **bank-access gadget proofs**, not authenticated program execution,
Stage 3 Exec statements, or terminal compact proofs.

Repeated proving exposed a zerocheck failure when the new driver honored the
padding-elision hint on reused buffers. The bank driver therefore explicitly
zeroes all padding even when elision is offered. Poisoned-buffer tests cover
both flag values and empty/partial counts; repeated changed-input proofs pass
in one process. No upstream source or dependency pin was changed. This
prototype's full zero-fill cost must be included in future resource censuses.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::access::proof_tests:: -- --ignored --test-threads=1
```

## Generic byte authentication and statement binding

`host/src/ixby/bounded_hash.rs` constrains full unkeyed BLAKE3 with a fixed
physical block/tree schedule and private length. Canonical length/index
checks, every unused message byte, chunk flags/counters, conditional record
selection, odd tree propagation, and the final ROOT compression are part of
the circuit. The count pass and compilation use identical emission.

`ixby/commitment.rs` wires the exact existing profile/program/input/output
commitments and final statement digest. Program/input/output contents and
lengths are private wires; only capacities and fixed profile bytes determine
setup. All five domains share the large compression and selection tables.
Checked prefix-length addition rejects overflow, and the public layout is
reconstructed from setup plus externally expected digest limbs.

New opt-in proofs passed with one setup reused across changed private lengths:

| Conformance relation | Flock bundle bytes | Evidence |
| --- | ---: | --- |
| Full bounded BLAKE3, 3,073-byte capacity | 167,915 | Five private lengths; locally valid but miswired compression rejected |
| Complete IxBy byte-commitment chain | 146,043 | Changed private artifacts; fresh-process digest-only verification; wrong digest/profile/capacity rejected |

The commitment verifier child has an empty inherited environment, runs outside
the worktree, and receives only 32 expected digest bytes plus the proof on
stdin. It reconstructs setup/public constants and does not evaluate gates or
receive artifact bytes, native execution, or a prover public-vector dump.
These are still **byte-authentication component proofs**, not Exec proofs.
Empty or malformed artifacts can have valid byte commitments; canonical
decoding, full code admission, machine transitions and their Lean refinement
must still be constrained. See [the hash construction and trust boundary](../docs/IxbyFlockHash.md).

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::hash_proof_tests:: -- --ignored --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::commitment_proof_tests:: -- --ignored --test-threads=1
```

## Generic ordered-frame control component

`host/src/ixby/control` constrains fixed-capacity local/continuation banks,
binding, typed Bool branches, calls, tail calls, returns, exact fuel and
absorbing terminal padding. Every reserved field and unused cell is checked;
selectors are derived from full metadata, not supplied as one-hot advice.

Five real eight-step conformance traces share one setup and each produce a
117,107-byte Flock bundle. Fresh-process verification takes only externally
expected endpoints and the proof. A locally valid but spliced intermediate
state is rejected by the inter-step wiring argument. Nine ordinary tests
exercise hostile advice, output/padding corruption, full banks, count/emit
geometry and complete scratch initialization.

These are **control-component proofs**: resolved actions are still private,
unauthenticated advice, so they are not generic program executions. The new
Lean ordered-bank rules and finite-trace theorem reach reference and byte
execution with explicit instruction/operand/codec premises; the native
constraint/representation bridge remains unfinished. See
[the control construction and exact proof boundary](../docs/IxbyFlockControl.md).

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::control::proof_tests:: -- --ignored --test-threads=1
```
