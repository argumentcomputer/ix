# Experimental IxBy / Flock native workspace

This independent workspace starts the generic IxBy execution backend. Its
current implementation connects canonical byte admission, a fixed-capacity
scalar/control and byte-capable interpreters, all 35 existing crypto-v0
primitives, bounded immutable constructors/PAPs, higher-order application,
explicit revision-1 exact Nats,
BLAKE3/Exec commitments, and direct Flock proofs, alongside labelled native
gadget regressions. The native constraint-to-reference refinement,
scalable guest execution, and compiled Stage 2 verifier remain unfinished.
See [the scalar execution boundary](../docs/IxbyFlockScalar.md)
and the explicit [byte](../docs/IxbyFlockBytes.md) and
[constructor](../docs/IxbyFlockObjects.md) setup upgrades, plus the
[exact-Nat setup and proof results](../docs/IxbyFlockNats.md) and explicit
[application setup](../docs/IxbyFlockApplications.md). The separate
[functional binary intake](../docs/IxbyFunctionalIntake.md),
[wide-fuel component](../docs/IxbyFlockWideFuel.md),
[constrained functional codecs](../docs/IxbyFunctionalCodec.md),
[record/reference components](../docs/IxbyFunctionalRecords.md),
[complete grammar-control component](../docs/IxbyFunctionalGrammar.md),
[scalar payload checks](../docs/IxbyFunctionalScalars.md),
[authenticated original-byte reads](../docs/IxbyFunctionalSource.md),
[state-selected whole-grammar dispatch](../docs/IxbyFunctionalDispatch.md),
[source-bound declaration/header registries](../docs/IxbyFunctionalRegistry.md) and
[complete instruction/reference checks](../docs/IxbyFunctionalReferences.md) start the
[full-guest scaling path](../docs/IxbyStage3ScalePlan.md); they do not yet
admit the compiler's IXBF artifact to the native Exec prover.
It is excluded from the root Cargo workspace and has no `aiur`, `multi-stark`,
or `ix-terminal` dependency. Test-only Plonky3 field crates provide arithmetic
differential oracles at the same revision used by the original tests.
`num-bigint` preserves unbounded functional-binary metadata during host intake
and also supplies independent multiword Nat arithmetic test differentials.

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
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace -- --test-threads=4
cargo fmt --manifest-path flock-stage3/Cargo.toml --all -- --check
cargo clippy --release --locked --manifest-path flock-stage3/Cargo.toml --workspace --all-targets -- -D warnings
```

All 244 ordinary tests pass, including byte, word, constructor, Nat,
application, complete-functional intake, wide-fuel, constrained-codec and
complete-grammar/scalar-payload, source-authentication, generic-dispatch and
source-bound registry, instruction/reference and
[typed transport-value](../docs/IxbyFunctionalValues.md) regressions;
41 proof/benchmark/external-fixture
tests are opt-in. The two imported
conformance proofs are opt-in and also passed locally on 2026-09-12, including their serialized
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

## Packed-word BLAKE3 experiment

`host/src/packed_blake3` adds a separate raw-compression component using ten
small Boolean tables. Four independent u32 lanes share each F128 word;
fixed add/XOR-rotate/lane-shuffle gates implement all seven rounds, and one
linear gate supplies the complete message schedule. The default Exec compiler
still uses the original compression table and retains its setup identity.
`compile_exec_profile_with_backend(..., Blake3Backend::PackedWordsV0)` now
selects the packed implementation explicitly at setup, never from a guest or
proof header. It binds a distinct implementation/registry/circuit/transcript
identity; no old-key reuse is claimed for this backend upgrade.

The new component has 23,808 A/B nonzero entries, down from the original
44,442,498, but uses 632 dense witness words per compression instead of 92.
Nineteen shared compressions require outer `nu=11`, not the old `nu=8`.
The integrated baseline has 53,288 dense words and 53 live PCS lanes, versus
43,028 and 43 for the default backend. Both retain Fast128/m23 and all 371
queries. These tradeoffs require fresh whole-relation admission before proving.

Seven ordinary tests cover every witness-column mutation, overflow/rotation,
all message basis bits, recycled padding, full upstream compression
differentials, independent hashes for lengths 0–64, and exact count/compile
registry agreement. Two real Fast128/m22 proofs verify in fresh processes
given only fixed setup, four externally expected output words, and the proof.
Each bundle is 114,027 bytes, excluding the 64-byte expected output. A proof
containing a valid local addition row with broken circuit wiring is rejected.
These particular proofs cover raw compression, not Exec or FFLONK.
The [historical component report](../flock-stage4/census/packed-blake3-components-v0.json)
also records the complete 14,121,316-row terminal A/B component census and its
limits; its counts are not a full-verifier estimate.

The bounded-hash and five-domain commitment chain now share all ten packed
tables and their fixed IV wire. Ordinary differentials cover private lengths
at block/chunk boundaries and odd trees through 7,169 bytes, with identical
count/compile layouts. A separate opt-in regression proves all 39 scalar/control
corpus cases under one packed setup. Each complete Exec bundle is 339,563
bytes, plus the independently expected 32-byte S. Fresh verifier children
receive only S and the proof. Both directions of cross-backend substitution,
forged matching headers, changed S, malformed transport and a recomputed valid
addition row violating global wiring are rejected. This is native Stage 3
execution evidence, not formal refinement or a terminal proof. See the
[integrated backend report](../flock-stage4/census/exec-packed-blake3-root-closed-v0.json)
for the separately measured Stage 4 relation and remaining admission gates.

```sh
ulimit -v 16777216
RAYON_NUM_THREADS=4 timeout 240 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  private_compressions_verify_in_fresh_process_and_reject_broken_wiring -- --ignored --test-threads=1 --nocapture
```
