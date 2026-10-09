# Proof compression

This crate provides the compression stages for an aggregated Ix certificate:
root Aiur proof → recursive FRI proof → KZG proof → recursive KZG proof.
The root may aggregate any number of certificate shards, and its Aiur proof
may itself contain multiple trace shards.

Configure compression locally, then provide only the proof address:

```sh
ix compression setup --srs /path/to/trusted.srs
ix compress ROOT_ADDRESS
ix verify COMPRESSED_ADDRESS
```

Both prover and verifier run setup independently with the same SRS, aggregate
backend, and bounds. Setup constructs a fixed circuit and its verification key;
it takes no certificate, proof, or imported compression key. The SRS is the
public KZG setup material, not a compression key supplied by a prover.

`compress` accepts a root produced by `ix aggregate` with the current default
aggregate parameters. It verifies the root, recursively wraps it through the
aggregate program, and pads that execution to the configured layout. It then
runs all three compression stages and verifies the final proof with the locally
generated key before writing it to the Ix store. The certificate claim is
preserved. The new address goes to stdout and progress to stderr.

The fixed layout has one Aiur trace shard, all circuits active, and one memory
closure pair per statically declared memory width. Function and memory tables
have `2^root-log-height` rows (default 20, supported 1–26); byte tables retain
their fixed heights. Every execution table must fit its bound, including the
recursive verification of the input root. Memory interval ends are private,
range-constrained inputs. Oversized executions are rejected; increasing the
bound requires a new setup on both sides. The number of original certificate
shards is not fixed, but the work to verify their aggregate proof must fit.
These bounds describe the normalized execution, not the input proof's size.

Local configurations live in `~/.ix/compression/<configuration-id>/`, separate
from the proof store. Override the directory with `IX_COMPRESSION_HOME`.
Each configuration contains `settings.json` and `verifier.bin`; `default` selects
the configuration used for proving. The compressed proof contains only a
version, configuration ID, and proof bytes. Verification selects an already
configured local key, never a key from the prover. Unknown configurations fail
with a setup error. Existing configurations remain available after another
setup becomes active. Treat this directory as trusted local configuration.

Setup stores the absolute SRS path for proving; verification needs only the
local verifier and settings, so the SRS file is not required for verification.
Repeated setup with the same parameters reuses the existing verifier.
For development only, use `--dev-srs` instead of `--srs FILE`; this generates
known-trapdoor parameters and stores `development.srs` locally. Such proofs
are not production-secure.

`--log-height` on setup sets the maximum KZG partition log-height
(16–26, default 24); the SRS must cover it. The FRI stage uses the aggregate
backend's query and proof-of-work parameters, blowup four, and partition
height `2^20`. Setup and proving can require substantial time and memory;
partition height is not a total memory limit. There is no automatic resume.
The aggregate environment audit remains available with
`ix verify --aggregate --ixe ENV [--ixes MANIFEST] COMPRESSED_ADDRESS`.

The SRS format is provided by `Srs::write` / `Srs::from_reader`: `IXKZGS01`,
a little-endian u32 log-length, `2^log-length` G1 powers, G2 and tau-G2, then
log-length + 1 degree keys, all in Ark's compressed point encoding. Import
checks subgroups and consistency; establish the SRS provenance independently.

The stages are library functions:

- `pipeline::FixedRoot` builds the fixed normalized-root verifier, and
  `pipeline::setup` derives the complete verification key without a witness.
  `FixedRoot::prepare` accepts only proofs matching that layout and policy.
- `pipeline::prepare_root` is the general, variable-layout API. It takes a trusted aggregate verifier key, the root
  proof, and the expected outer call claim reconstructed by the host. It
  checks Aiur's batch policy and builds a circuit verifying all trace shards.
- `Prepared::prove_fri` proves that circuit with caller-selected FRI parameters
  and a partition-height limit.
- `pipeline::prepare_kzg` constrains verification of the FRI proof and translates
  Goldilocks arithmetic to the BLS12-381 scalar field. `Prepared::prove_kzg`
  proves it with caller-supplied KZG parameters and a partition-height limit.
- `pipeline::prepare_recursive` builds the KZG verifier circuit.
  `RecursiveStage::prove` produces the final proof and pairing operands.
  `RecursiveVerifier::verify` checks the independently supplied expected claim,
  the outer proof, degree bounds, and both external pairing equations.

Every stage preserves the public statement. Activation claims are generated
by the lowering; no certificate digest, entrypoint index, partition count,
exact proof size, or measured table layout is hardcoded. Preparation and
proving are separate so callers can inspect the circuit and plan resources.
Verification objects retain verification parameters, not proving SRS powers.
KZG and recursive verifiers provide compact proof encoding and byte-level
verification; the expected certificate claim is supplied separately.

Verifier keys must be trusted independently of proof data. Keys produced by
local circuit construction can be used directly. Each stage verifier provides
`to_bytes` and `from_bytes` for versioned, verifier-only transport, including
its statement schema and public parameters. Authenticate the complete encoding
before loading it; accepting a key supplied alongside a proof does not establish
which certificate relation was proved. Decoders reject malformed metadata,
noncanonical encodings, and trailing bytes.

The stages do not manage an ix store, verifier registry, subprocesses, or
checkpoint files. KZG proving commits partitions separately and reconstructs
lookup traces from committed columns. The logical circuit, assignment and
prover coefficients remain resident; partition height is not a total memory
limit. The backend also exposes coefficient-checkpoint APIs for application
integration.

KZG parameters must have trusted provenance and pass `Srs::validate` before
use. `Srs::unsafe_dev_setup` is a deterministic test helper with a known
trapdoor; its proofs are not production-secure. No pipeline stage generates
an SRS implicitly. FRI parameters and resource limits are also chosen by the
caller. The circuit verifier currently supports Goldilocks with quadratic
challenges, cap-height zero, binary FRI, a constant final polynomial, active
preprocessed tables, and a bounded field-sampling retry budget. Unsupported
profiles fail during preparation.

`fri` contains the constrained transcript, algebra, Merkle and FRI verifier;
`foreign` translates field arithmetic; `kzg` implements the commitment backend;
`recursive` constrains KZG verification and exposes pairing operands.

Run generated fixtures, arithmetic comparisons, adversarial verification,
statement-binding, and streaming tests with:

```sh
cargo test --release -p ix-proof-compression
```

The complete-chain integration test uses a synthetic root relation with a
fixed layout, independently derives its key before constructing any proof,
runs all compression stages, and checks key equality and final verification
against the expected and a changed statement. Separate tests cover roots with
multiple Aiur trace shards. The synthetic relation is not the production Ix
aggregate program.
It uses development parameters and low FRI query counts to exercise the
algorithms; these are not production security settings. Run this expensive
test explicitly:

```sh
cargo test --release -p ix-proof-compression --test pipeline_root \
  complete_compression_chain -- --ignored --nocapture
```
