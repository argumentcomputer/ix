# Proof compression

Compress an aggregated Ix certificate through three stages:
root Aiur proof → FRI proof → KZG proof → recursive KZG proof.
The certificate claim remains unchanged. The root can aggregate any number of
shards, provided its recursive verification fits the configured trace bounds.

## Local setup and CLI

Build with `lake build ix`, then run `.lake/build/bin/ix` (called `ix` below):

```sh
ix compression setup --srs /path/to/trusted.srs
ix compress ROOT_ADDRESS
ix verify COMPRESSED_ADDRESS
```

The prover and verifier each run setup with the same SRS, compiled aggregate
backend, and bounds. Setup derives a fixed verifier locally without a certificate
or proof. The prover supplies only the proof; no verifier key is accepted from it.
`compress` accepts a root from `ix aggregate` using the current default aggregate
parameters, checks it, normalizes it, runs all three stages, and verifies the
result against the local key before saving it. It prints the new store address
to stdout and progress to stderr.

Configurations live in `~/.ix/compression/<configuration-id>/`; set
`IX_COMPRESSION_HOME` to use another directory. Each contains `settings.json` and
`verifier.bin`. The `default` file selects the proving configuration. Proofs carry
an identifier for an already configured local verifier. Unknown configurations
are rejected. Setup records the absolute SRS path for proving; verification needs
only settings and the verifier key. Repeated setup with identical parameters
reuses the key. Treat the configuration directory as trusted local data.

Use `--dev-srs` instead of `--srs FILE` only for development. It generates
known-trapdoor parameters in `development.srs`; those proofs are not
production-secure. Imported SRS files use `Srs::write` / `Srs::from_reader` format:
`IXKZGS01`, a little-endian u32 log-length, `2^log-length` G1 powers,
G2 and tau-G2, then log-length + 1 degree keys, all compressed Ark points.
Import checks point encodings, subgroups, and consistency; provenance must be
established independently.

## Trace bounds

The normalizer wraps the root through the aggregate program into one all-active
Aiur trace shard. Each function and memory trace has its own `u8` log-height;
byte tables retain their native heights. Setup fixes the complete layout before
any proof is provided. Oversized executions are rejected before trace allocation.

```sh
ix compression layout > root-layout.json
# Edit the bounds for the executions you intend to support.
ix compression setup --srs /path/to/trusted.srs --root-layout root-layout.json
```

The JSON contains `functions`, an array in compiled function-circuit order, and
`memory`, an object mapping every memory width to its log-height. For example,
`{"functions": [18, 12], "memory": {"1": 16, "8": 10}}` describes a backend with
two function circuits and two memory widths. Heights must be integers in 1–26;
missing entries and unknown fields are rejected. Templates start at 20; use
`compression layout --root-log-height N` to change that starting value.
Without `--root-layout`, setup uses uniform `--root-log-height N` (default 20).
The two setup flags are mutually exclusive.

These bounds cover verification of the input aggregate proof, including memory
closures; they do not describe the original shards or the proof's byte size.
Changing any bound requires matching setup on both sides.

The compression stages have independent partition limits:

| Setup flag | Log-height range | Default |
| --- | --- | --- |
| `--fri-log-height` | 16–26 | 23 |
| `--log-height` (intermediate KZG) | 16–26 | 24 |
| `--recursive-log-height` (final KZG) | 16–28 | `--log-height` |

The SRS must cover the larger KZG limit. The FRI stage uses the aggregate
backend's query and proof-of-work parameters with blowup four; its partition
must fit indivisible hash traces. Partition limits are part of the configuration
identity, not total memory limits or automatic RAM tuning. Setup and proving can
require substantial resources and do not resume automatically.

## Reproduce the sub-3 KB Init proof

Start with the stored root from aggregating all 16 shards of Init, and retain
`Init.ixe` and `Init-16.ixes` for the environment audit. The supplied
[Init layout](examples/init16-root-layout.json) fixes the 88 function-circuit
and 11 memory bounds used for this run. It is an example for this compiled
backend and workload, not a universal layout for every aggregate root.

From the repository root, in Bash:

```sh
lake build ix
export RAYON_NUM_THREADS=32
export IX_COMPRESSION_HOME="$PWD/compression"
ix=.lake/build/bin/ix
root=ROOT_ADDRESS # Replace with your stored 16-shard aggregate root address.

"$ix" compression setup --dev-srs \
  --root-layout crates/proof-compression/examples/init16-root-layout.json \
  --fri-log-height 23 --log-height 25 --recursive-log-height 28
compressed=$("$ix" compress "$root")
"$ix" verify "$compressed"
"$ix" verify --aggregate --ixe Init.ixe --ixes Init-16.ixes "$compressed"

# Copy and measure the complete serialized Ixon.Proof, including its claim.
cp "$HOME/.ix/store/${compressed:0:2}/${compressed:2:2}/${compressed:4:2}/${compressed:6}" compressed.proof
wc -c < compressed.proof
test "$(wc -c < compressed.proof)" -lt 3000
```

This configuration produced a 2,707-byte complete proof. The larger final
partition permits one arithmetic trace plus the lookup table, avoiding the
commitments and openings of multiple final arithmetic partitions. A smaller
final height can still prove the statement but produces a larger proof. The
size target depends on the layout and compiled circuits; it is not guaranteed
for arbitrary bounds. The development recipe exercises the full pipeline;
for production, replace `--dev-srs` with `--srs /path/to/trusted.srs` covering
`2^28` G1 powers, with the required degree keys.

## Library and tests

`pipeline::FixedRoot` and `pipeline::setup` derive the fixed verifier without a
witness. `pipeline::prepare_root` also supports variable root layouts with an
independently trusted aggregate key and expected outer claim. `Prepared::prove_fri`,
`prepare_kzg` / `Prepared::prove_kzg`, and `prepare_recursive` /
`RecursiveStage::prove` expose the three stages separately. The final verifier
checks the expected claim, outer proof, and both opening and degree pairing
equations. Verifier codecs contain no proving powers; authenticate keys before
loading them outside local setup.

The FRI verifier supports Goldilocks with quadratic challenges, cap-height zero,
binary FRI, a constant final polynomial, active preprocessed tables, and bounded
field-sampling retries. Unsupported profiles fail during preparation.

```sh
cargo test --release -p ix-proof-compression
```

Tests generate their fixtures and cover native/constrained verifier agreement,
statement binding, malformed inputs, degree bounds, and streaming equivalence.
The expensive complete-chain test independently derives a fixed key and proves
a synthetic relation with development parameters and low FRI query counts:

```sh
cargo test --release -p ix-proof-compression --test pipeline_root \
  complete_compression_chain -- --ignored --nocapture
```
