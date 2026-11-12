# Generic Aiur PLONK frontend

`aiur_backend::plonk::Exporter` lowers a checked BN254 Aiur trace plan to a
fixed-capacity schema and witness. It uses the same `CircuitInputs` and
main-trace packing as the KZG adapter. The schema fixes every circuit's row
capacity, constraints, lookup messages, fixed table values, and public entry.
The witness supplies native scalar cells and the typed public call. Its
values do not change the schema or key.

The gnark frontend constrains all current/next-row arithmetic and boundary
selectors. One global signed log-derivative argument connects the public call,
function calls, fixed maps, ROM, and compiler depth checks. The frontend commits
to every main cell and public value before sampling challenges. Each unsigned
multiplicity is constrained to 64 bits; the static lookup-slot count is below
`2^64`, so integer count sums cannot wrap BN254 Fr. Message fingerprints include
arity. Every denominator has a constrained nonzero inverse, including messages
with zero multiplicity.

The lookup fingerprint challenge is gnark's commitment challenge. Its independent
denominator challenge is the reduction of 64 BLAKE3 XOF bytes over
`"ix/aiur-plonk/logup/v1\0" || canonical_little_endian_scalar(challenge)`.
`aiur_plonk_blake3.go` implements this single-block computation with bit
constraints. It creates no lookup commitments inside the commitment callback
and introduces no MiMC. The fixed expansion costs 29,913 sparse constraints.
The stock PLONK protocol and Solidity verifier retain their existing transcript.

Schema validation checks canonical scalars, expression indices, matrix widths,
power-of-two capacities and conservative row/cell limits. Compilation checks
the actual sparse-constraint domain against the currently admitted `2^25`
maximum and checks that exactly one auxiliary commitment is present. It rejects
an oversized circuit before parameter loading or setup. Each capacity determines
the full next-row cycle, including zero-padded rows; authenticated fixed tables
retain their exact height.

The JSON schema and compiled constraint system are trusted key-generation inputs.
Host witness checks are diagnostics; their acceptance is not a proof assumption.
The compiler-to-PLONK lowering and log-derivative composition still require
independent review and formal coverage. The current prototype exposes typed
public fields. Final compression needs the explicit two-limb statement
projection, a retained proving/verification API, and the `CompressFinal`
verifier/pairing program before replacing the existing final pipeline.

## Focused regression

The checked-in `testdata/aiur` JSON comes from the actual compiler artifact
`crates/aiur/tests/fixtures/bn254-trace.ixa`. The source program recursively
increments a field value, reads a fixed map with a high Fr key, and stores/loads
ROM. Its independently expected call is `BN254Trace::run(3, -1) = 9`.
The Rust regression checks that the JSON still matches the compiler exporter;
the Go regression bypasses host validation when mutating trace cells.

From the repository root:

```sh
cargo test --locked -p ix-proof-compression --test aiur_plonk
cargo test --locked -p ix-proof-compression --features plonk --test aiur_plonk
cd tools/gnark
go test -mod=readonly -run 'TestAiurLookupBlake3|TestAiurPlonkCompilerConstraints|TestAiurPlonkRejectsMalformedSchema' .
```

The tests cover changed public fields, activation, recursion depth, function,
map and ROM multiplicities, ROM addresses and contents, negative counts,
noncanonical fields, malformed schemas and capacity overflows.
`plonk::gnark::compile` also exposes compilation through the existing C archive.

To produce an Ignition-backed proof, create a fresh output directory and export
the exact domain's powers using the established authenticated parameter loader:

```sh
cargo run --locked -p ix-proof-compression --example aiur_plonk_fixture -- target/aiur-plonk-fixture
IX_KZG_SRS=/path/to/admitted/srs.bin cargo run --locked --release -p ix-proof-compression --features plonk --example aiur_plonk_fixture -- target/aiur-plonk-fixture --srs-domain 32768
```

Then run `TestAiurPlonkIgnition` with `IX_AIUR_PLONK_SRS` pointing to that
export, `IX_AIUR_PLONK_SRS_BLAKE3` set to the independently generated receipt's
`blake3`, and `IX_AIUR_PLONK_OUTPUT` naming a new artifact directory. The test
checks the proof with gnark, rejects a changed public call, refuses to prove
an unsatisfied witness, and exports the key, Solidity verifier and proof.

For the local EVM test, copy the generated `PlonkVerifier.sol` to an isolated
Foundry project's `src/`, `testdata/aiur/AiurPlonk.t.sol` to its `test/`, and the
exported `proof.json` to its root. Enable Foundry read access to the project,
then run its tests with the existing pinned local Solidity toolchain. No RPC or
chain deployment is needed. The contract test derives the expected fields from
the source program rather than reading them from proof metadata.

The measured fixture uses 32,393 constraints, a `2^15` domain, three public
fields, and one auxiliary commitment. Its native proof is 584 bytes and its
Solidity payload is 864 bytes. The local Solidity test measured 350,760 gas
for the external verifier call and 1,092 bytes of ABI calldata. These figures
cover this small execution, not a final compression verifier or pairing.
