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
request multiplicity is boolean in the validated receiver-count path below.
Schemas outside that class retain 64-bit ranges for every unsigned multiplicity;
the static lookup-slot count is below `2^64`, so their integer count sums cannot
wrap BN254 Fr. Message fingerprints include arity. Every denominator has a constrained nonzero inverse, including messages
with zero multiplicity.

The lookup fingerprint challenge is gnark's commitment challenge. Its independent
denominator challenge is the reduction of 64 BLAKE3 XOF bytes over
`"ix/aiur-plonk/logup/v1\0" || canonical_little_endian_scalar(challenge)`.
`aiur_plonk_blake3.go` implements this single-block computation with bit
constraints. It creates no lookup commitments inside the commitment callback
and introduces no MiMC. The fixed expansion costs 29,913 sparse constraints.
The stock PLONK protocol and Solidity verifier retain their existing transcript.

The LogUp calculation shares gamma powers and constant message prefixes across
rows. It groups terms with the same committed multiplicity before multiplying
by that weight, and uses gnark's constrained batch inversion. Each inverse still
satisfies `inverse * denominator = 1`; zero denominators are rejected even for
zero-weight messages. These changes rearrange the same rational identity.

Schema validation checks canonical scalars, expression indices, matrix widths,
power-of-two capacities and conservative row/cell limits. Compilation checks
the actual sparse-constraint domain against the currently admitted `2^25`
maximum and checks that exactly one auxiliary commitment is present. It rejects
an oversized circuit before parameter loading or setup. Each capacity determines
the full next-row cycle, including zero-padded rows; authenticated fixed tables
retain their exact height.

The JSON schema and compiled constraint system are trusted key-generation inputs.
`boolean_requests` explicitly selects the compiler's boolean-enable contract.
Schemas with weighted requests leave it false and retain integer multiplicity
checks, so an honest request count greater than one remains supported.
Host witness checks are diagnostics; their acceptance is not a proof assumption.
The compiler-to-PLONK lowering and log-derivative composition still require
independent review and formal coverage. The current prototype exposes typed
public fields. Final compression needs the explicit two-limb statement
projection, a retained proving/verification API, and the `CompressFinal`
verifier/pairing program before replacing the existing final pipeline.

## Receiver weights and exact occurrence counts

The frontend can omit integer range checks on receiver weights only after its
structural validator establishes all of these properties:

- Every pull weight is a distinct current-row main column. It never occurs in
  a message or request weight, and cannot alias another pull weight.
- Every constraint mentioning a weight is homogeneous and linear in that one
  weight, with coefficients depending only on program cells. Cross-count,
  next-row, nonlinear and nonhomogeneous dependencies use the conservative path.
- Every request weight is constrained boolean. Including the public request,
  the statically checked potential-request budget fits `u64`, below BN254 Fr.
- The commitment binds every program cell and receiver weight before either
  lookup challenge is available.

For a fixed message, let P be its integer number of requests. Except for the
lookup argument's challenge-collision probability, its residue equality forces
the sum of matching receiver weights to equal P in Fr. If P>0, then P is nonzero
in Fr because of the request bound. At least one matching receiver consequently
has a nonzero weight. Every constraint `weight * coefficient(program) = 0`
on that receiver forces its coefficient to vanish. Assign that receiver the
ordinary integer P and assign all other matching receivers zero. Homogeneity
preserves every constraint; message independence preserves all messages. For a
message with P=0, assign all of its receiver weights zero. Weight isolation makes
these replacements independent across messages and rows.

The resulting witness has exact nonnegative `u64` occurrence counts and the
same program cells, public call and depth constraints. Thus this optimization
preserves the relation even though auxiliary field weights in a particular
proof may be negative or large. It does not permit missing or disabled receivers,
nonboolean requests, changed statements, or depth cycles. This is an argument
for the implemented invariant checks, not completed formal verification.

The dedicated tests accept valid duplicate receivers weighted -1 and 2, or
`2^200` and `1-2^200`, and reject missing/disabled receivers and changed public
calls. They also exercise each unsafe dependency class, the 64-bit fallback,
and nonboolean requests. The original compiler fixture's depth and ROM mutation
tests run through this optimized path.

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

The initial conservative fixture used 32,393 constraints. Validated receiver-weight
elision reduces it to 30,258, with the same `2^15` domain, three public fields,
and one auxiliary commitment. Its native proof is 584 bytes and its
Solidity payload is 864 bytes. The local Solidity test measured 350,760 gas
for the external verifier call and 1,092 bytes of ABI calldata. These figures
cover this small execution, not a final compression verifier or pairing.
