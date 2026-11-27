# Aiur terminal PLONK circuit

The terminal PLONK circuit is the constraint system that Lean builds and
checks (`plonk_export`, `MultiStark/Examples/PlonkExport.lean`, format
`ix-aiur-scs-v1`; `docs/aiur-plonk-lean-backend.md`). Both **BN254** and
**BLS12-381** are supported (`plonk_export` default BN254 or `--bls12-381`).
Gnark does not derive any gate from the Aiur program. `aiur_plonk_scs.go`
reads the file for the curve declared in `pairing.json`, checks its pinned
SHA-256 and validates it completely, then `aiurScsCircuit.Define` makes
exactly one `AddPlonkConstraint` per file gate, in file order, with the
file's coefficients. The only other constraints are gnark's `PairingCheck` on
the private output words (`aiur_plonk_pairing.go`) and the single BSB22
commitment over the file's commit list, whose output is the file's `γ` wire.

| Curve (`pairing.json` `"curve"`) | Private outputs (`"encoding": "affine-u80-v1"`) | Pairing gadget | Prover backend | CGo verifier |
|---|---|---|---|---|
| `"bn254"` | **18** words: two G1 points (`4` limbs × `80,80,80,14` bits per `x, y` + `1` `inf` bit) | `sw_bn254.PairingCheck` | CPU or CUDA | `ix_gnark_aiur_verify` |
| `"bls12-381"` | **22** words: two G1 points (`5` limbs × `80,80,80,80,61` bits per `x, y` + `1` `inf` bit) | `sw_bls12381.PairingCheck` | **CPU-only** (`openAiurProver` rejects `CUDA=true` on BLS12-381) | `ix_gnark_aiur_bls_verify` |

`TestAiurScsTerminal` (`aiur_plonk_scs_test.go`) checks the round trip on a
real BN254 file: every compiled file block equals the file gate for gate, and
the other blocks equal a separately compiled reference (pairing gadget and
commitment only). `aiur_plonk_bls_test.go` exercises BLS12-381 SCS parsing,
`sw_bls12381.PairingCheck` binding, full CPU PLONK prove/verify (native and
Solidity), and 7/7 negative controls (wrong pairing, non-canonical `Fq`,
bad infinity flag, bad G2 anchor, wrong public input, tampered proof, CUDA
rejection).

## Witness

The secret inputs are the file's input wires: the public statement limbs,
the private outputs (18 on BN254, 22 on BLS12-381), then each table's cells
(`cellBase + row·width + column`). Rust writes them
(`aiur_backend::plonk::scs::Witness`) in gnark's binary format: three
big-endian u32 counts (public, secret, total), then canonical 32-byte
big-endian scalar field words (`Fr`). The decoder checks the counts and the
exact length before allocating.

Every other wire is a prover hint (`aiur_plonk_scs_wires.go`), which adds no
constraint; a wrong value fails the gate it violates. Before the commitment a
wire is created at its solve gate. After it, log-derivative quotients share
batch-inverted hints and running sums and other add-one-term chains become
segmented chain hints, so the solver runs a few hundred levels instead of one
per message. Hints are created when a gate first reads them, so hint
instructions stay interleaved with the gates (gnark's constraint iterator
recurses per consecutive non-constraint instruction; compilation refuses a run
longer than 2^22).

## Preparation and proving

`ix_gnark_aiur_scs_compile` compiles the file with the terminal's pairing
configuration (`"curve": "bn254"` or `"bls12-381"`, `"encoding": "affine-u80-v1"`,
and the two G2 anchors as canonical decimal `Fq` coordinates), each pinned by
SHA-256. `ix_gnark_aiur_scs_prepare` sets up the keys from an independently
authenticated SRS export (Ignition for BN254; Filecoin/Powers-of-Tau for
BLS12-381) and writes `circuit.bin`, the keys, `PlonkVerifier.sol`,
`inputs.json` (the input layout the witness needs) and `pairing.json`. Its
manifest (`ix-aiur-scs-artifacts-v1`) records `ScsSHA256`, `PairingSHA256`,
the SRS digest and every file's SHA-256.

Opening checks those artifacts, their dimensions and the verifier embedded in
the proving key (and rejects CUDA requests when the manifest's `pairing.json`
selects BLS12-381). The manifest must come from trusted preparation or an
authenticated catalog. Verification (`ix_gnark_aiur_verify` for BN254,
`ix_gnark_aiur_bls_verify` for BLS12-381) requires the caller's expected
public fields, trusted verifier-key SHA-256 and independently selected setup
anchors.

## Tests

Requires Go `1.26.8` (`tools/gnark/go.mod`; `crates/proof-compression/build.rs`
sets `GOTOOLCHAIN=local`).

`go test -tags plonk .` runs the BN254 and BLS12-381 parser, hint, pairing,
and synthetic-file tests (compile, round trip, solve, pairing binding,
manifest checks); `IX_AIUR_TERMINAL_PROVE=1` adds development proofs with a
known-trapdoor setup. `target/e2e-l3-scs/run_test.sh` runs
`TestAiurScsTerminal` on the L3 file.
