# Aiur terminal PLONK circuit

The terminal PLONK circuit is the constraint system that Lean builds and
checks (`plonk_export`, `MultiStark/Examples/PlonkExport.lean`, format
`ix-aiur-scs-v1`; docs/aiur-plonk-lean-backend.md). Gnark does not derive any
gate from the Aiur program. `aiur_plonk_scs.go` reads the file, checks its
pinned SHA-256 and validates it completely, then `aiurScsCircuit.Define`
makes exactly one `AddPlonkConstraint` per file gate, in file order, with the
file's coefficients. The only other constraints are gnark's `PairingCheck` on
the 18 private output words (`aiur_plonk_pairing.go`) and the single BSB22
commitment over the file's commit list, whose output is the file's `γ` wire.

`TestAiurScsTerminal` (`aiur_plonk_scs_test.go`) checks the round trip on a
real file: every compiled file block equals the file gate for gate, and the
other blocks equal a separately compiled reference (pairing gadget and
commitment only).

## Witness

The secret inputs are the file's input wires: the two public statement limbs,
the 18 outputs, then each table's cells (`cellBase + row·width + column`).
Rust writes them (`aiur_backend::plonk::scs::Witness`) in gnark's binary
format: three big-endian u32 counts (public, secret, total), then canonical
32-byte big-endian field words. The decoder checks the counts and the exact
length before allocating.

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
configuration (the two G2 anchors, canonical decimal Fq coordinates), each
pinned by SHA-256. `ix_gnark_aiur_scs_prepare` sets up the keys from an
independently authenticated SRS export and writes `circuit.bin`, the keys,
`PlonkVerifier.sol`, `inputs.json` (the input layout the witness needs) and
`pairing.json`. Its manifest (`ix-aiur-scs-artifacts-v1`) records `ScsSHA256`,
`PairingSHA256`, the SRS digest and every file's SHA-256.

Opening checks those artifacts, their dimensions and the verifier embedded in
the proving key. The manifest must come from trusted preparation or an
authenticated catalog. Verification requires the caller's expected public
fields, trusted verifier-key SHA-256 and independently selected setup anchors.

## Tests

`go test -tags plonk .` runs the parser, hint and synthetic-file tests
(compile, round trip, solve, pairing binding, manifest checks);
`IX_AIUR_TERMINAL_PROVE=1` adds a development proof with a known-trapdoor
setup. `target/e2e-l3-scs/run_test.sh` runs `TestAiurScsTerminal` on the L3
file.
