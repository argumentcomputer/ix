//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"os"
	"path/filepath"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/constraint"
	csbn254 "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

// Compilation and key preparation of the terminal circuit from a
// Lean-exported `ix-aiur-scs-v1` file and the terminal's pairing
// configuration, each pinned by its SHA-256.

const aiurScsManifestFormat = "ix-aiur-scs-artifacts-v1"
const aiurScsInputsFormat = "ix-aiur-scs-inputs-v1"

var aiurScsFiles = []string{"circuit.bin", "proving-key.bin", "verifying-key.bin", "PlonkVerifier.sol", "inputs.json", "pairing.json"}

type aiurScsCompileRequest struct {
	Scs, ScsSHA256, Pairing, PairingSHA256, Output string
}

// aiurScsInputs is what the witness producer needs from the file: the input
// wires (publics, outputs, and each table's cells at cellBase + row·width +
// column), in the order of the binary witness.
type aiurScsInputs struct {
	Format         string
	Publics, Cells int
	Outputs        []uint32
	Tables         []aiurScsTable
}

type aiurScsPreparation struct {
	Scs, ScsSHA256, Pairing, PairingSHA256           string
	Circuit                                          string
	CircuitHash                                      artifact
	Info                                             circuitInfo
	SRS, SRSBLAKE3, Lagrange, LagrangeSHA256, Output string
}

func readAiurScsPinned(scsPath, scsDigest, pairingPath, pairingDigest string) (*aiurScs, *aiurPairing, error) {
	for _, digest := range []string{scsDigest, pairingDigest} {
		if _, err := unhex(digest, 32); err != nil {
			return nil, nil, err
		}
	}
	s, err := readAiurScs(scsPath, scsDigest)
	if err != nil {
		return nil, nil, err
	}
	p, err := readAiurScsPairing(pairingPath, pairingDigest)
	if err != nil {
		return nil, nil, err
	}
	return s, p, nil
}

func compileAiurScsCircuit(s *aiurScs, p *aiurPairing) (constraint.ConstraintSystem, circuitInfo, error) {
	var info circuitInfo
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, newAiurScsCircuit(s, p))
	if err != nil {
		return nil, info, err
	}
	info = circuitInfo{
		Domain:      ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables())),
		Constraints: ccs.GetNbConstraints(), PublicInputs: ccs.GetNbPublicVariables(),
		Commitments: len(ccs.GetCommitments().CommitmentIndexes()),
	}
	if info.Domain > aiurMaxDomain {
		return nil, info, fmt.Errorf("Aiur PLONK domain exceeds Ignition ceremony capacity (2^26)")
	}
	if info.Commitments != 1 || info.PublicInputs != s.Publics || ccs.GetNbSecretVariables() != s.Cells-s.Publics {
		return nil, info, fmt.Errorf("unexpected Aiur SCS commitment or input counts")
	}
	if run := aiurScsHintRun(ccs); run > aiurScsMaxHintRun {
		return nil, info, fmt.Errorf("Aiur SCS circuit has %d consecutive hint instructions", run)
	}
	return ccs, info, nil
}

// gnark's SparseR1CIterator (used by the PLONK setup) recurses once per
// consecutive non-constraint instruction, on a stack limited to 1 GB.
const aiurScsMaxHintRun = 1 << 22

func aiurScsHintRun(ccs constraint.ConstraintSystem) int {
	spr, ok := ccs.(*csbn254.SparseR1CS)
	if !ok {
		return 0
	}
	run, longest := 0, 0
	for _, inst := range spr.Instructions {
		if _, isGate := spr.Blueprints[inst.BlueprintID].(constraint.BlueprintSparseR1C); isGate {
			run = 0
		} else if run++; run > longest {
			longest = run
		}
	}
	return longest
}

func compileAiurScs(request *aiurScsCompileRequest) (circuitInfo, error) {
	if request.Output == "" {
		return circuitInfo{}, fmt.Errorf("Aiur SCS compilation requires an output path")
	}
	s, p, err := readAiurScsPinned(request.Scs, request.ScsSHA256, request.Pairing, request.PairingSHA256)
	if err != nil {
		return circuitInfo{}, err
	}
	phase := time.Now()
	ccs, info, err := compileAiurScsCircuit(s, p)
	if err != nil {
		return info, err
	}
	log.Printf("aiur-scs compile seconds=%.6f constraints=%d", time.Since(phase).Seconds(), info.Constraints)
	return info, atomicFile(request.Output, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
}

func (s *aiurScs) inputs() *aiurScsInputs {
	return &aiurScsInputs{Format: aiurScsInputsFormat, Publics: s.Publics, Cells: s.Cells, Outputs: s.Outputs, Tables: s.Tables}
}

func (in *aiurScsInputs) validate() error {
	if in.Format != aiurScsInputsFormat || in.Publics < 1 || in.Publics > aiurMaxPublic || in.Cells < in.Publics || in.Cells > aiurMaxSecret ||
		len(in.Outputs) != aiurTerminalOutputs {
		return fmt.Errorf("invalid Aiur SCS input layout")
	}
	return nil
}

func prepareAiurScs(request *aiurScsPreparation) (*aiurManifest, error) {
	if request.Output == "" || request.Circuit == "" || request.SRS == "" || request.Lagrange == "" {
		return nil, fmt.Errorf("Aiur preparation requires explicit artifact paths")
	}
	if request.CircuitHash.Bytes < 1 || request.CircuitHash.Bytes > 1<<40 {
		return nil, fmt.Errorf("invalid compiled Aiur circuit size")
	}
	if _, err := unhex(request.CircuitHash.SHA256, 32); err != nil {
		return nil, err
	}
	if err := validateAiurInfo(request.Info); err != nil {
		return nil, err
	}
	s, _, err := readAiurScsPinned(request.Scs, request.ScsSHA256, request.Pairing, request.PairingSHA256)
	if err != nil {
		return nil, err
	}
	pairing, err := os.ReadFile(request.Pairing)
	if err != nil {
		return nil, err
	}
	inputs, err := json.Marshal(s.inputs())
	if err != nil {
		return nil, err
	}
	phase := time.Now()
	ccs := plonk.NewCS(curveID)
	if err := readVerified(request.Circuit, request.CircuitHash, ccs); err != nil {
		return nil, err
	}
	if ccs.GetNbConstraints() != request.Info.Constraints || ccs.GetNbPublicVariables() != s.Publics || s.Publics != request.Info.PublicInputs ||
		ccs.GetNbSecretVariables() != s.Cells-s.Publics || len(ccs.GetCommitments().CommitmentIndexes()) != 1 {
		return nil, fmt.Errorf("compiled Aiur circuit differs from its trusted metadata")
	}
	log.Printf("aiur-plonk prepare phase=circuit-load seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	phase = time.Now()
	srs, err := readSRS(request.SRS, request.SRSBLAKE3, request.Info.Domain)
	if err != nil {
		return nil, err
	}
	log.Printf("aiur-plonk prepare phase=srs-load seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	phase = time.Now()
	lagrange, err := loadLagrange(srs, request.Info.Domain, request.Lagrange, request.LagrangeSHA256)
	if err != nil {
		return nil, err
	}
	log.Printf("aiur-plonk prepare phase=lagrange seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	phase = time.Now()
	pk, vk, err := plonk.Setup(ccs, srs, lagrange)
	if err != nil {
		return nil, err
	}
	log.Printf("aiur-plonk prepare phase=key-setup seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	phase = time.Now()
	for _, item := range []struct {
		name  string
		value io.WriterTo
	}{{"circuit.bin", ccs}, {"proving-key.bin", pk}, {"verifying-key.bin", vk}, {"inputs.json", bytes.NewReader(inputs)}, {"pairing.json", bytes.NewReader(pairing)}} {
		if err := atomicFile(filepath.Join(request.Output, item.name), func(w io.Writer) error { _, err := item.value.WriteTo(w); return err }); err != nil {
			return nil, err
		}
	}
	if err := atomicFile(filepath.Join(request.Output, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
		return nil, err
	}
	m := &aiurManifest{Format: aiurScsManifestFormat, ScsSHA256: request.ScsSHA256, PairingSHA256: request.PairingSHA256, SRSBLAKE3: request.SRSBLAKE3,
		Info: request.Info, Files: map[string]artifact{}}
	for _, name := range aiurScsFiles {
		item, err := fileHash(filepath.Join(request.Output, name))
		if err != nil {
			return nil, err
		}
		m.Files[name] = item
	}
	log.Printf("aiur-plonk prepare phase=artifact-write seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	return m, m.validate()
}

// validateScs checks a manifest of a circuit prepared from an SCS file.
func (m *aiurManifest) validateScs() error {
	for _, digest := range []string{m.ScsSHA256, m.PairingSHA256, m.SRSBLAKE3} {
		if _, err := unhex(digest, 32); err != nil {
			return err
		}
	}
	if len(m.Files) != len(aiurScsFiles) {
		return fmt.Errorf("invalid Aiur SCS artifact list")
	}
	for _, name := range aiurScsFiles {
		file := m.Files[name]
		if file.Bytes < 1 || file.Bytes > 1<<40 {
			return fmt.Errorf("invalid Aiur artifact size: %s", name)
		}
		if _, err := unhex(file.SHA256, 32); err != nil {
			return err
		}
	}
	if m.Files["pairing.json"].SHA256 != m.PairingSHA256 || m.Files["inputs.json"].Bytes > 16<<20 || m.Files["verifying-key.bin"].Bytes > 1<<20 {
		return fmt.Errorf("invalid Aiur SCS input or key metadata")
	}
	return nil
}

// aiurScsDimensions reads the prepared input layout, checked against the
// manifest, and returns its public and secret input counts.
func aiurScsDimensions(dir string, m *aiurManifest) (int, int, error) {
	data, err := readDescription(filepath.Join(dir, "inputs.json"))
	if err != nil {
		return 0, 0, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != m.Files["inputs.json"].SHA256 || int64(len(data)) != m.Files["inputs.json"].Bytes {
		return 0, 0, fmt.Errorf("Aiur SCS input layout differs")
	}
	var in aiurScsInputs
	if err := decodeReader(bytes.NewReader(data), &in); err != nil {
		return 0, 0, err
	}
	if err := in.validate(); err != nil {
		return 0, 0, err
	}
	return in.Publics, in.Cells - in.Publics, nil
}
