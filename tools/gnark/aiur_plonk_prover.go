//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"path/filepath"
	"sync"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
)

const aiurMaxPublic = 1 << 15
const aiurMaxSecret = aiurMaxDomain
const aiurMaxWitnessBytes = 12 + 32*(aiurMaxSecret+aiurMaxPublic)
const aiurManifestFormat = "ix-aiur-plonk-artifacts-v1"

type aiurPreparation struct {
	Schema                                           json.RawMessage
	Circuit                                          string
	CircuitHash                                      artifact
	Info                                             circuitInfo
	SRS, SRSBLAKE3, Lagrange, LagrangeSHA256, Output string
}

type aiurManifest struct {
	Format, SchemaSHA256, SRSBLAKE3 string
	Info                            circuitInfo
	Files                           map[string]artifact
}

func aiurDimensions(s *aiurSchema) (int, error) {
	if err := s.validate(); err != nil {
		return 0, err
	}
	if s.PublicInputs > aiurMaxPublic {
		return 0, fmt.Errorf("too many Aiur public fields")
	}
	secret := s.PrivateOutputs
	for _, c := range s.Circuits {
		secret += c.Rows * c.MainWidth
	}
	return secret, nil
}

func validateAiurInfo(info circuitInfo) error {
	if info.PublicInputs < 0 || info.PublicInputs > aiurMaxPublic || info.Constraints < 1 || info.Constraints > aiurMaxDomain || info.Domain < 2 || info.Domain > aiurMaxDomain || info.Domain != ecc.NextPowerOfTwo(uint64(info.Constraints+info.PublicInputs)) || info.Commitments != 1 {
		return fmt.Errorf("invalid Aiur PLONK dimensions")
	}
	return nil
}

func (m *aiurManifest) validate() error {
	if m.Format != aiurManifestFormat || m.Files == nil {
		return fmt.Errorf("invalid Aiur PLONK manifest")
	}
	if err := validateAiurInfo(m.Info); err != nil {
		return err
	}
	for _, digest := range []string{m.SchemaSHA256, m.SRSBLAKE3} {
		if _, err := unhex(digest, 32); err != nil {
			return err
		}
	}
	for _, name := range []string{"schema.json", "circuit.bin", "proving-key.bin", "verifying-key.bin", "PlonkVerifier.sol"} {
		file := m.Files[name]
		if file.Bytes < 1 || file.Bytes > 1<<40 {
			return fmt.Errorf("invalid Aiur artifact size: %s", name)
		}
		if _, err := unhex(file.SHA256, 32); err != nil {
			return err
		}
	}
	if m.Files["schema.json"].SHA256 != m.SchemaSHA256 || m.Files["schema.json"].Bytes > 16<<20 || m.Files["verifying-key.bin"].Bytes > 1<<20 {
		return fmt.Errorf("invalid Aiur schema or key metadata")
	}
	return nil
}

func prepareAiur(request *aiurPreparation) (*aiurManifest, error) {
	if request.Output == "" || request.Circuit == "" || request.SRS == "" || request.Lagrange == "" {
		return nil, fmt.Errorf("Aiur preparation requires explicit artifact paths")
	}
	if request.CircuitHash.Bytes < 1 || request.CircuitHash.Bytes > 1<<40 {
		return nil, fmt.Errorf("invalid compiled Aiur circuit size")
	}
	if _, err := unhex(request.CircuitHash.SHA256, 32); err != nil {
		return nil, err
	}
	if len(request.Schema) > 16<<20 {
		return nil, fmt.Errorf("Aiur schema is too large")
	}
	var schema aiurSchema
	if err := decodeReader(bytes.NewReader(request.Schema), &schema); err != nil {
		return nil, err
	}
	secret, err := aiurDimensions(&schema)
	if err != nil {
		return nil, err
	}
	if err := validateAiurInfo(request.Info); err != nil {
		return nil, err
	}
	phase := time.Now()
	ccs := plonk.NewCS(curveID)
	if err := readVerified(request.Circuit, request.CircuitHash, ccs); err != nil {
		return nil, err
	}
	if ccs.GetNbConstraints() != request.Info.Constraints || ccs.GetNbPublicVariables() != schema.PublicInputs || schema.PublicInputs != request.Info.PublicInputs || ccs.GetNbSecretVariables() != secret || len(ccs.GetCommitments().CommitmentIndexes()) != 1 {
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
	if err := atomicFile(filepath.Join(request.Output, "schema.json"), func(w io.Writer) error { _, err := w.Write(request.Schema); return err }); err != nil {
		return nil, err
	}
	for _, item := range []struct {
		name  string
		value io.WriterTo
	}{{"circuit.bin", ccs}, {"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		if err := atomicFile(filepath.Join(request.Output, item.name), func(w io.Writer) error { _, err := item.value.WriteTo(w); return err }); err != nil {
			return nil, err
		}
	}
	if err := atomicFile(filepath.Join(request.Output, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
		return nil, err
	}
	hash := sha256.Sum256(request.Schema)
	m := &aiurManifest{Format: aiurManifestFormat, SchemaSHA256: hex.EncodeToString(hash[:]), SRSBLAKE3: request.SRSBLAKE3, Info: request.Info, Files: map[string]artifact{}}
	for _, name := range []string{"schema.json", "circuit.bin", "proving-key.bin", "verifying-key.bin", "PlonkVerifier.sol"} {
		item, err := fileHash(filepath.Join(request.Output, name))
		if err != nil {
			return nil, err
		}
		m.Files[name] = item
	}
	log.Printf("aiur-plonk prepare phase=artifact-write seconds=%.6f domain=%d", time.Since(phase).Seconds(), request.Info.Domain)
	return m, m.validate()
}

// The authenticated schema fixes both counts. Validate them and the exact byte
// length before gnark allocates its vector; gnark then checks every field word.
func decodeAiurWitness(data []byte, public, secret int) (witness.Witness, error) {
	if public < 0 || public > aiurMaxPublic || secret < 0 || secret > aiurMaxSecret || len(data) != 12+32*(public+secret) {
		return nil, fmt.Errorf("Aiur binary witness length differs")
	}
	if binary.BigEndian.Uint32(data[:4]) != uint32(public) || binary.BigEndian.Uint32(data[4:8]) != uint32(secret) || binary.BigEndian.Uint32(data[8:12]) != uint32(public+secret) {
		return nil, fmt.Errorf("Aiur binary witness counts differ")
	}
	w, err := witness.New(curveID.ScalarField())
	if err != nil {
		return nil, err
	}
	r := bytes.NewReader(data)
	if _, err := w.ReadFrom(r); err != nil {
		return nil, err
	}
	if r.Len() != 0 {
		return nil, fmt.Errorf("trailing Aiur witness bytes")
	}
	return w, nil
}

func aiurPublicWitness(data []byte, count int) (witness.Witness, error) {
	if count < 0 || count > aiurMaxPublic || len(data) != 32*count {
		return nil, fmt.Errorf("Aiur public field count differs")
	}
	encoded := make([]byte, 12+len(data))
	binary.BigEndian.PutUint32(encoded[:4], uint32(count))
	binary.BigEndian.PutUint32(encoded[8:12], uint32(count))
	copy(encoded[12:], data)
	return decodeAiurWitness(encoded, count, 0)
}

type aiurProver struct {
	mu             sync.Mutex
	ccs            constraint.ConstraintSystem
	pk             plonk.ProvingKey
	vk             *nativeVerifyingKey
	public, secret int
	cleanup        func() error
	closed, failed bool
}

func openAiurProver(dir string, metadata []byte, config backendConfig) (*aiurProver, error) {
	var m aiurManifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	if err := m.validate(); err != nil {
		return nil, err
	}
	data, err := readDescription(filepath.Join(dir, "schema.json"))
	if err != nil {
		return nil, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != m.SchemaSHA256 || int64(len(data)) != m.Files["schema.json"].Bytes {
		return nil, fmt.Errorf("Aiur schema identity differs")
	}
	var schema aiurSchema
	if err := decodeReader(bytes.NewReader(data), &schema); err != nil {
		return nil, err
	}
	secret, err := aiurDimensions(&schema)
	if err != nil {
		return nil, err
	}
	p := &aiurProver{ccs: plonk.NewCS(curveID), pk: plonk.NewProvingKey(curveID), vk: new(nativeVerifyingKey), public: schema.PublicInputs, secret: secret}
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"circuit.bin", p.ccs}, {"proving-key.bin", p.pk}, {"verifying-key.bin", p.vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
			return nil, err
		}
	}
	if p.public != m.Info.PublicInputs || p.ccs.GetNbPublicVariables() != p.public || p.ccs.GetNbSecretVariables() != p.secret || p.ccs.GetNbConstraints() != m.Info.Constraints || len(p.ccs.GetCommitments().CommitmentIndexes()) != 1 || p.vk.Size != m.Info.Domain || p.vk.NbPublicVariables != uint64(p.public) || len(p.vk.Qcp) != 1 {
		return nil, fmt.Errorf("Aiur circuit/key dimensions differ")
	}
	var encoded bytes.Buffer
	if _, err := p.pk.VerifyingKey().(io.WriterTo).WriteTo(&encoded); err != nil {
		return nil, err
	}
	hash = sha256.Sum256(encoded.Bytes())
	if hex.EncodeToString(hash[:]) != m.Files["verifying-key.bin"].SHA256 {
		return nil, fmt.Errorf("Aiur proving key embeds another verifier")
	}
	p.cleanup, err = configureBackend(p.pk, config)
	if err != nil {
		return nil, err
	}
	return p, nil
}

func (p *aiurProver) prove(data, expected []byte) ([]byte, []byte, error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	defer func() {
		if value := recover(); value != nil {
			p.failed = true
			panic(value)
		}
	}()
	if p.closed || p.failed {
		return nil, nil, fmt.Errorf("Aiur prover is closed or failed")
	}
	if len(expected) != 32*p.public || len(data) < 12+len(expected) || !bytes.Equal(data[12:12+len(expected)], expected) {
		return nil, nil, fmt.Errorf("Aiur witness differs from the expected public call")
	}
	w, err := decodeAiurWitness(data, p.public, p.secret)
	if err != nil {
		return nil, nil, err
	}
	proof, err := plonk.Prove(p.ccs, p.pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		p.failed = true
		return nil, nil, err
	}
	public, err := w.Public()
	if err != nil {
		p.failed = true
		return nil, nil, err
	}
	if err := plonk.Verify(proof, p.vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		p.failed = true
		return nil, nil, err
	}
	var out bytes.Buffer
	if _, err := proof.WriteTo(&out); err != nil {
		return nil, nil, err
	}
	return out.Bytes(), proof.(*nativeProof).MarshalSolidity(), nil
}
func (p *aiurProver) close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.closed {
		return nil
	}
	p.closed = true
	err := p.cleanup()
	p.ccs, p.pk, p.vk = nil, nil, nil
	return err
}

func verifyAiurProof(key, trustedDigest, proof, expected, anchors []byte) error {
	if len(key) > 1<<20 || len(proof) > 1<<20 || len(trustedDigest) != 32 || len(anchors) != anchorBytesLen || len(expected) > 32*aiurMaxPublic || len(expected)%32 != 0 {
		return fmt.Errorf("invalid Aiur verification input length")
	}
	hash := sha256.Sum256(key)
	if !bytes.Equal(hash[:], trustedDigest) {
		return fmt.Errorf("trusted Aiur verification key digest differs")
	}
	vk := new(nativeVerifyingKey)
	r := bytes.NewReader(key)
	if _, err := vk.ReadFrom(r); err != nil {
		return err
	}
	if r.Len() != 0 || vk.NbPublicVariables != uint64(len(expected)/32) || len(vk.Qcp) != 1 || vk.Size < 2 || vk.Size > aiurMaxDomain || vk.Size&(vk.Size-1) != 0 {
		return fmt.Errorf("invalid Aiur verification key")
	}
	if !bytes.Equal(encodeAnchors(vk), anchors) {
		return fmt.Errorf("Aiur verification key setup anchors differ")
	}
	p, err := decodeProof(proof, 1)
	if err != nil {
		return err
	}
	public, err := aiurPublicWitness(expected, len(expected)/32)
	if err != nil {
		return err
	}
	return plonk.Verify(p, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK))
}
