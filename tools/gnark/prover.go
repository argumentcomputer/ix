//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"path/filepath"
	"runtime/debug"
	"sync"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

type backendConfig struct {
	CUDA        bool
	Device      int
	MemoryBytes uint64
	MaskMSM     bool
}

func compileCircuit(schema []byte, path string) (circuitInfo, error) {
	var info circuitInfo
	key, err := decodeVerifyingKey(schema)
	if err != nil {
		return info, err
	}
	ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, newCircuit(key))
	if err != nil {
		return info, err
	}
	info = circuitInfo{Domain: ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables())), Constraints: ccs.GetNbConstraints(), PublicInputs: ccs.GetNbPublicVariables(), Commitments: len(ccs.GetCommitments().CommitmentIndexes())}
	if info.PublicInputs != 2 {
		return info, fmt.Errorf("expected two public digest limbs")
	}
	return info, atomicFile(path, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
}

func prepareCircuit(schema []byte, circuitPath string, circuitHash artifact, domain uint64, srsPath, receipt, lagrangePath, lagrangeDigest, output string) error {
	if _, err := decodeVerifyingKey(schema); err != nil {
		return err
	}
	srs, err := readSRS(srsPath, receipt, domain)
	if err != nil {
		return err
	}
	lagrange, err := loadLagrange(srs, domain, lagrangePath, lagrangeDigest)
	if err != nil {
		return err
	}
	debug.FreeOSMemory()
	ccs := plonk.NewCS(curveID)
	if err := readVerified(circuitPath, circuitHash, ccs); err != nil {
		return err
	}
	if ccs.GetNbPublicVariables() != 2 || ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints()+2)) != domain {
		return fmt.Errorf("circuit domain differs")
	}
	pk, vk, err := plonk.Setup(ccs, srs, lagrange)
	if err != nil {
		return err
	}
	for _, item := range []struct {
		name  string
		value io.WriterTo
	}{{"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		if err := atomicFile(filepath.Join(output, item.name), func(w io.Writer) error { _, err := item.value.WriteTo(w); return err }); err != nil {
			return err
		}
	}
	return atomicFile(filepath.Join(output, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) })
}

type prover struct {
	mu             sync.Mutex
	key            *verifyingKey
	ccs            constraint.ConstraintSystem
	pk             plonk.ProvingKey
	vk             *nativeVerifyingKey
	cleanup        func() error
	closed, failed bool
}

func openProver(dir string, metadata []byte, config backendConfig) (*prover, error) {
	var m manifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	if err := m.validate(); err != nil {
		return nil, err
	}
	if !m.KeysReady {
		return nil, fmt.Errorf("PLONK keys are not prepared")
	}
	data, err := readDescription(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, err
	}
	sum := sha256.Sum256(data)
	if hex.EncodeToString(sum[:]) != m.InnerVKSHA256 || int64(len(data)) != m.Files["vk.json"].Bytes {
		return nil, fmt.Errorf("verifier description identity differs")
	}
	key, err := decodeVerifyingKey(data)
	if err != nil {
		return nil, err
	}
	p := &prover{key: key, ccs: plonk.NewCS(curveID), pk: plonk.NewProvingKey(curveID), vk: new(nativeVerifyingKey)}
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"circuit.bin", p.ccs}, {"proving-key.bin", p.pk}, {"verifying-key.bin", p.vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
			return nil, err
		}
	}
	if p.ccs.GetNbConstraints() != m.Constraints || p.ccs.GetNbPublicVariables() != 2 || len(p.ccs.GetCommitments().CommitmentIndexes()) != m.Commitments || p.vk.Size != m.Domain || p.vk.NbPublicVariables != 2 || len(p.vk.Qcp) != m.Commitments {
		return nil, fmt.Errorf("decoded circuit or key dimensions differ")
	}
	embedded := p.pk.VerifyingKey().(io.WriterTo)
	var encoded bytes.Buffer
	if _, err := embedded.WriteTo(&encoded); err != nil {
		return nil, err
	}
	hash := sha256.Sum256(encoded.Bytes())
	if hex.EncodeToString(hash[:]) != m.Files["verifying-key.bin"].SHA256 {
		return nil, fmt.Errorf("proving key embeds another verifying key")
	}
	p.cleanup, err = configureBackend(p.pk, config)
	if err != nil {
		return nil, err
	}
	return p, nil
}

func (p *prover) prove(data, expected []byte) ([]byte, []byte, error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	defer func() {
		if value := recover(); value != nil {
			p.failed = true
			panic(value)
		}
	}()
	if p.closed || p.failed {
		return nil, nil, fmt.Errorf("prover is closed or failed")
	}
	if len(expected) != 32 || len(data) > 16<<20 {
		return nil, nil, fmt.Errorf("invalid witness or claim size")
	}
	var input witnessJSON
	if err := decodeReader(bytes.NewReader(data), &input); err != nil {
		return nil, nil, err
	}
	digest, err := unhex(input.ClaimDigest, 32)
	if err != nil || !bytes.Equal(digest, expected) {
		return nil, nil, fmt.Errorf("witness differs from expected claim")
	}
	assignment, err := assignWitness(p.key, &input)
	if err != nil {
		return nil, nil, err
	}
	witness, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		return nil, nil, err
	}
	proof, err := plonk.Prove(p.ccs, p.pk, witness, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		p.failed = true
		return nil, nil, err
	}
	public, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(expected)}, curveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		p.failed = true
		return nil, nil, err
	}
	if err := plonk.Verify(proof, p.vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		p.failed = true
		return nil, nil, err
	}
	var encoded bytes.Buffer
	if _, err := proof.WriteTo(&encoded); err != nil {
		return nil, nil, err
	}
	return encoded.Bytes(), proof.(*nativeProof).MarshalSolidity(), nil
}

func (p *prover) close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.closed {
		return nil
	}
	p.closed = true
	err := p.cleanup()
	p.key, p.ccs, p.pk, p.vk = nil, nil, nil, nil
	return err
}

type manifest struct {
	InnerVKSHA256                          string
	SRSBLAKE3                              string
	KeysReady                              bool
	Domain                                 uint64
	Constraints, PublicInputs, Commitments int
	Files                                  map[string]artifact
}

func (m *manifest) validate() error {
	if m.PublicInputs != 2 || m.Constraints < 1 || m.Constraints > 1<<26 || m.Domain < uint64(m.Constraints+2) || m.Domain > 1<<26 || m.Domain&(m.Domain-1) != 0 || m.Commitments < 0 || m.Commitments > 1024 || m.Files == nil {
		return fmt.Errorf("invalid wrapper artifact metadata")
	}
	if m.KeysReady {
		if _, err := unhex(m.SRSBLAKE3, 32); err != nil {
			return err
		}
	}
	if m.Files["vk.json"].SHA256 != m.InnerVKSHA256 {
		return fmt.Errorf("verifying key identity differs")
	}
	return nil
}
