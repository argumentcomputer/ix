//go:build groth16 || !plonk

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"path/filepath"
	"sync"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	g16bls "github.com/consensys/gnark/backend/groth16/bls12-381"
	mpcbls "github.com/consensys/gnark/backend/groth16/bls12-381/mpcsetup"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	csbls "github.com/consensys/gnark/constraint/bls12-381"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

const groth16BLSMaxProofBytes = 292

func groth16ShapeBLS(ccs constraint.ConstraintSystem) (uint64, int, error) {
	commitments := len(ccs.GetCommitments().CommitmentIndexes())
	if ccs.Field().Cmp(blsCurveID.ScalarField()) != 0 || ccs.GetNbPublicVariables() != 3 {
		return 0, 0, fmt.Errorf("Groth16 requires BLS12-381 and two public digest limbs plus the implicit one")
	}
	if ccs.GetNbConstraints() < 1 || ccs.GetNbConstraints() > 1<<27 || commitments > 1 {
		return 0, 0, fmt.Errorf("Groth16 circuit exceeds the supported domain or Solidity commitment count")
	}
	return ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints())), commitments, nil
}

func groth16LoadBLS(dir string, m *groth16Manifest) (*verifyingKey, constraint.ConstraintSystem, error) {
	if err := m.validate(); err != nil {
		return nil, nil, err
	}
	data, err := readDescription(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, nil, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != m.InnerVK || m.Files["vk.json"].SHA256 != m.InnerVK || m.Files["vk.json"].Bytes != int64(len(data)) {
		return nil, nil, fmt.Errorf("BLS12-381 Groth16 inner verifier identity differs")
	}
	key, err := decodeVerifyingKeyBLS(data)
	if err != nil {
		return nil, nil, err
	}
	ccs := groth16.NewCS(blsCurveID)
	if err := readVerified(filepath.Join(dir, "circuit.bin"), m.Files["circuit.bin"], ccs); err != nil {
		return nil, nil, err
	}
	domain, commitments, err := groth16ShapeBLS(ccs)
	if err != nil {
		return nil, nil, err
	}
	if domain != m.Domain || commitments != m.Commitments || ccs.GetNbConstraints() != m.Constraints {
		return nil, nil, fmt.Errorf("BLS12-381 Groth16 circuit dimensions differ")
	}
	return key, ccs, nil
}

func compileGroth16BLS(schema []byte, path string) (circuitInfo, error) {
	var info circuitInfo
	key, err := decodeVerifyingKeyBLS(schema)
	if err != nil {
		return info, err
	}
	ccs, err := frontend.Compile(blsCurveID.ScalarField(), r1cs.NewBuilder, newCircuitBLS(key))
	if err != nil {
		return info, err
	}
	domain, commitments, err := groth16ShapeBLS(ccs)
	if err != nil {
		return info, err
	}
	info = circuitInfo{Domain: domain, Constraints: ccs.GetNbConstraints(), PublicInputs: 2, Commitments: commitments}
	return info, atomicFile(path, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
}

func groth16CheckKeyBLS(vk *g16bls.VerifyingKey, commitments int) error {
	if commitments < 0 || commitments > 1 || len(vk.PublicAndCommitmentCommitted) != commitments ||
		len(vk.CommitmentKeys) != commitments || len(vk.G1.K) != 3+commitments {
		return fmt.Errorf("BLS12-381 Groth16 key has an unsupported public-input or commitment schema")
	}
	return nil
}

func groth16CheckPairBLS(pk *g16bls.ProvingKey, vk *g16bls.VerifyingKey, domain uint64) error {
	if pk.Domain.Cardinality != domain || !pk.G1.Alpha.Equal(&vk.G1.Alpha) ||
		!pk.G1.Beta.Equal(&vk.G1.Beta) || !pk.G1.Delta.Equal(&vk.G1.Delta) ||
		!pk.G2.Beta.Equal(&vk.G2.Beta) || !pk.G2.Delta.Equal(&vk.G2.Delta) {
		return fmt.Errorf("BLS12-381 Groth16 proving and verifying keys differ")
	}
	return nil
}

func groth16SaveKeysBLS(dir string, m *groth16Manifest, pk groth16.ProvingKey, vk groth16.VerifyingKey, setup, ceremony string) error {
	native := vk.(*g16bls.VerifyingKey)
	if err := groth16CheckKeyBLS(native, m.Commitments); err != nil {
		return err
	}
	if err := groth16CheckPairBLS(pk.(*g16bls.ProvingKey), native, m.Domain); err != nil {
		return err
	}
	for _, item := range []struct {
		name  string
		value io.WriterTo
	}{{"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		hash := sha256.New()
		var size int64
		if err := atomicFile(filepath.Join(dir, item.name), func(w io.Writer) error {
			var err error
			size, err = item.value.WriteTo(io.MultiWriter(w, hash))
			return err
		}); err != nil {
			return err
		}
		m.Files[item.name] = artifact{SHA256: hex.EncodeToString(hash.Sum(nil)), Bytes: size}
	}
	if err := atomicFile(filepath.Join(dir, "Groth16Verifier.sol"), func(w io.Writer) error {
		return vk.ExportSolidity(w, solidity.WithHashToFieldFunction(sha256.New()), solidity.WithPragmaVersion("^0.8.28"))
	}); err != nil {
		return err
	}
	entry, err := fileHash(filepath.Join(dir, "Groth16Verifier.sol"))
	if err != nil {
		return err
	}
	m.Files["Groth16Verifier.sol"] = entry
	m.Setup, m.Ceremony, m.KeysReady = setup, ceremony, true
	return m.validate()
}

func groth16DevelopmentSetupBLS(dir string, m *groth16Manifest) error {
	_, ccs, err := groth16LoadBLS(dir, m)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("BLS12-381 Groth16 keys are already prepared")
	}
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return err
	}
	return groth16SaveKeysBLS(dir, m, pk, vk, "development", "")
}

func groth16MPCSetupBLS(dir string, m *groth16Manifest, path, trusted string) error {
	_, ccs, err := groth16LoadBLS(dir, m)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("BLS12-381 Groth16 keys are already prepared")
	}
	var ceremony groth16Ceremony
	if err := groth16PinnedJSON(path, trusted, &ceremony); err != nil {
		return err
	}
	if ceremony.Format != "ix-bls12-381-groth16-ceremony-v1" || ceremony.Curve != "bls12-381" ||
		ceremony.Circuit != m.Files["circuit.bin"].SHA256 || ceremony.Domain != m.Domain ||
		len(ceremony.Phase1) == 0 || len(ceremony.Phase2) == 0 || len(ceremony.Phase1) > 1024 || len(ceremony.Phase2) > 1024 {
		return fmt.Errorf("BLS12-381 Groth16 ceremony does not match this circuit")
	}
	b1, err := unhex(ceremony.Phase1Beacon, 32)
	if err != nil {
		return err
	}
	b2, err := unhex(ceremony.Phase2Beacon, 32)
	if err != nil {
		return err
	}
	previous1 := mpcbls.NewPhase1(m.Domain)
	for i, contribution := range ceremony.Phase1 {
		next := new(mpcbls.Phase1)
		name, err := groth16BundlePath(path, contribution)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, contribution.Artifact, next); err != nil {
			return err
		}
		if err := previous1.Verify(next); err != nil {
			return fmt.Errorf("BLS12-381 Groth16 phase one contribution %d: %w", i, err)
		}
		previous1 = next
	}
	commons := previous1.Seal(b1)
	previous2 := new(mpcbls.Phase2)
	evaluations := previous2.Initialize(ccs.(*csbls.R1CS), &commons)
	for i, contribution := range ceremony.Phase2 {
		next := new(mpcbls.Phase2)
		name, err := groth16BundlePath(path, contribution)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, contribution.Artifact, next); err != nil {
			return err
		}
		if err := previous2.Verify(next); err != nil {
			return fmt.Errorf("BLS12-381 Groth16 phase two contribution %d: %w", i, err)
		}
		previous2 = next
	}
	pk, vk := previous2.Seal(&commons, &evaluations, b2)
	return groth16SaveKeysBLS(dir, m, pk, vk, "mpc", trusted)
}

func groth16ImportBLS(dir string, m *groth16Manifest, path, trusted string) error {
	_, _, err := groth16LoadBLS(dir, m)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("BLS12-381 Groth16 keys are already prepared")
	}
	var release groth16Release
	if err := groth16PinnedJSON(path, trusted, &release); err != nil {
		return err
	}
	if release.Format != "ix-bls12-381-groth16-release-v1" || release.Curve != "bls12-381" ||
		release.Circuit != m.Files["circuit.bin"].SHA256 || release.InnerVK != m.InnerVK || release.CommitmentHash != "sha256" {
		return fmt.Errorf("BLS12-381 Groth16 release does not match this circuit")
	}
	if _, err := unhex(release.Ceremony, 32); err != nil {
		return err
	}
	pk := groth16.NewProvingKey(blsCurveID)
	vk := new(g16bls.VerifyingKey)
	for _, item := range []struct {
		source groth16CeremonyFile
		target io.ReaderFrom
	}{{release.ProvingKey, pk}, {release.VerifyingKey, vk}} {
		name, err := groth16BundlePath(path, item.source)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, item.source.Artifact, item.target); err != nil {
			return err
		}
	}
	if pk.(*g16bls.ProvingKey).Domain.Cardinality != m.Domain {
		return fmt.Errorf("BLS12-381 Groth16 proving key domain differs")
	}
	return groth16SaveKeysBLS(dir, m, pk, vk, "mpc", release.Ceremony)
}

type groth16SessionBLS struct {
	mu             sync.Mutex
	key            *verifyingKey
	ccs            constraint.ConstraintSystem
	pk             groth16.ProvingKey
	vk             *g16bls.VerifyingKey
	manifest       *groth16Manifest
	closed, failed bool
}

func openGroth16BLS(dir string, metadata []byte, config groth16Backend) (*groth16SessionBLS, error) {
	if config.Device < 0 {
		return nil, fmt.Errorf("invalid BLS12-381 Groth16 device")
	}
	if config.CUDA {
		return nil, fmt.Errorf("BLS12-381 Groth16 CUDA is not supported; use CPU Groth16")
	}
	var m groth16Manifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	p, ccs, err := groth16LoadBLS(dir, &m)
	if err != nil {
		return nil, err
	}
	if !m.KeysReady {
		return nil, fmt.Errorf("BLS12-381 Groth16 keys are not prepared")
	}
	if err := m.checkFile(dir, "Groth16Verifier.sol"); err != nil {
		return nil, err
	}
	pk := groth16.NewProvingKey(blsCurveID)
	vk := new(g16bls.VerifyingKey)
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
			return nil, err
		}
	}
	if err := groth16CheckKeyBLS(vk, m.Commitments); err != nil {
		return nil, err
	}
	if err := groth16CheckPairBLS(pk.(*g16bls.ProvingKey), vk, m.Domain); err != nil {
		return nil, err
	}
	return &groth16SessionBLS{key: p, ccs: ccs, pk: pk, vk: vk, manifest: &m}, nil
}

func (p *groth16SessionBLS) close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed {
		p.closed = true
		p.pk, p.ccs, p.key, p.vk = nil, nil, nil, nil
	}
	return nil
}

func groth16PublicBLS(digest []byte) (witness.Witness, error) {
	if len(digest) != 32 {
		return nil, fmt.Errorf("expected a 32-byte claim digest")
	}
	return frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, blsCurveID.ScalarField(), frontend.PublicOnly())
}

func (p *groth16SessionBLS) proveAssignment(assignment frontend.Circuit, expected []byte) (native, solidityBytes []byte, err error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	defer func() {
		if err != nil {
			p.failed = true
		}
		if failure := recover(); failure != nil {
			p.failed = true
			panic(failure)
		}
	}()
	if p.closed || p.failed {
		return nil, nil, fmt.Errorf("BLS12-381 Groth16 prover is closed or failed")
	}
	w, err := frontend.NewWitness(assignment, blsCurveID.ScalarField())
	if err != nil {
		return nil, nil, err
	}
	public, err := groth16PublicBLS(expected)
	if err != nil {
		return nil, nil, err
	}
	actual, err := w.Public()
	if err != nil {
		return nil, nil, err
	}
	got, err := actual.MarshalBinary()
	if err != nil {
		return nil, nil, err
	}
	want, err := public.MarshalBinary()
	if err != nil {
		return nil, nil, err
	}
	if !bytes.Equal(got, want) {
		return nil, nil, fmt.Errorf("BLS12-381 Groth16 witness claim differs from the independently expected digest")
	}
	proof, err := groth16.Prove(p.ccs, p.pk, w, backend.WithProverHashToFieldFunction(sha256.New()))
	if err != nil {
		return nil, nil, err
	}
	if err := groth16.Verify(proof, p.vk, public, backend.WithVerifierHashToFieldFunction(sha256.New())); err != nil {
		return nil, nil, err
	}
	var encoded bytes.Buffer
	if _, err := proof.WriteTo(&encoded); err != nil {
		return nil, nil, err
	}
	if _, err := decodeGroth16ProofBLS(encoded.Bytes(), p.manifest.Commitments); err != nil {
		return nil, nil, err
	}
	return encoded.Bytes(), proof.(*g16bls.Proof).MarshalSolidity(), nil
}

func (p *groth16SessionBLS) prove(data, claim []byte) ([]byte, []byte, error) {
	var input witnessJSON
	if err := decodeReader(bytes.NewReader(data), &input); err != nil {
		return nil, nil, err
	}
	p.mu.Lock()
	if p.closed || p.failed {
		p.mu.Unlock()
		return nil, nil, fmt.Errorf("BLS12-381 Groth16 prover is closed or failed")
	}
	assignment, err := assignWitnessBLS(p.key, &input)
	p.mu.Unlock()
	if err != nil {
		return nil, nil, err
	}
	return p.proveAssignment(assignment, claim)
}

func decodeGroth16ProofBLS(data []byte, commitments int) (*g16bls.Proof, error) {
	if commitments < 0 || commitments > 1 || len(data) != 244+48*commitments {
		return nil, fmt.Errorf("invalid BLS12-381 Groth16 proof length")
	}
	if binary.BigEndian.Uint32(data[192:196]) != uint32(commitments) {
		return nil, fmt.Errorf("BLS12-381 Groth16 commitment count differs from the trusted key")
	}
	for _, offset := range []int{0, 48, 144, 196, 196 + 48*commitments} {
		if !isCompressedPointBLS(data[offset]) {
			return nil, fmt.Errorf("noncanonical BLS12-381 Groth16 point encoding")
		}
	}
	proof := new(g16bls.Proof)
	n, err := proof.ReadFrom(bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	if n != int64(len(data)) {
		return nil, fmt.Errorf("trailing BLS12-381 Groth16 proof data")
	}
	if commitments == 0 && !proof.CommitmentPok.IsInfinity() {
		return nil, fmt.Errorf("unexpected unused BLS12-381 Groth16 commitment proof")
	}
	var canonical bytes.Buffer
	if _, err := proof.WriteTo(&canonical); err != nil {
		return nil, err
	}
	if !bytes.Equal(data, canonical.Bytes()) {
		return nil, fmt.Errorf("noncanonical BLS12-381 Groth16 proof")
	}
	return proof, nil
}

func verifyGroth16BLS(key, trusted, data, claim []byte) error {
	if len(key) > 1<<20 || len(trusted) != 32 {
		return fmt.Errorf("invalid BLS12-381 Groth16 verifying key")
	}
	hash := sha256.Sum256(key)
	if !bytes.Equal(hash[:], trusted) {
		return fmt.Errorf("BLS12-381 Groth16 key differs from the trusted digest")
	}
	vk := new(g16bls.VerifyingKey)
	n, err := vk.ReadFrom(bytes.NewReader(key))
	if err != nil {
		return err
	}
	if n != int64(len(key)) {
		return fmt.Errorf("trailing BLS12-381 Groth16 verifying key data")
	}
	commitments := len(vk.PublicAndCommitmentCommitted)
	if err := groth16CheckKeyBLS(vk, commitments); err != nil {
		return err
	}
	proof, err := decodeGroth16ProofBLS(data, commitments)
	if err != nil {
		return err
	}
	public, err := groth16PublicBLS(claim)
	if err != nil {
		return err
	}
	return groth16.Verify(proof, vk, public, backend.WithVerifierHashToFieldFunction(sha256.New()))
}

func setupGroth16BLS(dir string, metadata []byte, kind uint32, descriptor, pin string) ([]byte, error) {
	var m groth16Manifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	var err error
	switch kind {
	case 0:
		err = groth16DevelopmentSetupBLS(dir, &m)
	case 1:
		err = groth16MPCSetupBLS(dir, &m, descriptor, pin)
	case 2:
		err = groth16ImportBLS(dir, &m, descriptor, pin)
	default:
		return nil, fmt.Errorf("unknown Groth16 setup operation")
	}
	if err != nil {
		return nil, err
	}
	return json.Marshal(m)
}
