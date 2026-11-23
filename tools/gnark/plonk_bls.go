//go:build plonk || !groth16

package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime/debug"
	"sync"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	kzgbls "github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbls "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/zeebo/blake3"
)

func readAffinePointsBLS(r io.Reader, count uint64) ([]blsG1, error) {
	points := make([]blsG1, count)
	for i := range points {
		var raw [2 * blsBaseBytes]byte
		if _, err := io.ReadFull(r, raw[:]); err != nil {
			return nil, err
		}
		if err := points[i].X.SetBytesCanonical(raw[:blsBaseBytes]); err != nil {
			return nil, err
		}
		if err := points[i].Y.SetBytesCanonical(raw[blsBaseBytes:]); err != nil {
			return nil, err
		}
	}
	return points, nil
}

func writeAffinePointsBLS(w io.Writer, points []blsG1) error {
	b := bufio.NewWriterSize(w, 1<<20)
	for _, point := range points {
		x, y := point.X.Bytes(), point.Y.Bytes()
		if _, err := b.Write(x[:]); err != nil {
			return err
		}
		if _, err := b.Write(y[:]); err != nil {
			return err
		}
	}
	return b.Flush()
}

func loadLagrangeBLS(srs *kzgbls.SRS, domain uint64, path, expected string) (*kzgbls.SRS, error) {
	if domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || uint64(len(srs.Pk.G1)) < domain+3 {
		return nil, fmt.Errorf("invalid BLS12-381 Lagrange domain")
	}
	if expected != "" {
		f, err := os.Open(path)
		if err != nil {
			return nil, err
		}
		defer f.Close()
		info, err := f.Stat()
		if err != nil {
			return nil, err
		}
		if info.Size() != int64(2*blsBaseBytes*domain) {
			return nil, fmt.Errorf("BLS12-381 Lagrange cache size differs")
		}
		hash := sha256.New()
		reader := bufio.NewReaderSize(io.TeeReader(f, hash), 1<<20)
		points, err := readAffinePointsBLS(reader, domain)
		if err != nil {
			return nil, err
		}
		if _, err := reader.ReadByte(); err != io.EOF {
			return nil, fmt.Errorf("trailing BLS12-381 Lagrange cache data")
		}
		if hex.EncodeToString(hash.Sum(nil)) != expected {
			return nil, fmt.Errorf("BLS12-381 Lagrange cache checksum differs")
		}
		return &kzgbls.SRS{Pk: kzgbls.ProvingKey{G1: points}, Vk: srs.Vk}, nil
	}
	points, err := kzgbls.ToLagrangeG1(srs.Pk.G1[:domain])
	if err != nil {
		return nil, err
	}
	if err := atomicFile(path, func(w io.Writer) error { return writeAffinePointsBLS(w, points) }); err != nil {
		return nil, err
	}
	return &kzgbls.SRS{Pk: kzgbls.ProvingKey{G1: points}, Vk: srs.Vk}, nil
}

func readSRSBLS(path, expectedDigest string, domain uint64) (*kzgbls.SRS, error) {
	expected, err := unhex(expectedDigest, 32)
	if err != nil {
		return nil, err
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	h := blake3.New()
	if _, err := io.Copy(h, f); err != nil {
		return nil, err
	}
	if !bytes.Equal(h.Sum(nil), expected) {
		return nil, fmt.Errorf("BLS12-381 SRS export differs from the Rust loader's receipt")
	}
	if _, err := f.Seek(0, 0); err != nil {
		return nil, err
	}
	r := bufio.NewReaderSize(f, 1<<20)
	var header [88]byte
	if _, err := io.ReadFull(r, header[:]); err != nil {
		return nil, err
	}
	count := binary.LittleEndian.Uint64(header[80:])
	maxDegree := binary.LittleEndian.Uint64(header[40:48])
	if string(header[:8]) != blsSRSMagic || count != domain+3 || domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || count-1 > maxDegree {
		return nil, fmt.Errorf("BLS12-381 SRS identity, degree or required power count differs")
	}
	stat, err := f.Stat()
	if err != nil {
		return nil, err
	}
	if stat.Size() != int64(88+2*blsG2ExportBytes+2*blsBaseBytes*count) {
		return nil, fmt.Errorf("invalid BLS12-381 SRS export length")
	}
	srs := &kzgbls.SRS{}
	for i := range srs.Vk.G2 {
		var point [blsG2ExportBytes]byte
		if _, err := io.ReadFull(r, point[:]); err != nil {
			return nil, err
		}
		if srs.Vk.G2[i], err = decodeG2BLS(point[:]); err != nil {
			return nil, err
		}
		srs.Vk.Lines[i] = bls.PrecomputeLines(srs.Vk.G2[i])
	}
	srs.Pk.G1, err = readAffinePointsBLS(r, count)
	if err != nil {
		return nil, err
	}
	srs.Vk.G1 = srs.Pk.G1[0]
	if srs.Vk.G1.IsInfinity() || !srs.Vk.G1.IsOnCurve() || !srs.Vk.G1.IsInSubGroup() {
		return nil, fmt.Errorf("invalid BLS12-381 SRS G1 anchor")
	}
	return srs, nil
}

func decodeProofBLS(data []byte, commitments int) (*plonkbls.Proof, error) {
	if commitments < 0 || commitments > 1024 || len(data) != 9*blsPointBytesLen+232+(32+blsPointBytesLen)*commitments {
		return nil, fmt.Errorf("invalid BLS12-381 PLONK proof length")
	}
	if binary.BigEndian.Uint32(data[8*blsPointBytesLen:8*blsPointBytesLen+4]) != uint32(6+commitments) || binary.BigEndian.Uint32(data[9*blsPointBytesLen+228+32*commitments:9*blsPointBytesLen+232+32*commitments]) != uint32(commitments) {
		return nil, fmt.Errorf("invalid BLS12-381 PLONK proof vector length")
	}
	for i := 0; i < 8; i++ {
		if !isCompressedPointBLS(data[blsPointBytesLen*i]) {
			return nil, fmt.Errorf("uncompressed BLS12-381 proof point")
		}
	}
	if !isCompressedPointBLS(data[8*blsPointBytesLen+196+32*commitments]) {
		return nil, fmt.Errorf("uncompressed BLS12-381 shifted opening")
	}
	for i := 0; i < commitments; i++ {
		if !isCompressedPointBLS(data[9*blsPointBytesLen+232+32*commitments+blsPointBytesLen*i]) {
			return nil, fmt.Errorf("uncompressed BLS12-381 committed point")
		}
	}
	proof := new(plonkbls.Proof)
	r := bytes.NewReader(data)
	if _, err := proof.ReadFrom(r); err != nil {
		return nil, err
	}
	var canonical bytes.Buffer
	if _, err := proof.WriteTo(&canonical); err != nil {
		return nil, err
	}
	if r.Len() != 0 || !bytes.Equal(canonical.Bytes(), data) {
		return nil, fmt.Errorf("noncanonical BLS12-381 proof")
	}
	return proof, nil
}

func encodeAnchorsBLS(vk *plonkbls.VerifyingKey) []byte {
	g, h, t := vk.Kzg.G1.Bytes(), vk.Kzg.G2[0].Bytes(), vk.Kzg.G2[1].Bytes()
	out := make([]byte, 0, blsAnchorBytesLen)
	out = append(out, g[:]...)
	out = append(out, h[:]...)
	out = append(out, t[:]...)
	return out
}

func verifyProofBLS(key, trustedDigest, data, digest, expectedAnchors []byte) error {
	if len(key) > 1<<20 || len(data) > 1<<20 || len(trustedDigest) != 32 || len(digest) != 32 || len(expectedAnchors) != blsAnchorBytesLen {
		return fmt.Errorf("invalid BLS12-381 verification input length")
	}
	actual := sha256.Sum256(key)
	if !bytes.Equal(actual[:], trustedDigest) {
		return fmt.Errorf("trusted BLS12-381 wrapper verification key digest differs")
	}
	vk := new(plonkbls.VerifyingKey)
	reader := bytes.NewReader(key)
	if _, err := vk.ReadFrom(reader); err != nil {
		return err
	}
	if reader.Len() != 0 || vk.NbPublicVariables != 2 {
		return fmt.Errorf("invalid BLS12-381 wrapper verifying key")
	}
	if !bytes.Equal(encodeAnchorsBLS(vk), expectedAnchors) {
		return fmt.Errorf("BLS12-381 wrapper verification key setup anchors differ")
	}
	proof, err := decodeProofBLS(data, len(vk.Qcp))
	if err != nil {
		return err
	}
	public, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, blsCurveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		return err
	}
	return plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK))
}

func compileCircuitBLS(schema []byte, path string) (circuitInfo, error) {
	var info circuitInfo
	key, err := decodeVerifyingKeyBLS(schema)
	if err != nil {
		return info, err
	}
	ccs, err := frontend.Compile(blsCurveID.ScalarField(), scs.NewBuilder, newCircuitBLS(key))
	if err != nil {
		return info, err
	}
	info = circuitInfo{
		Domain:       ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables())),
		Constraints:  ccs.GetNbConstraints(),
		PublicInputs: ccs.GetNbPublicVariables(),
		Commitments:  len(ccs.GetCommitments().CommitmentIndexes()),
	}
	if info.PublicInputs != 2 {
		return info, fmt.Errorf("expected two public digest limbs")
	}
	return info, atomicFile(path, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
}

func prepareCircuitBLS(schema []byte, circuitPath string, circuitHash artifact, domain uint64, srsPath, receipt, lagrangePath, lagrangeDigest, output string) error {
	if _, err := decodeVerifyingKeyBLS(schema); err != nil {
		return err
	}
	srs, err := readSRSBLS(srsPath, receipt, domain)
	if err != nil {
		return err
	}
	lagrange, err := loadLagrangeBLS(srs, domain, lagrangePath, lagrangeDigest)
	if err != nil {
		return err
	}
	debug.FreeOSMemory()
	ccs := plonk.NewCS(blsCurveID)
	if err := readVerified(circuitPath, circuitHash, ccs); err != nil {
		return err
	}
	if ccs.GetNbPublicVariables() != 2 || ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints()+2)) != domain {
		return fmt.Errorf("BLS12-381 circuit domain differs")
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

type blsProver struct {
	mu             sync.Mutex
	key            *verifyingKey
	ccs            constraint.ConstraintSystem
	pk             plonk.ProvingKey
	vk             *plonkbls.VerifyingKey
	closed, failed bool
}

func openProverBLS(dir string, metadata []byte, config backendConfig) (*blsProver, error) {
	if config.CUDA {
		return nil, fmt.Errorf("BLS12-381 PLONK CUDA is not supported; use CPU PLONK")
	}
	var m manifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	if err := m.validate(); err != nil {
		return nil, err
	}
	if !m.KeysReady {
		return nil, fmt.Errorf("BLS12-381 PLONK keys are not prepared")
	}
	data, err := readDescription(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, err
	}
	sum := sha256.Sum256(data)
	if hex.EncodeToString(sum[:]) != m.InnerVKSHA256 || int64(len(data)) != m.Files["vk.json"].Bytes {
		return nil, fmt.Errorf("verifier description identity differs")
	}
	key, err := decodeVerifyingKeyBLS(data)
	if err != nil {
		return nil, err
	}
	p := &blsProver{
		key: key,
		ccs: plonk.NewCS(blsCurveID),
		pk:  plonk.NewProvingKey(blsCurveID),
		vk:  new(plonkbls.VerifyingKey),
	}
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"circuit.bin", p.ccs}, {"proving-key.bin", p.pk}, {"verifying-key.bin", p.vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
			return nil, err
		}
	}
	if p.ccs.GetNbConstraints() != m.Constraints || p.ccs.GetNbPublicVariables() != 2 || len(p.ccs.GetCommitments().CommitmentIndexes()) != m.Commitments || p.vk.Size != m.Domain || p.vk.NbPublicVariables != 2 || len(p.vk.Qcp) != m.Commitments {
		return nil, fmt.Errorf("decoded BLS12-381 circuit or key dimensions differ")
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
	return p, nil
}

func (p *blsProver) prove(data, expected []byte) ([]byte, []byte, error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	defer func() {
		if value := recover(); value != nil {
			p.failed = true
			panic(value)
		}
	}()
	if p.closed || p.failed {
		return nil, nil, fmt.Errorf("BLS12-381 prover is closed or failed")
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
	assignment, err := assignWitnessBLS(p.key, &input)
	if err != nil {
		return nil, nil, err
	}
	witness, err := frontend.NewWitness(assignment, blsCurveID.ScalarField())
	if err != nil {
		return nil, nil, err
	}
	proof, err := plonk.Prove(p.ccs, p.pk, witness, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		p.failed = true
		return nil, nil, err
	}
	public, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(expected)}, blsCurveID.ScalarField(), frontend.PublicOnly())
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
	return encoded.Bytes(), proof.(*plonkbls.Proof).MarshalSolidity(), nil
}

func (p *blsProver) close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.closed {
		return nil
	}
	p.closed = true
	p.key, p.ccs, p.pk, p.vk = nil, nil, nil, nil
	return nil
}
