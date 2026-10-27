package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime/debug"
	"strings"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbls "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/zeebo/blake3"
)

// readSRS consumes ix's authenticated export. The expected digest comes from
// the Rust parameter loader, independently of this file's contents.
func readSRS(path, expectedDigest string, domain uint64, p *profile) (*kzg.SRS, error) {
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
		return nil, fmt.Errorf("SRS export differs from the Rust loader's receipt")
	}
	if _, err := f.Seek(0, 0); err != nil {
		return nil, err
	}
	r := bufio.NewReaderSize(f, 1<<20)
	var header [88]byte
	if _, err := io.ReadFull(r, header[:]); err != nil {
		return nil, err
	}
	setup, err := unhex(p.SetupID, 32)
	if err != nil {
		return nil, err
	}
	count := binary.LittleEndian.Uint64(header[80:])
	if string(header[:8]) != "IXPSRS01" || !bytes.Equal(header[8:40], setup) || binary.LittleEndian.Uint64(header[40:48]) != p.PublicMaxDegree || count != domain+3 || domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || count-1 > p.PublicMaxDegree {
		return nil, fmt.Errorf("SRS identity, degree or required power count differs")
	}
	stat, err := f.Stat()
	if err != nil {
		return nil, err
	}
	if stat.Size() != int64(280+96*count) {
		return nil, fmt.Errorf("invalid SRS export length")
	}
	srs := &kzg.SRS{}
	for i := range srs.Vk.G2 {
		var point [96]byte
		if _, err := io.ReadFull(r, point[:]); err != nil {
			return nil, err
		}
		if _, err := srs.Vk.G2[i].SetBytes(point[:]); err != nil {
			return nil, err
		}
		srs.Vk.Lines[i] = bls.PrecomputeLines(srs.Vk.G2[i])
	}
	anchors, err := g2Keys(p.OuterKeys)
	if err != nil {
		return nil, err
	}
	if !srs.Vk.G2[0].Equal(&anchors[0]) || !srs.Vk.G2[1].Equal(&anchors[1]) {
		return nil, fmt.Errorf("SRS G2 anchors differ")
	}
	srs.Pk.G1, err = readAffinePoints(r, count)
	if err != nil {
		return nil, err
	}
	srs.Vk.G1 = srs.Pk.G1[0]
	g, err := p.Generator.native()
	if err != nil {
		return nil, err
	}
	if !srs.Vk.G1.Equal(&g) {
		return nil, fmt.Errorf("SRS G1 anchor differs")
	}
	return srs, nil
}

func prepare(dir, path, digest string) error {
	decodedDigest, err := unhex(digest, 32)
	if err != nil {
		return err
	}
	digest = hex.EncodeToString(decodedDigest)
	metadata, err := loadManifest(dir)
	if err != nil {
		return err
	}
	if metadata.KeysReady {
		if metadata.SRSBLAKE3 != digest {
			return fmt.Errorf("prepared keys belong to a different SRS export")
		}
		if err := metadata.checkKeys(dir); err != nil {
			return err
		}
		fmt.Printf("reused_keys=true verifying_key_sha256=%s\n", metadata.Files["verifying-key.bin"].SHA256)
		return nil
	}
	m := metadata
	if err := m.checkFile(dir, "circuit.bin"); err != nil {
		return err
	}
	p, err := loadProfile(filepath.Join(dir, "profile.json"))
	if err != nil {
		return err
	}
	fmt.Fprintf(os.Stderr, "stage=srs_import domain=%d\n", m.Domain)
	start := time.Now()
	srs, err := readSRS(path, digest, m.Domain, p)
	if err != nil {
		return err
	}
	m.Seconds["srsImport"] = time.Since(start).Seconds()
	start = time.Now()
	cacheRoot := os.Getenv("IX_PLONK_LAGRANGE_CACHE")
	if cacheRoot == "" {
		cacheRoot = filepath.Join(filepath.Dir(dir), "lagrange")
	}
	fmt.Fprintln(os.Stderr, "stage=lagrange")
	lagrangeSRS, reused, err := lagrangeParameters(cacheRoot, srs, m.Domain, p.SetupID, digest, m.ExecutableSHA256)
	if err != nil {
		return err
	}
	m.Seconds["lagrange"] = time.Since(start).Seconds()
	// The group FFT's temporary arrays must not overlap circuit deserialization.
	debug.FreeOSMemory()
	fmt.Fprintln(os.Stderr, "stage=load_circuit")
	_, ccs, _, err := loadCircuit(dir)
	if err != nil {
		return err
	}
	fmt.Fprintln(os.Stderr, "stage=index")
	start = time.Now()
	pk, vk, err := plonk.Setup(ccs, srs, lagrangeSRS)
	if err != nil {
		return err
	}
	m.Seconds["index"] = time.Since(start).Seconds()
	m.Commitments = len(vk.(*plonkbls.VerifyingKey).Qcp)
	debug.FreeOSMemory()
	fmt.Fprintln(os.Stderr, "stage=write_keys")
	if err := saveBinary(dir, "proving-key.bin", pk, m); err != nil {
		return err
	}
	if err := saveBinary(dir, "verifying-key.bin", vk, m); err != nil {
		return err
	}
	if err := atomicFile(filepath.Join(dir, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
		return err
	}
	m.Files["PlonkVerifier.sol"], err = fileHash(filepath.Join(dir, "PlonkVerifier.sol"))
	if err != nil {
		return err
	}
	m.SRSBLAKE3, m.KeysReady = digest, true
	if err := writeJSON(filepath.Join(dir, "manifest.json"), m); err != nil {
		return err
	}
	fmt.Printf("domain=%d extra_commitments=%d reused_lagrange=%t verifying_key_sha256=%s\n", m.Domain, m.Commitments, reused, m.Files["verifying-key.bin"].SHA256)
	return nil
}

func prove(dir, path, out string) error {
	p, ccs, m, err := loadCircuit(dir)
	if err != nil {
		return err
	}
	if err := m.checkKeys(dir); err != nil {
		return err
	}
	pk := plonk.NewProvingKey(ecc.BLS12_381)
	if err := readBinary(filepath.Join(dir, "proving-key.bin"), pk); err != nil {
		return err
	}
	vk := plonk.NewVerifyingKey(ecc.BLS12_381)
	if err := readBinary(filepath.Join(dir, "verifying-key.bin"), vk); err != nil {
		return err
	}
	assignment, err := witnessAssignment(p, path)
	if err != nil {
		return err
	}
	w, err := frontend.NewWitness(assignment, ecc.BLS12_381.ScalarField())
	if err != nil {
		return err
	}
	start := time.Now()
	proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		return err
	}
	seconds := time.Since(start).Seconds()
	public, err := w.Public()
	if err != nil {
		return err
	}
	start = time.Now()
	if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		return err
	}
	verifySeconds := time.Since(start).Seconds()
	if err := atomicFile(filepath.Join(out, "proof.bin"), func(w io.Writer) error { _, err := proof.WriteTo(w); return err }); err != nil {
		return err
	}
	solidityBytes := proof.(*plonkbls.Proof).MarshalSolidity()
	if err := atomicFile(filepath.Join(out, "proof.solidity.bin"), func(w io.Writer) error { _, err := w.Write(solidityBytes); return err }); err != nil {
		return err
	}
	report := map[string]any{"proveSeconds": seconds, "verifySeconds": verifySeconds, "solidityBytes": len(solidityBytes), "verifyingKeySHA256": m.Files["verifying-key.bin"].SHA256}
	if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
		return err
	}
	fmt.Printf("prove_seconds=%.3f verify_seconds=%.6f solidity_bytes=%d\n", seconds, verifySeconds, len(solidityBytes))
	return nil
}

func decodeProof(data []byte, commitments int) (*plonkbls.Proof, error) {
	if commitments < 0 || commitments > 1024 || len(data) != 664+80*commitments {
		return nil, fmt.Errorf("invalid PLONK proof length")
	}
	// Bound the two serialized vector lengths before gnark allocates them.
	if binary.BigEndian.Uint32(data[384:388]) != uint32(6+commitments) || binary.BigEndian.Uint32(data[660+32*commitments:664+32*commitments]) != uint32(commitments) {
		return nil, fmt.Errorf("invalid PLONK proof vector length")
	}
	for i := 0; i < 8; i++ {
		if data[48*i]&0x80 == 0 {
			return nil, fmt.Errorf("uncompressed proof point")
		}
	}
	if data[580+32*commitments]&0x80 == 0 {
		return nil, fmt.Errorf("uncompressed shifted opening")
	}
	for i := 0; i < commitments; i++ {
		if data[664+32*commitments+48*i]&0x80 == 0 {
			return nil, fmt.Errorf("uncompressed committed point")
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
		return nil, fmt.Errorf("noncanonical proof")
	}
	return proof, nil
}

type publicClaim struct {
	Claim [2]frontend.Variable `gnark:",public"`
}

func (*publicClaim) Define(frontend.API) error { return nil }

func verify(keyPath, trustedDigest, proofPath, expectedClaim string, expectedAnchors ...string) error {
	key, err := fileHash(keyPath)
	if err != nil {
		return err
	}
	if key.SHA256 != strings.TrimPrefix(trustedDigest, "0x") {
		return fmt.Errorf("trusted wrapper verification key digest differs")
	}
	vk := new(plonkbls.VerifyingKey)
	if err := readBinary(keyPath, vk); err != nil {
		return err
	}
	if vk.NbPublicVariables != 2 {
		return fmt.Errorf("wrapper key has wrong public-input schema")
	}
	if len(expectedAnchors) > 1 {
		return fmt.Errorf("expected one anchor encoding")
	}
	if len(expectedAnchors) == 1 {
		expected, err := unhex(expectedAnchors[0], 240)
		if err != nil {
			return err
		}
		g := vk.Kzg.G1.Bytes()
		h := vk.Kzg.G2[0].Bytes()
		tauH := vk.Kzg.G2[1].Bytes()
		actual := append(append(append([]byte(nil), g[:]...), h[:]...), tauH[:]...)
		if !bytes.Equal(actual, expected) {
			return fmt.Errorf("wrapper verification key setup anchors differ")
		}
	}
	digest, err := unhex(expectedClaim, 32)
	if err != nil {
		return err
	}
	f, err := os.Open(proofPath)
	if err != nil {
		return err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, 1<<20))
	if err != nil {
		return err
	}
	start := time.Now()
	proof, err := decodeProof(data, len(vk.Qcp))
	if err != nil {
		return err
	}
	w, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, ecc.BLS12_381.ScalarField(), frontend.PublicOnly())
	if err != nil {
		return err
	}
	if err := plonk.Verify(proof, vk, w, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		return err
	}
	fmt.Printf("verified claim=%s verify_seconds=%.6f\n", hex.EncodeToString(digest), time.Since(start).Seconds())
	return nil
}
