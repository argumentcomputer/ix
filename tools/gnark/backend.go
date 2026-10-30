//go:build plonk || !groth16

package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"io"
	"os"

	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/zeebo/blake3"
)

// readSRS consumes ix's authenticated export. The expected digest comes from
// the Rust parameter loader, independently of this file's contents.
// These parameters belong to PLONK, independently of the KZG verifier circuit.
func readSRS(path, expectedDigest string, domain uint64) (*nativeSRS, error) {
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
	count := binary.LittleEndian.Uint64(header[80:])
	maxDegree := binary.LittleEndian.Uint64(header[40:48])
	if string(header[:8]) != srsMagic || count != domain+3 || domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || count-1 > maxDegree {
		return nil, fmt.Errorf("SRS identity, degree or required power count differs")
	}
	stat, err := f.Stat()
	if err != nil {
		return nil, err
	}
	if stat.Size() != int64(88+2*g2ExportBytes+2*baseBytes*count) {
		return nil, fmt.Errorf("invalid SRS export length")
	}
	srs := &nativeSRS{}
	for i := range srs.Vk.G2 {
		var point [g2ExportBytes]byte
		if _, err := io.ReadFull(r, point[:]); err != nil {
			return nil, err
		}
		if srs.Vk.G2[i], err = decodeG2(point[:]); err != nil {
			return nil, err
		}
		srs.Vk.Lines[i] = precomputeLines(srs.Vk.G2[i])
	}
	srs.Pk.G1, err = readAffinePoints(r, count)
	if err != nil {
		return nil, err
	}
	srs.Vk.G1 = srs.Pk.G1[0]
	if srs.Vk.G1.IsInfinity() || !srs.Vk.G1.IsOnCurve() || !srs.Vk.G1.IsInSubGroup() {
		return nil, fmt.Errorf("invalid SRS G1 anchor")
	}
	return srs, nil
}

func decodeProof(data []byte, commitments int) (*nativeProof, error) {
	if commitments < 0 || commitments > 1024 || len(data) != 9*pointBytesLen+232+(32+pointBytesLen)*commitments {
		return nil, fmt.Errorf("invalid PLONK proof length")
	}
	// Bound the two serialized vector lengths before gnark allocates them.
	if binary.BigEndian.Uint32(data[8*pointBytesLen:8*pointBytesLen+4]) != uint32(6+commitments) || binary.BigEndian.Uint32(data[9*pointBytesLen+228+32*commitments:9*pointBytesLen+232+32*commitments]) != uint32(commitments) {
		return nil, fmt.Errorf("invalid PLONK proof vector length")
	}
	for i := 0; i < 8; i++ {
		if !isCompressedPoint(data[pointBytesLen*i]) {
			return nil, fmt.Errorf("uncompressed proof point")
		}
	}
	if !isCompressedPoint(data[8*pointBytesLen+196+32*commitments]) {
		return nil, fmt.Errorf("uncompressed shifted opening")
	}
	for i := 0; i < commitments; i++ {
		if !isCompressedPoint(data[9*pointBytesLen+232+32*commitments+pointBytesLen*i]) {
			return nil, fmt.Errorf("uncompressed committed point")
		}
	}
	proof := new(nativeProof)
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

func verifyProof(key, trustedDigest, data, digest, expectedAnchors []byte) error {
	if len(key) > 1<<20 || len(data) > 1<<20 || len(trustedDigest) != 32 || len(digest) != 32 || len(expectedAnchors) != anchorBytesLen {
		return fmt.Errorf("invalid verification input length")
	}
	actual := sha256.Sum256(key)
	if !bytes.Equal(actual[:], trustedDigest) {
		return fmt.Errorf("trusted wrapper verification key digest differs")
	}
	vk := new(nativeVerifyingKey)
	reader := bytes.NewReader(key)
	if _, err := vk.ReadFrom(reader); err != nil {
		return err
	}
	if reader.Len() != 0 || vk.NbPublicVariables != 2 {
		return fmt.Errorf("invalid wrapper verifying key")
	}
	if !bytes.Equal(encodeAnchors(vk), expectedAnchors) {
		return fmt.Errorf("wrapper verification key setup anchors differ")
	}
	proof, err := decodeProof(data, len(vk.Qcp))
	if err != nil {
		return err
	}
	public, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		return err
	}
	return plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK))
}

type nativeVerifyingKey = plonkbn254.VerifyingKey
type nativeProof = plonkbn254.Proof

func encodeAnchors(vk *nativeVerifyingKey) []byte {
	out := make([]byte, 0, 320)
	for _, v := range []*fp.Element{&vk.Kzg.G1.X, &vk.Kzg.G1.Y, &vk.Kzg.G2[0].X.A0, &vk.Kzg.G2[0].X.A1, &vk.Kzg.G2[0].Y.A0, &vk.Kzg.G2[0].Y.A1, &vk.Kzg.G2[1].X.A0, &vk.Kzg.G2[1].X.A1, &vk.Kzg.G2[1].Y.A0, &vk.Kzg.G2[1].Y.A1} {
		b := v.Bytes()
		out = append(out, b[:]...)
	}
	return out
}
