package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"time"

	bn "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/zeebo/blake3"
)

// readSP1Lagrange accepts the legacy gnark BN254 key layout used by SP1
// v6.1.0. Circuit-specific key data is discarded. Vector lengths are bounded
// before invoking gnark's decoder, and only compressed G1 arrays are accepted.
func readSP1Lagrange(path string, domain uint64, srs *nativeSRS) ([]nativeG1, [32]byte, error) {
	var digest [32]byte
	f, err := os.Open(path)
	if err != nil {
		return nil, digest, err
	}
	defer f.Close()
	if stat, err := f.Stat(); err != nil || !stat.Mode().IsRegular() {
		return nil, digest, fmt.Errorf("candidate must be a regular file")
	}
	if domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 {
		return nil, digest, fmt.Errorf("invalid candidate domain")
	}
	header := make([]byte, 112+8*32+4)
	if _, err := io.ReadFull(f, header); err != nil {
		return nil, digest, err
	}
	if binary.BigEndian.Uint64(header[:8]) != domain || binary.BigEndian.Uint64(header[72:80]) > 64 {
		return nil, digest, fmt.Errorf("SP1 key domain or public count differs")
	}
	commitments := binary.BigEndian.Uint32(header[len(header)-4:])
	if commitments > 64 {
		return nil, digest, fmt.Errorf("oversized SP1 commitment count")
	}
	for i := 0; i < 8; i++ {
		if !isCompressedPoint(header[112+32*i]) {
			return nil, digest, fmt.Errorf("uncompressed SP1 verifier point")
		}
	}
	// The fixed-G2 line table contains 2*2*66 lines with two Fp2 coefficients.
	tail := make([]byte, int(commitments)*32+32+2*64+2*2*66*2*2*32+4)
	if _, err := io.ReadFull(f, tail); err != nil {
		return nil, digest, err
	}
	for i := uint32(0); i <= commitments; i++ {
		if !isCompressedPoint(tail[32*i]) {
			return nil, digest, fmt.Errorf("uncompressed SP1 commitment or generator")
		}
	}
	for i := 0; i < 2; i++ {
		if !isCompressedPoint(tail[int(commitments)*32+32+64*i]) {
			return nil, digest, fmt.Errorf("uncompressed SP1 G2 anchor")
		}
	}
	indexes := binary.BigEndian.Uint32(tail[len(tail)-4:])
	if indexes != commitments {
		return nil, digest, fmt.Errorf("SP1 commitment index count differs")
	}
	header = append(header, tail...)
	last := make([]byte, int(indexes)*8)
	if _, err := io.ReadFull(f, last); err != nil {
		return nil, digest, err
	}
	header = append(header, last...)
	vk := new(nativeVerifyingKey)
	r := bytes.NewReader(header)
	if _, err := vk.ReadFrom(r); err != nil {
		return nil, digest, err
	}
	if r.Len() != 0 || !bytes.Equal(encodeAnchors(vk), encodeAnchors(&nativeVerifyingKey{Kzg: srs.Vk})) {
		return nil, digest, fmt.Errorf("SP1 setup anchors differ from admitted SRS")
	}
	d := fft.NewDomain(domain, fft.WithoutPrecompute())
	if !vk.Generator.Equal(&d.Generator) || !vk.SizeInv.Equal(&d.CardinalityInv) {
		return nil, digest, fmt.Errorf("SP1 evaluation domain differs")
	}
	var count [4]byte
	if _, err := io.ReadFull(f, count[:]); err != nil {
		return nil, digest, err
	}
	if uint64(binary.BigEndian.Uint32(count[:])) != domain+3 {
		return nil, digest, fmt.Errorf("SP1 monomial length differs")
	}
	offset, err := f.Seek(int64(32*(domain+3)), io.SeekCurrent)
	if err != nil {
		return nil, digest, err
	}
	stat, err := f.Stat()
	if err != nil {
		return nil, digest, err
	}
	if stat.Size() != offset+4+int64(32*domain) {
		return nil, digest, fmt.Errorf("SP1 key length differs")
	}
	encoded := make([]byte, 4+32*domain)
	if _, err := io.ReadFull(f, encoded); err != nil {
		return nil, digest, err
	}
	if uint64(binary.BigEndian.Uint32(encoded[:4])) != domain {
		return nil, digest, fmt.Errorf("SP1 Lagrange count differs")
	}
	for i := uint64(0); i < domain; i++ {
		if !isCompressedPoint(encoded[4+32*i]) {
			return nil, digest, fmt.Errorf("uncompressed SP1 Lagrange point")
		}
	}
	digest = sha256.Sum256(encoded)
	var points []nativeG1
	if err := bn.NewDecoder(bytes.NewReader(encoded)).Decode(&points); err != nil {
		return nil, digest, err
	}
	for i := range points {
		canonical := points[i].Bytes()
		if !bytes.Equal(canonical[:], encoded[4+32*i:4+32*(i+1)]) {
			return nil, digest, fmt.Errorf("noncanonical Lagrange point")
		}
	}
	return points, digest, nil
}

// A nonzero difference between two N-point prime-order bases is a group
// polynomial of degree below N. A challenge sampled after binding every
// candidate point detects it except with probability at most (N-1)/Fr.
// Interpolating the challenge powers uses scalar FFTs, avoiding a group FFT.
func validateLagrange(srs *nativeSRS, points []nativeG1, setup, receipt string, digest [32]byte) (string, error) {
	n := len(points)
	if n < 2 || n&(n-1) != 0 || len(srs.Pk.G1) < n {
		return "", fmt.Errorf("invalid Lagrange validation dimensions")
	}
	h := blake3.New()
	h.Write([]byte("ix/bn254/plonk/lagrange-validation/v1"))
	for _, text := range []string{setup, receipt} {
		value, err := unhex(text, 32)
		if err != nil {
			return "", err
		}
		h.Write(value)
	}
	var length [8]byte
	binary.LittleEndian.PutUint64(length[:], uint64(n))
	h.Write(length[:])
	h.Write(digest[:])
	var wide [64]byte
	if _, err := io.ReadFull(h.Digest(), wide[:]); err != nil {
		return "", err
	}
	var challenge, order fr.Element
	challenge.SetBytes(wide[:])
	order.Exp(challenge, new(big.Int).SetUint64(uint64(n)))
	if challenge.IsZero() || order.IsOne() {
		return "", fmt.Errorf("degenerate validation challenge")
	}
	powers := make([]fr.Element, n)
	powers[0].SetOne()
	for i := 1; i < n; i++ {
		powers[i].Mul(&powers[i-1], &challenge)
	}
	coefficients := append([]fr.Element(nil), powers...)
	domain := fft.NewDomain(uint64(n))
	domain.FFTInverse(coefficients, fft.DIF)
	fft.BitReverse(coefficients)
	expected, err := kzg.Commit(coefficients, srs.Pk)
	if err != nil {
		return "", err
	}
	actual, err := kzg.Commit(powers, nativeKzgProvingKey{G1: points})
	if err != nil {
		return "", err
	}
	if !actual.Equal(&expected) {
		return "", fmt.Errorf("candidate Lagrange basis does not match authenticated monomial SRS")
	}
	value := challenge.Bytes()
	return hex.EncodeToString(value[:]), nil
}

func importLagrangeSP1(artifacts, monomial, receipt, candidate string) error {
	started := time.Now()
	m, err := loadManifest(artifacts)
	if err != nil {
		return err
	}
	p, err := loadVerifyingKey(filepath.Join(artifacts, "vk.json"))
	if err != nil {
		return err
	}
	srs, err := readSRS(monomial, receipt, m.Domain, p)
	if err != nil {
		return err
	}
	points, digest, err := readSP1Lagrange(candidate, m.Domain, srs)
	if err != nil {
		return err
	}
	challenge, err := validateLagrange(srs, points, p.SetupID, receipt, digest)
	if err != nil {
		return err
	}
	root := os.Getenv("IX_PLONK_LAGRANGE_CACHE")
	if root == "" {
		root = filepath.Join(filepath.Dir(artifacts), "lagrange")
	}
	want, dir, err := lagrangeLocation(root, m.Domain, p.SetupID, receipt, m.ExecutableSHA256)
	if err != nil {
		return err
	}
	if _, err := os.Stat(filepath.Join(dir, "manifest.json")); !os.IsNotExist(err) {
		return fmt.Errorf("Lagrange cache already exists or cannot be inspected")
	}
	validation := map[string]any{"format": "ix-bn254-lagrange-validation-v1", "domain": m.Domain,
		"setupID": p.SetupID, "monomialBLAKE3": receipt, "candidateVectorSHA256": hex.EncodeToString(digest[:]),
		"challenge": challenge, "basisRelationVerified": true, "elapsedSeconds": time.Since(started).Seconds()}
	if err := writeJSON(filepath.Join(dir, "validation.json"), validation); err != nil {
		return err
	}
	if err := publishLagrange(dir, want, points); err != nil {
		return err
	}
	fmt.Printf("validated_lagrange_import=true domain=%d elapsed_seconds=%.3f\n", m.Domain, time.Since(started).Seconds())
	return nil
}
