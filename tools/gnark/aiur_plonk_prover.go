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
	"log"
	"os"
	"path/filepath"
	"runtime/pprof"
	"sync"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	csbn254 "github.com/consensys/gnark/constraint/bn254"
)

const aiurMaxPublic = 1 << 15
const aiurMaxSecret = aiurMaxDomain
const aiurMaxWitnessBytes = 12 + 32*(aiurMaxSecret+aiurMaxPublic)

type aiurManifest struct {
	Format, ScsSHA256, PairingSHA256, SRSBLAKE3 string
	Info                                        circuitInfo
	Files                                       map[string]artifact
}

func validateAiurInfo(info circuitInfo) error {
	if info.PublicInputs < 0 || info.PublicInputs > aiurMaxPublic || info.Constraints < 1 || info.Constraints > aiurMaxDomain || info.Domain < 2 || info.Domain > aiurMaxDomain || info.Domain != ecc.NextPowerOfTwo(uint64(info.Constraints+info.PublicInputs)) || info.Commitments != 1 {
		return fmt.Errorf("invalid Aiur PLONK dimensions")
	}
	return nil
}

func (m *aiurManifest) validate() error {
	if m.Format != aiurScsManifestFormat || m.Files == nil {
		return fmt.Errorf("invalid Aiur PLONK manifest")
	}
	if err := validateAiurInfo(m.Info); err != nil {
		return err
	}
	return m.validateScs()
}

// The prepared input layout fixes both counts. Validate them and the exact byte
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
	// traceReady is closed when a background trace precomputation ends.
	traceReady chan struct{}
}

func openAiurProver(dir string, metadata []byte, config backendConfig) (*aiurProver, error) {
	var m aiurManifest
	if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
		return nil, err
	}
	if err := m.validate(); err != nil {
		return nil, err
	}
	public, secret, err := aiurScsDimensions(dir, &m)
	if err != nil {
		return nil, err
	}
	p := &aiurProver{ccs: plonk.NewCS(curveID), pk: plonk.NewProvingKey(curveID), vk: new(nativeVerifyingKey), public: public, secret: secret}
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"circuit.bin", p.ccs}, {"verifying-key.bin", p.vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
			return nil, err
		}
	}
	phase := time.Now()
	source, err := loadAiurProvingKey(dir, m.Files["proving-key.bin"], &p.pk)
	if err != nil {
		return nil, err
	}
	log.Printf("aiur-plonk open phase=proving-key source=%s seconds=%.6f", source, time.Since(phase).Seconds())
	if p.public != m.Info.PublicInputs || p.ccs.GetNbPublicVariables() != p.public || p.ccs.GetNbSecretVariables() != p.secret || p.ccs.GetNbConstraints() != m.Info.Constraints || len(p.ccs.GetCommitments().CommitmentIndexes()) != 1 || p.vk.Size != m.Info.Domain || p.vk.NbPublicVariables != uint64(p.public) || len(p.vk.Qcp) != 1 {
		return nil, fmt.Errorf("Aiur circuit/key dimensions differ")
	}
	var encoded bytes.Buffer
	if _, err := p.pk.VerifyingKey().(io.WriterTo).WriteTo(&encoded); err != nil {
		return nil, err
	}
	hash := sha256.Sum256(encoded.Bytes())
	if hex.EncodeToString(hash[:]) != m.Files["verifying-key.bin"].SHA256 {
		return nil, fmt.Errorf("Aiur proving key embeds another verifier")
	}
	p.cleanup, err = configureBackend(p.pk, config)
	if err != nil {
		return nil, err
	}
	// The trace (selectors and permutation, about 16 GB at 2^25) depends only
	// on the circuit; a gnark that can precompute it builds it in the
	// background, while the prover waits for its witness, instead of inside
	// the first Prove. IX_PLONK_TRACE_AFTER=FILE delays it until FILE exists,
	// so that it does not add to an earlier stage's memory peak.
	if precompute, ok := p.pk.(interface{ PrecomputeTrace(*csbn254.SparseR1CS) }); ok {
		if spr, ok := p.ccs.(*csbn254.SparseR1CS); ok {
			p.traceReady = make(chan struct{})
			after := os.Getenv("IX_PLONK_TRACE_AFTER")
			go func() {
				defer close(p.traceReady)
				for after != "" {
					if _, err := os.Stat(after); err == nil {
						break
					}
					time.Sleep(20 * time.Millisecond)
				}
				phase := time.Now()
				precompute.PrecomputeTrace(spr)
				log.Printf("aiur-plonk open phase=trace seconds=%.6f", time.Since(phase).Seconds())
			}()
		}
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
	if p.traceReady != nil {
		<-p.traceReady
	}
	stopProfile, err := startCPUProfile()
	if err != nil {
		return nil, nil, err
	}
	proof, err := plonk.Prove(p.ccs, p.pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	stopProfile()
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

// startCPUProfile writes a Go CPU profile of the proving call to the file
// named by IX_PLONK_CPU_PROFILE (only the first proof of a process, since a
// later one would overwrite it); without it, it does nothing.
func startCPUProfile() (func(), error) {
	path := os.Getenv("IX_PLONK_CPU_PROFILE")
	if path == "" {
		return func() {}, nil
	}
	if _, err := os.Stat(path); err == nil {
		return func() {}, nil
	}
	file, err := os.Create(path)
	if err != nil {
		return nil, err
	}
	if err := pprof.StartCPUProfile(file); err != nil {
		file.Close()
		return nil, err
	}
	return func() {
		pprof.StopCPUProfile()
		file.Close()
	}, nil
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

// loadAiurProvingKey reads the proving key from its uncompressed encoding
// `proving-key.raw` when present and identical to the digest-pinned
// compressed one, and otherwise from `proving-key.bin`, writing the raw
// encoding for later loads. The raw file is decoded with gnark's checked
// reader (curve and subgroup membership), then re-encoded in the canonical
// compressed form, whose length and SHA-256 must be the manifest's
// `proving-key.bin`: a corrupted or substituted raw file is never used.
func loadAiurProvingKey(dir string, pinned artifact, pk *plonk.ProvingKey) (string, error) {
	raw := filepath.Join(dir, "proving-key.raw")
	if loaded, err := readRawProvingKey(raw, pinned); err == nil {
		*pk = loaded
		return "raw", nil
	} else if !os.IsNotExist(err) {
		log.Printf("aiur-plonk open raw proving key rejected: %v", err)
	}
	loaded := plonk.NewProvingKey(curveID)
	if err := readVerified(filepath.Join(dir, "proving-key.bin"), pinned, loaded); err != nil {
		return "", err
	}
	*pk = loaded
	if err := atomicFile(raw, func(w io.Writer) error {
		b := bufio.NewWriterSize(w, artifactBuffer)
		if _, err := loaded.WriteRawTo(b); err != nil {
			return err
		}
		return b.Flush()
	}); err != nil {
		log.Printf("aiur-plonk open raw proving key not written: %v", err)
	}
	return "compressed", nil
}

func readRawProvingKey(path string, pinned artifact) (plonk.ProvingKey, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	r := bufio.NewReaderSize(f, artifactBuffer)
	pk := plonk.NewProvingKey(curveID)
	if _, err := pk.ReadFrom(r); err != nil {
		return nil, err
	}
	var extra [1]byte
	if n, err := r.Read(extra[:]); n != 0 || err != io.EOF {
		return nil, fmt.Errorf("trailing raw proving key bytes")
	}
	hash := sha256.New()
	b := bufio.NewWriterSize(hash, artifactBuffer)
	n, err := pk.WriteTo(b)
	if err != nil {
		return nil, err
	}
	if err := b.Flush(); err != nil {
		return nil, err
	}
	if n != pinned.Bytes || hex.EncodeToString(hash.Sum(nil)) != pinned.SHA256 {
		return nil, fmt.Errorf("raw proving key differs from the pinned key")
	}
	return pk, nil
}
