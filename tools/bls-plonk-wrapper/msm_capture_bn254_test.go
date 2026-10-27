//go:build !bls12381

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"
	"unsafe"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/iop"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	native "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
)

const msmCaptureFormat = "ix-bn254-init-msm-capture-v1"
const msmScalarFormat = "bn254-fr-u64le-montgomery-v1"

var errMSMCaptureComplete = errors.New("required Init MSM captures are complete")

type msmCaptureRecord struct {
	Index                      int
	Caller, Basis, ScalarsFile string
	Offset, Count              uint64
	Scalars                    artifact
	CPUResult, CPUResultSHA256 string
	CPUSeconds, WriteSeconds   float64
}

type msmCaptureManifest struct {
	Format, ScalarFormat, Scope                                                 string
	Complete, StoppedBeforeQuotient                                             bool
	ArtifactManifestSHA256, ProvingKeySHA256, InnerVKSHA256, VerifyingKeySHA256 string
	ExpectedClaim, TestBinarySHA256                                             string
	Domain                                                                      uint64
	Constraints, PublicInputs, NumCPU, GOMAXPROCS                               int
	Witness                                                                     artifact
	ValidationSeconds, LoadSeconds, WitnessSeconds, CaptureSeconds              float64
	Records                                                                     []msmCaptureRecord
}

func msmTestRequired(t *testing.T, prefix, name string) string {
	t.Helper()
	value := os.Getenv(prefix + name)
	if value == "" {
		t.Fatalf("%s%s must be explicit", prefix, name)
	}
	return value
}

func rawMontgomery(values []fr.Element) []byte {
	if len(values) == 0 {
		return nil
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(&values[0])), len(values)*32)
}

func checkRawMontgomeryABI() error {
	var one uint64 = 1
	if unsafe.Sizeof(fr.Element{}) != 32 || *(*byte)(unsafe.Pointer(&one)) != 1 {
		return fmt.Errorf("MSM capture requires the 32-byte little-endian field ABI")
	}
	return nil
}

func authenticatedMSMKey(t *testing.T, dir, pin string) (*manifest, *native.ProvingKey, float64, float64) {
	t.Helper()
	started := time.Now()
	m, err := cpuProfileManifest(dir, pin)
	if err != nil {
		t.Fatal(err)
	}
	validation := time.Since(started).Seconds()
	started = time.Now()
	pk := new(native.ProvingKey)
	if err := cpuProfileReadBinary(filepath.Join(dir, "proving-key.bin"), m.Files["proving-key.bin"], pk); err != nil {
		t.Fatal(err)
	}
	if pk.Vk == nil || pk.Vk.Size != m.Domain || uint64(len(pk.Kzg.G1)) != m.Domain+3 || uint64(len(pk.KzgLagrange.G1)) != m.Domain {
		t.Fatal("authenticated proving-key dimensions differ")
	}
	h := sha256.New()
	n, err := pk.Vk.WriteTo(h)
	if err != nil {
		t.Fatal(err)
	}
	if n != m.Files["verifying-key.bin"].Bytes || hex.EncodeToString(h.Sum(nil)) != m.Files["verifying-key.bin"].SHA256 {
		t.Fatal("proving key embeds a different verifying key")
	}
	return m, pk, validation, time.Since(started).Seconds()
}

type recordingCPUAccelerator struct {
	mu      sync.Mutex
	pk      *native.ProvingKey
	out     string
	records []msmCaptureRecord
}

func (*recordingCPUAccelerator) ToCanonical(*fft.Domain, *iop.Polynomial) error {
	return fmt.Errorf("unexpected FFT during MSM-only capture")
}
func (*recordingCPUAccelerator) ComputeNumerator(*native.NumeratorInput) (*iop.Polynomial, error) {
	return nil, fmt.Errorf("unexpected numerator during MSM-only capture")
}

func captureBasisRange(full, points []curve.G1Affine) (uint64, bool) {
	if len(full) == 0 || len(points) == 0 {
		return 0, false
	}
	width := unsafe.Sizeof(curve.G1Affine{})
	start := uintptr(unsafe.Pointer(&full[0]))
	end := start + uintptr(len(full))*width
	pointStart := uintptr(unsafe.Pointer(&points[0]))
	pointEnd := pointStart + uintptr(len(points))*width
	if end < start || pointEnd < pointStart || pointStart < start || pointEnd > end || (pointStart-start)%width != 0 {
		return 0, false
	}
	return uint64((pointStart - start) / width), true
}

func captureCaller() string {
	var pcs [20]uintptr
	n := runtime.Callers(2, pcs[:])
	frames := runtime.CallersFrames(pcs[:n])
	for {
		frame, more := frames.Next()
		if strings.Contains(frame.Function, "commitToLRO.func") || strings.HasSuffix(frame.Function, ".bsb22Hint") {
			return frame.Function
		}
		if !more {
			return "unknown"
		}
	}
}

func (a *recordingCPUAccelerator) MultiExp(points []curve.G1Affine, scalars []fr.Element) (curve.G1Affine, error) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if len(a.records) >= 4 {
		return curve.G1Affine{}, errMSMCaptureComplete
	}
	if len(points) != len(scalars) {
		return curve.G1Affine{}, fmt.Errorf("capture MSM length mismatch")
	}
	offset, ok := captureBasisRange(a.pk.KzgLagrange.G1, points)
	if !ok {
		return curve.G1Affine{}, fmt.Errorf("capture expected the initial Lagrange MSMs")
	}
	row := msmCaptureRecord{Index: len(a.records), Caller: captureCaller(), Basis: "lagrange", Offset: offset, Count: uint64(len(scalars))}
	row.ScalarsFile = fmt.Sprintf("msm-%02d.scalars.bin", row.Index)
	started := time.Now()
	var result curve.G1Affine
	if _, err := result.MultiExp(points, scalars, ecc.MultiExpConfig{}); err != nil {
		return result, err
	}
	row.CPUSeconds = time.Since(started).Seconds()
	started = time.Now()
	f, err := os.OpenFile(filepath.Join(a.out, row.ScalarsFile), os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
	if err != nil {
		return result, err
	}
	h := sha256.New()
	n, writeErr := io.Copy(io.MultiWriter(f, h), bytes.NewReader(rawMontgomery(scalars)))
	if writeErr == nil {
		writeErr = f.Sync()
	}
	writeErr = errors.Join(writeErr, f.Close())
	if writeErr != nil {
		return result, writeErr
	}
	if n != int64(row.Count*32) {
		return result, fmt.Errorf("incomplete scalar capture")
	}
	row.Scalars = artifact{SHA256: hex.EncodeToString(h.Sum(nil)), Bytes: n}
	encoded := result.Bytes()
	row.CPUResult = hex.EncodeToString(encoded[:])
	row.CPUResultSHA256 = fmt.Sprintf("%x", sha256.Sum256(encoded[:]))
	row.WriteSeconds = time.Since(started).Seconds()
	a.records = append(a.records, row)
	runtime.KeepAlive(points)
	runtime.KeepAlive(scalars)
	if len(a.records) == 4 {
		return result, errMSMCaptureComplete
	}
	return result, nil
}

func validateCapture(m *msmCaptureManifest, artifacts *manifest) error {
	if m.Format != msmCaptureFormat || m.ScalarFormat != msmScalarFormat || !m.Complete || !m.StoppedBeforeQuotient || len(m.Records) != 4 || m.Domain != artifacts.Domain || m.Constraints != artifacts.Constraints || m.PublicInputs != 2 || m.ProvingKeySHA256 != artifacts.Files["proving-key.bin"].SHA256 || m.InnerVKSHA256 != artifacts.Files["verifying-key.bin"].SHA256 || m.InnerVKSHA256 != artifacts.InnerVKSHA256 {
		return fmt.Errorf("capture identity or shape differs")
	}
	shapes := make(map[[2]uint64]int)
	for i, row := range m.Records {
		if row.Index != i || row.Basis != "lagrange" || row.ScalarsFile != fmt.Sprintf("msm-%02d.scalars.bin", i) || row.Count == 0 || row.Offset > m.Domain || row.Count > m.Domain-row.Offset || row.Scalars.Bytes != int64(row.Count*32) {
			return fmt.Errorf("invalid capture range or filename")
		}
		if _, err := cpuProfileDigest(row.Scalars.SHA256); err != nil {
			return err
		}
		encoded, err := unhex(row.CPUResult, 32)
		if err != nil {
			return err
		}
		if fmt.Sprintf("%x", sha256.Sum256(encoded)) != row.CPUResultSHA256 {
			return fmt.Errorf("captured CPU result digest differs")
		}
		shapes[[2]uint64{row.Offset, row.Count}]++
	}
	rows := uint64(m.Constraints + m.PublicInputs)
	if len(shapes) != 3 || shapes[[2]uint64{0, m.Domain}] != 1 || shapes[[2]uint64{0, rows}] != 1 || shapes[[2]uint64{2, uint64(m.Constraints)}] != 2 {
		return fmt.Errorf("capture does not contain BSB22 and all three LRO MSMs")
	}
	return nil
}

func TestCaptureActualInitMSMs(t *testing.T) {
	if os.Getenv("IX_PLONK_CUDA_MSM_CAPTURE") != "1" {
		t.Skip("set IX_PLONK_CUDA_MSM_CAPTURE=1 with explicit artifact and claim pins")
	}
	if os.Getenv("GOMAXPROCS") != "" {
		t.Fatal("unset GOMAXPROCS for default CPU parallelism")
	}
	if err := checkRawMontgomeryABI(); err != nil {
		t.Fatal(err)
	}
	const prefix = "IX_PLONK_CUDA_MSM_CAPTURE_"
	dir, out, witnessPath := msmTestRequired(t, prefix, "ARTIFACTS"), msmTestRequired(t, prefix, "OUTPUT"), msmTestRequired(t, prefix, "WITNESS")
	pin, err := cpuProfileDigest(msmTestRequired(t, prefix, "MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	claim, err := cpuProfileDigest(msmTestRequired(t, prefix, "EXPECTED_CLAIM"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(out, 0700); err != nil {
		t.Fatal(err)
	}
	m, pk, validationSeconds, keySeconds := authenticatedMSMKey(t, dir, pin)
	started := time.Now()
	ccs := plonk.NewCS(curveID)
	if err := cpuProfileReadBinary(filepath.Join(dir, "circuit.bin"), m.Files["circuit.bin"], ccs); err != nil {
		t.Fatal(err)
	}
	vk := new(native.VerifyingKey)
	if err := cpuProfileReadBinary(filepath.Join(dir, "verifying-key.bin"), m.Files["verifying-key.bin"], vk); err != nil {
		t.Fatal(err)
	}
	if ccs.GetNbConstraints() != m.Constraints || ccs.GetNbPublicVariables() != 2 || len(ccs.GetCommitments().CommitmentIndexes()) != 1 {
		t.Fatal("capture circuit metadata differs")
	}
	p, err := loadVerifyingKey(filepath.Join(dir, "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := m.checkFile(dir, "vk.json"); err != nil {
		t.Fatal(err)
	}
	loadSeconds := keySeconds + time.Since(started).Seconds()
	started = time.Now()
	witnessIdentity, err := fileHash(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	assignment, err := witnessAssignment(p, witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	after, err := fileHash(witnessPath)
	if err != nil || after != witnessIdentity {
		t.Fatal("witness changed during loading")
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	digest, _ := hex.DecodeString(claim)
	expected, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatal(err)
	}
	actual, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	wantBytes, err := expected.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	actualBytes, err := actual.MarshalBinary()
	if err != nil || !bytes.Equal(actualBytes, wantBytes) {
		t.Fatal("capture witness differs from independently expected claim")
	}
	identity, err := executableHash()
	if err != nil {
		t.Fatal(err)
	}
	report := msmCaptureManifest{Format: msmCaptureFormat, ScalarFormat: msmScalarFormat, Scope: "Actual pinned Init witness solved on CPU; first four Lagrange MSMs captured before any quotient. CPU callbacks are serialized at default CPU parallelism. Raw local scalar captures are test artifacts, not proofs.", ArtifactManifestSHA256: pin, ProvingKeySHA256: m.Files["proving-key.bin"].SHA256, VerifyingKeySHA256: m.Files["verifying-key.bin"].SHA256, InnerVKSHA256: m.InnerVKSHA256, ExpectedClaim: claim, TestBinarySHA256: identity, Domain: m.Domain, Constraints: m.Constraints, PublicInputs: 2, Witness: witnessIdentity, NumCPU: runtime.NumCPU(), GOMAXPROCS: runtime.GOMAXPROCS(0), ValidationSeconds: validationSeconds, LoadSeconds: loadSeconds, WitnessSeconds: time.Since(started).Seconds()}
	capture := &recordingCPUAccelerator{pk: pk, out: out}
	pk.SetAccelerator(capture)
	defer pk.SetAccelerator(nil)
	started = time.Now()
	_, err = plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	report.CaptureSeconds = time.Since(started).Seconds()
	report.Records = capture.records
	if !errors.Is(err, errMSMCaptureComplete) || len(report.Records) != 4 {
		t.Fatalf("capture did not reach the expected stop; completed MSM count=%d", len(report.Records))
	}
	report.Complete, report.StoppedBeforeQuotient = true, true
	if err := validateCapture(&report, m); err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(out, "capture.json")
	if err := writeJSON(path, &report); err != nil {
		t.Fatal(err)
	}
	receipt, err := fileHash(path)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("capture_manifest_sha256=%s msm_count=%d stopped_before_quotient=true", receipt.SHA256, len(report.Records))
}

type rawScalarVector []fr.Element

func (values rawScalarVector) ReadFrom(reader io.Reader) (int64, error) {
	n, err := io.ReadFull(reader, rawMontgomery(values))
	return int64(n), err
}

func readCaptureManifest(path, pin string) (*msmCaptureManifest, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, (1<<20)+1))
	if err != nil {
		return nil, err
	}
	if len(data) > 1<<20 || fmt.Sprintf("%x", sha256.Sum256(data)) != pin {
		return nil, fmt.Errorf("capture manifest differs from trusted SHA-256")
	}
	var m msmCaptureManifest
	d := json.NewDecoder(bytes.NewReader(data))
	d.DisallowUnknownFields()
	if err := d.Decode(&m); err != nil {
		return nil, err
	}
	if err := d.Decode(new(any)); err != io.EOF {
		return nil, fmt.Errorf("trailing capture manifest data")
	}
	return &m, nil
}
