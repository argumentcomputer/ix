//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/constraint"
	csbn254 "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/std/multicommit"
)

// aiurScsFile assembles an `ix-aiur-scs-v1` file from its sections.
type aiurScsFile struct {
	publics, wires, pre int
	gamma, beta         uint32
	outputs             []uint32
	coeffs              []int64
	gates               []aiurScsGate
	commits             []uint32
	kinds               []uint8
	hx, hy              []uint32
}

func (f *aiurScsFile) bytes() []byte {
	var b bytes.Buffer
	b.WriteString(aiurScsMagic)
	for _, x := range []uint64{uint64(f.publics), uint64(len(f.outputs)), uint64(f.wires), uint64(len(f.gates)), uint64(f.pre),
		uint64(len(f.commits)), uint64(f.gamma), uint64(f.beta), uint64(len(f.coeffs)), 0} {
		binary.Write(&b, binary.LittleEndian, x)
	}
	binary.Write(&b, binary.LittleEndian, f.outputs)
	for _, c := range f.coeffs {
		be := new(fr.Element).SetInt64(c).Bytes()
		for j := 31; j >= 0; j-- {
			b.WriteByte(be[j])
		}
	}
	for _, g := range f.gates {
		binary.Write(&b, binary.LittleEndian, []uint32{g.A, g.B, g.C})
		b.WriteByte(g.Sel)
		binary.Write(&b, binary.LittleEndian, []uint32{g.Al, g.Be, g.Om})
		b.WriteByte(byte(g.QC))
	}
	binary.Write(&b, binary.LittleEndian, f.commits)
	for x := 0; x < f.wires; x++ {
		b.WriteByte(f.kinds[x])
		binary.Write(&b, binary.LittleEndian, []uint32{f.hx[x], f.hy[x]})
	}
	return b.Bytes()
}

// A small well-formed file: 2 publics, 18 outputs (wires 2..19), a cell
// x = 20, a pre-commitment gate 3·x − y = 0 solving y = 21, and the
// post-commitment gate γ·y − z = 0 solving z = 23 (γ = 22).
func aiurScsSample() *aiurScsFile {
	f := &aiurScsFile{publics: 2, wires: 24, pre: 1, gamma: 22, beta: 23, coeffs: []int64{1, 3}}
	for i := 0; i < aiurTerminalOutputs; i++ {
		f.outputs = append(f.outputs, uint32(2+i))
	}
	f.gates = []aiurScsGate{
		{A: 20, B: 20, C: 21, Sel: 1 | 4, Al: 1, Be: 0, Om: 0, QC: 0},
		{A: 22, B: 21, C: 23, Sel: 8 | 4, Al: 0, Be: 0, Om: 0, QC: 0},
	}
	f.commits = []uint32{0, 1, 20}
	f.kinds = make([]uint8, f.wires)
	f.hx = make([]uint32, f.wires)
	f.hy = make([]uint32, f.wires)
	f.kinds[21], f.hx[21] = aiurScsSolve, 0
	f.kinds[22] = aiurScsChallenge
	f.kinds[23], f.hx[23] = aiurScsSolve, 1
	return f
}

func TestAiurScsParse(t *testing.T) {
	good := aiurScsSample()
	s, err := parseAiurScs(good.bytes())
	if err != nil {
		t.Fatal(err)
	}
	if s.Cells != 21 || s.Publics != 2 || s.Gates != 2 || s.Pre != 1 || len(s.Commits) != 3 {
		t.Fatalf("parsed shape %+v", s)
	}
	data := good.bytes()
	if _, err := parseAiurScs(append(append([]byte{}, data...), 0)); err == nil {
		t.Fatal("trailing byte accepted")
	}
	for name, edit := range map[string]func(f *aiurScsFile){
		"zero coefficient":       func(f *aiurScsFile) { f.coeffs[1] = 0 },
		"selector above 15":      func(f *aiurScsFile) { f.gates[0].Sel = 16 },
		"coefficient id":         func(f *aiurScsFile) { f.gates[1].Om = 2 },
		"wire out of range":      func(f *aiurScsFile) { f.gates[1].C = 24 },
		"repeated commit":        func(f *aiurScsFile) { f.commits = []uint32{0, 0} },
		"commit of a hint wire":  func(f *aiurScsFile) { f.commits = []uint32{21} },
		"pre beyond gates":       func(f *aiurScsFile) { f.pre = 3 },
		"two challenges":         func(f *aiurScsFile) { f.kinds[23] = aiurScsChallenge },
		"inputs not a prefix":    func(f *aiurScsFile) { f.kinds[23] = aiurScsInput },
		"solve gate without it":  func(f *aiurScsFile) { f.hx[23] = 0 },
		"unknown kind":           func(f *aiurScsFile) { f.kinds[23] = 9 },
		"no publics among cells": func(f *aiurScsFile) { f.publics = 22 },
	} {
		f := aiurScsSample()
		edit(f)
		if _, err := parseAiurScs(f.bytes()); err == nil {
			t.Errorf("%s accepted", name)
		}
	}
	bad := append([]byte{}, data...)
	copy(bad, "ixscs002")
	if _, err := parseAiurScs(bad); err == nil {
		t.Error("wrong magic accepted")
	}
}

func TestAiurScsSolveHint(t *testing.T) {
	m := fr.Modulus()
	field := func(x int64) *big.Int { return new(fr.Element).SetInt64(x).BigInt(new(big.Int)) }
	solve := func(code int64, al, be, om int64, w [3]int64, withInverse bool) (*big.Int, error) {
		in := []*big.Int{field(code), field(al), field(be), field(om), field(0), field(w[0]), field(w[1]), field(w[2])}
		if inv, ok := aiurScsSolveInverse(uint64(code), in[1], in[2], in[3]); ok && withInverse {
			in[4] = inv
		}
		res := []*big.Int{new(big.Int)}
		return res[0], aiurScsSolveHint(m, in, res)
	}
	// 3·a + 5·b − c + 15·a·b − 4 = 0 (α = 3, β = 5, ω = −1, all selectors,
	// qC = −4) at a = 7, b = 2 gives c = 21 + 10 + 210 − 4 = 237.
	for _, inverse := range []bool{true, false} {
		if c, err := solve(15|4<<4|(-4+128)<<8, 3, 5, -1, [3]int64{7, 2, 0}, inverse); err != nil || c.Int64() != 237 {
			t.Fatalf("solved c = %v, %v", c, err)
		}
	}
	// Solving a (slot a only, A = 3 + 15·b depends on b): a = 7 at b = 2, c = 237.
	if a, err := solve(15|1<<4|(-4+128)<<8, 3, 5, -1, [3]int64{0, 2, 237}, true); err != nil || a.Int64() != 7 {
		t.Fatalf("solved a = %v, %v", a, err)
	}
	// u in slots a and c of 2·u + 3·b − 1·u + 4 = 0 (no qM): u = −3·b − 4.
	if u, err := solve(1|2|4|5<<4|(4+128)<<8, 2, 3, -1, [3]int64{0, 5, 0}, true); err != nil || u.Cmp(field(-19)) != 0 {
		t.Fatalf("solved u = %v, %v", u, err)
	}
	// A gate quadratic in the unsolved wire (u in a and b with qM) is refused.
	if _, err := solve(8|4|3<<4|128<<8, 1, 1, 1, [3]int64{0, 0, 5}, true); err == nil {
		t.Fatal("quadratic gate solved")
	}
}

func BenchmarkAiurScsSolveHint(b *testing.B) {
	field := func(x int64) *big.Int { return new(fr.Element).SetInt64(x).BigInt(new(big.Int)) }
	in := []*big.Int{field(15 | 4<<4 | (-4+128)<<8), field(3), field(5), field(-1), field(0), field(7), field(2), field(0)}
	in[4], _ = aiurScsSolveInverse(in[0].Uint64(), in[1], in[2], in[3])
	res := []*big.Int{new(big.Int)}
	for i := 0; i < b.N; i++ {
		if err := aiurScsSolveHint(nil, in, res); err != nil {
			b.Fatal(err)
		}
	}
}

// aiurScsReference is the non-file part of the loaded circuit: the same
// inputs, PairingCheck on the outputs and the commitment over the file's
// commit list, with an empty callback.
type aiurScsReference struct {
	Public  []frontend.Variable `gnark:",public"`
	Cells   []frontend.Variable
	Scs     *aiurScs     `gnark:"-"`
	Pairing *aiurPairing `gnark:"-"`
}

func (c *aiurScsReference) Define(api frontend.API) error {
	s := c.Scs
	v := append(append([]frontend.Variable{}, c.Public...), c.Cells...)
	outputs := make([]frontend.Variable, len(s.Outputs))
	for i, x := range s.Outputs {
		outputs[i] = v[x]
	}
	if err := c.Pairing.constrain(api, outputs); err != nil {
		return err
	}
	committed := make([]frontend.Variable, len(s.Commits))
	for i, x := range s.Commits {
		committed[i] = v[x]
	}
	multicommit.WithCommitment(api, func(frontend.API, frontend.Variable) error { return nil }, committed...)
	return nil
}

type aiurScsRoundTrip struct {
	Constraints, Gates, Pre, Prefix, Suffix, Commits, RangeCommits int
	Public, Secret                                                 int
}

// checkAiurScsRoundTrip compares a compiled loader circuit with the file and
// with the compiled reference:
//
//	[file gates 0..pre) [reference 0..P) [file gates pre..) [reference P..)
//
// where P ends at the reference's commitment row (the file callback runs
// right after it). File blocks must match gate for gate (wires through the
// VID map, coefficients as field elements); reference blocks match up to a
// bijective renaming of internal VIDs, with input VIDs fixed.
func checkAiurScsRoundTrip(s *aiurScs, vids []uint32, real, ref *csbn254.SparseR1CS) (aiurScsRoundTrip, error) {
	var rt aiurScsRoundTrip
	rc, fc := real.GetSparseR1Cs(), ref.GetSparseR1Cs()
	rt.Constraints, rt.Gates, rt.Pre = len(rc), s.Gates, s.Pre
	rt.Public, rt.Secret = real.GetNbPublicVariables(), real.GetNbSecretVariables()
	if rt.Public != s.Publics || rt.Secret != s.Cells-s.Publics || ref.GetNbPublicVariables() != rt.Public || ref.GetNbSecretVariables() != rt.Secret {
		return rt, fmt.Errorf("input counts differ: %d public, %d secret", rt.Public, rt.Secret)
	}
	if len(rc) != s.Gates+len(fc) {
		return rt, fmt.Errorf("%d constraints, expected %d file gates + %d reference", len(rc), s.Gates, len(fc))
	}
	rcm, fcm := real.GetCommitments().(constraint.PlonkCommitments), ref.GetCommitments().(constraint.PlonkCommitments)
	if len(rcm) != 1 || len(fcm) != 1 {
		return rt, fmt.Errorf("expected one commitment, got %d and %d", len(rcm), len(fcm))
	}
	prefix := fcm[0].CommitmentIndex + 1
	rt.Prefix, rt.Suffix = prefix, len(fc)-prefix
	if rcm[0].CommitmentIndex != s.Pre+prefix-1 {
		return rt, fmt.Errorf("commitment row %d, expected %d", rcm[0].CommitmentIndex, s.Pre+prefix-1)
	}
	coeff := func(cs *csbn254.SparseR1CS, id uint32) fr.Element { return cs.Coefficients[id] }
	for i := 0; i < s.Gates; i++ {
		k := i
		if i >= s.Pre {
			k = i + prefix
		}
		g, c := s.gate(i), rc[k]
		for _, w := range []uint32{g.A, g.B, g.C} {
			if vids[w] == math.MaxUint32 {
				return rt, fmt.Errorf("gate %d: wire %d was never created", i, w)
			}
		}
		if c.XA != vids[g.A] || c.XB != vids[g.B] || c.XC != vids[g.C] || c.Commitment != constraint.NOT {
			return rt, fmt.Errorf("gate %d: compiled wires %d %d %d differ", i, c.XA, c.XB, c.XC)
		}
		var want [5]fr.Element
		al, be, om := new(fr.Element).SetBigInt(&s.Coeffs[g.Al]), new(fr.Element).SetBigInt(&s.Coeffs[g.Be]), new(fr.Element).SetBigInt(&s.Coeffs[g.Om])
		if g.Sel&1 != 0 {
			want[0] = *al
		}
		if g.Sel&2 != 0 {
			want[1] = *be
		}
		if g.Sel&4 != 0 {
			want[2] = *om
		}
		if g.Sel&8 != 0 {
			want[3].Mul(al, be)
		}
		want[4].SetInt64(int64(g.QC))
		got := [5]fr.Element{coeff(real, c.QL), coeff(real, c.QR), coeff(real, c.QO), coeff(real, c.QM), coeff(real, c.QC)}
		if got != want {
			return rt, fmt.Errorf("gate %d: compiled coefficients differ", i)
		}
	}
	inputs := uint32(s.Cells)
	forward, backward := map[uint32]uint32{}, map[uint32]uint32{}
	rename := func(a, b uint32) bool {
		if a < inputs || b < inputs {
			return a == b
		}
		if x, ok := forward[a]; ok {
			return x == b
		}
		if _, ok := backward[b]; ok {
			return false
		}
		forward[a], backward[b] = b, a
		return true
	}
	for j := range fc {
		k := s.Pre + j
		if j >= prefix {
			k = s.Gates + j
		}
		a, b := rc[k], fc[j]
		if !rename(a.XA, b.XA) || !rename(a.XB, b.XB) || !rename(a.XC, b.XC) || a.Commitment != b.Commitment ||
			coeff(real, a.QL) != coeff(ref, b.QL) || coeff(real, a.QR) != coeff(ref, b.QR) || coeff(real, a.QO) != coeff(ref, b.QO) ||
			coeff(real, a.QM) != coeff(ref, b.QM) || coeff(real, a.QC) != coeff(ref, b.QC) {
			return rt, fmt.Errorf("reference constraint %d (compiled %d) differs", j, k)
		}
	}
	// Committed rows: the file's commit list in order, then only wires that
	// are not file wires (the emulated range checks).
	file := make(map[uint32]bool, len(vids))
	for _, id := range vids {
		if id != math.MaxUint32 {
			file[id] = true
		}
	}
	committed := rcm[0].Committed
	if len(committed) < len(s.Commits) {
		return rt, fmt.Errorf("commitment covers %d wires, fewer than the file's %d", len(committed), len(s.Commits))
	}
	for i, row := range committed {
		xa := rc[row].XA
		if i < len(s.Commits) {
			if xa != vids[s.Commits[i]] {
				return rt, fmt.Errorf("committed row %d is not file commit %d", row, i)
			}
		} else if file[xa] {
			return rt, fmt.Errorf("committed row %d commits file wire VID %d outside the commit list", row, xa)
		}
	}
	rt.Commits, rt.RangeCommits = len(s.Commits), len(committed)-len(s.Commits)
	return rt, nil
}

func aiurScsEnv(t *testing.T, name string) string {
	v := os.Getenv(name)
	if v == "" {
		t.Skipf("set %s", name)
	}
	return v
}

func logPhase(t *testing.T, name string, start time.Time) {
	t.Logf("phase %s seconds %.3f", name, time.Since(start).Seconds())
}

// TestAiurScsTerminal loads a Lean-exported terminal SCS, compiles it,
// checks the round trip against the file and the reference, and with a
// witness and SRS sets up, proves (CUDA when built with it), verifies,
// refuses a changed statement and writes the verifier artifacts.
//
//	IX_AIUR_SCS_FILE, IX_AIUR_SCS_SHA256: the file and its pin
//	IX_AIUR_SCS_PAIRING, IX_AIUR_SCS_PAIRING_SHA256: the pairing configuration
//	IX_AIUR_SCS_WITNESS: gnark binary witness (publics, then input wires)
//	IX_AIUR_SCS_SRS, IX_AIUR_SCS_SRS_BLAKE3, IX_AIUR_SCS_LAGRANGE, IX_AIUR_SCS_LAGRANGE_SHA256
//	IX_AIUR_SCS_OUT: output directory; IX_AIUR_SCS_CUDA=1: CUDA prover
func TestAiurScsTerminal(t *testing.T) {
	path := aiurScsEnv(t, "IX_AIUR_SCS_FILE")
	start := time.Now()
	s, err := readAiurScs(path, os.Getenv("IX_AIUR_SCS_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	pairing, err := readAiurScsPairing(os.Getenv("IX_AIUR_SCS_PAIRING"), os.Getenv("IX_AIUR_SCS_PAIRING_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	logPhase(t, "read", start)
	t.Logf("file: %d publics, %d wires, %d gates (%d pre), %d commits, %d cells, %d coefficients", s.Publics, s.Wires, s.Gates, s.Pre, len(s.Commits), s.Cells, len(s.Coeffs))
	start = time.Now()
	circuit := newAiurScsCircuit(s, pairing)
	circuit.VIDs = make([]uint32, s.Wires)
	for i := range circuit.VIDs {
		circuit.VIDs[i] = math.MaxUint32
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, circuit)
	if err != nil {
		t.Fatal(err)
	}
	logPhase(t, "compile", start)
	start = time.Now()
	ref, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &aiurScsReference{
		Public: make([]frontend.Variable, s.Publics), Cells: make([]frontend.Variable, s.Cells-s.Publics), Scs: s, Pairing: pairing,
	})
	if err != nil {
		t.Fatal(err)
	}
	logPhase(t, "compile_reference", start)
	start = time.Now()
	rt, err := checkAiurScsRoundTrip(s, circuit.VIDs, ccs.(*csbn254.SparseR1CS), ref.(*csbn254.SparseR1CS))
	if err != nil {
		t.Fatal(err)
	}
	logPhase(t, "round_trip", start)
	domain := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables()))
	t.Logf("round trip: %+v, domain %d", rt, domain)
	ref = nil
	out := os.Getenv("IX_AIUR_SCS_OUT")
	summary := map[string]any{"format": "ix-aiur-scs-terminal-run-v1", "scs_sha256": os.Getenv("IX_AIUR_SCS_SHA256"),
		"pairing_sha256": os.Getenv("IX_AIUR_SCS_PAIRING_SHA256"), "round_trip": rt, "constraints": ccs.GetNbConstraints(), "domain": domain}
	writeSummary := func() {
		if out == "" {
			return
		}
		data, _ := json.MarshalIndent(summary, "", "  ")
		if err := os.WriteFile(filepath.Join(out, "summary.json"), data, 0o644); err != nil {
			t.Error(err)
		}
	}
	defer writeSummary()
	witnessPath := os.Getenv("IX_AIUR_SCS_WITNESS")
	if witnessPath == "" {
		return
	}
	data, err := os.ReadFile(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	w, err := decodeAiurWitness(data, s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	start = time.Now()
	srs, err := readSRS(aiurScsEnv(t, "IX_AIUR_SCS_SRS"), os.Getenv("IX_AIUR_SCS_SRS_BLAKE3"), domain)
	if err != nil {
		t.Fatal(err)
	}
	lagrange, err := loadLagrange(srs, domain, aiurScsEnv(t, "IX_AIUR_SCS_LAGRANGE"), os.Getenv("IX_AIUR_SCS_LAGRANGE_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	logPhase(t, "srs", start)
	start = time.Now()
	pk, vk, err := plonk.Setup(ccs, srs, lagrange)
	if err != nil {
		t.Fatal(err)
	}
	srs, lagrange = nil, nil
	logPhase(t, "setup", start)
	summary["setup_seconds"] = time.Since(start).Seconds()
	cleanup, err := configureBackend(pk, backendConfig{CUDA: os.Getenv("IX_AIUR_SCS_CUDA") == "1", MemoryBytes: 64 << 30})
	if err != nil {
		t.Fatal(err)
	}
	defer func() {
		if err := cleanup(); err != nil {
			t.Error(err)
		}
	}()
	public, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	start = time.Now()
	if _, err := ccs.Solve(w); err != nil {
		t.Fatal(err)
	}
	logPhase(t, "solve", start)
	summary["solve_seconds"] = time.Since(start).Seconds()
	var proof plonk.Proof
	for run := 0; run < 2; run++ {
		start = time.Now()
		proof, err = plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
		if err != nil {
			t.Fatal(err)
		}
		logPhase(t, fmt.Sprintf("prove_%d", run), start)
		summary[fmt.Sprintf("prove_%d_seconds", run)] = time.Since(start).Seconds()
	}
	start = time.Now()
	if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatal(err)
	}
	logPhase(t, "verify", start)
	// A changed statement: the verifier rejects the proof against it, and
	// the prover cannot prove it (the root message no longer balances).
	changed := append([]byte{}, data...)
	last := 12 + 32*1 - 1
	changed[last] ^= 1
	wrongWitness, err := decodeAiurWitness(changed, s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	wrongPublic, err := wrongWitness.Public()
	if err != nil {
		t.Fatal(err)
	}
	rejected := plonk.Verify(proof, vk, wrongPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)) != nil
	_, proveErr := plonk.Prove(ccs, pk, wrongWitness, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	summary["wrong_statement_rejected_by_verifier"] = rejected
	summary["wrong_statement_refused_by_prover"] = proveErr != nil
	if !rejected || proveErr == nil {
		t.Fatalf("changed statement: verifier rejected %v, prover refused %v", rejected, proveErr != nil)
	}
	if out == "" {
		return
	}
	var key, proofBytes bytes.Buffer
	if _, err := vk.WriteTo(&key); err != nil {
		t.Fatal(err)
	}
	if _, err := proof.WriteTo(&proofBytes); err != nil {
		t.Fatal(err)
	}
	var sol bytes.Buffer
	if err := vk.ExportSolidity(&sol); err != nil {
		t.Fatal(err)
	}
	files := map[string][]byte{"verifying-key.bin": key.Bytes(), "proof.bin": proofBytes.Bytes(),
		"proof.solidity.bin": proof.(*nativeProof).MarshalSolidity(), "PlonkVerifier.sol": sol.Bytes(), "public.bin": data[12 : 12+32*s.Publics]}
	digests := map[string]string{}
	for name, b := range files {
		if err := os.WriteFile(filepath.Join(out, name), b, 0o644); err != nil {
			t.Fatal(err)
		}
		h := sha256.Sum256(b)
		digests[name] = hex.EncodeToString(h[:])
	}
	summary["files_sha256"] = digests
}
