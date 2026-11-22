//go:build plonk || !groth16

package main

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bn254 "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	csbn254 "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

// aiurScsSynthetic is a small file whose non-input wires use every kind of
// prover hint: before the commitment a sum and a product; after it γ·c_i
// (product), d_i = γ·c_i + 7 (sum with a constant), quotients q_i = m_i/d_i
// (division batches), the running chain s_i = s_{i−1} + 2·q_i from cell z
// (chain segments), the bits of γ with booleanity gates, the general solve
// hint (a gate whose coefficient of u depends on x), a chain link that
// depends on its own chain, and a free wire. It returns the file and the cell values (publics, outputs, cells).
func aiurScsSynthetic(n int) (*aiurScsFile, []string) {
	_, _, g, _ := bn254.Generators()
	var tauG, negative nativeG1
	tauG.ScalarMultiplication(&g, big.NewInt(7))
	negative.Neg(&g)
	outputs := append(aiurG1Words(tauG), aiurG1Words(negative)...)
	f := &aiurScsFile{publics: 2, coeffs: []int64{1, -1, 3, 5, 2, -2, -3}}
	const one, minus, three, five, two, minusTwo, minusThree = 0, 1, 2, 3, 4, 5, 6
	cells := []string{"17", "29"}
	for i := range outputs {
		f.outputs = append(f.outputs, uint32(2+i))
	}
	cells = append(cells, outputs...)
	next := uint32(len(cells))
	cell := func(v int64) uint32 {
		cells = append(cells, big.NewInt(v).String())
		next++
		return next - 1
	}
	x, w, z := cell(4), cell(12), cell(9)
	c, m := make([]uint32, n), make([]uint32, n)
	for i := range c {
		c[i], m[i] = cell(int64(3+i)), cell(int64(11*i+1))
	}
	f.commits = []uint32{x, w, z}
	f.commits = append(append(f.commits, c...), m...)
	inputs := int(next)
	type hintOf struct {
		kind   uint8
		hx, hy uint32
	}
	var hints []hintOf
	wire := func(kind uint8, hx, hy uint32) uint32 {
		hints = append(hints, hintOf{kind, hx, hy})
		next++
		return next - 1
	}
	gate := func(a, b, cw uint32, sel uint8, al, be, om uint32, qc int8) uint32 {
		f.gates = append(f.gates, aiurScsGate{A: a, B: b, C: cw, Sel: sel, Al: al, Be: be, Om: om, QC: qc})
		return uint32(len(f.gates) - 1)
	}
	solved := func(at func(u uint32) uint32) uint32 {
		u := wire(aiurScsSolve, uint32(len(f.gates)), 0)
		at(u)
		return u
	}
	// Before the commitment: y = 3x, p = 5x², and w = 3x.
	y := solved(func(u uint32) uint32 { return gate(x, x, u, 1|4, three, one, minus, 0) })
	solved(func(u uint32) uint32 { return gate(x, x, u, 8|4, five, one, minus, 0) })
	gate(w, x, x, 1|2, one, minusThree, one, 0)
	gate(w, y, y, 1|2, one, minus, one, 0)
	f.pre = len(f.gates)
	gamma := wire(aiurScsChallenge, 0, 0)
	f.gamma, f.beta = gamma, gamma
	s := z
	for i := range c {
		fp := solved(func(u uint32) uint32 { return gate(gamma, c[i], u, 8|4, one, one, minus, 0) })
		d := solved(func(u uint32) uint32 { return gate(fp, fp, u, 1|4, one, one, minus, 7) })
		q := solved(func(u uint32) uint32 { return gate(u, d, m[i], 8|4, one, one, minus, 0) })
		prev := s
		s = solved(func(u uint32) uint32 { return gate(prev, q, u, 1|2|4, one, two, minus, 0) })
	}
	// A last link r = s + e whose term e = 2·s reads the chain's own tail: its
	// segment is dissolved into single hints.
	last := s
	e := solved(func(u uint32) uint32 { return gate(last, last, u, 1|4, two, one, minus, 0) })
	solved(func(u uint32) uint32 { return gate(last, e, u, 1|2|4, one, one, minus, 0) })
	for k := uint32(0); k < 4; k++ {
		b := wire(aiurScsBit, gamma, k)
		gate(b, b, b, 1|8, minus, minus, one, 0)
	}
	// 2·u − 4·x·u + s = 0: the coefficient 2 − 4x of u depends on x.
	solved(func(u uint32) uint32 { return gate(u, x, s, 1|8|4, two, minusTwo, one, 0) })
	free := wire(aiurScsFree, 0, 0)
	gate(free, x, free, 8, one, one, one, 0)
	f.wires = int(next)
	f.kinds, f.hx, f.hy = make([]uint8, f.wires), make([]uint32, f.wires), make([]uint32, f.wires)
	for i, hk := range hints {
		f.kinds[inputs+i], f.hx[inputs+i], f.hy[inputs+i] = hk.kind, hk.hx, hk.hy
	}
	return f, cells
}

func aiurScsTestPairing() *aiurPairing {
	_, _, _, h := bn254.Generators()
	var tauH nativeG2
	tauH.ScalarMultiplication(&h, big.NewInt(7))
	return &aiurPairing{Curve: "bn254", Encoding: "affine-u80-v1", G2: [][]string{aiurG2Words(h), aiurG2Words(tauH)}}
}

func TestAiurScsWiresSolve(t *testing.T) {
	batch, segment := aiurScsDivBatch, aiurScsChainSegment
	aiurScsDivBatch, aiurScsChainSegment = 2, 3
	defer func() { aiurScsDivBatch, aiurScsChainSegment = batch, segment }()
	file, cells := aiurScsSynthetic(8)
	s, err := parseAiurScs(file.bytes())
	if err != nil {
		t.Fatal(err)
	}
	pairing := aiurScsTestPairing()
	circuit := newAiurScsCircuit(s, pairing)
	circuit.VIDs = make([]uint32, s.Wires)
	for i := range circuit.VIDs {
		circuit.VIDs[i] = math.MaxUint32
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, circuit)
	if err != nil {
		t.Fatal(err)
	}
	ref, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &aiurScsReference{
		Public: make([]frontend.Variable, s.Publics), Cells: make([]frontend.Variable, s.Cells-s.Publics), Scs: s, Pairing: pairing,
	})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := checkAiurScsRoundTrip(s, circuit.VIDs, ccs.(*csbn254.SparseR1CS), ref.(*csbn254.SparseR1CS)); err != nil {
		t.Fatal(err)
	}
	used := map[string]bool{}
	for _, name := range ccs.(*csbn254.SparseR1CS).MHintsDependencies {
		used[name] = true
	}
	for _, h := range []solver.Hint{aiurScsSolveHint, aiurScsBitHint, aiurScsZeroHint, aiurScsSumHint, aiurScsProductHint, aiurScsChainHint, aiurScsDivHint} {
		if !used[solver.GetHintName(h)] {
			t.Errorf("%s is not used", solver.GetHintName(h))
		}
	}
	assign := func(values []string) *aiurScsCircuit {
		a := newAiurScsCircuit(s, pairing)
		for i, v := range values {
			if i < s.Publics {
				a.Public[i] = v
			} else {
				a.Cells[i-s.Publics] = v
			}
		}
		return a
	}
	witness, err := frontend.NewWitness(assign(cells), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ccs.Solve(witness); err != nil {
		t.Fatal(err)
	}
	// w = 3x is a gate on two cells: changing w makes the solve fail.
	bad := append([]string{}, cells...)
	bad[20+1] = "13"
	witness, err = frontend.NewWitness(assign(bad), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ccs.Solve(witness); err == nil {
		t.Fatal("a violated gate solved")
	}
}

func TestAiurScsWireHints(t *testing.T) {
	q := fr.Modulus()
	field := func(x int64) *big.Int { return new(fr.Element).SetInt64(x).BigInt(new(big.Int)) }
	out := []*big.Int{new(big.Int), new(big.Int), new(big.Int)}
	if err := aiurScsSumHint(q, []*big.Int{field(-1), field(5), field(-7)}, out[:1]); err != nil || out[0].Cmp(field(-3)) != 0 {
		t.Fatalf("sum %v %v", out[0], err)
	}
	if err := aiurScsProductHint(q, []*big.Int{field(-2), field(5), field(3)}, out[:1]); err != nil || out[0].Cmp(field(-7)) != 0 {
		t.Fatalf("product %v %v", out[0], err)
	}
	if err := aiurScsChainHint(q, []*big.Int{field(10), field(-1), field(2), field(3), field(-20)}, out); err != nil ||
		out[0].Cmp(field(11)) != 0 || out[1].Cmp(field(14)) != 0 || out[2].Cmp(field(-6)) != 0 {
		t.Fatalf("chain %v %v", out, err)
	}
	if err := aiurScsDivHint(q, []*big.Int{field(6), field(3), field(-10), field(5)}, out[:2]); err != nil ||
		out[0].Cmp(field(2)) != 0 || out[1].Cmp(field(-2)) != 0 {
		t.Fatalf("div %v %v", out[:2], err)
	}
	if err := aiurScsDivHint(q, []*big.Int{field(6), field(0)}, out[:1]); err == nil {
		t.Fatal("division by zero accepted")
	}
}

func TestAiurScsCompileAndManifest(t *testing.T) {
	file, _ := aiurScsSynthetic(2)
	dir := t.TempDir()
	scsPath, pairingPath := filepath.Join(dir, "t.ixscs"), filepath.Join(dir, "pairing.json")
	pairing, err := json.Marshal(aiurScsTestPairing())
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(scsPath, file.bytes(), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(pairingPath, pairing, 0o644); err != nil {
		t.Fatal(err)
	}
	digest := func(path string) string {
		a, err := fileHash(path)
		if err != nil {
			t.Fatal(err)
		}
		return a.SHA256
	}
	request := aiurScsCompileRequest{Scs: scsPath, ScsSHA256: digest(scsPath), Pairing: pairingPath, PairingSHA256: digest(pairingPath), Output: filepath.Join(dir, "circuit.bin")}
	info, err := compileAiurScs(&request)
	if err != nil {
		t.Fatal(err)
	}
	if info.PublicInputs != 2 || info.Commitments != 1 || info.Domain != ecc.NextPowerOfTwo(uint64(info.Constraints+2)) {
		t.Fatalf("compile info %+v", info)
	}
	wrong := request
	wrong.PairingSHA256 = request.ScsSHA256
	if _, err := compileAiurScs(&wrong); err == nil {
		t.Fatal("a pairing configuration with another digest compiled")
	}
	hex64 := strings.Repeat("ab", 32)
	m := aiurManifest{Format: aiurScsManifestFormat, ScsSHA256: hex64, PairingSHA256: hex64, SRSBLAKE3: hex64,
		Info: circuitInfo{Domain: 4, Constraints: 2, PublicInputs: 2, Commitments: 1}, Files: map[string]artifact{}}
	for _, name := range aiurScsFiles {
		m.Files[name] = artifact{SHA256: hex64, Bytes: 10}
	}
	if err := m.validate(); err != nil {
		t.Fatal(err)
	}
	for name, edit := range map[string]func(m *aiurManifest){
		"translator format":   func(m *aiurManifest) { m.Format = "ix-aiur-plonk-artifacts-v1" },
		"pairing file digest": func(m *aiurManifest) { m.Files["pairing.json"] = artifact{SHA256: strings.Repeat("cd", 32), Bytes: 10} },
		"missing inputs":      func(m *aiurManifest) { delete(m.Files, "inputs.json") },
		"short SCS digest":    func(m *aiurManifest) { m.ScsSHA256 = "ab" },
	} {
		c := m
		c.Files = map[string]artifact{}
		for k, v := range m.Files {
			c.Files[k] = v
		}
		edit(&c)
		if err := c.validate(); err == nil {
			t.Errorf("%s accepted", name)
		}
	}
}

func aiurG1Words(point nativeG1) []string {
	words := make([]string, 9)
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 80), big.NewInt(1))
	coordinates := []*big.Int{point.X.BigInt(new(big.Int)), point.Y.BigInt(new(big.Int))}
	for i, coordinate := range coordinates {
		for limb := 0; limb < 4; limb++ {
			words[4*i+limb] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(coordinate), uint(80*limb)), mask).String()
		}
	}
	words[8] = "0"
	if point.IsInfinity() {
		words[8] = "1"
	}
	return words
}

func aiurG2Words(point nativeG2) []string {
	return []string{point.X.A0.String(), point.X.A1.String(), point.Y.A0.String(), point.Y.A1.String()}
}

// aiurScsSyntheticWitness is the gnark binary witness of the synthetic
// file's input wires.
func aiurScsSyntheticWitness(t *testing.T, s *aiurScs, cells []string) []byte {
	t.Helper()
	a := newAiurScsCircuit(s, aiurScsTestPairing())
	for i, v := range cells {
		if i < s.Publics {
			a.Public[i] = v
		} else {
			a.Cells[i-s.Publics] = v
		}
	}
	w, err := frontend.NewWitness(a, ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	data, err := w.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func TestAiurScsBinaryWitnessStrictDecoding(t *testing.T) {
	file, cells := aiurScsSynthetic(2)
	s, err := parseAiurScs(file.bytes())
	if err != nil {
		t.Fatal(err)
	}
	data := aiurScsSyntheticWitness(t, s, cells)
	public, secret := s.Publics, s.Cells-s.Publics
	decoded, err := decodeAiurWitness(data, public, secret)
	if err != nil {
		t.Fatal(err)
	}
	if roundtrip, err := decoded.MarshalBinary(); err != nil || !bytes.Equal(roundtrip, data) {
		t.Fatal("binary witness round trip differs", err)
	}
	for _, index := range []int{0, 4, 8, 12} {
		bad := append([]byte(nil), data...)
		if index == 12 {
			for i := 12; i < 44; i++ {
				bad[i] = 0xff
			}
		} else {
			binary.BigEndian.PutUint32(bad[index:index+4], ^uint32(0))
		}
		if _, err := decodeAiurWitness(bad, public, secret); err == nil {
			t.Fatalf("accepted altered field/count at %d", index)
		}
	}
	for _, bad := range [][]byte{data[:len(data)-1], append(append([]byte(nil), data...), 0)} {
		if _, err := decodeAiurWitness(bad, public, secret); err == nil {
			t.Fatal("accepted wrong witness length")
		}
	}
}

// The outputs are bound to gnark's PairingCheck: other points fail to solve.
func TestAiurScsPairingBindsOutputs(t *testing.T) {
	file, cells := aiurScsSynthetic(2)
	s, err := parseAiurScs(file.bytes())
	if err != nil {
		t.Fatal(err)
	}
	ccs, _, err := compileAiurScsCircuit(s, aiurScsTestPairing())
	if err != nil {
		t.Fatal(err)
	}
	_, _, g, _ := bn254.Generators()
	var other nativeG1
	other.ScalarMultiplication(&g, big.NewInt(8))
	bad := append([]string{}, cells...)
	copy(bad[2:11], aiurG1Words(other))
	for name, values := range map[string][]string{"honest": cells, "other point": bad} {
		w, err := decodeAiurWitness(aiurScsSyntheticWitness(t, s, values), s.Publics, s.Cells-s.Publics)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := ccs.Solve(w); (err == nil) != (name == "honest") {
			t.Fatalf("%s: solve error %v", name, err)
		}
	}
}

// A development proof (known trapdoor) of the synthetic file: prove, verify,
// and reject a changed statement and an altered proof.
func TestAiurScsDevelopmentProof(t *testing.T) {
	if os.Getenv("IX_AIUR_TERMINAL_PROVE") != "1" {
		t.Skip("set IX_AIUR_TERMINAL_PROVE=1 for the development proving regression")
	}
	file, cells := aiurScsSynthetic(4)
	s, err := parseAiurScs(file.bytes())
	if err != nil {
		t.Fatal(err)
	}
	ccs, info, err := compileAiurScsCircuit(s, aiurScsTestPairing())
	if err != nil {
		t.Fatal(err)
	}
	srs, err := kzg.NewSRS(info.Domain+3, big.NewInt(42))
	if err != nil {
		t.Fatal(err)
	}
	lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:info.Domain])
	if err != nil {
		t.Fatal(err)
	}
	pk, vk, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
	if err != nil {
		t.Fatal(err)
	}
	data := aiurScsSyntheticWitness(t, s, cells)
	w, err := decodeAiurWitness(data, s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		t.Fatal(err)
	}
	expected := data[12 : 12+32*s.Publics]
	public, err := aiurPublicWitness(expected, s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatal(err)
	}
	changed := append([]byte(nil), expected...)
	changed[31] ^= 1
	changedPublic, err := aiurPublicWitness(changed, s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(proof, vk, changedPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("accepted a changed statement")
	}
	_, _, generator, _ := bn254.Generators()
	bad := proof.(*plonkbn254.Proof)
	bad.LRO[0].Add(&bad.LRO[0], &generator)
	if err := plonk.Verify(bad, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("accepted an altered proof commitment")
	}
	t.Logf("development proof: %d constraints, domain %d", info.Constraints, info.Domain)
}
