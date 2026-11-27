//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	blsfp "github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	kzgbls "github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbls "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/backend/solidity"
	csbls "github.com/consensys/gnark/constraint/bls12-381"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/zeebo/blake3"
)

func aiurG1WordsBLS(point blsG1) []string {
	words := make([]string, 11)
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 80), big.NewInt(1))
	if point.IsInfinity() {
		for i := 0; i < 10; i++ {
			words[i] = "0"
		}
		words[10] = "1"
		return words
	}
	coordinates := []*big.Int{point.X.BigInt(new(big.Int)), point.Y.BigInt(new(big.Int))}
	for i, coordinate := range coordinates {
		for limb := 0; limb < 5; limb++ {
			words[5*i+limb] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(coordinate), uint(80*limb)), mask).String()
		}
	}
	words[10] = "0"
	return words
}

func aiurFqWordsBLS(v *big.Int) []string {
	words := make([]string, 5)
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 80), big.NewInt(1))
	for limb := 0; limb < 5; limb++ {
		words[limb] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(v), uint(80*limb)), mask).String()
	}
	return words
}

func aiurG2WordsBLS(point blsG2) []string {
	return []string{point.X.A0.String(), point.X.A1.String(), point.Y.A0.String(), point.Y.A1.String()}
}

func aiurScsTestPairingBLS(tau int64) *aiurPairing {
	_, _, _, h := bls.Generators()
	var tauH blsG2
	tauH.ScalarMultiplication(&h, big.NewInt(tau))
	return &aiurPairing{
		Curve:    "bls12-381",
		Encoding: "affine-u80-v1",
		G2:       [][]string{aiurG2WordsBLS(h), aiurG2WordsBLS(tauH)},
	}
}

// aiurScsFileBLS encodes an `ix-aiur-scs-v1` file with BLS12-381 Fr coefficients.
func (f *aiurScsFile) bytesBLS() []byte {
	var b bytes.Buffer
	b.WriteString(aiurScsMagic)
	for _, x := range []uint64{
		uint64(f.publics), uint64(len(f.outputs)), uint64(f.wires), uint64(len(f.gates)), uint64(f.pre),
		uint64(len(f.commits)), uint64(f.gamma), uint64(f.beta), uint64(len(f.coeffs)), 0,
	} {
		binary.Write(&b, binary.LittleEndian, x)
	}
	binary.Write(&b, binary.LittleEndian, f.outputs)
	for _, c := range f.coeffs {
		be := new(blsfr.Element).SetInt64(c).Bytes()
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

// aiurScsSyntheticBLS mirrors aiurScsSynthetic over BLS12-381 Fr with 22
// pairing output wires (two BLS12-381 G1 points in 5x80-bit + infinity form).
func aiurScsSyntheticBLS(n int) (*aiurScsFile, []string) {
	_, _, g, _ := bls.Generators()
	var tauG, negative blsG1
	tauG.ScalarMultiplication(&g, big.NewInt(7))
	negative.Neg(&g)
	outputs := append(aiurG1WordsBLS(tauG), aiurG1WordsBLS(negative)...)
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
	last := s
	e := solved(func(u uint32) uint32 { return gate(last, last, u, 1|4, two, one, minus, 0) })
	solved(func(u uint32) uint32 { return gate(last, e, u, 1|2|4, one, one, minus, 0) })
	for k := uint32(0); k < 4; k++ {
		b := wire(aiurScsBit, gamma, k)
		gate(b, b, b, 1|8, minus, minus, one, 0)
	}
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

func aiurScsSyntheticWitnessBLS(t *testing.T, s *aiurScs, pairing *aiurPairing, cells []string) []byte {
	t.Helper()
	a := newAiurScsCircuit(s, pairing)
	for i, v := range cells {
		if i < s.Publics {
			a.Public[i] = v
		} else {
			a.Cells[i-s.Publics] = v
		}
	}
	w, err := frontend.NewWitness(a, ecc.BLS12_381.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	data, err := w.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	return data
}

type blsPairingOnlyCircuit struct {
	Outputs [aiurTerminalOutputsBLS]frontend.Variable
	Pairing *aiurPairing `gnark:"-"`
}

func (c *blsPairingOnlyCircuit) Define(api frontend.API) error {
	return c.Pairing.constrain(api, c.Outputs[:])
}

func TestAiurPlonkBLSPairingCheckAndNegativeControls(t *testing.T) {
	pairing := aiurScsTestPairingBLS(7)
	ccs, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &blsPairingOnlyCircuit{Pairing: pairing})
	if err != nil {
		t.Fatalf("compile BLS12-381 pairing gadget: %v", err)
	}
	t.Logf("BLS12-381 Aiur PairingCheck gadget: %d SCS constraints", ccs.GetNbConstraints())

	solveOutputs := func(words []string) error {
		var assign blsPairingOnlyCircuit
		assign.Pairing = pairing
		for i, w := range words {
			assign.Outputs[i] = w
		}
		w, err := frontend.NewWitness(&assign, ecc.BLS12_381.ScalarField())
		if err != nil {
			return err
		}
		_, err = ccs.Solve(w)
		return err
	}

	_, _, g, _ := bls.Generators()
	var tauG, negG, wrongG blsG1
	tauG.ScalarMultiplication(&g, big.NewInt(7))
	negG.Neg(&g)
	wrongG.ScalarMultiplication(&g, big.NewInt(8))

	// Valid finite pairing pair: e(7*G1, H) * e(-G1, 7*H) = 1.
	honest := append(aiurG1WordsBLS(tauG), aiurG1WordsBLS(negG)...)
	if err := solveOutputs(honest); err != nil {
		t.Fatalf("honest BLS12-381 pairing failed: %v", err)
	}

	// Valid infinity pair: e(O, H) * e(O, 7*H) = 1.
	infinityPair := append(aiurG1WordsBLS(blsG1{}), aiurG1WordsBLS(blsG1{})...)
	if err := solveOutputs(infinityPair); err != nil {
		t.Fatalf("infinity BLS12-381 pairing failed: %v", err)
	}

	// Negative control 1: tampered G1 output (8*G1 instead of 7*G1).
	tamperedG1 := append(aiurG1WordsBLS(wrongG), aiurG1WordsBLS(negG)...)
	if err := solveOutputs(tamperedG1); err == nil {
		t.Fatal("accepted tampered BLS12-381 G1 output point")
	}

	// Negative control 2: tampered single G1 limb (+1 on x limb 0).
	tamperedLimb := append([]string{}, honest...)
	v, _ := new(big.Int).SetString(tamperedLimb[0], 10)
	tamperedLimb[0] = new(big.Int).Add(v, big.NewInt(1)).String()
	if err := solveOutputs(tamperedLimb); err == nil {
		t.Fatal("accepted tampered BLS12-381 G1 output limb")
	}

	// Negative control 3: wrong G2 anchor (compiled with tau=8, witness for tau=7).
	wrongAnchorCCS, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &blsPairingOnlyCircuit{Pairing: aiurScsTestPairingBLS(8)})
	if err != nil {
		t.Fatal(err)
	}
	var wrongAnchorAssign blsPairingOnlyCircuit
	for i, w := range honest {
		wrongAnchorAssign.Outputs[i] = w
	}
	wWrongAnchor, err := frontend.NewWitness(&wrongAnchorAssign, ecc.BLS12_381.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if _, err := wrongAnchorCCS.Solve(wWrongAnchor); err == nil {
		t.Fatal("accepted witness against wrong BLS12-381 G2 anchor")
	}

	// Negative control 4: non-canonical Fq coordinate (x == Fq modulus, still < 2^381).
	nonCanon := append([]string{}, infinityPair...)
	copy(nonCanon[0:5], aiurFqWordsBLS(blsfp.Modulus()))
	nonCanon[10] = "0"
	if err := solveOutputs(nonCanon); err == nil {
		t.Fatal("accepted non-canonical BLS12-381 Fq coordinate (x == p)")
	}

	// Negative control 5: top limb overflow (2^61 in limb 4).
	topOverflow := append([]string{}, honest...)
	topOverflow[4] = new(big.Int).Lsh(big.NewInt(1), 61).String()
	if err := solveOutputs(topOverflow); err == nil {
		t.Fatal("accepted BLS12-381 top limb >= 2^61")
	}

	// Negative control 6: non-subgroup torsion point (0, 2) on y^2 = x^3 + 4.
	var torsion blsG1
	torsion.Y.SetUint64(2)
	if !torsion.IsOnCurve() || torsion.IsInSubGroup() {
		t.Fatal("expected (0, 2) to be on-curve but off-subgroup")
	}
	torsionOut := append(aiurG1WordsBLS(torsion), aiurG1WordsBLS(blsG1{})...)
	if err := solveOutputs(torsionOut); err == nil {
		t.Fatal("accepted off-subgroup BLS12-381 G1 torsion point (0, 2)")
	}

	// Negative control 7: non-boolean infinity flag.
	badInfFlag := append([]string{}, infinityPair...)
	badInfFlag[10] = "2"
	if err := solveOutputs(badInfFlag); err == nil {
		t.Fatal("accepted non-boolean infinity flag")
	}

	// Negative control 8: nonzero coordinate with infinity flag = 1.
	badInfCoord := append([]string{}, infinityPair...)
	badInfCoord[0] = "1"
	if err := solveOutputs(badInfCoord); err == nil {
		t.Fatal("accepted nonzero coordinate with infinity flag = 1")
	}

	// Negative control 9: zero coordinates (0, 0) with infinity flag = 0.
	zeroNotInf := append([]string{}, infinityPair...)
	zeroNotInf[10] = "0"
	if err := solveOutputs(zeroNotInf); err == nil {
		t.Fatal("accepted zero coordinates with infinity flag = 0")
	}

	// Negative control 10: invalid BLS12-381 pairing JSON configs.
	_, _, _, h := bls.Generators()
	var badG2 blsG2
	badG2.X.A0.SetUint64(1)
	badG2.Y.A0.SetUint64(2)
	for name, cfg := range map[string]*aiurPairing{
		"wrong encoding":  {Curve: "bls12-381", Encoding: "affine-u64-v1", G2: pairing.G2},
		"identity G2":     {Curve: "bls12-381", Encoding: "affine-u80-v1", G2: [][]string{aiurG2WordsBLS(blsG2{}), aiurG2WordsBLS(h)}},
		"off-curve G2":    {Curve: "bls12-381", Encoding: "affine-u80-v1", G2: [][]string{aiurG2WordsBLS(badG2), aiurG2WordsBLS(h)}},
		"noncanonical Fq": {Curve: "bls12-381", Encoding: "affine-u80-v1", G2: [][]string{{blsfp.Modulus().String(), "0", "0", "0"}, aiurG2WordsBLS(h)}},
		"leading zero":    {Curve: "bls12-381", Encoding: "affine-u80-v1", G2: [][]string{{"0" + pairing.G2[0][0], pairing.G2[0][1], pairing.G2[0][2], pairing.G2[0][3]}, pairing.G2[1]}},
		"wrong g2 count":  {Curve: "bls12-381", Encoding: "affine-u80-v1", G2: [][]string{pairing.G2[0]}},
	} {
		if err := cfg.validate(); err == nil {
			t.Errorf("anchorsBLS accepted invalid config %q", name)
		}
	}
}

func TestAiurPlonkBLSScsParseHintsAndWires(t *testing.T) {
	batch, segment := aiurScsDivBatch, aiurScsChainSegment
	aiurScsDivBatch, aiurScsChainSegment = 2, 3
	defer func() { aiurScsDivBatch, aiurScsChainSegment = batch, segment }()

	// Verify wire hints directly over BLS12-381 Fr, including values > BN254 Fr modulus.
	q := blsfr.Modulus()
	field := func(x int64) *big.Int { return new(blsfr.Element).SetInt64(x).BigInt(new(big.Int)) }
	minusOne := field(-1)
	if minusOne.Cmp(scalarModulus()) <= 0 {
		t.Fatal("expected BLS12-381 -1 to exceed BN254 Fr modulus")
	}
	out := []*big.Int{new(big.Int), new(big.Int)}
	if err := aiurScsDivHint(q, []*big.Int{field(6), field(3), field(-10), field(5)}, out); err != nil ||
		out[0].Cmp(field(2)) != 0 || out[1].Cmp(field(-2)) != 0 {
		t.Fatalf("BLS12-381 div hint: %v %v", out, err)
	}
	if err := aiurScsDivHint(q, []*big.Int{field(6), field(0)}, out[:1]); err == nil {
		t.Fatal("BLS12-381 div hint accepted zero denominator")
	}
	code := int64(15 | 4<<4 | (-4+128)<<8)
	in := []*big.Int{field(code), field(3), field(5), field(-1), field(0), field(7), field(2), field(0)}
	if inv, ok := aiurScsSolveInverseFor[blsfr.Element, *blsfr.Element](uint64(code), in[1], in[2], in[3]); !ok {
		t.Fatal("expected constant inverse for BLS12-381 solve hint")
	} else {
		in[4] = inv
	}
	if err := aiurScsSolveHint(q, in, out[:1]); err != nil || out[0].Cmp(field(237)) != 0 {
		t.Fatalf("BLS12-381 solve hint c: %v %v", out[0], err)
	}

	// Synthetic BLS12-381 SCS file: -1 mod r_bls exceeds BN254 modulus, so BN254 parser MUST reject it.
	file, cells := aiurScsSyntheticBLS(6)
	raw := file.bytesBLS()
	if _, err := parseAiurScs(raw); err == nil {
		t.Fatal("BN254 parseAiurScs accepted BLS12-381 SCS file")
	}
	s, err := parseAiurScsFor(raw, ecc.BLS12_381)
	if err != nil {
		t.Fatalf("parseAiurScsFor BLS12-381: %v", err)
	}
	pairing := aiurScsTestPairingBLS(7)
	ccs, info, err := compileAiurScsCircuit(s, pairing)
	if err != nil {
		t.Fatalf("compileAiurScsCircuit BLS12-381: %v", err)
	}
	t.Logf("synthetic BLS12-381 SCS: constraints=%d domain=%d publics=%d commitments=%d",
		info.Constraints, info.Domain, info.PublicInputs, info.Commitments)

	spr, ok := ccs.(*csbls.SparseR1CS)
	if !ok {
		t.Fatalf("expected *csbls.SparseR1CS, got %T", ccs)
	}
	used := map[string]bool{}
	for _, name := range spr.MHintsDependencies {
		used[name] = true
	}
	for _, h := range []solver.Hint{aiurScsSolveHint, aiurScsBitHint, aiurScsZeroHint, aiurScsSumHint, aiurScsProductHint, aiurScsChainHint, aiurScsDivHint} {
		if !used[solver.GetHintName(h)] {
			t.Errorf("%s is not used in BLS12-381 SCS circuit", solver.GetHintName(h))
		}
	}

	witnessBytes := aiurScsSyntheticWitnessBLS(t, s, pairing, cells)
	w, err := decodeAiurWitnessFor(ecc.BLS12_381, witnessBytes, s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ccs.Solve(w); err != nil {
		t.Fatalf("BLS12-381 SCS honest witness failed to solve: %v", err)
	}

	// Violated gate (w = 3*x changed from 12 to 13) must fail to solve.
	bad := append([]string{}, cells...)
	bad[2+aiurTerminalOutputsBLS+1] = "13"
	badW, err := decodeAiurWitnessFor(ecc.BLS12_381, aiurScsSyntheticWitnessBLS(t, s, pairing, bad), s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ccs.Solve(badW); err == nil {
		t.Fatal("BLS12-381 SCS solved with violated gate")
	}
}

func writeDevBLSSRSExport(t *testing.T, dir string, domain uint64) (path, receipt string, srs *kzgbls.SRS) {
	t.Helper()
	dev, err := kzgbls.NewSRS(domain+3, big.NewInt(42))
	if err != nil {
		t.Fatal(err)
	}
	var source bytes.Buffer
	var header [88]byte
	copy(header[:8], blsSRSMagic)
	id := blake3.Sum256([]byte("aiur-plonk-bls-test-srs"))
	copy(header[8:40], id[:])
	binary.LittleEndian.PutUint64(header[40:48], domain+2)
	copy(header[48:80], id[:])
	binary.LittleEndian.PutUint64(header[80:88], domain+3)
	source.Write(header[:])
	for _, point := range dev.Vk.G2 {
		encoded := point.Bytes()
		source.Write(encoded[:])
	}
	if err := writeAffinePointsBLS(&source, dev.Pk.G1); err != nil {
		t.Fatal(err)
	}
	sum := blake3.Sum256(source.Bytes())
	srsPath := filepath.Join(dir, "bls-srs.bin")
	if err := os.WriteFile(srsPath, source.Bytes(), 0o600); err != nil {
		t.Fatal(err)
	}
	return srsPath, hex.EncodeToString(sum[:]), dev
}

func TestAiurPlonkBLSEndToEndPrepareProveVerify(t *testing.T) {
	dir := t.TempDir()
	file, cells := aiurScsSyntheticBLS(4)
	scsPath := filepath.Join(dir, "terminal.ixscs")
	pairingPath := filepath.Join(dir, "pairing.json")
	circuitPath := filepath.Join(dir, "compiled.bin")
	lagrangePath := filepath.Join(dir, "lagrange.bin")
	preparedDir := filepath.Join(dir, "prepared")

	if err := os.WriteFile(scsPath, file.bytesBLS(), 0o644); err != nil {
		t.Fatal(err)
	}
	pairing := aiurScsTestPairingBLS(7)
	pairingJSON, err := json.Marshal(pairing)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(pairingPath, pairingJSON, 0o644); err != nil {
		t.Fatal(err)
	}
	hashOf := func(p string) artifact {
		a, err := fileHash(p)
		if err != nil {
			t.Fatal(err)
		}
		return a
	}
	scsHash := hashOf(scsPath)
	pairingHash := hashOf(pairingPath)

	// 1. Compile SCS + BLS12-381 PairingCheck.
	t0 := time.Now()
	info, err := compileAiurScs(&aiurScsCompileRequest{
		Scs:           scsPath,
		ScsSHA256:     scsHash.SHA256,
		Pairing:       pairingPath,
		PairingSHA256: pairingHash.SHA256,
		Output:        circuitPath,
	})
	if err != nil {
		t.Fatalf("compileAiurScs BLS12-381: %v", err)
	}
	compileSec := time.Since(t0).Seconds()
	circuitHash := hashOf(circuitPath)

	// 2. Prepare BLS12-381 proving & verifying keys with authenticated SRS export.
	srsPath, srsReceipt, _ := writeDevBLSSRSExport(t, dir, info.Domain)
	t1 := time.Now()
	manifest, err := prepareAiurScs(&aiurScsPreparation{
		Scs:           scsPath,
		ScsSHA256:     scsHash.SHA256,
		Pairing:       pairingPath,
		PairingSHA256: pairingHash.SHA256,
		Circuit:       circuitPath,
		CircuitHash:   circuitHash,
		Info:          info,
		SRS:           srsPath,
		SRSBLAKE3:     srsReceipt,
		Lagrange:      lagrangePath,
		Output:        preparedDir,
	})
	if err != nil {
		t.Fatalf("prepareAiurScs BLS12-381: %v", err)
	}
	prepareSec := time.Since(t1).Seconds()
	manifestBytes, err := json.Marshal(manifest)
	if err != nil {
		t.Fatal(err)
	}

	// 3. Reject CUDA on BLS12-381.
	if _, err := openAiurProver(preparedDir, manifestBytes, backendConfig{CUDA: true}); err == nil {
		t.Fatal("openAiurProver accepted CUDA for BLS12-381")
	}

	// 4. Open BLS12-381 prover and prove honest witness.
	prover, err := openAiurProver(preparedDir, manifestBytes, backendConfig{})
	if err != nil {
		t.Fatalf("openAiurProver BLS12-381: %v", err)
	}
	defer func() {
		if err := prover.close(); err != nil {
			t.Errorf("close prover: %v", err)
		}
	}()

	s, err := parseAiurScsFor(file.bytesBLS(), ecc.BLS12_381)
	if err != nil {
		t.Fatal(err)
	}
	witnessBytes := aiurScsSyntheticWitnessBLS(t, s, pairing, cells)
	expectedPublic := witnessBytes[12 : 12+32*s.Publics]

	t2 := time.Now()
	proofBytes, solidityBytes, err := prover.prove(witnessBytes, expectedPublic)
	if err != nil {
		t.Fatalf("prover.prove BLS12-381: %v", err)
	}
	proveSec := time.Since(t2).Seconds()
	if len(solidityBytes) == 0 {
		t.Fatal("empty BLS12-381 Solidity proof")
	}

	// 5. Standalone verifyAiurProofBLS against pinned VK digest and BLS12-381 anchors.
	vkBytes, err := os.ReadFile(filepath.Join(preparedDir, "verifying-key.bin"))
	if err != nil {
		t.Fatal(err)
	}
	vkDigest := sha256.Sum256(vkBytes)
	vk := new(plonkbls.VerifyingKey)
	if _, err := vk.ReadFrom(bytes.NewReader(vkBytes)); err != nil {
		t.Fatal(err)
	}
	anchors := encodeAnchorsBLS(vk)

	t3 := time.Now()
	if err := verifyAiurProofBLS(vkBytes, vkDigest[:], proofBytes, expectedPublic, anchors); err != nil {
		t.Fatalf("verifyAiurProofBLS failed: %v", err)
	}
	verifySec := time.Since(t3).Seconds()
	t.Logf("BLS12-381 Aiur PLONK E2E: constraints=%d domain=%d compile=%.3fs prepare=%.3fs prove=%.3fs verify=%.3fs proof=%dB solidity=%dB",
		info.Constraints, info.Domain, compileSec, prepareSec, proveSec, verifySec, len(proofBytes), len(solidityBytes))

	// Negative control A: tampered public input rejected by verifier.
	badPublic := append([]byte(nil), expectedPublic...)
	badPublic[31] ^= 1
	if err := verifyAiurProofBLS(vkBytes, vkDigest[:], proofBytes, badPublic, anchors); err == nil {
		t.Fatal("verifyAiurProofBLS accepted tampered public input")
	}

	// Negative control B: tampered public input refused by prover.
	if _, _, err := prover.prove(witnessBytes, badPublic); err == nil {
		t.Fatal("prover.prove accepted witness differing from expected public input")
	}

	// Negative control C: wrong SRS anchors rejected by verifier.
	badAnchors := append([]byte(nil), anchors...)
	badAnchors[0] ^= 1
	if err := verifyAiurProofBLS(vkBytes, vkDigest[:], proofBytes, expectedPublic, badAnchors); err == nil {
		t.Fatal("verifyAiurProofBLS accepted tampered SRS anchors")
	}

	// Negative control D: tampered proof byte rejected by verifier.
	badProof := append([]byte(nil), proofBytes...)
	badProof[len(badProof)-1] ^= 1
	if err := verifyAiurProofBLS(vkBytes, vkDigest[:], badProof, expectedPublic, anchors); err == nil {
		t.Fatal("verifyAiurProofBLS accepted tampered proof byte")
	}

	// Negative control E: truncated proof rejected.
	if err := verifyAiurProofBLS(vkBytes, vkDigest[:], proofBytes[:len(proofBytes)-1], expectedPublic, anchors); err == nil {
		t.Fatal("verifyAiurProofBLS accepted truncated proof")
	}

	// Negative control F: BN254 verifier rejects BLS12-381 key/proof.
	if err := verifyAiurProof(vkBytes, vkDigest[:], proofBytes, expectedPublic, anchors); err == nil {
		t.Fatal("BN254 verifyAiurProof accepted BLS12-381 proof")
	}

	// Negative control G: tampered G1 output limb in witness rejected by prover.
	badCells := append([]string{}, cells...)
	v0, _ := new(big.Int).SetString(badCells[2], 10)
	badCells[2] = new(big.Int).Add(v0, big.NewInt(1)).String()
	badWitness := aiurScsSyntheticWitnessBLS(t, s, pairing, badCells)
	if _, _, err := prover.prove(badWitness, expectedPublic); err == nil {
		t.Fatal("prover.prove accepted tampered BLS12-381 G1 output limb")
	}
}

// aiurScsRawBLSCircuit is a test-only wrapper for verifying a real Lean
// `plonk_export --bls12-381` SCS file whose entry does not emit 22 pairing
// outputs (e.g. a compiled KzgAlgebraPure program). Production circuits always
// use aiurScsCircuit with a validated aiurPairing.
type aiurScsRawBLSCircuit struct {
	Public []frontend.Variable `gnark:",public"`
	Cells  []frontend.Variable
	Scs    *aiurScs `gnark:"-"`
}

func (c *aiurScsRawBLSCircuit) Define(api frontend.API) error {
	return defineAiurScsGates(api, c.Scs, ecc.BLS12_381, c.Public, c.Cells, nil, nil)
}

// TestAiurPlonkBLSRealLeanExportE2E loads a real `plonk_export --bls12-381`
// `.ixscs` file and its binary witness (`IX_AIUR_BLS_SCS_FILE`,
// `IX_AIUR_BLS_WITNESS`), compiles it in gnark over BLS12-381 Fr, runs
// plonk.Setup, plonk.Prove, plonk.Verify, and asserts negative controls.
func TestAiurPlonkBLSRealLeanExportE2E(t *testing.T) {
	scsPath := aiurScsEnv(t, "IX_AIUR_BLS_SCS_FILE")
	witnessPath := aiurScsEnv(t, "IX_AIUR_BLS_WITNESS")

	rawScs, err := os.ReadFile(scsPath)
	if err != nil {
		t.Fatal(err)
	}
	s, err := parseAiurScsWithOutputs(rawScs, ecc.BLS12_381, -1)
	if err != nil {
		t.Fatalf("parse real BLS12-381 SCS: %v", err)
	}
	t.Logf("real Lean BLS12-381 SCS: publics=%d outputs=%d wires=%d cells=%d gates=%d (pre=%d) commits=%d coeffs=%d tables=%d",
		s.Publics, len(s.Outputs), s.Wires, s.Cells, s.Gates, s.Pre, len(s.Commits), len(s.Coeffs), len(s.Tables))

	t0 := time.Now()
	ccs, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &aiurScsRawBLSCircuit{
		Public: make([]frontend.Variable, s.Publics),
		Cells:  make([]frontend.Variable, s.Cells-s.Publics),
		Scs:    s,
	})
	if err != nil {
		t.Fatalf("compile real Lean BLS12-381 SCS: %v", err)
	}
	compileSec := time.Since(t0).Seconds()
	domain := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables()))

	witnessBytes, err := os.ReadFile(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	w, err := decodeAiurWitnessFor(ecc.BLS12_381, witnessBytes, s.Publics, s.Cells-s.Publics)
	if err != nil {
		t.Fatalf("decode BLS12-381 witness: %v", err)
	}

	t1 := time.Now()
	if _, err := ccs.Solve(w); err != nil {
		t.Fatalf("solve real Lean BLS12-381 SCS: %v", err)
	}
	solveSec := time.Since(t1).Seconds()

	t2 := time.Now()
	srs, err := kzgbls.NewSRS(domain+3, big.NewInt(42))
	if err != nil {
		t.Fatal(err)
	}
	lagrange, err := kzgbls.ToLagrangeG1(srs.Pk.G1[:domain])
	if err != nil {
		t.Fatal(err)
	}
	pk, vk, err := plonk.Setup(ccs, srs, &kzgbls.SRS{Pk: kzgbls.ProvingKey{G1: lagrange}, Vk: srs.Vk})
	if err != nil {
		t.Fatalf("plonk.Setup BLS12-381: %v", err)
	}
	setupSec := time.Since(t2).Seconds()

	t3 := time.Now()
	proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		t.Fatalf("plonk.Prove BLS12-381: %v", err)
	}
	proveSec := time.Since(t3).Seconds()

	expectedPublic := witnessBytes[12 : 12+32*s.Publics]
	pubWitness, err := aiurPublicWitnessFor(ecc.BLS12_381, expectedPublic, s.Publics)
	if err != nil {
		t.Fatal(err)
	}
	t4 := time.Now()
	if err := plonk.Verify(proof, vk, pubWitness, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatalf("plonk.Verify BLS12-381: %v", err)
	}
	verifySec := time.Since(t4).Seconds()

	var vkBuf, proofBuf bytes.Buffer
	if _, err := vk.WriteTo(&vkBuf); err != nil {
		t.Fatal(err)
	}
	if _, err := proof.WriteTo(&proofBuf); err != nil {
		t.Fatal(err)
	}
	vkDigest := sha256.Sum256(vkBuf.Bytes())
	anchors := encodeAnchorsBLS(vk.(*plonkbls.VerifyingKey))
	if err := verifyAiurProofBLS(vkBuf.Bytes(), vkDigest[:], proofBuf.Bytes(), expectedPublic, anchors); err != nil {
		t.Fatalf("verifyAiurProofBLS on real Lean SCS: %v", err)
	}

	// Negative controls on the real Lean-exported BLS12-381 SCS proof.
	badPublic := append([]byte(nil), expectedPublic...)
	badPublic[31] ^= 1
	if err := verifyAiurProofBLS(vkBuf.Bytes(), vkDigest[:], proofBuf.Bytes(), badPublic, anchors); err == nil {
		t.Fatal("accepted tampered public input on real Lean BLS12-381 SCS")
	}
	badProof := append([]byte(nil), proofBuf.Bytes()...)
	badProof[len(badProof)-1] ^= 1
	if err := verifyAiurProofBLS(vkBuf.Bytes(), vkDigest[:], badProof, expectedPublic, anchors); err == nil {
		t.Fatal("accepted tampered proof byte on real Lean BLS12-381 SCS")
	}

	t.Logf("REAL LEAN plonk_export --bls12-381 -> gnark BLS12-381 PLONK PASS: constraints=%d domain=%d compile=%.3fs solve=%.3fs setup=%.3fs prove=%.3fs verify=%.3fs proof=%dB solidity=%dB",
		ccs.GetNbConstraints(), domain, compileSec, solveSec, setupSec, proveSec, verifySec,
		proofBuf.Len(), len(proof.(*plonkbls.Proof).MarshalSolidity()))
	fmt.Printf("REAL_LEAN_BLS12_381_PLONK constraints=%d domain=%d compile_s=%.3f solve_s=%.3f setup_s=%.3f prove_s=%.3f verify_s=%.3f proof_bytes=%d\n",
		ccs.GetNbConstraints(), domain, compileSec, solveSec, setupSec, proveSec, verifySec, proofBuf.Len())
}
