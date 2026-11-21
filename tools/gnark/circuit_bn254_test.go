package main

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bn254 "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bn254"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/bits"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/test"
)

type encodingCircuit struct {
	Point   sw.G1Affine
	Encoded [32]uints.U8
}

func (c *encodingCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[sw.BaseField](api)
	if err != nil {
		return err
	}
	pairing, err := sw.NewPairing(api)
	if err != nil {
		return err
	}
	pairing.AssertIsOnG1(&c.Point)
	for i, b := range pointBytes(api, u, f, &c.Point) {
		u.Bytes.AssertIsEqual(b, c.Encoded[i])
	}
	return nil
}

func TestIdentityAndCanonicalPointEncoding(t *testing.T) {
	_, _, g, _ := bn254.Generators()
	var negative bn254.G1Affine
	negative.Neg(&g)
	for _, point := range []bn254.G1Affine{{}, g, negative} {
		assignment := &encodingCircuit{Point: sw.NewG1Affine(point)}
		bytes := encodePoint(point)
		copy(assignment.Encoded[:], uints.NewU8Array(bytes[:]))
		if err := test.IsSolved(&encodingCircuit{}, assignment, ecc.BN254.ScalarField()); err != nil {
			t.Fatal(err)
		}
		assignment.Encoded[31] = uints.NewU8(bytes[31] ^ 0x80)
		if err := test.IsSolved(&encodingCircuit{}, assignment, ecc.BN254.ScalarField()); err == nil {
			t.Fatal("accepted wrong sign bit")
		}
	}
	identity := encodePoint(bn254.G1Affine{})
	alias := &encodingCircuit{Point: sw.NewG1Affine(bn254.G1Affine{})}
	copy(alias.Encoded[:], uints.NewU8Array(identity[:]))
	alias.Point.X.Limbs = make([]frontend.Variable, 4)
	modulus := fp.Modulus()
	for i := range alias.Point.X.Limbs {
		alias.Point.X.Limbs[i] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(modulus), uint(64*i)), new(big.Int).SetUint64(^uint64(0)))
	}
	if err := test.IsSolved(&encodingCircuit{}, alias, ecc.BN254.ScalarField()); err == nil {
		t.Fatal("accepted noncanonical identity coordinates")
	}
}

func TestBN254CanonicalVectors(t *testing.T) {
	_, _, g, _ := bn254.Generators()
	var negative bn254.G1Affine
	negative.Neg(&g)
	cases := []struct {
		p           bn254.G1Affine
		first, last byte
	}{{g, 1, 0}, {negative, 1, 0x80}, {bn254.G1Affine{}, 0, 0x40}}
	for _, c := range cases {
		b := encodePoint(c.p)
		for i, v := range b {
			want := byte(0)
			if i == 0 {
				want = c.first
			}
			if i == 31 {
				want = c.last
			}
			if v != want {
				t.Fatalf("byte %d: %x != %x", i, v, want)
			}
		}
	}
}

type completeMSMCircuit struct {
	Points   [2]circuitG1
	Scalars  [2]frontend.Variable
	Expected circuitG1
}

func (c *completeMSMCircuit) Define(api frontend.API) error {
	field, err := emulated.NewField[scalarField](api)
	if err != nil {
		return err
	}
	parameters := curveParameters()
	parameters.PreferClassicGLV = true
	curve, err := sw_emulated.New[baseField, scalarField](api, parameters)
	if err != nil {
		return err
	}
	actual, err := completeMSM(api, curve, field, []*circuitG1{&c.Points[0], &c.Points[1]}, c.Scalars[:])
	if err != nil {
		return err
	}
	curve.AssertIsEqual(actual, &c.Expected)
	return nil
}

func TestBN254CompleteMSMExceptionalCases(t *testing.T) {
	_, _, g, _ := bn254.Generators()
	var neg, twice bn254.G1Affine
	neg.Neg(&g)
	twice.Add(&g, &g)
	for _, c := range []struct {
		points   [2]bn254.G1Affine
		scalars  [2]frontend.Variable
		expected bn254.G1Affine
	}{
		{[2]bn254.G1Affine{g, g}, [2]frontend.Variable{0, 0}, bn254.G1Affine{}},
		{[2]bn254.G1Affine{g, neg}, [2]frontend.Variable{1, 1}, bn254.G1Affine{}},
		{[2]bn254.G1Affine{{}, g}, [2]frontend.Variable{7, 0}, bn254.G1Affine{}},
		{[2]bn254.G1Affine{g, g}, [2]frontend.Variable{1, 1}, twice},
	} {
		w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(c.points[0]), newCircuitG1(c.points[1])}, Scalars: c.scalars, Expected: newCircuitG1(c.expected)}
		if err := test.IsSolved(&completeMSMCircuit{}, w, curveID.ScalarField()); err != nil {
			t.Fatal(err)
		}
	}
}

func TestBN254ClassicGLVMatchesNativeMSM(t *testing.T) {
	_, _, g, _ := bn254.Generators()
	var neg, twice, other bn254.G1Affine
	neg.Neg(&g)
	twice.Add(&g, &g)
	other.ScalarMultiplication(&g, big.NewInt(1234567))
	minusOne := new(big.Int).Sub(scalarModulus(), big.NewInt(1))
	scalars := []*big.Int{new(big.Int), big.NewInt(1), big.NewInt(2), minusOne, new(big.Int).Rsh(new(big.Int).Set(scalarModulus()), 1), new(big.Int).Lsh(big.NewInt(1), 200)}
	pairs := [][2]bn254.G1Affine{{g, g}, {g, neg}, {g, twice}, {other, g}, {{}, g}, {{}, {}}}
	for i, pair := range pairs {
		for j, s1 := range scalars {
			s2 := scalars[(j+i)%len(scalars)]
			var a, b, want bn254.G1Affine
			a.ScalarMultiplication(&pair[0], s1)
			b.ScalarMultiplication(&pair[1], s2)
			want.Add(&a, &b)
			w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(pair[0]), newCircuitG1(pair[1])}, Scalars: [2]frontend.Variable{s1, s2}, Expected: newCircuitG1(want)}
			if err := test.IsSolved(&completeMSMCircuit{}, w, curveID.ScalarField()); err != nil {
				t.Fatalf("pair %d scalar %d: %v", i, j, err)
			}
		}
	}
	w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(g), newCircuitG1(neg)}, Scalars: [2]frontend.Variable{1, 1}, Expected: newCircuitG1(g)}
	if err := test.IsSolved(&completeMSMCircuit{}, w, curveID.ScalarField()); err == nil {
		t.Fatal("accepted incorrect MSM result")
	}
}

type foldedPairingCircuit struct {
	Left     circuitG1
	Right    circuitG1
	Deferred [2]circuitG1
	Outer    [2]nativeG2 `gnark:"-"`
	Inner    [2]nativeG2 `gnark:"-"`
}

func (c *foldedPairingCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[baseField](api)
	if err != nil {
		return err
	}
	s, err := emulated.NewField[scalarField](api)
	if err != nil {
		return err
	}
	params := curveParameters()
	params.PreferClassicGLV = true
	curve, err := sw_emulated.New[baseField, scalarField](api, params)
	if err != nil {
		return err
	}
	pairing, err := newPairing(api)
	if err != nil {
		return err
	}
	pairing.AssertIsOnG1(&c.Left)
	pairing.AssertIsOnG1(&c.Right)
	pairing.AssertIsOnG1(&c.Deferred[0])
	pairing.AssertIsOnG1(&c.Deferred[1])
	t := newTranscript(api, u, []byte("folded-pairing-test"))
	t.observe(uints.NewU8Array([]byte("ix/pairing-fold/v1")))
	t.observe(pointBytes(api, u, f, &c.Left))
	t.observe(pointBytes(api, u, f, &c.Right))
	t.observe(pointBytes(api, u, f, &c.Deferred[0]))
	t.observe(pointBytes(api, u, f, &c.Deferred[1]))
	rho := t.sampleFinal()
	rhoScalar := s.FromBits(bits.ToBinary(api, rho)...)
	scaledD0, err := curve.MultiScalarMul([]*circuitG1{&c.Deferred[0]}, []*circuitScalar{rhoScalar})
	if err != nil {
		return err
	}
	scaledD1, err := curve.MultiScalarMul([]*circuitG1{&c.Deferred[1]}, []*circuitScalar{rhoScalar})
	if err != nil {
		return err
	}
	negRight := curve.Neg(&c.Right)
	h, tauH := newCircuitG2Fixed(c.Outer[0]), newCircuitG2Fixed(c.Outer[1])
	if c.Outer[0].Equal(&c.Inner[0]) && c.Outer[1].Equal(&c.Inner[1]) {
		foldedLeft := curve.AddUnified(&c.Left, scaledD0)
		foldedRight := curve.AddUnified(negRight, scaledD1)
		return pairing.PairingCheck([]*circuitG1{foldedLeft, foldedRight}, []*circuitG2{&h, &tauH})
	}
	ih, itauH := newCircuitG2Fixed(c.Inner[0]), newCircuitG2Fixed(c.Inner[1])
	return pairing.PairingCheck(
		[]*circuitG1{&c.Left, negRight, scaledD0, scaledD1},
		[]*circuitG2{&h, &tauH, &ih, &itauH},
	)
}

func TestBN254FoldedPairingSoundnessAndEdgeCases(t *testing.T) {
	_, _, g1, g2 := bn254.Generators()
	tau1 := big.NewInt(7)
	tau2 := big.NewInt(13)
	var tau1H, tau2H nativeG2
	tau1H.ScalarMultiplication(&g2, tau1)
	tau2H.ScalarMultiplication(&g2, tau2)

	scaleG1 := func(k int64) bn254.G1Affine {
		var p bn254.G1Affine
		if k >= 0 {
			p.ScalarMultiplication(&g1, big.NewInt(k))
		} else {
			p.ScalarMultiplication(&g1, big.NewInt(-k))
			p.Neg(&p)
		}
		return p
	}

	// 1. Same G2 keys (2-pair fast path): valid pair, infinity cases, and rogue cancellation rejection.
	sameKeys := [2]nativeG2{g2, tau1H}
	sameCircuit := &foldedPairingCircuit{Outer: sameKeys, Inner: sameKeys}
	validCases := []struct {
		left, right, d0, d1 bn254.G1Affine
	}{
		{scaleG1(7), scaleG1(1), scaleG1(14), scaleG1(-2)},
		{bn254.G1Affine{}, bn254.G1Affine{}, scaleG1(7), scaleG1(-1)},
		{scaleG1(7), scaleG1(1), bn254.G1Affine{}, bn254.G1Affine{}},
	}
	for i, tc := range validCases {
		w := &foldedPairingCircuit{
			Left:     newCircuitG1(tc.left),
			Right:    newCircuitG1(tc.right),
			Deferred: [2]circuitG1{newCircuitG1(tc.d0), newCircuitG1(tc.d1)},
		}
		if err := test.IsSolved(sameCircuit, w, curveID.ScalarField()); err != nil {
			t.Fatalf("same-keys valid case %d failed: %v", i, err)
		}
	}
	// Rogue cross-cancellation: e(8G, h)·e(-G, 7h) = e(G, h) ≠ 1 and
	// e(6G, h)·e(-G, 7h) = e(-G, h) = e(G, h)^{-1}; naive sum cancels to 1,
	// but ρ-folding MUST reject!
	rogueSame := &foldedPairingCircuit{
		Left:     newCircuitG1(scaleG1(8)),
		Right:    newCircuitG1(scaleG1(1)),
		Deferred: [2]circuitG1{newCircuitG1(scaleG1(6)), newCircuitG1(scaleG1(-1))},
	}
	if err := test.IsSolved(sameCircuit, rogueSame, curveID.ScalarField()); err == nil {
		t.Fatal("same-keys folded pairing accepted rogue cross-cancellation")
	}

	// 2. Distinct G2 keys (4-pair fallback): valid pair accepted, rogue cancellation rejected.
	diffCircuit := &foldedPairingCircuit{Outer: [2]nativeG2{g2, tau1H}, Inner: [2]nativeG2{g2, tau2H}}
	validDiff := &foldedPairingCircuit{
		Left:     newCircuitG1(scaleG1(7)),
		Right:    newCircuitG1(scaleG1(1)),
		Deferred: [2]circuitG1{newCircuitG1(scaleG1(26)), newCircuitG1(scaleG1(-2))},
	}
	if err := test.IsSolved(diffCircuit, validDiff, curveID.ScalarField()); err != nil {
		t.Fatalf("distinct-keys valid case failed: %v", err)
	}
	// Rogue cancellation across distinct keys: outer = e(G, h), inner = e(-G, h).
	rogueDiff := &foldedPairingCircuit{
		Left:     newCircuitG1(scaleG1(8)),
		Right:    newCircuitG1(scaleG1(1)),
		Deferred: [2]circuitG1{newCircuitG1(scaleG1(12)), newCircuitG1(scaleG1(-1))},
	}
	if err := test.IsSolved(diffCircuit, rogueDiff, curveID.ScalarField()); err == nil {
		t.Fatal("distinct-keys 4-pair fallback accepted rogue cross-cancellation")
	}
}
