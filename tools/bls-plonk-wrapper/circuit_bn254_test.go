//go:build bn254

package main

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bn254"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
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
	_, _, g, _ := bls.Generators()
	var negative bls.G1Affine
	negative.Neg(&g)
	for _, point := range []bls.G1Affine{{}, g, negative} {
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
	identity := encodePoint(bls.G1Affine{})
	alias := &encodingCircuit{Point: sw.NewG1Affine(bls.G1Affine{})}
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
	_, _, g, _ := bls.Generators()
	var negative bls.G1Affine
	negative.Neg(&g)
	cases := []struct {
		p           bls.G1Affine
		first, last byte
	}{{g, 1, 0}, {negative, 1, 0x80}, {bls.G1Affine{}, 0, 0x40}}
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
	Points     [2]circuitG1
	Scalars    [2]frontend.Variable
	Expected   circuitG1
	ClassicGLV bool `gnark:"-"`
}

func (c *completeMSMCircuit) Define(api frontend.API) error {
	field, err := emulated.NewField[scalarField](api)
	if err != nil {
		return err
	}
	parameters := curveParameters()
	parameters.PreferClassicGLV = c.ClassicGLV
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
	_, _, g, _ := bls.Generators()
	var neg, twice bls.G1Affine
	neg.Neg(&g)
	twice.Add(&g, &g)
	for _, c := range []struct {
		points   [2]bls.G1Affine
		scalars  [2]frontend.Variable
		expected bls.G1Affine
	}{
		{[2]bls.G1Affine{g, g}, [2]frontend.Variable{0, 0}, bls.G1Affine{}},
		{[2]bls.G1Affine{g, neg}, [2]frontend.Variable{1, 1}, bls.G1Affine{}},
		{[2]bls.G1Affine{{}, g}, [2]frontend.Variable{7, 0}, bls.G1Affine{}},
		{[2]bls.G1Affine{g, g}, [2]frontend.Variable{1, 1}, twice},
	} {
		w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(c.points[0]), newCircuitG1(c.points[1])}, Scalars: c.scalars, Expected: newCircuitG1(c.expected)}
		if err := test.IsSolved(&completeMSMCircuit{}, w, curveID.ScalarField()); err != nil {
			t.Fatal(err)
		}
	}
}

func TestBN254ClassicGLVMatchesNativeMSM(t *testing.T) {
	_, _, g, _ := bls.Generators()
	var neg, twice, other bls.G1Affine
	neg.Neg(&g)
	twice.Add(&g, &g)
	other.ScalarMultiplication(&g, big.NewInt(1234567))
	minusOne := new(big.Int).Sub(scalarModulus(), big.NewInt(1))
	scalars := []*big.Int{new(big.Int), big.NewInt(1), big.NewInt(2), minusOne, new(big.Int).Rsh(new(big.Int).Set(scalarModulus()), 1), new(big.Int).Lsh(big.NewInt(1), 200)}
	pairs := [][2]bls.G1Affine{{g, g}, {g, neg}, {g, twice}, {other, g}, {{}, g}, {{}, {}}}
	for i, pair := range pairs {
		for j, s1 := range scalars {
			s2 := scalars[(j+i)%len(scalars)]
			var a, b, want bls.G1Affine
			a.ScalarMultiplication(&pair[0], s1)
			b.ScalarMultiplication(&pair[1], s2)
			want.Add(&a, &b)
			w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(pair[0]), newCircuitG1(pair[1])}, Scalars: [2]frontend.Variable{s1, s2}, Expected: newCircuitG1(want), ClassicGLV: true}
			if err := test.IsSolved(&completeMSMCircuit{ClassicGLV: true}, w, curveID.ScalarField()); err != nil {
				t.Fatalf("pair %d scalar %d: %v", i, j, err)
			}
		}
	}
	w := &completeMSMCircuit{Points: [2]circuitG1{newCircuitG1(g), newCircuitG1(neg)}, Scalars: [2]frontend.Variable{1, 1}, Expected: newCircuitG1(g), ClassicGLV: true}
	if err := test.IsSolved(&completeMSMCircuit{ClassicGLV: true}, w, curveID.ScalarField()); err == nil {
		t.Fatal("accepted incorrect MSM result")
	}
}
