package main

import (
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	blsfp "github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark/frontend"
	swbls "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/test"
)

type blsEncodingCircuit struct {
	Point   swbls.G1Affine
	Encoded [48]uints.U8
}

func (c *blsEncodingCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[swbls.BaseField](api)
	if err != nil {
		return err
	}
	pairing, err := swbls.NewPairing(api)
	if err != nil {
		return err
	}
	pairing.AssertIsOnG1(&c.Point)
	for i, b := range pointBytesBLS(api, u, f, &c.Point) {
		u.Bytes.AssertIsEqual(b, c.Encoded[i])
	}
	return nil
}

func TestBLS12381IdentityAndCanonicalPointEncoding(t *testing.T) {
	_, _, g, _ := bls.Generators()
	var negative bls.G1Affine
	negative.Neg(&g)
	for _, point := range []bls.G1Affine{{}, g, negative} {
		assignment := &blsEncodingCircuit{Point: swbls.NewG1Affine(point)}
		encoded := encodePointBLS(point)
		copy(assignment.Encoded[:], uints.NewU8Array(encoded))
		if err := test.IsSolved(&blsEncodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err != nil {
			t.Fatal(err)
		}
		assignment.Encoded[0] = uints.NewU8(encoded[0] ^ 0x20)
		if err := test.IsSolved(&blsEncodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err == nil {
			t.Fatal("accepted wrong sign bit")
		}
	}
	// Mandatory BLS12-381 G1 cofactor subgroup check: (0, 2) is on y^2 = x^3 + 4
	// but NOT in the prime-order subgroup G1.
	var torsion bls.G1Affine
	torsion.Y.SetUint64(2)
	if !torsion.IsOnCurve() || torsion.IsInSubGroup() {
		t.Fatal("expected (0, 2) to be an off-subgroup curve point")
	}
	assignment := &blsEncodingCircuit{Point: swbls.NewG1Affine(torsion)}
	raw := torsion.Bytes()
	copy(assignment.Encoded[:], uints.NewU8Array(raw[:]))
	if err := test.IsSolved(&blsEncodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err == nil {
		t.Fatal("accepted wrong-subgroup BLS12-381 point")
	}

	identity := new(bls.G1Affine).Bytes()
	alias := &blsEncodingCircuit{Point: swbls.NewG1Affine(bls.G1Affine{})}
	copy(alias.Encoded[:], uints.NewU8Array(identity[:]))
	alias.Point.X.Limbs = make([]frontend.Variable, 6)
	modulus := blsfp.Modulus()
	for i := range alias.Point.X.Limbs {
		alias.Point.X.Limbs[i] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(modulus), uint(64*i)), new(big.Int).SetUint64(^uint64(0)))
	}
	if err := test.IsSolved(&blsEncodingCircuit{}, alias, ecc.BLS12_381.ScalarField()); err == nil {
		t.Fatal("accepted noncanonical BLS12-381 identity coordinates")
	}
}

type blsCompleteMSMCircuit struct {
	Points   [2]blsCircuitG1
	Scalars  [2]frontend.Variable
	Expected blsCircuitG1
}

func (c *blsCompleteMSMCircuit) Define(api frontend.API) error {
	field, err := emulated.NewField[blsScalarField](api)
	if err != nil {
		return err
	}
	curve, err := sw_emulated.New[blsBaseField, blsScalarField](api, sw_emulated.GetBLS12381Params())
	if err != nil {
		return err
	}
	actual, err := completeMSMBLS(api, curve, field, []*blsCircuitG1{&c.Points[0], &c.Points[1]}, c.Scalars[:])
	if err != nil {
		return err
	}
	curve.AssertIsEqual(actual, &c.Expected)
	return nil
}

func TestBLS12381CompleteMSM(t *testing.T) {
	_, _, g, _ := bls.Generators()
	var g2 bls.G1Affine
	g2.ScalarMultiplication(&g, big.NewInt(5))
	var minusOne big.Int
	minusOne.Sub(blsfr.Modulus(), big.NewInt(1))
	cases := []struct {
		p0, p1 bls.G1Affine
		s0, s1 *big.Int
	}{
		{g, g2, big.NewInt(0), big.NewInt(0)},
		{g, g, big.NewInt(1), new(big.Int).Set(&minusOne)},
		{g, g, big.NewInt(3), big.NewInt(4)},
		{g, g2, big.NewInt(1), big.NewInt(7)},
	}
	for _, tc := range cases {
		var a, b, sum bls.G1Jac
		var expected bls.G1Affine
		a.FromAffine(&tc.p0)
		b.FromAffine(&tc.p1)
		a.ScalarMultiplication(&a, tc.s0)
		b.ScalarMultiplication(&b, tc.s1)
		sum.AddAssign(&a).AddAssign(&b)
		expected.FromJacobian(&sum)
		assignment := &blsCompleteMSMCircuit{
			Points:   [2]blsCircuitG1{swbls.NewG1Affine(tc.p0), swbls.NewG1Affine(tc.p1)},
			Scalars:  [2]frontend.Variable{tc.s0, tc.s1},
			Expected: swbls.NewG1Affine(expected),
		}
		if err := test.IsSolved(&blsCompleteMSMCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err != nil {
			t.Fatalf("completeMSMBLS failed for s0=%v s1=%v: %v", tc.s0, tc.s1, err)
		}
	}
}

func TestBLS12381RejectsBN254VerifyingKeyFormat(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := decodeVerifyingKeyBLS(data); err == nil {
		t.Fatal("BLS12-381 decoder accepted BN254 verifying key")
	}
}
