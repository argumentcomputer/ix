//go:build !bn254

package main

import (
	"math/big"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/test"
)

type encodingCircuit struct {
	Point   sw.G1Affine
	Encoded [48]uints.U8
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
		bytes := point.Bytes()
		copy(assignment.Encoded[:], uints.NewU8Array(bytes[:]))
		if err := test.IsSolved(&encodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err != nil {
			t.Fatal(err)
		}
		assignment.Encoded[0] = uints.NewU8(bytes[0] ^ 0x20)
		if err := test.IsSolved(&encodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err == nil {
			t.Fatal("accepted wrong sign bit")
		}
	}
	var torsion bls.G1Affine
	torsion.Y.SetUint64(2)
	assignment := &encodingCircuit{Point: sw.NewG1Affine(torsion)}
	bytes := torsion.Bytes()
	copy(assignment.Encoded[:], uints.NewU8Array(bytes[:]))
	if err := test.IsSolved(&encodingCircuit{}, assignment, ecc.BLS12_381.ScalarField()); err == nil {
		t.Fatal("accepted wrong-subgroup point")
	}
	identity := new(bls.G1Affine).Bytes()
	alias := &encodingCircuit{Point: sw.NewG1Affine(bls.G1Affine{})}
	copy(alias.Encoded[:], uints.NewU8Array(identity[:]))
	alias.Point.X.Limbs = make([]frontend.Variable, 6)
	modulus := fp.Modulus()
	for i := range alias.Point.X.Limbs {
		alias.Point.X.Limbs[i] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(modulus), uint(64*i)), new(big.Int).SetUint64(^uint64(0)))
	}
	if err := test.IsSolved(&encodingCircuit{}, alias, ecc.BLS12_381.ScalarField()); err == nil {
		t.Fatal("accepted noncanonical identity coordinates")
	}
}

func TestFullVerifierWitness(t *testing.T) {
	p, err := loadProfile(filepath.Join("testdata", "outer", "profile.json"))
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"fixture", "fixture-other-statement", "fixture-bad-pairing"} {
		assignment, err := witnessAssignment(p, filepath.Join("testdata", "outer", name+".json"))
		if err != nil {
			t.Fatal(err)
		}
		err = test.IsSolved(newCircuit(p), assignment, ecc.BLS12_381.ScalarField())
		if name == "fixture-bad-pairing" {
			if err == nil {
				t.Fatal("accepted valid outer proof with invalid deferred pairing")
			}
		} else if err != nil {
			t.Fatalf("%s: %v", name, err)
		}
	}
	assignment, err := witnessAssignment(p, filepath.Join("testdata", "outer", "fixture.json"))
	if err != nil {
		t.Fatal(err)
	}
	assignment.Claim[0] = 123
	if err := test.IsSolved(newCircuit(p), assignment, ecc.BLS12_381.ScalarField()); err == nil {
		t.Fatal("accepted a changed claim")
	}
}
