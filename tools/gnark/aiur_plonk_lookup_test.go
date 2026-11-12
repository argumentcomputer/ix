//go:build plonk || !groth16

package main

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

type aiurFingerprintTest struct {
	Gamma, Beta, Value frontend.Variable
	Output             [3]frontend.Variable `gnark:",public"`
}

func (c *aiurFingerprintTest) Define(api frontend.API) error {
	powers := []frontend.Variable{1, c.Gamma, api.Mul(c.Gamma, c.Gamma)}
	powers = append(powers, api.Mul(powers[2], c.Gamma), api.Mul(powers[2], powers[2]))
	cache := make(map[string]frontend.Variable)
	for i, args := range [][]frontend.Variable{{1, 7, c.Value}, {1, 8, c.Value}, {1, 7, c.Value, 0}} {
		denominator := aiurLookupDenominator(api, c.Beta, powers, args, cache)
		var expected frontend.Variable = len(args)
		for j := len(args) - 1; j >= 0; j-- {
			expected = api.Add(api.Mul(expected, c.Gamma), args[j])
		}
		api.AssertIsEqual(denominator, api.Add(c.Beta, expected))
		api.AssertIsEqual(denominator, c.Output[i])
	}
	return nil
}

func TestAiurPlonkHoistedFingerprintsMatchPolynomial(t *testing.T) {
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &aiurFingerprintTest{})
	if err != nil {
		t.Fatal(err)
	}
	for _, gamma := range []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(17), new(big.Int).Sub(scalarModulus(), big.NewInt(1))} {
		assignment := &aiurFingerprintTest{Gamma: gamma, Beta: 23, Value: 31}
		for i, args := range [][]int64{{1, 7, 31}, {1, 8, 31}, {1, 7, 31, 0}} {
			expected := big.NewInt(int64(len(args)))
			for j := len(args) - 1; j >= 0; j-- {
				expected.Mul(expected, gamma)
				expected.Add(expected, big.NewInt(args[j]))
			}
			expected.Add(expected, big.NewInt(23))
			expected.Mod(expected, scalarModulus())
			assignment.Output[i] = expected
		}
		witness, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(witness); err != nil {
			t.Fatal(err)
		}
	}
}

type aiurInverseTest struct {
	Denominator frontend.Variable
	Output      frontend.Variable `gnark:",public"`
}

func (c *aiurInverseTest) Define(api frontend.API) error {
	var inverse frontend.Variable
	if batch, ok := api.(frontend.BatchInverter); ok {
		inverse = batch.BatchInvert([]frontend.Variable{c.Denominator})[0]
	} else {
		inverse = api.Inverse(c.Denominator)
	}
	api.AssertIsEqual(inverse, c.Output)
	return nil
}
func TestAiurPlonkBatchInverseRejectsZero(t *testing.T) {
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &aiurInverseTest{})
	if err != nil {
		t.Fatal(err)
	}
	for _, output := range []int{0, 1, 17} {
		witness, err := frontend.NewWitness(&aiurInverseTest{Denominator: 0, Output: output}, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(witness); err == nil {
			t.Fatal("accepted zero lookup denominator")
		}
	}
	honest, err := frontend.NewWitness(&aiurInverseTest{Denominator: 7, Output: new(big.Int).ModInverse(big.NewInt(7), scalarModulus())}, ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(honest); err != nil {
		t.Fatal(err)
	}
}
