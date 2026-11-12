package main

import (
	"io"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/zeebo/blake3"
)

type aiurBlakeTest struct {
	Gamma frontend.Variable
	Beta  frontend.Variable `gnark:",public"`
}

func (c *aiurBlakeTest) Define(api frontend.API) error {
	api.AssertIsEqual(aiurLookupBeta(api, c.Gamma), c.Beta)
	return nil
}
func aiurNativeBeta(gamma *big.Int) *big.Int {
	encoded := gamma.FillBytes(make([]byte, 32))
	for i, j := 0, 31; i < j; i, j = i+1, j-1 {
		encoded[i], encoded[j] = encoded[j], encoded[i]
	}
	h := blake3.New()
	h.Write([]byte(aiurLookupDomain))
	h.Write(encoded)
	out := make([]byte, 64)
	if _, err := io.ReadFull(h.Digest(), out); err != nil {
		panic(err)
	}
	for i, j := 0, 63; i < j; i, j = i+1, j-1 {
		out[i], out[j] = out[j], out[i]
	}
	return new(big.Int).Mod(new(big.Int).SetBytes(out), scalarModulus())
}
func TestAiurLookupBlake3(t *testing.T) {
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &aiurBlakeTest{})
	if err != nil {
		t.Fatal(err)
	}
	if len(ccs.GetCommitments().CommitmentIndexes()) != 0 {
		t.Fatal("challenge expansion created a nested commitment")
	}
	cases := []*big.Int{new(big.Int), big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 200), new(big.Int).Sub(scalarModulus(), big.NewInt(1))}
	for i := range 8 {
		hash := blake3.Sum256([]byte{byte(i), 0xa5})
		cases = append(cases, new(big.Int).Mod(new(big.Int).SetBytes(hash[:]), scalarModulus()))
	}
	for _, gamma := range cases {
		beta := aiurNativeBeta(gamma)
		w, err := frontend.NewWitness(&aiurBlakeTest{Gamma: gamma, Beta: beta}, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(w); err != nil {
			t.Fatal(err)
		}
		bad, err := frontend.NewWitness(&aiurBlakeTest{Gamma: gamma, Beta: new(big.Int).Add(beta, big.NewInt(1))}, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(bad); err == nil {
			t.Fatal("accepted changed BLAKE3 output")
		}
	}
	t.Logf("lookup BLAKE3 constraints=%d, commitments=0", ccs.GetNbConstraints())
}
