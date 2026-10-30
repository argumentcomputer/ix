package main

import (
	"encoding/json"
	"github.com/consensys/gnark/frontend"
	"io"
	"os"
)

// fixtureSRSBLAKE3 pins testdata/bn254/srs.bin.
const fixtureSRSBLAKE3 = "90b6709b32be44fb315ce6c1007bf7debe38526f430e50746481bc712f622d7e"

func writeJSON(path string, value any) error {
	return atomicFile(path, func(w io.Writer) error { enc := json.NewEncoder(w); enc.SetIndent("", "  "); return enc.Encode(value) })
}

func decodeJSON(path string, out any) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	return decodeReader(io.LimitReader(f, 16<<20), out)
}

func loadVerifyingKey(path string) (*verifyingKey, error) {
	var p verifyingKey
	if err := decodeJSON(path, &p); err != nil {
		return nil, err
	}
	if err := p.validate(); err != nil {
		return nil, err
	}
	return &p, nil
}

func witnessAssignment(p *verifyingKey, path string) (*wrapperCircuit, error) {
	var w witnessJSON
	if err := decodeJSON(path, &w); err != nil {
		return nil, err
	}
	return assignWitness(p, &w)
}

type backendCircuit struct {
	Claim  [2]frontend.Variable `gnark:",public"`
	X      frontend.Variable
	Commit bool `gnark:"-"`
}

func (c *backendCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(api.Mul(c.X, c.X), c.Claim[0])
	api.AssertIsEqual(c.Claim[1], 1)
	if c.Commit {
		challenge, err := api.(frontend.Committer).Commit(c.X)
		if err != nil {
			return err
		}
		api.AssertIsDifferent(challenge, 0)
	}
	return nil
}
