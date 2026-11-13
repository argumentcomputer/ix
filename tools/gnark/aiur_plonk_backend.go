//go:build plonk || !groth16

package main

import (
	"bytes"
	"fmt"
	"io"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

func compileAiurCircuit(schema *aiurSchema) (constraint.ConstraintSystem, circuitInfo, error) {
	var info circuitInfo
	circuit, err := newAiurCircuit(schema)
	if err != nil {
		return nil, info, err
	}
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, circuit)
	if err != nil {
		return nil, info, err
	}
	info = circuitInfo{
		Domain:      ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables())),
		Constraints: ccs.GetNbConstraints(), PublicInputs: ccs.GetNbPublicVariables(),
		Commitments: len(ccs.GetCommitments().CommitmentIndexes()),
	}
	if info.Domain > aiurMaxDomain {
		return nil, info, fmt.Errorf("Aiur PLONK domain exceeds Ignition ceremony capacity (2^26)")
	}
	if info.Commitments != 1 || info.PublicInputs != schema.PublicInputs {
		return nil, info, fmt.Errorf("unexpected Aiur PLONK commitment or public-input count")
	}
	return ccs, info, nil
}

func compileAiur(schema []byte, path string) (circuitInfo, error) {
	var decoded aiurSchema
	if err := decodeReader(bytes.NewReader(schema), &decoded); err != nil {
		return circuitInfo{}, err
	}
	ccs, info, err := compileAiurCircuit(&decoded)
	if err != nil {
		return info, err
	}
	return info, atomicFile(path, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
}
