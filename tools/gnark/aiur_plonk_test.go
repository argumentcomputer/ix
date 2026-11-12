//go:build plonk || !groth16

package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
)

func aiurFixture(t *testing.T) (*aiurSchema, *aiurWitness, map[string][2]int) {
	t.Helper()
	directory := os.Getenv("IX_AIUR_PLONK_FIXTURE")
	if directory == "" {
		directory = filepath.Join("testdata", "aiur")
	}
	var schema aiurSchema
	var witness aiurWitness
	var mutations map[string][2]int
	for _, item := range []struct {
		name  string
		value any
	}{{"schema.json", &schema}, {"witness.json", &witness}, {"mutations.json", &mutations}} {
		if err := decodeJSON(filepath.Join(directory, item.name), item.value); err != nil {
			t.Fatal(err)
		}
	}
	return &schema, &witness, mutations
}
func aiurCompile(t *testing.T, schema *aiurSchema) constraint.ConstraintSystem {
	t.Helper()
	ccs, info, err := compileAiurCircuit(schema)
	if err != nil {
		t.Fatal(err)
	}
	domain := info.Domain
	t.Logf("Aiur PLONK constraints=%d public=%d domain=%d commitments=1", ccs.GetNbConstraints(), ccs.GetNbPublicVariables(), domain)
	return ccs
}
func aiurAssignment(t *testing.T, schema *aiurSchema, witness *aiurWitness) *aiurCircuit {
	t.Helper()
	assignment, err := assignAiur(schema, witness)
	if err != nil {
		t.Fatal(err)
	}
	return assignment
}
func aiurIncrement(value string) string {
	x, _ := canonical(value, scalarModulus())
	x.Add(x, big.NewInt(1))
	x.Mod(x, scalarModulus())
	return x.String()
}
func TestAiurPlonkCompilerConstraints(t *testing.T) {
	schema, witness, mutations := aiurFixture(t)
	ccs := aiurCompile(t, schema)
	assignment := aiurAssignment(t, schema, witness)
	w, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err != nil {
		t.Fatal(err)
	}
	for name, position := range mutations {
		old := witness.Main[position[0]][position[1]]
		witness.Main[position[0]][position[1]] = aiurIncrement(old)
		assignment := aiurAssignment(t, schema, witness)
		witness.Main[position[0]][position[1]] = old
		bad, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(bad); err == nil {
			t.Fatalf("accepted altered %s", name)
		}
	}
	for i := range witness.Public {
		old := witness.Public[i]
		witness.Public[i] = aiurIncrement(old)
		assignment := aiurAssignment(t, schema, witness)
		witness.Public[i] = old
		bad, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		if err := ccs.IsSolved(bad); err == nil {
			t.Fatalf("accepted altered public field %d", i)
		}
	}
	// A negative table multiplicity is a field element but not a permitted
	// integer count, even when an attacker controls its full canonical encoding.
	position := mutations["map_count"]
	witness.Main[position[0]][position[1]] = new(big.Int).Sub(scalarModulus(), big.NewInt(1)).String()
	bad, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(bad); err == nil {
		t.Fatal("accepted negative multiplicity")
	}
}

func TestAiurPlonkIgnition(t *testing.T) {
	path := os.Getenv("IX_AIUR_PLONK_SRS")
	pin := os.Getenv("IX_AIUR_PLONK_SRS_BLAKE3")
	if path == "" || pin == "" {
		t.Skip("set independently authenticated IX_AIUR_PLONK_SRS and IX_AIUR_PLONK_SRS_BLAKE3")
	}
	schema, witness, _ := aiurFixture(t)
	ccs := aiurCompile(t, schema)
	domain := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables()))
	srs, err := readSRS(path, pin, domain)
	if err != nil {
		t.Fatal(err)
	}
	lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:domain])
	if err != nil {
		t.Fatal(err)
	}
	pk, vk, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
	if err != nil {
		t.Fatal(err)
	}
	w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		t.Fatal(err)
	}
	public, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatal(err)
	}
	original := witness.Public[0]
	witness.Public[0] = aiurIncrement(original)
	bad, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	witness.Public[0] = original
	badPublic, _ := bad.Public()
	if err := plonk.Verify(proof, vk, badPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("verified changed public call")
	}
	if _, err := plonk.Prove(ccs, pk, bad, solidity.WithProverTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("proved an unsatisfied public call")
	}
	native := new(bytes.Buffer)
	if _, err := proof.WriteTo(native); err != nil {
		t.Fatal(err)
	}
	payload := proof.(*plonkbn254.Proof).MarshalSolidity()
	commitments := len(vk.(*plonkbn254.VerifyingKey).Qcp)
	if commitments != 1 || len(payload) != 864 {
		t.Fatalf("unexpected payload: %d bytes, %d commitments", len(payload), commitments)
	}
	directory := os.Getenv("IX_AIUR_PLONK_OUTPUT")
	if directory == "" {
		directory = t.TempDir()
	}
	if err := os.MkdirAll(directory, 0755); err != nil {
		t.Fatal(err)
	}
	contract := new(bytes.Buffer)
	if err := vk.ExportSolidity(contract); err != nil {
		t.Fatal(err)
	}
	key := new(bytes.Buffer)
	if _, err := vk.WriteTo(key); err != nil {
		t.Fatal(err)
	}
	vector, err := json.MarshalIndent(map[string]any{"format": aiurPlonkFormat, "public": witness.Public, "proof": "0x" + hex.EncodeToString(payload), "domain": domain, "constraints": ccs.GetNbConstraints(), "commitments": commitments, "native_bytes": native.Len(), "solidity_bytes": len(payload)}, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	for name, data := range map[string][]byte{"proof.bin": native.Bytes(), "proof.solidity.bin": payload, "proof.json": vector, "verifying-key.bin": key.Bytes(), "PlonkVerifier.sol": contract.Bytes()} {
		if err := os.WriteFile(filepath.Join(directory, name), data, 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Ignition Aiur PLONK native=%d bytes Solidity=%d bytes output=%s", native.Len(), len(payload), directory)
}

func TestAiurPlonkRejectsMalformedSchema(t *testing.T) {
	original, witness, _ := aiurFixture(t)
	encoded, err := json.Marshal(original)
	if err != nil {
		t.Fatal(err)
	}
	cases := []func(*aiurSchema){func(s *aiurSchema) { s.Format = "" }, func(s *aiurSchema) { s.Circuits[0].Rows = aiurMaxDomain + 1 }, func(s *aiurSchema) { s.Circuits[0].Nodes[0] = aiurNode{Op: "add", A: 0, B: 0} }, func(s *aiurSchema) { s.Circuits[0].Constraints = append(s.Circuits[0].Constraints, -1) }, func(s *aiurSchema) { s.Circuits[0].Lookups[0].Count = -1 }, func(s *aiurSchema) {
		s.Circuits[0].Nodes[0] = aiurNode{Op: "constant", Value: scalarModulus().String()}
	}}
	for i, mutate := range cases {
		var schema aiurSchema
		if err := json.Unmarshal(encoded, &schema); err != nil {
			t.Fatal(err)
		}
		mutate(&schema)
		if err := schema.validate(); err == nil {
			t.Fatal(fmt.Sprintf("accepted malformed schema case %d", i))
		}
	}
	witness.Main[0] = append(witness.Main[0], "0")
	if _, err := assignAiur(original, witness); err == nil {
		t.Fatal("accepted excess main cells")
	}
}

func TestAiurPlonkROMTransitionAndPadding(t *testing.T) {
	schema, witness, mutations := aiurFixture(t)
	index := mutations["rom_address"][0]
	chip := &schema.Circuits[index]
	if chip.Rows != 1 {
		t.Fatal("unexpected ROM fixture capacity")
	}
	chip.Rows = 2
	for range chip.MainWidth {
		witness.Main[index] = append(witness.Main[index], "0")
	}
	ccs := aiurCompile(t, schema)
	solve := func() error {
		w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
		if err != nil {
			return err
		}
		return ccs.IsSolved(w)
	}
	if err := solve(); err != nil {
		t.Fatal(err)
	}
	// An unused active ROM member may have zero multiplicity, but its address
	// must continue the active prefix and cannot introduce a gap.
	second := witness.Main[index][chip.MainWidth:]
	second[1], second[2] = "1", "1"
	if err := solve(); err != nil {
		t.Fatal(err)
	}
	second[2] = "2"
	if err := solve(); err == nil {
		t.Fatal("accepted a ROM address gap")
	}
	second[1], second[2], second[0] = "0", "0", "1"
	if err := solve(); err == nil {
		t.Fatal("accepted nonzero multiplicity on inactive padding")
	}
}

func TestAiurPlonkLookupArityIsBound(t *testing.T) {
	schema, witness, _ := aiurFixture(t)
	chip := &schema.Circuits[0]
	zero := len(chip.Nodes)
	chip.Nodes = append(chip.Nodes, aiurNode{Op: "constant", Value: "0"})
	chip.Lookups[0].Args = append(chip.Lookups[0].Args, zero)
	ccs := aiurCompile(t, schema)
	w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err == nil {
		t.Fatal("accepted trailing-zero extension of a call message")
	}
}
