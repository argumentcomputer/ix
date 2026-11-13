//go:build plonk || !groth16

package main

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"testing"
	"time"

	bn254 "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
)

func aiurG1Words(point nativeG1) []string {
	words := make([]string, 9)
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 80), big.NewInt(1))
	coordinates := []*big.Int{point.X.BigInt(new(big.Int)), point.Y.BigInt(new(big.Int))}
	for i, coordinate := range coordinates {
		for limb := 0; limb < 4; limb++ {
			words[4*i+limb] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(coordinate), uint(80*limb)), mask).String()
		}
	}
	words[8] = "0"
	if point.IsInfinity() {
		words[8] = "1"
	}
	return words
}

func aiurG2Words(point nativeG2) []string {
	return []string{point.X.A0.String(), point.X.A1.String(), point.Y.A0.String(), point.Y.A1.String()}
}

func aiurTerminalFixture() (*aiurSchema, *aiurWitness) {
	_, _, g, h := bn254.Generators()
	var tauG nativeG1
	var negative nativeG1
	var tauH nativeG2
	tauG.ScalarMultiplication(&g, big.NewInt(7))
	negative.Neg(&g)
	tauH.ScalarMultiplication(&h, big.NewInt(7))
	outputs := append(aiurG1Words(tauG), aiurG1Words(negative)...)
	nodes := []aiurNode{{Op: "constant", Value: "1"}, {Op: "constant", Value: "0"}}
	args := []int{0, 1}
	for i := 0; i < 20; i++ {
		args = append(args, len(nodes))
		nodes = append(nodes, aiurNode{Op: "main", Column: i})
	}
	schema := &aiurSchema{Format: aiurTerminalFormat, Callable: 0, PublicInputs: 2,
		PrivateOutputs: aiurTerminalOutputs,
		Pairing:        &aiurPairing{Curve: "bn254", Encoding: "affine-u80-v1", G2: [][]string{aiurG2Words(h), aiurG2Words(tauH)}},
		Circuits: []aiurChip{{Name: "root", Rows: 1, MainWidth: 20, Nodes: nodes,
			Lookups: []aiurLookup{{Negative: true, Count: 0, Args: args}}}}}
	public := []string{"17", "29"}
	return schema, &aiurWitness{Public: public, Main: [][]string{append(append([]string{}, public...), outputs...)}, PrivateOutputs: outputs}
}

func cloneAiurTerminalWitness(w *aiurWitness) *aiurWitness {
	return &aiurWitness{Public: append([]string{}, w.Public...), Main: [][]string{append([]string{}, w.Main[0]...)}, PrivateOutputs: append([]string{}, w.PrivateOutputs...)}
}

func TestAiurTerminalSchemaRejectsMissingOrMalformedPairing(t *testing.T) {
	schema, witness := aiurTerminalFixture()
	encoded, err := json.Marshal(schema)
	if err != nil {
		t.Fatal(err)
	}
	for name, mutate := range map[string]func(*aiurSchema){
		"generic with only gadget":  func(s *aiurSchema) { s.Format = aiurPlonkFormat; s.PrivateOutputs = 0 },
		"generic with only outputs": func(s *aiurSchema) { s.Format = aiurPlonkFormat; s.Pairing = nil },
		"generic":                   func(s *aiurSchema) { s.Format = aiurPlonkFormat },
		"no gadget":                 func(s *aiurSchema) { s.Pairing = nil },
		"no outputs":                func(s *aiurSchema) { s.PrivateOutputs = 0 },
		"wrong output width":        func(s *aiurSchema) { s.PrivateOutputs = 17 },
		"wrong public width":        func(s *aiurSchema) { s.PublicInputs = 3 },
		"curve":                     func(s *aiurSchema) { s.Pairing.Curve = "other" },
		"encoding":                  func(s *aiurSchema) { s.Pairing.Encoding = "compressed" },
		"missing anchor":            func(s *aiurSchema) { s.Pairing.G2 = s.Pairing.G2[:1] },
		"extra anchor":              func(s *aiurSchema) { s.Pairing.G2 = append(s.Pairing.G2, s.Pairing.G2[0]) },
		"missing coordinate":        func(s *aiurSchema) { s.Pairing.G2[0] = s.Pairing.G2[0][:3] },
		"extra coordinate":          func(s *aiurSchema) { s.Pairing.G2[0] = append(s.Pairing.G2[0], "0") },
		"noncanonical coordinate":   func(s *aiurSchema) { s.Pairing.G2[0][0] = baseModulus().String() },
		"nondecimal coordinate":     func(s *aiurSchema) { s.Pairing.G2[0][0] = "0x1" },
		"negative coordinate":       func(s *aiurSchema) { s.Pairing.G2[0][0] = "-1" },
		"leading zero":              func(s *aiurSchema) { s.Pairing.G2[0][0] = "00" },
		"infinity anchor":           func(s *aiurSchema) { s.Pairing.G2[0] = []string{"0", "0", "0", "0"} },
		"off-curve anchor":          func(s *aiurSchema) { s.Pairing.G2[0] = []string{"1", "0", "2", "0"} },
	} {
		var changed aiurSchema
		if err := json.Unmarshal(encoded, &changed); err != nil {
			t.Fatal(err)
		}
		mutate(&changed)
		if err := changed.validate(); err == nil {
			t.Fatalf("accepted %s", name)
		}
	}
	wrong := cloneAiurTerminalWitness(witness)
	wrong.PrivateOutputs = wrong.PrivateOutputs[:17]
	if _, err := assignAiur(schema, wrong); err == nil {
		t.Fatal("accepted wrong private output length")
	}
	generic, values, _ := aiurFixture(t)
	values.PrivateOutputs = []string{"0"}
	if _, err := assignAiur(generic, values); err == nil {
		t.Fatal("generic witness accepted a private output")
	}
}

func TestAiurTerminalPairingBindsExactPrivateOutputs(t *testing.T) {
	schema, honest := aiurTerminalFixture()
	ccs := aiurCompile(t, schema)
	if ccs.GetNbPublicVariables() != 2 || ccs.GetNbSecretVariables() != 38 {
		t.Fatalf("unexpected terminal dimensions public=%d secret=%d", ccs.GetNbPublicVariables(), ccs.GetNbSecretVariables())
	}
	_, _, g, _ := bn254.Generators()
	var twice, twiceTau, negativeTwice nativeG1
	twice.ScalarMultiplication(&g, big.NewInt(2))
	twiceTau.ScalarMultiplication(&g, big.NewInt(14))
	negativeTwice.Neg(&twice)
	validOther := append(aiurG1Words(twiceTau), aiurG1Words(negativeTwice)...)
	infinity := aiurG1Words(nativeG1{})
	cases := []struct {
		name   string
		valid  bool
		mutate func(*aiurWitness)
	}{
		{"honest", true, func(*aiurWitness) {}},
		{"both infinity", true, func(w *aiurWitness) { w.PrivateOutputs = append(append([]string{}, infinity...), infinity...) }},
		{"first infinity", false, func(w *aiurWitness) { copy(w.PrivateOutputs[:9], infinity) }},
		{"second infinity", false, func(w *aiurWitness) { copy(w.PrivateOutputs[9:], infinity) }},
		{"wrong valid point", false, func(w *aiurWitness) { copy(w.PrivateOutputs[9:], aiurG1Words(g)) }},
		{"noncanonical x", false, func(w *aiurWitness) {
			value := new(big.Int).Add(baseModulus(), big.NewInt(1))
			mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 80), big.NewInt(1))
			for i := 0; i < 4; i++ {
				w.PrivateOutputs[9+i] = new(big.Int).And(new(big.Int).Rsh(new(big.Int).Set(value), uint(80*i)), mask).String()
			}
		}},
		{"overwide low limb", false, func(w *aiurWitness) { w.PrivateOutputs[0] = new(big.Int).Lsh(big.NewInt(1), 80).String() }},
		{"overwide high limb", false, func(w *aiurWitness) { w.PrivateOutputs[3] = new(big.Int).Lsh(big.NewInt(1), 14).String() }},
		{"invalid infinity flag", false, func(w *aiurWitness) { w.PrivateOutputs[8] = "2" }},
		{"nonzero infinity", false, func(w *aiurWitness) { w.PrivateOutputs[8] = "1" }},
		{"unmarked infinity", false, func(w *aiurWitness) { copy(w.PrivateOutputs[:9], infinity); w.PrivateOutputs[8] = "0" }},
	}
	for _, tc := range cases {
		w := cloneAiurTerminalWitness(honest)
		tc.mutate(w)
		copy(w.Main[0][2:], w.PrivateOutputs)
		assignment, err := frontend.NewWitness(aiurAssignment(t, schema, w), curveID.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		err = ccs.IsSolved(assignment)
		if (err == nil) != tc.valid {
			t.Fatalf("%s: expected valid=%t, got %v", tc.name, tc.valid, err)
		}
	}
	changed := cloneAiurTerminalWitness(honest)
	changed.PrivateOutputs = validOther
	assignment, err := frontend.NewWitness(aiurAssignment(t, schema, changed), curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(assignment); err == nil {
		t.Fatal("accepted a different valid pairing pair detached from the Aiur root outputs")
	}
	copy(changed.Main[0][2:], validOther)
	assignment, err = frontend.NewWitness(aiurAssignment(t, schema, changed), curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(assignment); err != nil {
		t.Fatalf("alternate valid pair: %v", err)
	}
}

func TestAiurTerminalBinaryWitnessAppendsPrivateOutputs(t *testing.T) {
	schema, values := aiurTerminalFixture()
	assignment, err := frontend.NewWitness(aiurAssignment(t, schema, values), curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	data, err := assignment.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	secret, err := aiurDimensions(schema)
	if err != nil || secret != 38 {
		t.Fatalf("secret count %d: %v", secret, err)
	}
	if binary.BigEndian.Uint32(data[:4]) != 2 || binary.BigEndian.Uint32(data[4:8]) != 38 {
		t.Fatal("wrong terminal binary counts")
	}
	var expected bytes.Buffer
	for _, value := range append(append(append([]string{}, values.Public...), values.Main[0]...), values.PrivateOutputs...) {
		x, err := canonical(value, scalarModulus())
		if err != nil {
			t.Fatal(err)
		}
		word := make([]byte, 32)
		x.FillBytes(word)
		expected.Write(word)
	}
	if !bytes.Equal(data[12:], expected.Bytes()) {
		t.Fatal("private outputs are not after main witness cells")
	}
	if _, err := decodeAiurWitness(data, 2, secret); err != nil {
		t.Fatal(err)
	}
}

func TestAiurTerminalPrivateOutputsConsumeTheSecretBudget(t *testing.T) {
	schema, _ := aiurTerminalFixture()
	schema.Circuits = []aiurChip{{Name: "capacity", Rows: 1, MainWidth: aiurMaxDomain - aiurTerminalOutputs}}
	if err := schema.validate(); err != nil {
		t.Fatal(err)
	}
	secret, err := aiurDimensions(schema)
	if err != nil || secret != aiurMaxDomain {
		t.Fatalf("combined secret count %d: %v", secret, err)
	}
	schema.Circuits[0].MainWidth++
	if err := schema.validate(); err == nil {
		t.Fatal("private outputs exceeded the combined secret budget")
	}
}

func TestAiurTerminalRustFixture(t *testing.T) {
	directory := os.Getenv("IX_AIUR_TERMINAL_FIXTURE")
	if directory == "" {
		t.Skip("requires the explicitly exported terminal Rust fixture")
	}
	schemaBytes, err := os.ReadFile(filepath.Join(directory, "honest-schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	forgedSchema, err := os.ReadFile(filepath.Join(directory, "forged-schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(schemaBytes, forgedSchema) {
		t.Fatal("honest and forged fixtures require different schemas")
	}
	var schema aiurSchema
	if err := decodeReader(bytes.NewReader(schemaBytes), &schema); err != nil {
		t.Fatal(err)
	}
	secret, err := aiurDimensions(&schema)
	if err != nil {
		t.Fatal(err)
	}
	ccs := plonk.NewCS(curveID)
	if compiled := os.Getenv("IX_AIUR_TERMINAL_CIRCUIT"); compiled != "" {
		file, err := os.Open(compiled)
		if err != nil {
			t.Fatal(err)
		}
		defer file.Close()
		if _, err := ccs.ReadFrom(file); err != nil {
			t.Fatal(err)
		}
		var suffix [1]byte
		if _, err := file.Read(suffix[:]); err != io.EOF {
			t.Fatal("trailing compiled circuit bytes", err)
		}
	} else {
		ccs = aiurCompile(t, &schema)
	}
	if ccs.GetNbPublicVariables() != 2 || ccs.GetNbSecretVariables() != secret || len(ccs.GetCommitments().CommitmentIndexes()) != 1 {
		t.Fatal("terminal compiled dimensions differ from Rust schema")
	}
	public, err := os.ReadFile(filepath.Join(directory, "public.bin"))
	if err != nil {
		t.Fatal(err)
	}
	if len(public) != 64 {
		t.Fatal("terminal statement must contain two field words")
	}
	var honestBytes []byte
	for _, name := range []string{"honest", "forged"} {
		data, err := os.ReadFile(filepath.Join(directory, name+"-witness.bin"))
		if err != nil {
			t.Fatal(err)
		}
		private, err := os.ReadFile(filepath.Join(directory, name+"-private.bin"))
		if err != nil {
			t.Fatal(err)
		}
		if len(data) < 12+64+32*aiurTerminalOutputs || len(private) != 32*aiurTerminalOutputs || !bytes.Equal(data[len(data)-len(private):], private) || !bytes.Equal(data[12:12+len(public)], public) {
			t.Fatal("Rust public/private binary layout mismatch")
		}
		witness, err := decodeAiurWitness(data, 2, secret)
		if err != nil {
			t.Fatal(err)
		}
		err = ccs.IsSolved(witness)
		if (err == nil) != (name == "honest") {
			t.Fatalf("%s source execution: %v", name, err)
		}
		if name == "honest" {
			honestBytes = data
		}
	}
	changed := append([]byte(nil), honestBytes...)
	start := len(changed) - 32*aiurTerminalOutputs
	clear(changed[start:])
	changed[start+8*32+31], changed[start+17*32+31] = 1, 1
	if bytes.Equal(changed, honestBytes) {
		t.Fatal("fixture needs a nonzero honest accumulator")
	}
	witness, err := decodeAiurWitness(changed, 2, secret)
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(witness); err == nil {
		t.Fatal("actual Aiur root accepted detached identity pairing outputs")
	}
	t.Logf("Rust terminal fixture constraints=%d public=2 secret=%d commitments=1", ccs.GetNbConstraints(), secret)
}

func TestAiurTerminalDevelopmentProof(t *testing.T) {
	if os.Getenv("IX_AIUR_TERMINAL_PROVE") != "1" {
		t.Skip("set IX_AIUR_TERMINAL_PROVE=1 for the explicit development proving regression")
	}
	phase := time.Now()
	timings := make(map[string]float64)
	finished := func(name string) {
		timings[name] = time.Since(phase).Seconds()
		t.Logf("development-only phase=%s seconds=%.6f", name, timings[name])
		phase = time.Now()
	}
	schema, values := aiurTerminalFixture()
	ccs, info, err := compileAiurCircuit(schema)
	if err != nil {
		t.Fatal(err)
	}
	finished("compile")
	// Known toxic waste is confined to this protocol regression.
	srs, err := kzg.NewSRS(info.Domain+3, big.NewInt(42))
	if err != nil {
		t.Fatal(err)
	}
	finished("srs")
	lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:info.Domain])
	if err != nil {
		t.Fatal(err)
	}
	finished("lagrange")
	pk, vk, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
	if err != nil {
		t.Fatal(err)
	}
	finished("setup")
	expected := make([]byte, 32*len(values.Public))
	for i, value := range values.Public {
		word, err := canonical(value, scalarModulus())
		if err != nil {
			t.Fatal(err)
		}
		word.FillBytes(expected[32*i : 32*(i+1)])
	}
	assignment, err := frontend.NewWitness(aiurAssignment(t, schema, values), curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	data, err := assignment.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	secret, err := aiurDimensions(schema)
	if err != nil {
		t.Fatal(err)
	}
	witness, err := decodeAiurWitness(data, schema.PublicInputs, secret)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(data[12:12+len(expected)], expected) {
		t.Fatal("binary witness differs from independent public values")
	}
	public, err := aiurPublicWitness(expected, schema.PublicInputs)
	if err != nil {
		t.Fatal(err)
	}
	finished("witness_decode")
	proof, err := plonk.Prove(ccs, pk, witness, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		t.Fatal(err)
	}
	finished("prove")
	var encoded bytes.Buffer
	if _, err := proof.WriteTo(&encoded); err != nil {
		t.Fatal(err)
	}
	decoded := plonk.NewProof(curveID)
	if _, err := decoded.ReadFrom(bytes.NewReader(encoded.Bytes())); err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(decoded, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatal(err)
	}
	finished("verify")
	changed := append([]byte(nil), expected...)
	changed[31] ^= 1
	changedPublic, err := aiurPublicWitness(changed, schema.PublicInputs)
	if err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(proof, vk, changedPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("terminal proof accepted a changed statement")
	}
	_, _, generator, _ := bn254.Generators()
	bad := decoded.(*plonkbn254.Proof)
	bad.LRO[0].Add(&bad.LRO[0], &generator)
	if err := plonk.Verify(bad, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
		t.Fatal("terminal verifier accepted an altered proof commitment")
	}
	finished("negative_verification")
	payload := proof.(*plonkbn254.Proof).MarshalSolidity()
	if len(payload) != 864 {
		t.Fatalf("unexpected Solidity payload %d", len(payload))
	}
	if out := os.Getenv("IX_AIUR_TERMINAL_PROOF_OUT"); out != "" {
		if err := os.Mkdir(out, 0755); err != nil {
			t.Fatal(err)
		}
		var key bytes.Buffer
		if _, err := vk.WriteTo(&key); err != nil {
			t.Fatal(err)
		}
		report, err := json.MarshalIndent(map[string]any{"format": "ix-aiur-terminal-development-proof-v1", "setup": "known-trapdoor test-only", "constraints": info.Constraints, "domain": info.Domain, "public_inputs": info.PublicInputs, "commitments": info.Commitments, "native_bytes": encoded.Len(), "solidity_bytes": len(payload), "timings_seconds": timings, "binary_private_output_bridge": true, "independent_public_checked": true, "changed_statement_rejected": true, "changed_proof_rejected": true}, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		for name, data := range map[string][]byte{"proof.bin": encoded.Bytes(), "proof.solidity.bin": payload, "public.bin": expected, "verifying-key.bin": key.Bytes(), "report.json": report} {
			if err := os.WriteFile(filepath.Join(out, name), data, 0644); err != nil {
				t.Fatal(err)
			}
		}
	}
	t.Logf("development-only terminal proof verified: constraints=%d domain=%d public=%d commitments=%d native_bytes=%d solidity_bytes=%d", info.Constraints, info.Domain, info.PublicInputs, info.Commitments, encoded.Len(), len(payload))
}
