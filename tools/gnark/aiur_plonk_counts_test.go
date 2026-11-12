//go:build plonk || !groth16

package main

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
)

func aiurCountFixture() (*aiurSchema, *aiurWitness) {
	// Nodes: message value, receiver weight, activation, 1, 0,
	// (1-active), weight*(1-active), active*(1-active).
	nodes := []aiurNode{{Op: "main", Column: 0}, {Op: "main", Column: 1}, {Op: "main", Column: 2}, {Op: "constant", Value: "1"}, {Op: "constant", Value: "0"}, {Op: "sub", A: 3, B: 2}, {Op: "mul", A: 1, B: 5}, {Op: "mul", A: 2, B: 5}}
	schema := &aiurSchema{Format: aiurPlonkFormat, Callable: 0, PublicInputs: 1, BooleanRequests: true, Circuits: []aiurChip{{Name: "receiver", Rows: 2, MainWidth: 3, Nodes: nodes, Constraints: []int{6, 7}, Lookups: []aiurLookup{{Negative: true, Count: 1, Args: []int{3, 4, 0}}}}}}
	witness := &aiurWitness{Public: []string{"7"}, Main: [][]string{{"7", "1", "1", "7", "0", "1"}}}
	return schema, witness
}

func TestAiurPlonkReceiverCountElision(t *testing.T) {
	schema, witness := aiurCountFixture()
	if err := schema.validate(); err != nil {
		t.Fatal(err)
	}
	if !schema.countElisionSafe() {
		t.Fatal("isolated receiver counts were not recognized")
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
	for _, weight := range []*big.Int{new(big.Int).Sub(scalarModulus(), big.NewInt(1)), new(big.Int).Lsh(big.NewInt(1), 200)} {
		complement := new(big.Int).Sub(big.NewInt(1), weight)
		complement.Mod(complement, scalarModulus())
		witness.Main[0][1], witness.Main[0][4] = weight.String(), complement.String()
		if err := solve(); err != nil {
			t.Fatalf("valid duplicate receivers with arbitrary field weights: %v", err)
		}
	}
	// Every receiver still needs the requested message and a valid active row.
	witness.Main[0][0], witness.Main[0][3] = "8", "8"
	if err := solve(); err == nil {
		t.Fatal("accepted missing receiver message")
	}
	witness.Main[0][0], witness.Main[0][3] = "7", "7"
	witness.Main[0][2], witness.Main[0][5] = "0", "0"
	if err := solve(); err == nil {
		t.Fatal("accepted disabled receivers")
	}
	witness.Main[0][2], witness.Main[0][5] = "1", "1"
	witness.Public[0] = "8"
	if err := solve(); err == nil {
		t.Fatal("accepted changed public statement")
	}
}

func TestAiurPlonkCountElisionRejectsUnsafeCoupling(t *testing.T) {
	cases := []struct {
		name   string
		change func(*aiurSchema)
	}{
		{"message", func(s *aiurSchema) { s.Circuits[0].Lookups[0].Args[2] = 1 }},
		{"push", func(s *aiurSchema) {
			s.Circuits[0].Lookups = append(s.Circuits[0].Lookups, aiurLookup{Count: 1, Args: []int{3, 4, 0}})
		}},
		{"next-row", func(s *aiurSchema) { s.Circuits[0].Nodes[1].Next = true }},
		{"nonlinear", func(s *aiurSchema) {
			c := &s.Circuits[0]
			c.Nodes = append(c.Nodes, aiurNode{Op: "mul", A: 1, B: 1})
			c.Constraints = append(c.Constraints, len(c.Nodes)-1)
		}},
		{"nonhomogeneous", func(s *aiurSchema) {
			c := &s.Circuits[0]
			c.Nodes = append(c.Nodes, aiurNode{Op: "sub", A: 1, B: 3})
			c.Constraints = append(c.Constraints, len(c.Nodes)-1)
		}},
		{"coupled", func(s *aiurSchema) {
			c := &s.Circuits[0]
			c.MainWidth = 4
			c.Nodes = append(c.Nodes, aiurNode{Op: "main", Column: 3})
			second := len(c.Nodes) - 1
			c.Lookups = append(c.Lookups, aiurLookup{Negative: true, Count: second, Args: []int{3, 4, 0}})
			c.Nodes = append(c.Nodes, aiurNode{Op: "sub", A: 1, B: second})
			c.Constraints = append(c.Constraints, len(c.Nodes)-1)
		}},
		{"alias", func(s *aiurSchema) { s.Circuits[0].Lookups = append(s.Circuits[0].Lookups, s.Circuits[0].Lookups[0]) }},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			schema, _ := aiurCountFixture()
			test.change(schema)
			if err := schema.validate(); err != nil {
				t.Fatal(err)
			}
			if schema.countElisionSafe() {
				t.Fatal("unsafe count replacement enabled")
			}
		})
	}
	// Nonlinear constraints trigger the conservative integer-count path even
	// when a modular pair of weights would otherwise balance the public demand.
	schema, witness := aiurCountFixture()
	c := &schema.Circuits[0]
	c.Nodes = append(c.Nodes, aiurNode{Op: "constant", Value: "2"}, aiurNode{Op: "add", A: 1, B: 3}, aiurNode{Op: "sub", A: 1, B: 8}, aiurNode{Op: "mul", A: 9, B: 10})
	c.Constraints = append(c.Constraints, 11)
	if schema.countElisionSafe() {
		t.Fatal("nonlinear count constraint escaped analysis")
	}
	witness.Main[0][1] = new(big.Int).Sub(scalarModulus(), big.NewInt(1)).String()
	witness.Main[0][4] = "2"
	ccs := aiurCompile(t, schema)
	w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err == nil {
		t.Fatal("conservative path accepted negative receiver count")
	}
}

func TestAiurPlonkCountElisionRequiresBooleanPushes(t *testing.T) {
	schema, witness := aiurCountFixture()
	c := &schema.Circuits[0]
	c.Rows = 1
	c.MainWidth = 4
	c.Nodes = append(c.Nodes, aiurNode{Op: "main", Column: 3})
	c.Lookups = append(c.Lookups, aiurLookup{Count: 8, Args: []int{3, 4, 0}})
	witness.Main[0] = []string{"7", "2", "1", "1"}
	if !schema.countElisionSafe() {
		t.Fatal("isolated counts should be safe with constrained requests")
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
	witness.Main[0][1], witness.Main[0][3] = "3", "2"
	if err := solve(); err == nil {
		t.Fatal("accepted a nonboolean request multiplicity")
	}
}

func TestAiurPlonkWeightedRequestsRetainCompleteness(t *testing.T) {
	schema, witness := aiurCountFixture()
	schema.BooleanRequests = false
	c := &schema.Circuits[0]
	c.Rows = 1
	c.MainWidth = 4
	c.Nodes = append(c.Nodes, aiurNode{Op: "main", Column: 3})
	c.Lookups = append(c.Lookups, aiurLookup{Count: 8, Args: []int{3, 4, 0}})
	witness.Main[0] = []string{"7", "3", "1", "2"}
	if schema.countElisionSafe() {
		t.Fatal("weighted requests were treated as boolean")
	}
	ccs := aiurCompile(t, schema)
	w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err != nil {
		t.Fatalf("honest weighted request must prove: %v", err)
	}
}

func TestAiurPlonkCoupledCountsRetainIntegerSemantics(t *testing.T) {
	schema, witness := aiurCountFixture()
	c := &schema.Circuits[0]
	c.Rows = 1
	c.MainWidth = 4
	c.Nodes = append(c.Nodes, aiurNode{Op: "main", Column: 3}, aiurNode{Op: "sub", A: 1, B: 8})
	c.Lookups = append(c.Lookups, aiurLookup{Negative: true, Count: 8, Args: []int{3, 4, 0}})
	c.Constraints = append(c.Constraints, 9)
	if schema.countElisionSafe() {
		t.Fatal("cross-count equality escaped isolation validation")
	}
	half := new(big.Int).ModInverse(big.NewInt(2), scalarModulus()).String()
	witness.Main[0] = []string{"7", half, "1", half}
	ccs := aiurCompile(t, schema)
	w, err := frontend.NewWitness(aiurAssignment(t, schema, witness), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err == nil {
		t.Fatal("accepted modular half-counts under coupled constraints")
	}
}
