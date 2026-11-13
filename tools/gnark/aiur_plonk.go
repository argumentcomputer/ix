package main

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/multicommit"
)

const aiurPlonkFormat = "ix-aiur-plonk-v1"

// The next power-of-two domain would exceed Ignition's 100,800,000 powers.
// Parameter loading independently requires the exact domain+3 opening powers.
const aiurMaxDomain = 1 << 26

type aiurNode struct {
	Op     string `json:"op"`
	Value  string `json:"value,omitempty"`
	Column int    `json:"column,omitempty"`
	Next   bool   `json:"next,omitempty"`
	A      int    `json:"a,omitempty"`
	B      int    `json:"b,omitempty"`
}

type aiurLookup struct {
	Negative bool  `json:"negative"`
	Count    int   `json:"count"`
	Args     []int `json:"args"`
}

type aiurChip struct {
	Name        string       `json:"name"`
	Rows        int          `json:"rows"`
	MainWidth   int          `json:"main_width"`
	FixedWidth  int          `json:"fixed_width"`
	Fixed       []string     `json:"fixed"`
	Nodes       []aiurNode   `json:"nodes"`
	Constraints []int        `json:"constraints"`
	Lookups     []aiurLookup `json:"lookups"`
}

type aiurSchema struct {
	Format          string       `json:"format"`
	Callable        int          `json:"callable"`
	PublicInputs    int          `json:"public_inputs"`
	PrivateOutputs  int          `json:"private_outputs,omitempty"`
	Pairing         *aiurPairing `json:"pairing,omitempty"`
	BooleanRequests bool         `json:"boolean_requests,omitempty"`
	Circuits        []aiurChip   `json:"circuits"`
}

type aiurWitness struct {
	Public         []string   `json:"public"`
	Main           [][]string `json:"main"`
	PrivateOutputs []string   `json:"private_outputs,omitempty"`
}

type aiurCircuit struct {
	Public         []frontend.Variable `gnark:",public"`
	Main           [][]frontend.Variable
	PrivateOutputs []frontend.Variable
	Schema         *aiurSchema `gnark:"-"`
}

func (s *aiurSchema) validate() error {
	if err := s.validateOutputContract(); err != nil {
		return err
	}
	if s.Callable < 0 || s.PublicInputs < 0 || s.PublicInputs > aiurMaxDomain || len(s.Circuits) == 0 {
		return fmt.Errorf("invalid Aiur PLONK header")
	}
	rows, cells := 0, s.PrivateOutputs
	var slots uint64 = 1
	for _, c := range s.Circuits {
		if c.Rows <= 0 || c.Rows > aiurMaxDomain || c.Rows&(c.Rows-1) != 0 || c.MainWidth <= 0 || c.MainWidth > aiurMaxDomain || c.FixedWidth < 0 || c.FixedWidth > aiurMaxDomain {
			return fmt.Errorf("invalid Aiur circuit capacity")
		}
		rows += c.Rows
		if rows > aiurMaxDomain || c.MainWidth > aiurMaxDomain/c.Rows {
			return fmt.Errorf("Aiur capacity exceeds the Ignition ceremony bound")
		}
		cells += c.Rows * c.MainWidth
		if cells > aiurMaxDomain {
			return fmt.Errorf("Aiur trace and private-output cells exceed PLONK capacity")
		}
		if c.FixedWidth > aiurMaxDomain/c.Rows || len(c.Fixed) != c.Rows*c.FixedWidth {
			return fmt.Errorf("invalid authenticated fixed matrix")
		}
		if uint64(len(c.Lookups)) > (^uint64(0)-slots)/uint64(c.Rows) {
			return fmt.Errorf("lookup budget overflow")
		}
		slots += uint64(c.Rows) * uint64(len(c.Lookups))
		for _, v := range c.Fixed {
			if _, err := canonical(v, scalarModulus()); err != nil {
				return err
			}
		}
		for i, n := range c.Nodes {
			operand := func(id int) bool { return id >= 0 && id < i }
			switch n.Op {
			case "constant":
				if _, err := canonical(n.Value, scalarModulus()); err != nil {
					return err
				}
			case "main":
				if n.Column < 0 || n.Column >= c.MainWidth {
					return fmt.Errorf("main column out of range")
				}
			case "fixed":
				if n.Column < 0 || n.Column >= c.FixedWidth {
					return fmt.Errorf("fixed column out of range")
				}
			case "first", "last", "transition":
			case "add", "sub", "mul":
				if !operand(n.A) || !operand(n.B) {
					return fmt.Errorf("non-topological expression")
				}
			case "neg":
				if !operand(n.A) {
					return fmt.Errorf("non-topological expression")
				}
			default:
				return fmt.Errorf("unsupported Aiur expression %q", n.Op)
			}
		}
		root := func(id int) bool { return id >= 0 && id < len(c.Nodes) }
		for _, id := range c.Constraints {
			if !root(id) {
				return fmt.Errorf("constraint index out of range")
			}
		}
		for _, l := range c.Lookups {
			if !root(l.Count) || len(l.Args) < 2 {
				return fmt.Errorf("invalid lookup")
			}
			for _, id := range l.Args {
				if !root(id) {
					return fmt.Errorf("lookup index out of range")
				}
			}
		}
	}
	// At most 2^64 slots, each with a 64-bit unsigned multiplicity. Thus the
	// integer sum is below 2^128, far below the BN254 scalar characteristic.
	return nil
}

func newAiurCircuit(schema *aiurSchema) (*aiurCircuit, error) {
	if err := schema.validate(); err != nil {
		return nil, err
	}
	c := &aiurCircuit{Schema: schema, Public: make([]frontend.Variable, schema.PublicInputs), Main: make([][]frontend.Variable, len(schema.Circuits)), PrivateOutputs: make([]frontend.Variable, schema.PrivateOutputs)}
	for i, chip := range schema.Circuits {
		c.Main[i] = make([]frontend.Variable, chip.Rows*chip.MainWidth)
	}
	return c, nil
}

func assignAiur(schema *aiurSchema, w *aiurWitness) (*aiurCircuit, error) {
	c, err := newAiurCircuit(schema)
	if err != nil {
		return nil, err
	}
	if len(w.Public) != len(c.Public) || len(w.Main) != len(c.Main) || len(w.PrivateOutputs) != len(c.PrivateOutputs) {
		return nil, fmt.Errorf("Aiur witness shape differs")
	}
	convert := func(dst []frontend.Variable, src []string) error {
		if len(dst) != len(src) {
			return fmt.Errorf("Aiur witness capacity differs")
		}
		for i, v := range src {
			x, err := canonical(v, scalarModulus())
			if err != nil {
				return err
			}
			dst[i] = x
		}
		return nil
	}
	if err := convert(c.Public, w.Public); err != nil {
		return nil, err
	}
	for i := range c.Main {
		if err := convert(c.Main[i], w.Main[i]); err != nil {
			return nil, err
		}
	}
	if err := convert(c.PrivateOutputs, w.PrivateOutputs); err != nil {
		return nil, err
	}
	return c, nil
}

func (c *aiurCircuit) Define(api frontend.API) error {
	if api.Compiler().Field().Cmp(scalarModulus()) != 0 {
		return fmt.Errorf("Aiur PLONK requires BN254 Fr")
	}
	if c.Schema == nil {
		return fmt.Errorf("missing trusted Aiur schema")
	}
	if err := c.Schema.validate(); err != nil {
		return err
	}
	if len(c.Public) != c.Schema.PublicInputs || len(c.Main) != len(c.Schema.Circuits) || len(c.PrivateOutputs) != c.Schema.PrivateOutputs {
		return fmt.Errorf("Aiur circuit shape differs")
	}
	elideCounts := c.Schema.countElisionSafe()
	var committed []frontend.Variable
	committed = append(committed, c.Public...)
	root := append([]frontend.Variable{1, c.Schema.Callable}, c.Public...)
	root = append(root, c.PrivateOutputs...)
	messages := []aiurMessageGroup{{count: 1, args: [][]frontend.Variable{root}}}
	for i, chip := range c.Schema.Circuits {
		if len(c.Main[i]) != chip.Rows*chip.MainWidth {
			return fmt.Errorf("Aiur main capacity differs")
		}
		committed = append(committed, c.Main[i]...)
		fixed := make([]*big.Int, len(chip.Fixed))
		for j, v := range chip.Fixed {
			fixed[j], _ = canonical(v, scalarModulus())
		}
		for row := 0; row < chip.Rows; row++ {
			values := make([]frontend.Variable, len(chip.Nodes))
			for id, n := range chip.Nodes {
				at := row
				if n.Next {
					at = (row + 1) % chip.Rows
				}
				switch n.Op {
				case "constant":
					values[id], _ = canonical(n.Value, scalarModulus())
				case "main":
					values[id] = c.Main[i][at*chip.MainWidth+n.Column]
				case "fixed":
					values[id] = fixed[at*chip.FixedWidth+n.Column]
				case "first":
					values[id] = 0
					if row == 0 {
						values[id] = 1
					}
				case "last":
					values[id] = 0
					if row == chip.Rows-1 {
						values[id] = 1
					}
				case "transition":
					values[id] = 0
					if row != chip.Rows-1 {
						values[id] = 1
					}
				case "add":
					values[id] = api.Add(values[n.A], values[n.B])
				case "sub":
					values[id] = api.Sub(values[n.A], values[n.B])
				case "mul":
					values[id] = api.Mul(values[n.A], values[n.B])
				case "neg":
					values[id] = api.Neg(values[n.A])
				}
			}
			for _, id := range chip.Constraints {
				api.AssertIsEqual(values[id], 0)
			}
			checkedCounts := make(map[int]bool)
			type groupKey struct {
				count    int
				negative bool
			}
			groups := make(map[groupKey]int)
			for _, lookup := range chip.Lookups {
				count := values[lookup.Count]
				if !elideCounts && !checkedCounts[lookup.Count] {
					api.ToBinary(count, 64)
					checkedCounts[lookup.Count] = true
				} else if elideCounts && !lookup.Negative && !checkedCounts[lookup.Count] {
					api.AssertIsBoolean(count)
					checkedCounts[lookup.Count] = true
				}
				args := make([]frontend.Variable, len(lookup.Args))
				for j, id := range lookup.Args {
					args[j] = values[id]
				}
				key := groupKey{count: lookup.Count, negative: lookup.Negative}
				if index, ok := groups[key]; ok {
					messages[index].args = append(messages[index].args, args)
				} else {
					groups[key] = len(messages)
					messages = append(messages, aiurMessageGroup{count: count, negative: lookup.Negative, args: [][]frontend.Variable{args}})
				}
			}
		}
	}
	committed = append(committed, c.PrivateOutputs...)
	// Emulated arithmetic registers deferred range checks before the shared
	// multicommit callback closes its collection of committed variables.
	if c.Schema.Pairing != nil {
		if err := c.Schema.Pairing.constrain(api, c.PrivateOutputs); err != nil {
			return err
		}
	}
	multicommit.WithCommitment(api, func(api frontend.API, gamma frontend.Variable) error {
		return aiurLogUp(api, gamma, messages)
	}, committed...)
	return nil
}
