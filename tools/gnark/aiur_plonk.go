package main

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/multicommit"
)

const aiurPlonkFormat = "ix-aiur-plonk-v1"
const aiurMaxDomain = 1 << 25

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
	Format       string     `json:"format"`
	Callable     int        `json:"callable"`
	PublicInputs int        `json:"public_inputs"`
	Circuits     []aiurChip `json:"circuits"`
}

type aiurWitness struct {
	Public []string   `json:"public"`
	Main   [][]string `json:"main"`
}

type aiurCircuit struct {
	Public []frontend.Variable `gnark:",public"`
	Main   [][]frontend.Variable
	Schema *aiurSchema `gnark:"-"`
}

func (s *aiurSchema) validate() error {
	if s.Format != aiurPlonkFormat || s.Callable < 0 || s.PublicInputs < 0 || s.PublicInputs > aiurMaxDomain || len(s.Circuits) == 0 {
		return fmt.Errorf("invalid Aiur PLONK header")
	}
	rows, cells := 0, 0
	var slots uint64 = 1
	for _, c := range s.Circuits {
		if c.Rows <= 0 || c.Rows > aiurMaxDomain || c.Rows&(c.Rows-1) != 0 || c.MainWidth <= 0 || c.MainWidth > aiurMaxDomain || c.FixedWidth < 0 || c.FixedWidth > aiurMaxDomain {
			return fmt.Errorf("invalid Aiur circuit capacity")
		}
		rows += c.Rows
		if rows > aiurMaxDomain || c.MainWidth > aiurMaxDomain/c.Rows {
			return fmt.Errorf("Aiur capacity exceeds retained Ignition bound")
		}
		cells += c.Rows * c.MainWidth
		if cells > aiurMaxDomain {
			return fmt.Errorf("Aiur trace cells exceed PLONK capacity")
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
	c := &aiurCircuit{Schema: schema, Public: make([]frontend.Variable, schema.PublicInputs), Main: make([][]frontend.Variable, len(schema.Circuits))}
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
	if len(w.Public) != len(c.Public) || len(w.Main) != len(c.Main) {
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
	return c, nil
}

type aiurMessage struct {
	count    frontend.Variable
	negative bool
	args     []frontend.Variable
}

func (c *aiurCircuit) Define(api frontend.API) error {
	if c.Schema == nil {
		return fmt.Errorf("missing trusted Aiur schema")
	}
	if err := c.Schema.validate(); err != nil {
		return err
	}
	if len(c.Public) != c.Schema.PublicInputs || len(c.Main) != len(c.Schema.Circuits) {
		return fmt.Errorf("Aiur circuit shape differs")
	}
	var committed []frontend.Variable
	committed = append(committed, c.Public...)
	messages := []aiurMessage{{count: 1, args: append([]frontend.Variable{1, c.Schema.Callable}, c.Public...)}}
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
			for _, lookup := range chip.Lookups {
				// Signed direction is trusted schema data; each underlying count must
				// be an unsigned integer, preventing cancellation through negative counts.
				count := values[lookup.Count]
				api.ToBinary(count, 64)
				args := make([]frontend.Variable, len(lookup.Args))
				for j, id := range lookup.Args {
					args[j] = values[id]
				}
				messages = append(messages, aiurMessage{count: count, negative: lookup.Negative, args: args})
			}
		}
	}
	multicommit.WithCommitment(api, func(api frontend.API, gamma frontend.Variable) error {
		beta := aiurLookupBeta(api, gamma)
		var sum frontend.Variable = 0
		for _, message := range messages {
			// Length is a leading coefficient, so different arities cannot collide
			// by appending zero-valued fields to a message.
			var fingerprint frontend.Variable = len(message.args)
			for j := len(message.args) - 1; j >= 0; j-- {
				fingerprint = api.Add(api.Mul(fingerprint, gamma), message.args[j])
			}
			denominator := api.Add(beta, fingerprint)
			inverse := api.Inverse(denominator)
			api.AssertIsEqual(api.Mul(inverse, denominator), 1)
			term := api.Mul(message.count, inverse)
			if message.negative {
				sum = api.Sub(sum, term)
			} else {
				sum = api.Add(sum, term)
			}
		}
		api.AssertIsEqual(sum, 0)
		return nil
	}, committed...)
	return nil
}
