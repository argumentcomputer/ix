//go:build plonk || !groth16

package main

// Loader for the terminal constraint system that Lean builds and checks
// (`plonk_export`, `ix-aiur-scs-v1`, docs/aiur-plonk-lean-backend.md §7).
//
// The file fixes every gate, coefficient, selector and wire role. The loader
// makes exactly one AddPlonkConstraint per file gate, in file order, with the
// file's coefficients; the only constraints it does not read from the file
// are those of gnark's PairingCheck gadget on the 18 output wires and of the
// single BSB22 commitment (multicommit) over the file's commit list, whose
// output is the file's γ wire.
//
// Wires that are not inputs are prover hints (no constraints), created in
// aiur_plonk_scs_wires.go from the file's hint table: "solve gate i" (the
// gate is affine in the wire), "bit y of wire x", or zero.

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"log"
	"math/big"
	"os"

	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/multicommit"
)

const aiurScsMagic = "ixscs001"
const aiurScsGateBytes = 26
const aiurScsHintBytes = 9

const (
	aiurScsInput = iota
	aiurScsSolve
	aiurScsBit
	aiurScsChallenge
	aiurScsFree
)

type aiurScsTable struct {
	Name        string
	CellBase    uint64
	Rows, Width uint32
}

// aiurScs is a validated `ix-aiur-scs-v1` file. Gates and hints stay in
// their packed encodings and are decoded on access.
type aiurScs struct {
	Publics, Wires, Gates, Pre int
	Gamma, Beta                uint32
	Cells                      int
	Outputs                    []uint32
	Coeffs                     []big.Int
	Commits                    []uint32
	Tables                     []aiurScsTable
	gates, hints               []byte
}

type aiurScsGate struct {
	A, B, C    uint32
	Sel        uint8
	Al, Be, Om uint32
	QC         int8
}

func (s *aiurScs) gate(i int) aiurScsGate {
	g := s.gates[aiurScsGateBytes*i:]
	return aiurScsGate{
		A: binary.LittleEndian.Uint32(g[0:]), B: binary.LittleEndian.Uint32(g[4:]), C: binary.LittleEndian.Uint32(g[8:]),
		Sel: g[12],
		Al:  binary.LittleEndian.Uint32(g[13:]), Be: binary.LittleEndian.Uint32(g[17:]), Om: binary.LittleEndian.Uint32(g[21:]),
		QC: int8(g[25]),
	}
}

func (s *aiurScs) hint(x uint32) (kind uint8, a, b uint32) {
	h := s.hints[aiurScsHintBytes*int(x):]
	return h[0], binary.LittleEndian.Uint32(h[1:]), binary.LittleEndian.Uint32(h[5:])
}

// readAiurScs reads the file, checks its SHA-256 against the pinned digest
// and validates it completely before anything is built from it.
func readAiurScs(path, digest string) (*aiurScs, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != digest {
		return nil, fmt.Errorf("Aiur SCS file differs from its pinned SHA-256")
	}
	return parseAiurScs(data)
}

func parseAiurScs(data []byte) (*aiurScs, error) {
	if len(data) < 88 || string(data[:8]) != aiurScsMagic {
		return nil, fmt.Errorf("not an ix-aiur-scs-v1 file")
	}
	var h [10]uint64
	for i := range h {
		h[i] = binary.LittleEndian.Uint64(data[8+8*i:])
	}
	publics, outputs, wires, gates, pre, commits, gamma, beta, coeffs, tables := h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8], h[9]
	const limit = 1 << 32
	if wires == 0 || wires >= limit || gates >= limit || coeffs >= limit || commits >= limit || tables >= 1<<16 ||
		outputs != aiurTerminalOutputs || publics == 0 || publics > aiurMaxPublic || pre > gates || gamma >= wires || beta >= wires {
		return nil, fmt.Errorf("invalid Aiur SCS header")
	}
	body := 88 + 4*outputs + 32*coeffs + aiurScsGateBytes*gates + 4*commits + aiurScsHintBytes*wires
	if uint64(len(data)) < body {
		return nil, fmt.Errorf("truncated Aiur SCS file")
	}
	s := &aiurScs{Publics: int(publics), Wires: int(wires), Gates: int(gates), Pre: int(pre), Gamma: uint32(gamma), Beta: uint32(beta)}
	o := uint64(88)
	inRange := func(x uint32) bool { return uint64(x) < wires }
	s.Outputs = make([]uint32, outputs)
	for i := range s.Outputs {
		s.Outputs[i] = binary.LittleEndian.Uint32(data[o:])
		if !inRange(s.Outputs[i]) {
			return nil, fmt.Errorf("Aiur SCS output wire out of range")
		}
		o += 4
	}
	r := scalarModulus()
	s.Coeffs = make([]big.Int, coeffs)
	var le [32]byte
	for i := range s.Coeffs {
		for j := 0; j < 32; j++ {
			le[31-j] = data[o+uint64(j)]
		}
		s.Coeffs[i].SetBytes(le[:])
		if s.Coeffs[i].Sign() == 0 || s.Coeffs[i].Cmp(r) >= 0 {
			return nil, fmt.Errorf("Aiur SCS coefficient %d is zero or not canonical", i)
		}
		o += 32
	}
	s.gates = data[o : o+aiurScsGateBytes*gates]
	o += aiurScsGateBytes * gates
	for i := 0; i < s.Gates; i++ {
		g := s.gate(i)
		if !inRange(g.A) || !inRange(g.B) || !inRange(g.C) || g.Sel > 15 ||
			uint64(g.Al) >= coeffs || uint64(g.Be) >= coeffs || uint64(g.Om) >= coeffs {
			return nil, fmt.Errorf("Aiur SCS gate %d out of range", i)
		}
	}
	s.Commits = make([]uint32, commits)
	seen := make([]bool, wires)
	for i := range s.Commits {
		x := binary.LittleEndian.Uint32(data[o:])
		if !inRange(x) || seen[x] {
			return nil, fmt.Errorf("Aiur SCS commit list is out of range or repeats a wire")
		}
		seen[x] = true
		s.Commits[i] = x
		o += 4
	}
	s.hints = data[o : o+aiurScsHintBytes*wires]
	o += aiurScsHintBytes * wires
	challenges := 0
	for x := uint32(0); uint64(x) < wires; x++ {
		kind, a, b := s.hint(x)
		switch kind {
		case aiurScsInput:
			if int(x) != s.Cells {
				return nil, fmt.Errorf("Aiur SCS input wires are not a prefix")
			}
			s.Cells++
		case aiurScsSolve:
			if uint64(a) >= gates {
				return nil, fmt.Errorf("Aiur SCS solve hint of wire %d names no gate", x)
			}
			g := s.gate(int(a))
			if g.A != x && g.B != x && g.C != x {
				return nil, fmt.Errorf("Aiur SCS solve hint of wire %d names a gate without it", x)
			}
		case aiurScsBit:
			if !inRange(a) || b >= 256 {
				return nil, fmt.Errorf("Aiur SCS bit hint of wire %d out of range", x)
			}
		case aiurScsChallenge:
			if x != s.Gamma {
				return nil, fmt.Errorf("Aiur SCS challenge hint on a wire other than γ")
			}
			challenges++
		case aiurScsFree:
		default:
			return nil, fmt.Errorf("Aiur SCS wire %d has an unknown kind", x)
		}
	}
	if challenges != 1 || s.Cells < s.Publics {
		return nil, fmt.Errorf("Aiur SCS needs one γ and its publics among the inputs")
	}
	for _, x := range append(append([]uint32{}, s.Outputs...), s.Commits...) {
		if int(x) >= s.Cells {
			return nil, fmt.Errorf("Aiur SCS outputs and commits must be input wires")
		}
	}
	for t := uint64(0); t < tables; t++ {
		if uint64(len(data)) < o+2 {
			return nil, fmt.Errorf("truncated Aiur SCS table section")
		}
		n := uint64(binary.LittleEndian.Uint16(data[o:]))
		o += 2
		if uint64(len(data)) < o+n+16 {
			return nil, fmt.Errorf("truncated Aiur SCS table section")
		}
		tb := aiurScsTable{Name: string(data[o : o+n])}
		o += n
		tb.CellBase = binary.LittleEndian.Uint64(data[o:])
		tb.Rows = binary.LittleEndian.Uint32(data[o+8:])
		tb.Width = binary.LittleEndian.Uint32(data[o+12:])
		o += 16
		if tb.CellBase+uint64(tb.Rows)*uint64(tb.Width) > uint64(s.Cells) {
			return nil, fmt.Errorf("Aiur SCS table %q exceeds the input wires", tb.Name)
		}
		s.Tables = append(s.Tables, tb)
	}
	if o != uint64(len(data)) {
		return nil, fmt.Errorf("trailing Aiur SCS bytes")
	}
	return s, nil
}

// aiurScsCircuit: wire i < Publics is Public[i]; input wire i ≥ Publics is
// Cells[i − Publics].
type aiurScsCircuit struct {
	Public  []frontend.Variable `gnark:",public"`
	Cells   []frontend.Variable
	Scs     *aiurScs     `gnark:"-"`
	Pairing *aiurPairing `gnark:"-"`
	// When set (one entry per file wire), Define records the VID of every
	// wire it created and leaves the other entries unchanged.
	VIDs []uint32 `gnark:"-"`
}

func newAiurScsCircuit(s *aiurScs, pairing *aiurPairing) *aiurScsCircuit {
	return &aiurScsCircuit{
		Public: make([]frontend.Variable, s.Publics), Cells: make([]frontend.Variable, s.Cells-s.Publics),
		Scs: s, Pairing: pairing,
	}
}

func (c *aiurScsCircuit) Define(api frontend.API) error {
	s := c.Scs
	if s == nil || c.Pairing == nil {
		return fmt.Errorf("missing Aiur SCS or pairing configuration")
	}
	if api.Compiler().Field().Cmp(scalarModulus()) != 0 {
		return fmt.Errorf("Aiur SCS requires BN254 Fr")
	}
	if len(c.Public) != s.Publics || len(c.Cells) != s.Cells-s.Publics {
		return fmt.Errorf("Aiur SCS circuit shape differs")
	}
	plonkAPI, ok := api.(frontend.PlonkAPI)
	if !ok {
		return fmt.Errorf("Aiur SCS requires a PLONK builder")
	}
	v := make([]frontend.Variable, s.Wires)
	copy(v, c.Public)
	copy(v[s.Publics:], c.Cells)
	// Every non-input wire is created by w as an unconstrained prover hint.
	w := newAiurScsWires(api, s, v)
	sel := func(g aiurScsGate, bit uint) int { return int(g.Sel>>bit) & 1 }
	add := func(i int) error {
		g := s.gate(i)
		var xs [3]frontend.Variable
		for k, y := range []uint32{g.A, g.B, g.C} {
			var err error
			if xs[k], err = w.wire(y, i); err != nil {
				return err
			}
		}
		plonkAPI.AddPlonkConstraint(api.Mul(xs[0], &s.Coeffs[g.Al]), api.Mul(xs[1], &s.Coeffs[g.Be]), api.Mul(xs[2], &s.Coeffs[g.Om]),
			sel(g, 0), sel(g, 1), sel(g, 2), sel(g, 3), int(g.QC))
		return nil
	}
	for i := 0; i < s.Pre; i++ {
		if err := add(i); err != nil {
			return err
		}
	}
	outputs := make([]frontend.Variable, len(s.Outputs))
	for i, x := range s.Outputs {
		outputs[i] = v[x]
	}
	// The pairing gadget registers its range-check commitment before
	// multicommit closes, so the file's commit list shares the one BSB22
	// commitment, and the file's callback runs first (it receives the
	// commitment itself, not a power of it).
	if err := c.Pairing.constrain(api, outputs); err != nil {
		return err
	}
	committed := make([]frontend.Variable, len(s.Commits))
	for i, x := range s.Commits {
		committed[i] = v[x]
	}
	var postErr error
	multicommit.WithCommitment(api, func(api frontend.API, commitment frontend.Variable) error {
		if err := w.post(api, commitment); err != nil {
			postErr = err
			return err
		}
		for i := s.Pre; i < s.Gates; i++ {
			if err := add(i); err != nil {
				postErr = err
				return err
			}
		}
		log.Printf("aiur-scs hints: %s", w.stats())
		if c.VIDs != nil {
			c.recordVIDs(api, v)
		}
		return nil
	}, committed...)
	return postErr
}

func (c *aiurScsCircuit) recordVIDs(api frontend.API, v []frontend.Variable) {
	for x, y := range v {
		if y == nil {
			continue
		}
		if t, ok := api.Compiler().ToCanonicalVariable(y).(constraint.Term); ok {
			c.VIDs[x] = t.VID
		}
	}
}

// readAiurScsPairing reads the terminal's pairing configuration (the
// `pairing` object of the terminal schema) and checks its SHA-256.
func readAiurScsPairing(path, digest string) (*aiurPairing, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != digest {
		return nil, fmt.Errorf("Aiur pairing configuration differs from its pinned SHA-256")
	}
	var p aiurPairing
	if err := decodeReader(bytes.NewReader(data), &p); err != nil {
		return nil, err
	}
	if _, err := p.anchors(); err != nil {
		return nil, err
	}
	return &p, nil
}
