package main

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/emulated"
)

const aiurTerminalFormat = "ix-aiur-plonk-terminal-v1"
const aiurTerminalOutputs = 18

type aiurPairing struct {
	Curve    string     `json:"curve"`
	Encoding string     `json:"encoding"`
	G2       [][]string `json:"g2"`
}

func (s *aiurSchema) validateOutputContract() error {
	switch s.Format {
	case aiurPlonkFormat:
		if s.PrivateOutputs != 0 || s.Pairing != nil {
			return fmt.Errorf("generic Aiur schema cannot carry terminal outputs or pairing")
		}
	case aiurTerminalFormat:
		if s.PublicInputs != 2 || s.PrivateOutputs != aiurTerminalOutputs || s.Pairing == nil {
			return fmt.Errorf("terminal Aiur schema requires two public fields and eighteen private pairing outputs")
		}
		if _, err := s.Pairing.anchors(); err != nil {
			return err
		}
	default:
		return fmt.Errorf("unsupported Aiur PLONK format")
	}
	return nil
}

func (p *aiurPairing) anchors() ([2]nativeG2, error) {
	var anchors [2]nativeG2
	if p.Curve != "bn254" || p.Encoding != "affine-u80-v1" || len(p.G2) != 2 {
		return anchors, fmt.Errorf("invalid Aiur pairing configuration")
	}
	for i, coordinates := range p.G2 {
		if len(coordinates) != 4 {
			return anchors, fmt.Errorf("Aiur G2 anchor needs four coordinates")
		}
		encoded := make([]byte, 4*baseBytes)
		for j, text := range coordinates {
			value, ok := new(big.Int).SetString(text, 10)
			if !ok || value.Sign() < 0 || value.Cmp(baseModulus()) >= 0 || value.String() != text {
				return anchors, fmt.Errorf("Aiur G2 coordinate is not canonical decimal Fq")
			}
			value.FillBytes(encoded[j*baseBytes : (j+1)*baseBytes])
		}
		point, err := decodeG2(encoded)
		if err != nil {
			return anchors, fmt.Errorf("Aiur G2 anchor %d: %w", i, err)
		}
		anchors[i] = point
	}
	return anchors, nil
}

func aiurCoordinate(api frontend.API, field *emulated.Field[baseField], words []frontend.Variable) *emulated.Element[baseField] {
	bits := make([]frontend.Variable, 0, 254)
	for i, word := range words {
		width := 80
		if i == 3 {
			width = 14
		}
		bits = append(bits, api.ToBinary(word, width)...)
	}
	coordinate := field.FromBits(bits...)
	field.AssertIsInRange(coordinate)
	return coordinate
}

func (p *aiurPairing) constrain(api frontend.API, outputs []frontend.Variable) error {
	if len(outputs) != aiurTerminalOutputs {
		return fmt.Errorf("Aiur pairing output width differs")
	}
	anchors, err := p.anchors()
	if err != nil {
		return err
	}
	field, err := emulated.NewField[baseField](api)
	if err != nil {
		return err
	}
	pairing, err := newPairing(api)
	if err != nil {
		return err
	}
	points := make([]*circuitG1, 2)
	for i := range points {
		words := outputs[9*i : 9*(i+1)]
		infinity := words[8]
		api.AssertIsBoolean(infinity)
		for _, word := range words[:8] {
			api.AssertIsEqual(api.Mul(infinity, word), 0)
		}
		x := aiurCoordinate(api, field, words[:4])
		y := aiurCoordinate(api, field, words[4:8])
		api.AssertIsEqual(infinity, api.And(field.IsZero(x), field.IsZero(y)))
		points[i] = &circuitG1{X: *x, Y: *y}
		// The generator gives the infinity branch a valid curve-check input;
		// the pairing receives the original, constrained zero coordinates.
		safe := circuitG1{X: *field.Select(infinity, field.NewElement(1), x), Y: *field.Select(infinity, field.NewElement(2), y)}
		pairing.AssertIsOnG1(&safe)
	}
	left := newCircuitG2Fixed(anchors[0])
	right := newCircuitG2Fixed(anchors[1])
	return pairing.PairingCheck(points, []*circuitG2{&left, &right})
}
