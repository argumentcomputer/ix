package main

import (
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	blsfp "github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark/frontend"
	swbls "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/math/emulated"
)

const aiurTerminalOutputs = 18
const aiurTerminalOutputsBLS = 22

type aiurPairing struct {
	Curve    string     `json:"curve"`
	Encoding string     `json:"encoding"`
	G2       [][]string `json:"g2"`
}

func aiurTerminalOutputsFor(curve ecc.ID) (int, error) {
	switch curve {
	case ecc.BN254:
		return aiurTerminalOutputs, nil
	case ecc.BLS12_381:
		return aiurTerminalOutputsBLS, nil
	default:
		return 0, fmt.Errorf("unsupported Aiur curve %s", curve)
	}
}

func aiurScalarModulusFor(curve ecc.ID) (*big.Int, error) {
	switch curve {
	case ecc.BN254:
		return scalarModulus(), nil
	case ecc.BLS12_381:
		return blsfr.Modulus(), nil
	default:
		return nil, fmt.Errorf("unsupported Aiur curve %s", curve)
	}
}

func (p *aiurPairing) curveID() (ecc.ID, error) {
	switch p.Curve {
	case "bn254":
		return ecc.BN254, nil
	case "bls12-381":
		return ecc.BLS12_381, nil
	default:
		return ecc.UNKNOWN, fmt.Errorf("unsupported Aiur pairing curve %q", p.Curve)
	}
}

func (p *aiurPairing) outputCount() (int, error) {
	id, err := p.curveID()
	if err != nil {
		return 0, err
	}
	return aiurTerminalOutputsFor(id)
}

func (p *aiurPairing) scalarModulus() (*big.Int, error) {
	id, err := p.curveID()
	if err != nil {
		return nil, err
	}
	return aiurScalarModulusFor(id)
}

func (p *aiurPairing) validate() error {
	switch p.Curve {
	case "bn254":
		_, err := p.anchors()
		return err
	case "bls12-381":
		_, err := p.anchorsBLS()
		return err
	default:
		return fmt.Errorf("invalid Aiur pairing configuration")
	}
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

func (p *aiurPairing) anchorsBLS() ([2]blsG2, error) {
	var anchors [2]blsG2
	if p.Curve != "bls12-381" || p.Encoding != "affine-u80-v1" || len(p.G2) != 2 {
		return anchors, fmt.Errorf("invalid Aiur BLS12-381 pairing configuration")
	}
	modulus := blsfp.Modulus()
	for i, coordinates := range p.G2 {
		if len(coordinates) != 4 {
			return anchors, fmt.Errorf("Aiur BLS12-381 G2 anchor needs four coordinates")
		}
		var point blsG2
		elems := []*blsfp.Element{&point.X.A0, &point.X.A1, &point.Y.A0, &point.Y.A1}
		for j, text := range coordinates {
			value, ok := new(big.Int).SetString(text, 10)
			if !ok || value.Sign() < 0 || value.Cmp(modulus) >= 0 || value.String() != text {
				return anchors, fmt.Errorf("Aiur BLS12-381 G2 coordinate is not canonical decimal Fq")
			}
			var raw [blsBaseBytes]byte
			value.FillBytes(raw[:])
			if err := elems[j].SetBytesCanonical(raw[:]); err != nil {
				return anchors, fmt.Errorf("Aiur BLS12-381 G2 anchor %d coordinate %d: %w", i, j, err)
			}
		}
		if point.IsInfinity() || !point.IsOnCurve() || !point.IsInSubGroup() {
			return anchors, fmt.Errorf("Aiur BLS12-381 G2 anchor %d is not a valid G2 subgroup point", i)
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

// aiurCoordinateBLS decodes a 381-bit BLS12-381 Fq coordinate from five
// little-endian limbs (four 80-bit limbs + one 61-bit top limb = 381 bits,
// matching CurveOpsPure Limb5) and enforces canonical Fq range (< p).
func aiurCoordinateBLS(api frontend.API, field *emulated.Field[blsBaseField], words []frontend.Variable) *emulated.Element[blsBaseField] {
	bits := make([]frontend.Variable, 0, 381)
	for i, word := range words {
		width := 80
		if i == 4 {
			width = 61
		}
		bits = append(bits, api.ToBinary(word, width)...)
	}
	coordinate := field.FromBits(bits...)
	field.AssertIsInRange(coordinate)
	return coordinate
}

func (p *aiurPairing) constrain(api frontend.API, outputs []frontend.Variable) error {
	switch p.Curve {
	case "bn254":
		return p.constrainBN254(api, outputs)
	case "bls12-381":
		return p.constrainBLS(api, outputs)
	default:
		return fmt.Errorf("invalid Aiur pairing configuration")
	}
}

func (p *aiurPairing) constrainBN254(api frontend.API, outputs []frontend.Variable) error {
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

func (p *aiurPairing) constrainBLS(api frontend.API, outputs []frontend.Variable) error {
	if len(outputs) != aiurTerminalOutputsBLS {
		return fmt.Errorf("Aiur BLS12-381 pairing output width differs")
	}
	anchors, err := p.anchorsBLS()
	if err != nil {
		return err
	}
	field, err := emulated.NewField[blsBaseField](api)
	if err != nil {
		return err
	}
	pairing, err := swbls.NewPairing(api)
	if err != nil {
		return err
	}
	_, _, g1Gen, _ := bls.Generators()
	gen := swbls.NewG1Affine(g1Gen)
	points := make([]*blsCircuitG1, 2)
	for i := range points {
		words := outputs[11*i : 11*(i+1)]
		infinity := words[10]
		api.AssertIsBoolean(infinity)
		for _, word := range words[:10] {
			api.AssertIsEqual(api.Mul(infinity, word), 0)
		}
		x := aiurCoordinateBLS(api, field, words[:5])
		y := aiurCoordinateBLS(api, field, words[5:10])
		api.AssertIsEqual(infinity, api.And(field.IsZero(x), field.IsZero(y)))
		points[i] = &blsCircuitG1{X: *x, Y: *y}
		// The BLS12-381 G1 generator gives the infinity branch a valid
		// on-curve and prime-order subgroup input; the pairing receives the
		// original constrained zero coordinates.
		safe := blsCircuitG1{X: *field.Select(infinity, &gen.X, x), Y: *field.Select(infinity, &gen.Y, y)}
		pairing.AssertIsOnG1(&safe)
	}
	left := swbls.NewG2AffineFixed(anchors[0])
	right := swbls.NewG2AffineFixed(anchors[1])
	return pairing.PairingCheck(points, []*blsCircuitG2{&left, &right})
}
