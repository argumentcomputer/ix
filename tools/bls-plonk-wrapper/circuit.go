package main

import (
	"encoding/binary"
	"fmt"
	"math/big"

	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/bits"
	"github.com/consensys/gnark/std/math/cmp"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
)

type wrapperCircuit struct {
	Claim    [2]frontend.Variable `gnark:",public"`
	Points   []sw.G1Affine
	Deferred [2]sw.G1Affine
	Values   []frontend.Variable
	Profile  *profile `gnark:"-"`
}

func scalarBytes(api frontend.API, u *uints.BinaryField[uints.U32], v frontend.Variable) []uints.U8 {
	b := bits.ToBinary(api, v, bits.WithNbDigits(256))
	out := make([]uints.U8, 32)
	for i := range out {
		out[i] = u.Bytes.FromBits(b[8*i : 8*i+8]...)
	}
	return out
}

func pointBytes(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[sw.BaseField], point *sw.G1Affine) []uints.U8 {
	f.AssertIsInRange(&point.X)
	f.AssertIsInRange(&point.Y)
	x := f.ToBitsCanonical(&point.X)
	y := f.ToBitsCanonical(&point.Y)
	half := new(big.Int).Rsh(new(big.Int).Set(fp.Modulus()), 1)
	bound := make([]frontend.Variable, len(y))
	for i := range bound {
		bound[i] = half.Bit(i)
	}
	sign := cmp.IsLessBinary(api, bound, y)
	infinity := api.And(f.IsZero(&point.X), f.IsZero(&point.Y))
	for len(x) < 384 {
		x = append(x, 0)
	}
	out := make([]uints.U8, 48)
	for i := range out {
		out[47-i] = u.Bytes.FromBits(x[8*i : 8*i+8]...)
	}
	out[0] = u.ByteValueOf(api.Add(u.Value(out[0]), 128, api.Mul(64, infinity), api.Mul(32, sign)))
	return out
}

func constantU64(value uint64) []uints.U8 {
	var bytes [8]byte
	binary.LittleEndian.PutUint64(bytes[:], value)
	return uints.NewU8Array(bytes[:])
}

func littleEndian(api frontend.API, u *uints.BinaryField[uints.U32], bytes []uints.U8) frontend.Variable {
	var value frontend.Variable = 0
	for i := len(bytes) - 1; i >= 0; i-- {
		value = api.Add(api.Mul(value, 256), u.Value(bytes[i]))
	}
	return value
}

func (c *wrapperCircuit) challenges(api frontend.API, u *uints.BinaryField[uints.U32], encoded [][]uints.U8, publics []frontend.Variable) []frontend.Variable {
	p := c.Profile
	seed, _ := unhex(p.Seed, -1)
	t := newTranscript(api, u, seed)
	field := func(v frontend.Variable) { t.observe(scalarBytes(api, u, v)) }
	commitment := func(round int) {
		t.observe(constantU64(2))
		for i := 0; i < 2; i++ {
			m := p.Matrices[2*round+i]
			t.observe(constantU64(uint64(m.Width)))
			for j := 0; j < m.Width; j++ {
				t.observe(encoded[m.PointOffset+j])
			}
		}
	}
	field(2)
	for _, circuit := range p.Circuits {
		for _, value := range circuit.Shape {
			field(value)
		}
	}
	field(1)
	field(1)
	commitment(3)
	commitment(0)
	for _, circuit := range p.Circuits {
		field(circuit.LogDegree)
	}
	field(23)
	for i, value := range publics {
		field(4)
		field(94)
		field(1)
		field(i)
		field(value)
	}
	ch := make([]frontend.Variable, 6)
	ch[0] = t.sample()
	field(ch[0])
	ch[1] = t.sample()
	field(ch[1])
	commitment(1)
	field(c.Values[0])
	field(0)
	ch[2] = t.sample()
	commitment(2)
	ch[3] = t.sample()
	for round := 0; round < 4; round++ {
		commitment(round)
		for _, circuit := range p.Circuits {
			t.observe(constantU64(uint64(circuit.LogDegree)))
		}
	}
	for _, value := range c.Values[1:] {
		field(value)
	}
	ch[4] = t.sample()
	for _, point := range encoded[p.WitnessOffset:p.PointCount] {
		t.observe(point)
	}
	ch[5] = t.sample()
	return ch
}

func (p *scalarProgram) constrain(api frontend.API, challenges, values, publics []frontend.Variable) ([]frontend.Variable, []frontend.Variable) {
	nodes := make([]frontend.Variable, len(p.Nodes))
	inputs := map[string][]frontend.Variable{"challenge": challenges, "value": values, "public": publics}
	for i, n := range p.Nodes {
		switch n.Op {
		case "constant":
			nodes[i] = n.Value
		case "input":
			nodes[i] = inputs[n.Kind][n.Index]
		case "add":
			nodes[i] = api.Add(nodes[n.A], nodes[n.B])
		case "sub":
			nodes[i] = api.Sub(nodes[n.A], nodes[n.B])
		case "mul":
			nodes[i] = api.Mul(nodes[n.A], nodes[n.B])
		case "inverse":
			nodes[i] = api.Inverse(nodes[n.A])
		default:
			panic("unvalidated scalar program")
		}
	}
	for _, id := range p.Assertions {
		api.AssertIsEqual(nodes[id], 0)
	}
	outputs := func(ids []int) []frontend.Variable {
		out := make([]frontend.Variable, len(ids))
		for i, id := range ids {
			out[i] = nodes[id]
		}
		return out
	}
	return outputs(p.Coefficients), outputs(p.Witnesses)
}

func (c *wrapperCircuit) Define(api frontend.API) error {
	return c.constrain(api, 6)
}

func (c *wrapperCircuit) constrain(api frontend.API, phase int) error {
	p := c.Profile
	if p == nil {
		return fmt.Errorf("missing trusted profile")
	}
	if err := p.validate(); err != nil {
		return err
	}
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[sw.BaseField](api)
	if err != nil {
		return err
	}
	s, err := emulated.NewField[sw.ScalarField](api)
	if err != nil {
		return err
	}
	curve, err := sw_emulated.New[sw.BaseField, sw.ScalarField](api, sw_emulated.GetBLS12381Params())
	if err != nil {
		return err
	}
	pairing, err := sw.NewPairing(api)
	if err != nil {
		return err
	}
	encoded := make([][]uints.U8, p.PointCount+len(p.Fixed))
	points := make([]*sw.G1Affine, 0, p.PointCount+len(p.Fixed)+1)
	for i := range c.Points {
		pairing.AssertIsOnG1(&c.Points[i])
		encoded[i] = pointBytes(api, u, f, &c.Points[i])
		points = append(points, &c.Points[i])
	}
	for i, fixed := range p.Fixed {
		native, _ := fixed.native()
		point := sw.NewG1Affine(native)
		points = append(points, &point)
		bytes := native.Bytes()
		encoded[p.PointCount+i] = uints.NewU8Array(bytes[:])
	}
	g, _ := p.Generator.native()
	generator := sw.NewG1Affine(g)
	points = append(points, &generator)
	publics := make([]frontend.Variable, 23)
	publics[0] = 0
	for i, word := range p.Prefix {
		publics[1+i] = word
	}
	for half := 0; half < 2; half++ {
		b := bits.ToBinary(api, c.Claim[half], bits.WithNbDigits(128))
		for word := 0; word < 4; word++ {
			publics[11+4*half+word] = bits.FromBinary(api, b[32*word:32*word+32])
		}
	}
	for i := range c.Deferred {
		pairing.AssertIsOnG1(&c.Deferred[i])
		bytes := pointBytes(api, u, f, &c.Deferred[i])
		publics[19+2*i] = littleEndian(api, u, bytes[:24])
		publics[20+2*i] = littleEndian(api, u, bytes[24:])
	}
	if phase == 1 {
		return nil
	}
	challenges := c.challenges(api, u, encoded, publics)
	if phase == 2 {
		return nil
	}
	coefficients, witnessCoefficients := p.Program.constrain(api, challenges, c.Values, publics)
	if phase == 3 {
		return nil
	}
	leftPoints, leftCoefficients := foldFixedBases(api, p, points, coefficients)
	left, err := completeMSM(api, curve, s, leftPoints, leftCoefficients)
	if err != nil {
		return err
	}
	right, err := completeMSM(api, curve, s, points[p.WitnessOffset:p.PointCount], witnessCoefficients)
	if err != nil {
		return err
	}
	if phase == 4 {
		return nil
	}
	outer, _ := g2Keys(p.OuterKeys)
	h, tauH := sw.NewG2AffineFixed(outer[0]), sw.NewG2AffineFixed(outer[1])
	if err := pairing.PairingCheck([]*sw.G1Affine{left, curve.Neg(right)}, []*sw.G2Affine{&h, &tauH}); err != nil {
		return err
	}
	if phase == 5 {
		return nil
	}
	inner, _ := g2Keys(p.DeferredKeys)
	ih, itauH := sw.NewG2AffineFixed(inner[0]), sw.NewG2AffineFixed(inner[1])
	return pairing.PairingCheck([]*sw.G1Affine{&c.Deferred[0], &c.Deferred[1]}, []*sw.G2Affine{&ih, &itauH})
}

// Fixed-point relations are checked at circuit construction. Variable inputs
// retain their curve and subgroup checks even when a scalar is constant zero.
func foldFixedBases(api frontend.API, p *profile, points []*sw.G1Affine, scalars []frontend.Variable) ([]*sw.G1Affine, []frontend.Variable) {
	weights := append([]frontend.Variable(nil), scalars...)
	indices := make([]int, p.PointCount)
	for i := range indices {
		indices[i] = i
	}
	generator, _ := p.Generator.native()
	generatorIndex := len(points) - 1
	type base struct {
		point bls.G1Affine
		index int
	}
	kept := []base{{generator, generatorIndex}}
	for i, fixed := range p.Fixed {
		point, _ := fixed.native()
		index := p.PointCount + i
		if point.IsInfinity() {
			continue
		}
		matched := false
		for _, previous := range kept {
			var negative bls.G1Affine
			negative.Neg(&previous.point)
			if point.Equal(&previous.point) || point.Equal(&negative) {
				weight := weights[index]
				if point.Equal(&negative) {
					weight = api.Neg(weight)
				}
				weights[previous.index] = api.Add(weights[previous.index], weight)
				matched = true
				break
			}
			for _, shift := range []int64{-2, -1, 1, 2} {
				var offset, candidate bls.G1Affine
				magnitude := shift
				if magnitude < 0 {
					magnitude = -magnitude
				}
				offset.ScalarMultiplication(&generator, big.NewInt(magnitude))
				if shift < 0 {
					offset.Neg(&offset)
				}
				candidate.Add(&previous.point, &offset)
				if !point.Equal(&candidate) {
					continue
				}
				weights[previous.index] = api.Add(weights[previous.index], weights[index])
				weights[generatorIndex] = api.Add(weights[generatorIndex], api.Mul(shift, weights[index]))
				matched = true
				break
			}
			if matched {
				break
			}
		}
		if !matched {
			kept = append(kept, base{point, index})
			indices = append(indices, index)
		}
	}
	indices = append(indices, generatorIndex)
	selected := make([]*sw.G1Affine, len(indices))
	coefficients := make([]frontend.Variable, len(indices))
	for i, index := range indices {
		selected[i], coefficients[i] = points[index], weights[index]
	}
	return selected, coefficients
}

func completeMSM(api frontend.API, curve *sw_emulated.Curve[sw.BaseField, sw.ScalarField], field *emulated.Field[sw.ScalarField], points []*sw.G1Affine, scalars []frontend.Variable) (*sw.G1Affine, error) {
	if len(points) != len(scalars) {
		return nil, fmt.Errorf("MSM point and scalar counts differ")
	}
	var direct *sw.G1Affine
	var bases []*sw.G1Affine
	var coefficients []*sw.Scalar
	minusOne := new(big.Int).Sub(fr.Modulus(), big.NewInt(1))
	for i, point := range points {
		if constant, ok := api.Compiler().ConstantValue(scalars[i]); ok {
			if constant.Sign() == 0 {
				continue
			}
			if constant.IsInt64() && constant.Int64() == 1 || constant.Cmp(minusOne) == 0 {
				if constant.Cmp(minusOne) == 0 {
					point = curve.Neg(point)
				}
				if direct == nil {
					direct = point
				} else {
					direct = curve.AddUnified(direct, point)
				}
				continue
			}
		}
		bases = append(bases, point)
		coefficients = append(coefficients, field.FromBits(bits.ToBinary(api, scalars[i])...))
	}
	result, err := curve.MultiScalarMul(bases, coefficients)
	if err != nil {
		return nil, err
	}
	if direct != nil {
		result = curve.AddUnified(direct, result)
	}
	return result, nil
}
