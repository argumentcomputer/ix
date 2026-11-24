package main

import (
	"bytes"
	"fmt"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc"
	bls "github.com/consensys/gnark-crypto/ecc/bls12-381"
	blsfp "github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark/frontend"
	swbls "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/bits"
	"github.com/consensys/gnark/std/math/cmp"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
)

type blsG1 = bls.G1Affine
type blsG2 = bls.G2Affine
type blsCircuitG1 = swbls.G1Affine
type blsCircuitG2 = swbls.G2Affine
type blsCircuitScalar = swbls.Scalar
type blsBaseField = swbls.BaseField
type blsScalarField = swbls.ScalarField

const (
	blsCurveID        = ecc.BLS12_381
	blsBaseBytes      = 48
	blsPointBytesLen  = 48
	blsPointLimbBytes = 24
	blsG2ExportBytes  = 96
	blsAnchorBytesLen = 240
	blsSRSMagic       = "IXPSRS01"
	blsVKFormat       = "ix-bls-plonk-vk-v1"
)

func isCompressedPointBLS(b byte) bool { return b&0x80 != 0 }

func encodePointBLS(p blsG1) []byte { b := p.Bytes(); return b[:] }

func decodeG2BLS(b []byte) (blsG2, error) {
	var p blsG2
	if len(b) != blsG2ExportBytes {
		return p, fmt.Errorf("invalid BLS12-381 G2 length")
	}
	if _, err := p.SetBytes(b); err != nil {
		return p, err
	}
	canonical := p.Bytes()
	if p.IsInfinity() || !p.IsOnCurve() || !p.IsInSubGroup() || !bytes.Equal(canonical[:], b) {
		return p, fmt.Errorf("invalid BLS12-381 G2 anchor")
	}
	return p, nil
}

func (p pointJSON) nativeBLS() (blsG1, error) {
	var result blsG1
	x, err := canonical(p.X, blsfp.Modulus())
	if err != nil {
		return result, err
	}
	y, err := canonical(p.Y, blsfp.Modulus())
	if err != nil {
		return result, err
	}
	result.X.SetBigInt(x)
	result.Y.SetBigInt(y)
	if !result.IsOnCurve() || !result.IsInSubGroup() {
		return result, fmt.Errorf("invalid BLS12-381 G1 point")
	}
	return result, nil
}

func g2KeysBLS(encoded []string) ([2]blsG2, error) {
	var result [2]blsG2
	if len(encoded) != 2 {
		return result, fmt.Errorf("expected two BLS12-381 G2 anchors")
	}
	for i, s := range encoded {
		b, err := unhex(s, blsG2ExportBytes)
		if err != nil {
			return result, err
		}
		if result[i], err = decodeG2BLS(b); err != nil {
			return result, err
		}
	}
	return result, nil
}

func pointBytesBLS(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[blsBaseField], point *blsCircuitG1) []uints.U8 {
	f.AssertIsInRange(&point.X)
	f.AssertIsInRange(&point.Y)
	x := f.ToBitsCanonical(&point.X)
	y := f.ToBitsCanonical(&point.Y)
	half := new(big.Int).Rsh(new(big.Int).Set(blsfp.Modulus()), 1)
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

func decodeVerifyingKeyBLS(data []byte) (*verifyingKey, error) {
	var key verifyingKey
	if len(data) > 16<<20 {
		return nil, fmt.Errorf("verifying key description is too large")
	}
	if err := decodeReader(bytes.NewReader(data), &key); err != nil {
		return nil, err
	}
	if err := key.validateBLS(); err != nil {
		return nil, err
	}
	return &key, nil
}

func (p *verifyingKey) validateBLS() error {
	if p.Claims == nil || p.Publics == nil || p.Format != blsVKFormat || len(p.Prefix) != 10 || len(p.Circuits) < 2 || len(p.Matrices) != 4*len(p.Circuits) || p.PointCount < 1 || p.PointCount > 4096 || p.FieldCount < 1 || p.FieldCount > 65536 || len(p.Fixed) > 4096 || p.WitnessOffset < 0 || p.WitnessOffset > p.PointCount || p.OpeningCount < 2 || p.OpeningCount > 16 || p.WitnessOffset+p.OpeningCount != p.PointCount || p.AccumulatorCount != len(p.Circuits)-1 || (p.deferredCount() != 0 && p.deferredCount() != 2) {
		return fmt.Errorf("invalid BLS12-381 wrapper verifying key dimensions")
	}
	modulus := blsfr.Modulus()
	publicCount := len(p.Publics)
	for i, source := range p.Publics {
		set := 0
		if source.Constant != nil {
			set++
			if _, err := canonical(*source.Constant, modulus); err != nil {
				return err
			}
		}
		if source.Prefix != nil {
			set++
			if *source.Prefix < 0 || *source.Prefix >= 10 {
				return fmt.Errorf("invalid prefix public %d", i)
			}
		}
		if source.DigestWord != nil {
			set++
			if *source.DigestWord < 0 || *source.DigestWord >= 8 {
				return fmt.Errorf("invalid digest public %d", i)
			}
		}
		if source.DeferredHalf != nil {
			set++
			if *source.DeferredHalf < 0 || *source.DeferredHalf >= 2*p.deferredCount() {
				return fmt.Errorf("invalid deferred public %d", i)
			}
		}
		if set != 1 {
			return fmt.Errorf("public source %d must have exactly one kind", i)
		}
	}
	for r, row := range p.Claims {
		if len(row) == 0 || len(row) > 16 {
			return fmt.Errorf("invalid claim row %d", r)
		}
		for _, slot := range row {
			switch {
			case slot.Constant != nil && slot.Public == nil:
				if _, err := canonical(*slot.Constant, modulus); err != nil {
					return err
				}
			case slot.Public != nil && slot.Constant == nil:
				if *slot.Public < 0 || *slot.Public >= publicCount {
					return fmt.Errorf("claim row %d references an unknown public", r)
				}
			default:
				return fmt.Errorf("claim row %d slot must be a constant or a public", r)
			}
		}
	}
	if _, err := unhex(p.VKID, 32); err != nil {
		return err
	}
	if _, err := unhex(p.SetupID, 32); err != nil {
		return err
	}
	if _, err := unhex(p.Seed, -1); err != nil {
		return err
	}
	for _, c := range p.Circuits {
		if c.LogDegree < 1 || c.LogDegree > 32 || c.Shape[2] != uint64(1)<<uint(c.LogDegree) {
			return fmt.Errorf("invalid BLS12-381 circuit domain")
		}
	}
	for i, m := range p.Matrices {
		if m.Width < 0 || m.Rows < 1 || m.Rows > 2 || m.ValueOffset < 1 || m.ValueOffset > p.FieldCount || m.Width > (p.FieldCount-m.ValueOffset)/m.Rows || m.PointOffset < 0 || m.PointOffset > p.PointCount+len(p.Fixed) || m.Width > p.PointCount+len(p.Fixed)-m.PointOffset {
			return fmt.Errorf("invalid matrix %d", i)
		}
	}
	for _, f := range append(append([]pointJSON(nil), p.Fixed...), p.Generator) {
		if _, err := f.nativeBLS(); err != nil {
			return err
		}
	}
	g, _ := p.Generator.nativeBLS()
	if g.IsInfinity() {
		return fmt.Errorf("identity BLS12-381 G1 anchor")
	}
	if _, err := g2KeysBLS(p.OuterKeys); err != nil {
		return err
	}
	if p.deferredCount() == 2 {
		if _, err := g2KeysBLS(p.DeferredKeys); err != nil {
			return err
		}
	}
	if len(p.Program.Coefficients) != p.PointCount+len(p.Fixed)+1 || len(p.Program.Witnesses) != p.OpeningCount || len(p.Program.Assertions) != len(p.Circuits) {
		return fmt.Errorf("invalid scalar program outputs")
	}
	for i, n := range p.Program.Nodes {
		valid := func(id int) bool { return id >= 0 && id < i }
		switch n.Op {
		case "constant":
			if _, err := canonical(n.Value, modulus); err != nil {
				return err
			}
		case "input":
			bound := map[string]int{"challenge": 6, "value": p.FieldCount, "public": publicCount}[n.Kind]
			if n.Index < 0 || n.Index >= bound {
				return fmt.Errorf("invalid scalar input")
			}
		case "add", "sub", "mul":
			if !valid(n.A) || !valid(n.B) {
				return fmt.Errorf("invalid scalar reference")
			}
		case "inverse":
			if !valid(n.A) {
				return fmt.Errorf("invalid inverse reference")
			}
		default:
			return fmt.Errorf("unknown scalar instruction %q", n.Op)
		}
	}
	for _, ids := range [][]int{p.Program.Assertions, p.Program.Coefficients, p.Program.Witnesses} {
		for _, id := range ids {
			if id < 0 || id >= len(p.Program.Nodes) {
				return fmt.Errorf("invalid scalar output")
			}
		}
	}
	want, err := unhex(p.ProgramDigest, 32)
	if err != nil {
		return fmt.Errorf("invalid program digest: %w", err)
	}
	got, err := p.Program.digestFor(modulus)
	if err != nil {
		return err
	}
	if !bytes.Equal(got[:], want) {
		return fmt.Errorf("scalar program digest mismatch: got 0x%x, want 0x%x", got, want)
	}
	return nil
}

type blsWrapperCircuit struct {
	Claim    [2]frontend.Variable `gnark:",public"`
	Points   []blsCircuitG1
	Deferred []blsCircuitG1
	Values   []frontend.Variable
	VK       *verifyingKey `gnark:"-"`
}

func newCircuitBLS(p *verifyingKey) *blsWrapperCircuit {
	return &blsWrapperCircuit{
		VK:       p,
		Points:   make([]blsCircuitG1, p.PointCount),
		Deferred: make([]blsCircuitG1, p.deferredCount()),
		Values:   make([]frontend.Variable, p.FieldCount),
	}
}

func assignWitnessBLS(p *verifyingKey, w *witnessJSON) (*blsWrapperCircuit, error) {
	if len(w.Points) != p.PointCount || len(w.Deferred) != p.deferredCount() || len(w.Values) != p.FieldCount {
		return nil, fmt.Errorf("BLS12-381 witness dimensions differ from verifying key")
	}
	result := newCircuitBLS(p)
	digest, err := unhex(w.ClaimDigest, 32)
	if err != nil {
		return nil, err
	}
	result.Claim = digestLimbs(digest)
	for i, point := range w.Points {
		v, err := point.nativeBLS()
		if err != nil {
			return nil, err
		}
		result.Points[i] = swbls.NewG1Affine(v)
	}
	for i, point := range w.Deferred {
		v, err := point.nativeBLS()
		if err != nil {
			return nil, err
		}
		result.Deferred[i] = swbls.NewG1Affine(v)
	}
	modulus := blsfr.Modulus()
	for i, v := range w.Values {
		scalar, err := canonical(v, modulus)
		if err != nil {
			return nil, err
		}
		result.Values[i] = scalar
	}
	return result, nil
}

func (c *blsWrapperCircuit) Define(api frontend.API) error {
	p := c.VK
	if p == nil {
		return fmt.Errorf("missing trusted BLS12-381 verifying key")
	}
	if err := p.validateBLS(); err != nil {
		return err
	}
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[blsBaseField](api)
	if err != nil {
		return err
	}
	s, err := emulated.NewField[blsScalarField](api)
	if err != nil {
		return err
	}
	curve, err := sw_emulated.New[blsBaseField, blsScalarField](api, sw_emulated.GetBLS12381Params())
	if err != nil {
		return err
	}
	pairing, err := swbls.NewPairing(api)
	if err != nil {
		return err
	}
	encoded := make([][]uints.U8, p.PointCount+len(p.Fixed))
	points := make([]*blsCircuitG1, 0, p.PointCount+len(p.Fixed)+1)
	for i := range c.Points {
		// Mandatory BLS12-381 on-curve + prime-order subgroup check (h1 != 1).
		pairing.AssertIsOnG1(&c.Points[i])
		encoded[i] = pointBytesBLS(api, u, f, &c.Points[i])
		points = append(points, &c.Points[i])
	}
	for i, fixed := range p.Fixed {
		native, _ := fixed.nativeBLS()
		point := swbls.NewG1Affine(native)
		points = append(points, &point)
		raw := encodePointBLS(native)
		encoded[p.PointCount+i] = uints.NewU8Array(raw)
	}
	g, _ := p.Generator.nativeBLS()
	generator := swbls.NewG1Affine(g)
	points = append(points, &generator)
	if len(c.Deferred) != p.deferredCount() {
		return fmt.Errorf("deferred operand count differs from the verifying key")
	}
	var digestWords [8]frontend.Variable
	for half := 0; half < 2; half++ {
		b := bits.ToBinary(api, c.Claim[half], bits.WithNbDigits(128))
		for word := 0; word < 4; word++ {
			digestWords[4*half+word] = bits.FromBinary(api, b[32*word:32*word+32])
		}
	}
	deferredHalves := make([]frontend.Variable, 0, 2*len(c.Deferred))
	deferredEncoded := make([][]uints.U8, len(c.Deferred))
	for i := range c.Deferred {
		pairing.AssertIsOnG1(&c.Deferred[i])
		raw := pointBytesBLS(api, u, f, &c.Deferred[i])
		deferredEncoded[i] = raw
		deferredHalves = append(
			deferredHalves,
			littleEndian(api, u, raw[:blsPointLimbBytes]),
			littleEndian(api, u, raw[blsPointLimbBytes:]),
		)
	}
	sources := p.Publics
	publics := make([]frontend.Variable, len(sources))
	for i, source := range sources {
		switch {
		case source.Constant != nil:
			publics[i] = *source.Constant
		case source.Prefix != nil:
			publics[i] = p.Prefix[*source.Prefix]
		case source.DigestWord != nil:
			publics[i] = digestWords[*source.DigestWord]
		default:
			publics[i] = deferredHalves[*source.DeferredHalf]
		}
	}
	challenges, transcript := challengesFor(api, u, p, c.Values, encoded, publics, blsfr.Modulus())
	coefficients, witnessCoefficients := p.Program.constrain(api, challenges, c.Values, publics)
	leftPoints, leftCoefficients := foldFixedBasesBLS(api, p, points, coefficients)
	left, err := completeMSMBLS(api, curve, s, leftPoints, leftCoefficients)
	if err != nil {
		return err
	}
	right, err := completeMSMBLS(api, curve, s, points[p.WitnessOffset:p.PointCount], witnessCoefficients)
	if err != nil {
		return err
	}
	outer, _ := g2KeysBLS(p.OuterKeys)
	h, tauH := swbls.NewG2AffineFixed(outer[0]), swbls.NewG2AffineFixed(outer[1])
	if len(c.Deferred) == 0 {
		return pairing.PairingCheck([]*blsCircuitG1{left, curve.Neg(right)}, []*blsCircuitG2{&h, &tauH})
	}
	leftReduced := blsCircuitG1{X: *f.ReduceStrict(&left.X), Y: *f.ReduceStrict(&left.Y)}
	rightReduced := blsCircuitG1{X: *f.ReduceStrict(&right.X), Y: *f.ReduceStrict(&right.Y)}
	transcript.observe(uints.NewU8Array([]byte("ix/pairing-fold/v1")))
	transcript.observe(pointBytesBLS(api, u, f, &leftReduced))
	transcript.observe(pointBytesBLS(api, u, f, &rightReduced))
	transcript.observe(deferredEncoded[0])
	transcript.observe(deferredEncoded[1])
	rho := transcript.sampleFinal()
	rhoScalar := s.FromBits(bits.ToBinary(api, rho)...)
	scaledD0, err := curve.MultiScalarMul([]*blsCircuitG1{&c.Deferred[0]}, []*blsCircuitScalar{rhoScalar})
	if err != nil {
		return err
	}
	scaledD1, err := curve.MultiScalarMul([]*blsCircuitG1{&c.Deferred[1]}, []*blsCircuitScalar{rhoScalar})
	if err != nil {
		return err
	}
	negRight := curve.Neg(right)
	inner, _ := g2KeysBLS(p.DeferredKeys)
	if outer[0].Equal(&inner[0]) && outer[1].Equal(&inner[1]) {
		foldedLeft := curve.AddUnified(left, scaledD0)
		foldedRight := curve.AddUnified(negRight, scaledD1)
		return pairing.PairingCheck([]*blsCircuitG1{foldedLeft, foldedRight}, []*blsCircuitG2{&h, &tauH})
	}
	ih, itauH := swbls.NewG2AffineFixed(inner[0]), swbls.NewG2AffineFixed(inner[1])
	return pairing.PairingCheck(
		[]*blsCircuitG1{left, negRight, scaledD0, scaledD1},
		[]*blsCircuitG2{&h, &tauH, &ih, &itauH},
	)
}

func foldFixedBasesBLS(api frontend.API, p *verifyingKey, points []*blsCircuitG1, scalars []frontend.Variable) ([]*blsCircuitG1, []frontend.Variable) {
	weights := append([]frontend.Variable(nil), scalars...)
	indices := make([]int, p.PointCount)
	for i := range indices {
		indices[i] = i
	}
	generator, _ := p.Generator.nativeBLS()
	generatorIndex := len(points) - 1
	type base struct {
		point blsG1
		index int
	}
	kept := []base{{generator, generatorIndex}}
	for i, fixed := range p.Fixed {
		point, _ := fixed.nativeBLS()
		index := p.PointCount + i
		if point.IsInfinity() {
			continue
		}
		matched := false
		for _, previous := range kept {
			var negative blsG1
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
				var offset, candidate blsG1
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
	selected := make([]*blsCircuitG1, len(indices))
	coefficients := make([]frontend.Variable, len(indices))
	for i, index := range indices {
		selected[i], coefficients[i] = points[index], weights[index]
	}
	return selected, coefficients
}

func completeMSMBLS(api frontend.API, curve *sw_emulated.Curve[blsBaseField, blsScalarField], field *emulated.Field[blsScalarField], points []*blsCircuitG1, scalars []frontend.Variable) (*blsCircuitG1, error) {
	if len(points) != len(scalars) {
		return nil, fmt.Errorf("MSM point and scalar counts differ")
	}
	var direct *blsCircuitG1
	var bases []*blsCircuitG1
	var coefficients []*blsCircuitScalar
	minusOne := new(big.Int).Sub(blsfr.Modulus(), big.NewInt(1))
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
