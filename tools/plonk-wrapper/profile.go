package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"strings"

	"github.com/consensys/gnark/frontend"
)

type pointJSON struct{ X, Y string }
type matrix struct{ Width, Rows, PointOffset, ValueOffset int }
type circuitShape struct {
	LogDegree int
	Shape     [7]uint64
}
type instruction struct {
	Op, Value, Kind string
	Index, A, B     int
}
type scalarProgram struct {
	Nodes                               []instruction
	Assertions, Coefficients, Witnesses []int
}

// One entry of a claim row: a circuit constant or an index into the
// verifier-supplied public scalars.
type claimSlot struct {
	Constant *string
	Public   *int
}

// Where the verifier takes one public scalar from: a constant, a word of the
// fixed statement prefix, a word of the claim digest, or a half of a deferred
// pairing operand's encoding.
type publicSource struct {
	Constant                         *string
	Prefix, DigestWord, DeferredHalf *int
}

type verifyingKey struct {
	Format, VKID, SetupID, Seed                         string
	PublicMaxDegree                                     uint64
	Prefix                                              []uint64
	Circuits                                            []circuitShape
	Matrices                                            []matrix
	PointCount, FieldCount, WitnessOffset, OpeningCount int
	Fixed                                               []pointJSON
	Generator                                           pointJSON
	OuterKeys, DeferredKeys                             []string
	Program                                             scalarProgram
	AccumulatorCount                                    int
	Claims                                              [][]claimSlot
	Publics                                             []publicSource
}

func (p *verifyingKey) deferredCount() int {
	return len(p.DeferredKeys)
}

type witnessJSON struct {
	ClaimDigest      string
	Points, Deferred []pointJSON
	Values           []string
}

func decodeReader(reader io.Reader, out any) error {
	d := json.NewDecoder(reader)
	d.DisallowUnknownFields()
	if err := d.Decode(out); err != nil {
		return err
	}
	if err := d.Decode(new(any)); err != io.EOF {
		return fmt.Errorf("trailing JSON data")
	}
	return nil
}

func decodeVerifyingKey(data []byte) (*verifyingKey, error) {
	var key verifyingKey
	if len(data) > 16<<20 {
		return nil, fmt.Errorf("verifying key description is too large")
	}
	if err := decodeReader(bytes.NewReader(data), &key); err != nil {
		return nil, err
	}
	if err := key.validate(); err != nil {
		return nil, err
	}
	return &key, nil
}

func unhex(s string, length int) ([]byte, error) {
	b, err := hex.DecodeString(strings.TrimPrefix(s, "0x"))
	if err != nil || (length >= 0 && len(b) != length) {
		return nil, fmt.Errorf("invalid hexadecimal encoding (expected %d bytes)", length)
	}
	return b, nil
}

func canonical(s string, modulus *big.Int) (*big.Int, error) {
	v, ok := new(big.Int).SetString(s, 0)
	if !ok || v.Sign() < 0 || v.Cmp(modulus) >= 0 {
		return nil, fmt.Errorf("noncanonical field element")
	}
	return v, nil
}

func (p pointJSON) native() (nativeG1, error) {
	var result nativeG1
	x, err := canonical(p.X, baseModulus())
	if err != nil {
		return result, err
	}
	y, err := canonical(p.Y, baseModulus())
	if err != nil {
		return result, err
	}
	result.X.SetBigInt(x)
	result.Y.SetBigInt(y)
	if !result.IsOnCurve() || !result.IsInSubGroup() {
		return result, fmt.Errorf("invalid G1 point")
	}
	return result, nil
}

func g2Keys(encoded []string) ([2]nativeG2, error) {
	var result [2]nativeG2
	if len(encoded) != 2 {
		return result, fmt.Errorf("expected two G2 anchors")
	}
	for i, s := range encoded {
		b, err := unhex(s, g2ExportBytes)
		if err != nil {
			return result, err
		}
		if result[i], err = decodeG2(b); err != nil {
			return result, err
		}
	}
	return result, nil
}

func (p *verifyingKey) validate() error {
	if p.Claims == nil || p.Publics == nil || p.Format != vkFormat || len(p.Prefix) != 10 || len(p.Circuits) < 2 || len(p.Matrices) != 4*len(p.Circuits) || p.PointCount < 1 || p.PointCount > 4096 || p.FieldCount < 1 || p.FieldCount > 65536 || len(p.Fixed) > 4096 || p.WitnessOffset < 0 || p.WitnessOffset > p.PointCount || p.OpeningCount < 2 || p.OpeningCount > 16 || p.WitnessOffset+p.OpeningCount != p.PointCount || p.AccumulatorCount != len(p.Circuits)-1 || (p.deferredCount() != 0 && p.deferredCount() != 2) {
		return fmt.Errorf("invalid wrapper verifying key dimensions")
	}
	publicCount := len(p.Publics)
	for i, source := range p.Publics {
		set := 0
		if source.Constant != nil {
			set++
			if _, err := canonical(*source.Constant, scalarModulus()); err != nil {
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
				if _, err := canonical(*slot.Constant, scalarModulus()); err != nil {
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
		if c.LogDegree < 1 || c.LogDegree > 28 || c.Shape[2] != 1<<c.LogDegree {
			return fmt.Errorf("invalid circuit domain")
		}
	}
	for i, m := range p.Matrices {
		if m.Width < 0 || m.Rows < 1 || m.Rows > 2 || m.ValueOffset < 1 || m.ValueOffset > p.FieldCount || m.Width > (p.FieldCount-m.ValueOffset)/m.Rows || m.PointOffset < 0 || m.PointOffset > p.PointCount+len(p.Fixed) || m.Width > p.PointCount+len(p.Fixed)-m.PointOffset {
			return fmt.Errorf("invalid matrix %d", i)
		}
	}
	for _, f := range append(append([]pointJSON(nil), p.Fixed...), p.Generator) {
		if _, err := f.native(); err != nil {
			return err
		}
	}
	g, _ := p.Generator.native()
	if g.IsInfinity() {
		return fmt.Errorf("identity G1 anchor")
	}
	_, err := g2Keys(p.OuterKeys)
	if err != nil {
		return err
	}
	if p.deferredCount() == 2 {
		_, err := g2Keys(p.DeferredKeys)
		if err != nil {
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
			if _, err := canonical(n.Value, scalarModulus()); err != nil {
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
	return nil
}

func newCircuit(p *verifyingKey) *wrapperCircuit {
	return &wrapperCircuit{VK: p, Points: make([]circuitG1, p.PointCount), Deferred: make([]circuitG1, p.deferredCount()), Values: make([]frontend.Variable, p.FieldCount)}
}

func assignWitness(p *verifyingKey, w *witnessJSON) (*wrapperCircuit, error) {
	if len(w.Points) != p.PointCount || len(w.Deferred) != p.deferredCount() || len(w.Values) != p.FieldCount {
		return nil, fmt.Errorf("witness dimensions differ from verifying key")
	}
	result := newCircuit(p)
	digest, err := unhex(w.ClaimDigest, 32)
	if err != nil {
		return nil, err
	}
	result.Claim = digestLimbs(digest)
	for i, point := range w.Points {
		v, err := point.native()
		if err != nil {
			return nil, err
		}
		result.Points[i] = newCircuitG1(v)
	}
	for i, point := range w.Deferred {
		v, err := point.native()
		if err != nil {
			return nil, err
		}
		result.Deferred[i] = newCircuitG1(v)
	}
	for i, v := range w.Values {
		scalar, err := canonical(v, scalarModulus())
		if err != nil {
			return nil, err
		}
		result.Values[i] = scalar
	}
	return result, nil
}

func digestLimbs(digest []byte) [2]frontend.Variable {
	var result [2]frontend.Variable
	for i := range result {
		var half [16]byte
		for j := range half {
			half[15-j] = digest[16*i+j]
		}
		result[i] = new(big.Int).SetBytes(half[:])
	}
	return result
}
