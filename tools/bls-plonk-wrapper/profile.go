package main

import (
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"

	"github.com/consensys/gnark-crypto/ecc"
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
type profile struct {
	Format, ProfileID, SetupID, Seed                    string
	PublicMaxDegree                                     uint64
	Prefix                                              []uint64
	Circuits                                            []circuitShape
	Matrices                                            []matrix
	PointCount, FieldCount, WitnessOffset, OpeningCount int
	Fixed                                               []pointJSON
	Generator                                           pointJSON
	OuterKeys, DeferredKeys                             []string
	Program                                             scalarProgram
}
type witnessJSON struct {
	ClaimDigest      string
	Points, Deferred []pointJSON
	Values           []string
}

func decodeJSON(path string, out any) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	d := json.NewDecoder(io.LimitReader(f, 16<<20))
	d.DisallowUnknownFields()
	if err := d.Decode(out); err != nil {
		return err
	}
	if err := d.Decode(new(any)); err != io.EOF {
		return fmt.Errorf("trailing JSON data")
	}
	return nil
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

func loadProfile(path string) (*profile, error) {
	var p profile
	if err := decodeJSON(path, &p); err != nil {
		return nil, err
	}
	if err := p.validate(); err != nil {
		return nil, err
	}
	return &p, nil
}

func (p *profile) validate() error {
	if p.Format != profileFormat || len(p.Prefix) != 10 || len(p.Circuits) != 2 || len(p.Matrices) != 8 || p.PointCount < 1 || p.PointCount > 256 || p.FieldCount < 1 || p.FieldCount > 4096 || len(p.Fixed) > 4096 || p.WitnessOffset < 0 || p.WitnessOffset > p.PointCount || p.OpeningCount < 2 || p.OpeningCount > 3 || p.WitnessOffset+p.OpeningCount != p.PointCount {
		return fmt.Errorf("invalid wrapper profile dimensions")
	}
	if _, err := unhex(p.ProfileID, 32); err != nil {
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
	outer, err := g2Keys(p.OuterKeys)
	if err != nil {
		return err
	}
	inner, err := g2Keys(p.DeferredKeys)
	if err != nil {
		return err
	}
	if curveID == ecc.BLS12_381 && (!outer[0].Equal(&inner[0]) || !outer[1].Equal(&inner[1])) {
		return fmt.Errorf("Filecoin pairing anchors differ")
	}
	if len(p.Program.Coefficients) != p.PointCount+len(p.Fixed)+1 || len(p.Program.Witnesses) != p.OpeningCount || len(p.Program.Assertions) != 2 {
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
			bound := map[string]int{"challenge": 6, "value": p.FieldCount, "public": 23}[n.Kind]
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

func newCircuit(p *profile) *wrapperCircuit {
	return &wrapperCircuit{Profile: p, Points: make([]circuitG1, p.PointCount), Values: make([]frontend.Variable, p.FieldCount)}
}

func witnessAssignment(p *profile, path string) (*wrapperCircuit, error) {
	var w witnessJSON
	if err := decodeJSON(path, &w); err != nil {
		return nil, err
	}
	if len(w.Points) != p.PointCount || len(w.Deferred) != 2 || len(w.Values) != p.FieldCount {
		return nil, fmt.Errorf("witness dimensions differ from profile")
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
