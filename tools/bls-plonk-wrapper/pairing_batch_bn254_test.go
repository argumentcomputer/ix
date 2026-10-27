//go:build bn254

package main

import (
	"bytes"
	"math/big"
	"path/filepath"
	"testing"

	bn "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/test"
	"github.com/zeebo/blake3"
)

type pairingBatchCircuit struct {
	Operands      [4]circuitG1
	Claim         [2]frontend.Variable
	PacketDigest  [32]uints.U8
	Profile       *profile `gnark:"-"`
	ExpectedRho   frontend.Variable
	ChallengeOnly bool `gnark:"-"`
}

func (c *pairingBatchCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	f, err := emulated.NewField[baseField](api)
	if err != nil {
		return err
	}
	s, err := emulated.NewField[scalarField](api)
	if err != nil {
		return err
	}
	curve, err := sw_emulated.New[baseField, scalarField](api, curveParameters())
	if err != nil {
		return err
	}
	pairing, err := newPairing(api)
	if err != nil {
		return err
	}
	for i := range c.Operands {
		pairing.AssertIsOnG1(&c.Operands[i])
	}
	if c.ChallengeOnly {
		context, err := pairingBatchContext(c.Profile)
		if err != nil {
			return err
		}
		rho := pairingBatchChallenge(api, u, f, context, c.Claim, c.PacketDigest[:], [4]*circuitG1{&c.Operands[0], &c.Operands[1], &c.Operands[2], &c.Operands[3]})
		api.AssertIsEqual(rho, c.ExpectedRho)
		return nil
	}
	w := &wrapperCircuit{Profile: c.Profile, Claim: c.Claim, Deferred: [2]circuitG1{c.Operands[2], c.Operands[3]}}
	return w.batchedPairing(api, u, f, s, curve, c.PacketDigest[:], &c.Operands[0], &c.Operands[1])
}

func nativePairingBatchChallenge(p *profile, claim [2]uint64, packet [32]byte, points [4]nativeG1) *big.Int {
	input, err := pairingBatchContext(p)
	if err != nil {
		panic(err)
	}
	for _, limb := range claim {
		for i := 0; i < 16; i++ {
			var b byte
			if i < 8 {
				b = byte(limb >> uint(8*i))
			}
			input = append(input, b)
		}
	}
	input = append(input, packet[:]...)
	for _, point := range points {
		input = append(input, encodePoint(point)...)
	}
	h := blake3.New()
	h.Write(input)
	wide := make([]byte, 64)
	h.Digest().Read(wide)
	for i, j := 0, len(wide)-1; i < j; i, j = i+1, j-1 {
		wide[i], wide[j] = wide[j], wide[i]
	}
	return new(big.Int).Mod(new(big.Int).SetBytes(wide), scalarModulus())
}

func TestPairingBatchSoundnessAndChallengeBinding(t *testing.T) {
	p, srs, _ := importedFixture(t)
	C, T := srs.Pk.G1[0], srs.Pk.G1[1]
	_, _, g, _ := bn.Generators()
	var negC nativeG1
	negC.Neg(&C)
	valid := [4]nativeG1{T, C, T, negC}
	claim := [2]uint64{123, 456}
	packet := [32]byte{9, 8, 7}
	assignment := func(points [4]nativeG1, profile *profile) *pairingBatchCircuit {
		w := &pairingBatchCircuit{Profile: profile, Claim: [2]frontend.Variable{claim[0], claim[1]}, ExpectedRho: nativePairingBatchChallenge(profile, claim, packet, points)}
		copy(w.PacketDigest[:], uints.NewU8Array(packet[:]))
		for i := range points {
			w.Operands[i] = newCircuitG1(points[i])
		}
		return w
	}
	check := func(name string, points [4]nativeG1, ok bool) {
		t.Helper()
		err := test.IsSolved(&pairingBatchCircuit{Profile: p}, assignment(points, p), curveID.ScalarField())
		if (err == nil) != ok {
			t.Fatalf("%s: expected accepted=%t: %v", name, ok, err)
		}
	}
	check("both-valid", valid, true)
	check("all-infinity", [4]nativeG1{}, true)
	check("one-identity-equation", [4]nativeG1{T, C, {}, {}}, true)
	bad := valid
	bad[0].Add(&bad[0], &g)
	check("invalid-outer", bad, false)
	bad = valid
	bad[2].Add(&bad[2], &g)
	check("invalid-deferred", bad, false)
	bad = [4]nativeG1{}
	bad[0] = g
	check("invalid-outer-identity-deferred", bad, false)
	bad = [4]nativeG1{}
	bad[2] = g
	check("valid-outer-invalid-deferred", bad, false)
	var weighted nativeG1
	weighted.ScalarMultiplication(&g, big.NewInt(7))
	cancel := [4]nativeG1{T, C, g, g}
	cancel[0].Sub(&T, &weighted)
	cancel[1].Add(&C, &weighted)
	if nativePairingBatchChallenge(p, claim, packet, cancel).Cmp(big.NewInt(7)) == 0 {
		t.Fatal("cancellation fixture has accidental challenge collision")
	}
	anchors, _ := g2Keys(p.OuterKeys)
	var a, b, neg nativeG1
	neg.Neg(&cancel[1])
	for _, equation := range [][2]nativeG1{{cancel[0], neg}, {cancel[2], cancel[3]}} {
		if ok, err := bn.PairingCheck(equation[:], anchors[:]); err != nil || ok {
			t.Fatal("cancellation fixture must have two invalid equations", err)
		}
	}
	a.Add(&cancel[0], &weighted)
	neg.Neg(&cancel[1])
	b.Add(&neg, &weighted)
	if ok, err := bn.PairingCheck([]nativeG1{a, b}, anchors[:]); err != nil || !ok {
		t.Fatal("predetermined-coefficient cancellation fixture is invalid", err)
	}
	check("predetermined-coefficient-cancellation", cancel, false)
	for _, points := range [][4]nativeG1{valid, cancel, {}} {
		w := assignment(points, p)
		if err := test.IsSolved(&pairingBatchCircuit{Profile: p, ChallengeOnly: true}, w, curveID.ScalarField()); err != nil {
			t.Fatal(err)
		}
	}
	for _, kind := range []string{"left", "right", "deferred-a", "deferred-b", "claim-low", "claim-high", "packet", "context"} {
		w := assignment(valid, p)
		profileCopy := *p
		switch kind {
		case "left", "right", "deferred-a", "deferred-b":
			i := map[string]int{"left": 0, "right": 1, "deferred-a": 2, "deferred-b": 3}[kind]
			point := valid[i]
			point.Add(&point, &g)
			w.Operands[i] = newCircuitG1(point)
		case "claim-low":
			w.Claim[0] = claim[0] + 1
		case "claim-high":
			w.Claim[1] = claim[1] + 1
		case "packet":
			w.PacketDigest[0] = uints.NewU8(packet[0] ^ 1)
		case "context":
			profileCopy.Seed = "0x01"
		}
		if err := test.IsSolved(&pairingBatchCircuit{Profile: &profileCopy, ChallengeOnly: true}, w, curveID.ScalarField()); err == nil {
			t.Fatalf("unbound %s", kind)
		}
	}
	w := assignment(valid, p)
	w.ExpectedRho = 0
	if err := test.IsSolved(&pairingBatchCircuit{Profile: p, ChallengeOnly: true}, w, curveID.ScalarField()); err == nil {
		t.Fatal("accepted zero challenge")
	}
	other := *p
	other.DeferredKeys = []string{p.DeferredKeys[1], p.DeferredKeys[0]}
	if err := test.IsSolved(&pairingBatchCircuit{Profile: &other}, assignment(valid, &other), curveID.ScalarField()); err == nil {
		t.Fatal("accepted mismatched anchors")
	}
	context, _ := pairingBatchContext(p)
	other = *p
	other.SetupID = "0x" + string(bytes.Repeat([]byte{'0'}, 64))
	changed, _ := pairingBatchContext(&other)
	if bytes.Equal(context, changed) {
		t.Fatal("setup identity absent from context")
	}
}

func TestBN254OptimizedFullVerifier(t *testing.T) {
	p, err := loadProfile(filepath.Join("testdata", "bn254", "profile.json"))
	if err != nil {
		t.Fatal(err)
	}
	for _, options := range []circuitOptions{{batchPairings: true}, {classicGLV: true}, {batchPairings: true, classicGLV: true}} {
		c := &optimizedCircuit{Inner: *newCircuit(p), Options: options}
		for _, kind := range []string{"valid", "claim", "evaluation", "commitment", "deferred"} {
			w, err := witnessAssignment(p, filepath.Join("testdata", "bn254", "witness.json"))
			if err != nil {
				t.Fatal(err)
			}
			switch kind {
			case "claim":
				w.Claim[0] = new(big.Int).Add(w.Claim[0].(*big.Int), big.NewInt(1))
			case "evaluation":
				w.Values[1] = new(big.Int).Add(w.Values[1].(*big.Int), big.NewInt(1))
			case "commitment":
				_, _, g, _ := bn.Generators()
				w.Points[0] = newCircuitG1(g)
			case "deferred":
				_, _, g, _ := bn.Generators()
				w.Deferred[0] = newCircuitG1(g)
			}
			err = test.IsSolved(c, &optimizedCircuit{Inner: *w, Options: options}, curveID.ScalarField())
			if (err == nil) != (kind == "valid") {
				t.Fatalf("options=%+v mutation=%s: %v", options, kind, err)
			}
		}
	}
}

type pairingBatchReductionCircuit struct {
	Wide     [64]uints.U8
	Expected frontend.Variable
}

func (c *pairingBatchReductionCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	wide := make([]uints.U8, len(c.Wide))
	for i, b := range c.Wide {
		wide[i] = u.ByteValueOf(u.Value(b))
	}
	api.AssertIsEqual(pairingBatchScalar(api, u, wide), c.Expected)
	return nil
}

func TestPairingBatchReductionRejectsZero(t *testing.T) {
	for _, value := range []*big.Int{new(big.Int), new(big.Int).Set(scalarModulus()), big.NewInt(1), new(big.Int).Add(scalarModulus(), big.NewInt(9)), new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 512), big.NewInt(1))} {
		wide := value.FillBytes(make([]byte, 64))
		for i, j := 0, len(wide)-1; i < j; i, j = i+1, j-1 {
			wide[i], wide[j] = wide[j], wide[i]
		}
		expected := new(big.Int).Mod(value, scalarModulus())
		w := &pairingBatchReductionCircuit{Expected: expected}
		copy(w.Wide[:], uints.NewU8Array(wide))
		err := test.IsSolved(&pairingBatchReductionCircuit{}, w, curveID.ScalarField())
		if (err == nil) != (expected.Sign() != 0) {
			t.Fatalf("challenge reduction %s: %v", value, err)
		}
	}
}
