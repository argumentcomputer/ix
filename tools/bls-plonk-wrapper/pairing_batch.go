package main

import (
	"encoding/json"
	"fmt"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/bits"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/zeebo/blake3"
)

func pairingBatchContext(p *profile) ([]byte, error) {
	encoded, err := json.Marshal(p)
	if err != nil {
		return nil, err
	}
	digest := blake3.Sum256(encoded)
	return append([]byte("ix/plonk/pairing-batch/"+curveID.String()+"/v1\x00"), digest[:]...), nil
}

// The final inner transcript state commits to all packet scalars and points,
// including the deferred public operands and the final opening witnesses.
// The fresh challenge also binds the computed MSM outputs after they are fixed.
func pairingBatchChallenge(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[baseField], context []byte, claim [2]frontend.Variable, packetDigest []uints.U8, operands [4]*circuitG1) frontend.Variable {
	if len(packetDigest) != 32 {
		panic("invalid packet transcript digest length")
	}
	input := uints.NewU8Array(context)
	for _, limb := range claim {
		b := bits.ToBinary(api, limb, bits.WithNbDigits(128))
		for j := 0; j < 16; j++ {
			input = append(input, u.Bytes.FromBits(b[8*j:8*j+8]...))
		}
	}
	input = append(input, packetDigest...)
	for _, point := range operands {
		input = append(input, pointBytes(api, u, f, point)...)
	}
	out := blakeXOF(u, input, 64)
	return pairingBatchScalar(api, u, out)
}

func pairingBatchScalar(api frontend.API, u *uints.BinaryField[uints.U32], wide []uints.U8) frontend.Variable {
	if len(wide) != 64 {
		panic("batching challenge requires 512 bits")
	}
	rho := littleEndian(api, u, wide)
	api.AssertIsDifferent(rho, 0)
	return rho
}

func (c *wrapperCircuit) batchedPairing(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[baseField], s *emulated.Field[scalarField], curve *sw_emulated.Curve[baseField, scalarField], packetDigest []uints.U8, left, right *circuitG1) error {
	outer, err := g2Keys(c.Profile.OuterKeys)
	if err != nil {
		return err
	}
	inner, err := g2Keys(c.Profile.DeferredKeys)
	if err != nil {
		return err
	}
	if !outer[0].Equal(&inner[0]) || !outer[1].Equal(&inner[1]) {
		return fmt.Errorf("pairing batching requires identical ordered G2 anchors")
	}
	context, err := pairingBatchContext(c.Profile)
	if err != nil {
		return err
	}
	leftCanonical := circuitG1{X: *f.ReduceStrict(&left.X), Y: *f.ReduceStrict(&left.Y)}
	rightCanonical := circuitG1{X: *f.ReduceStrict(&right.X), Y: *f.ReduceStrict(&right.Y)}
	rho := pairingBatchChallenge(api, u, f, context, c.Claim, packetDigest, [4]*circuitG1{&leftCanonical, &rightCanonical, &c.Deferred[0], &c.Deferred[1]})
	scalar := s.FromBits(bits.ToBinary(api, rho)...)
	a := curve.AddUnified(left, curve.ScalarMul(&c.Deferred[0], scalar))
	b := curve.AddUnified(curve.Neg(right), curve.ScalarMul(&c.Deferred[1], scalar))
	pairing, err := newPairing(api)
	if err != nil {
		return err
	}
	h, tauH := newCircuitG2Fixed(outer[0]), newCircuitG2Fixed(outer[1])
	return pairing.PairingCheck([]*circuitG1{a, b}, []*circuitG2{&h, &tauH})
}
