//go:build !bn254

package main

import (
	"bytes"
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"
	native "github.com/consensys/gnark-crypto/ecc/bls12-381"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fp"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	backend "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bls12381"
	"github.com/consensys/gnark/std/algebra/emulated/sw_emulated"
	"github.com/consensys/gnark/std/math/cmp"
	"github.com/consensys/gnark/std/math/emulated"
	"github.com/consensys/gnark/std/math/uints"
	"math/big"
)

type nativeG1 = native.G1Affine
type nativeG2 = native.G2Affine
type nativeSRS = kzg.SRS
type nativeKzgProvingKey = kzg.ProvingKey
type nativeVerifyingKey = backend.VerifyingKey
type nativeProof = backend.Proof
type circuitG1 = sw.G1Affine
type circuitG2 = sw.G2Affine
type circuitScalar = sw.Scalar
type baseField = sw.BaseField
type scalarField = sw.ScalarField

var baseModulus = fp.Modulus
var scalarModulus = fr.Modulus
var precomputeLines = native.PrecomputeLines
var toLagrange = kzg.ToLagrangeG1
var newCircuitG1 = sw.NewG1Affine
var newCircuitG2Fixed = sw.NewG2AffineFixed
var newPairing = sw.NewPairing

const curveID = ecc.BLS12_381
const baseBytes = 48
const pointBytesLen = 48
const pointLimbBytes = 24
const g2ExportBytes = 96
const anchorBytesLen = 240
const srsMagic = "IXPSRS01"
const profileFormat = "ix-bls-plonk-profile-v1"
const artifactFormat = "ix-bls-plonk-artifacts-v1"
const lagrangeFormat = "ix-plonk-lagrange-v1"

var curveParameters = sw_emulated.GetBLS12381Params

func isCompressedPoint(b byte) bool { return b&0x80 != 0 }
func encodePoint(p nativeG1) []byte { b := p.Bytes(); return b[:] }
func decodeG2(b []byte) (nativeG2, error) {
	var p nativeG2
	if _, err := p.SetBytes(b); err != nil {
		return p, err
	}
	canonical := p.Bytes()
	if p.IsInfinity() || !bytes.Equal(canonical[:], b) {
		return p, fmt.Errorf("invalid G2 anchor")
	}
	return p, nil
}
func encodeAnchors(vk *nativeVerifyingKey) []byte {
	g, h, t := vk.Kzg.G1.Bytes(), vk.Kzg.G2[0].Bytes(), vk.Kzg.G2[1].Bytes()
	return append(append(append([]byte{}, g[:]...), h[:]...), t[:]...)
}
func pointBytes(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[baseField], point *circuitG1) []uints.U8 {
	f.AssertIsInRange(&point.X)
	f.AssertIsInRange(&point.Y)
	x := f.ToBitsCanonical(&point.X)
	y := f.ToBitsCanonical(&point.Y)
	half := new(big.Int).Rsh(new(big.Int).Set(baseModulus()), 1)
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

func importLagrangeSP1(_, _, _, _ string) error {
	return fmt.Errorf("SP1 Lagrange import requires the BN254 build")
}
