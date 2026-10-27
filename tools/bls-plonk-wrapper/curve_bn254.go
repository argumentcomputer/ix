//go:build bn254

package main

import (
	"fmt"
	"github.com/consensys/gnark-crypto/ecc"
	native "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	backend "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/frontend"
	sw "github.com/consensys/gnark/std/algebra/emulated/sw_bn254"
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

const curveID = ecc.BN254
const baseBytes = 32
const pointBytesLen = 32
const pointLimbBytes = 16
const g2ExportBytes = 128
const anchorBytesLen = 320
const srsMagic = "IXBPSR01"
const vkFormat = "ix-bn254-plonk-vk-v1"
const artifactFormat = "ix-bn254-plonk-artifacts-v1"
const lagrangeFormat = "ix-bn254-plonk-lagrange-v1"

var curveParameters = sw_emulated.GetBN254Params

func isCompressedPoint(b byte) bool { return b&0xc0 != 0 }
func encodePoint(p nativeG1) []byte {
	out := make([]byte, 32)
	if p.IsInfinity() {
		out[31] = 0x40
		return out
	}
	x := p.X.Bytes()
	for i := range out {
		out[i] = x[31-i]
	}
	var y big.Int
	p.Y.BigInt(&y)
	if y.Cmp(new(big.Int).Rsh(new(big.Int).Set(fp.Modulus()), 1)) > 0 {
		out[31] |= 0x80
	}
	return out
}
func decodeG2(b []byte) (nativeG2, error) {
	var p nativeG2
	if len(b) != 128 {
		return p, fmt.Errorf("invalid G2 length")
	}
	for i, v := range []*fp.Element{&p.X.A0, &p.X.A1, &p.Y.A0, &p.Y.A1} {
		if err := v.SetBytesCanonical(b[i*32 : (i+1)*32]); err != nil {
			return p, err
		}
	}
	if p.IsInfinity() || !p.IsOnCurve() || !p.IsInSubGroup() {
		return p, fmt.Errorf("invalid G2 anchor")
	}
	return p, nil
}
func encodeAnchors(vk *nativeVerifyingKey) []byte {
	out := make([]byte, 0, 320)
	for _, v := range []*fp.Element{&vk.Kzg.G1.X, &vk.Kzg.G1.Y, &vk.Kzg.G2[0].X.A0, &vk.Kzg.G2[0].X.A1, &vk.Kzg.G2[0].Y.A0, &vk.Kzg.G2[0].Y.A1, &vk.Kzg.G2[1].X.A0, &vk.Kzg.G2[1].X.A1, &vk.Kzg.G2[1].Y.A0, &vk.Kzg.G2[1].Y.A1} {
		b := v.Bytes()
		out = append(out, b[:]...)
	}
	return out
}
func pointBytes(api frontend.API, u *uints.BinaryField[uints.U32], f *emulated.Field[baseField], p *circuitG1) []uints.U8 {
	f.AssertIsInRange(&p.X)
	f.AssertIsInRange(&p.Y)
	x, y := f.ToBitsCanonical(&p.X), f.ToBitsCanonical(&p.Y)
	half := new(big.Int).Rsh(new(big.Int).Set(fp.Modulus()), 1)
	bound := make([]frontend.Variable, len(y))
	for i := range bound {
		bound[i] = half.Bit(i)
	}
	sign := cmp.IsLessBinary(api, bound, y)
	infinity := api.And(f.IsZero(&p.X), f.IsZero(&p.Y))
	for len(x) < 256 {
		x = append(x, 0)
	}
	out := make([]uints.U8, 32)
	for i := range out {
		out[i] = u.Bytes.FromBits(x[8*i : 8*i+8]...)
	}
	out[31] = u.ByteValueOf(api.Add(u.Value(out[31]), api.Mul(64, infinity), api.Mul(128, sign)))
	return out
}
