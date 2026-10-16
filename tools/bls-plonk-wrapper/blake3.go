package main

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/uints"
)

var blakeIV = [8]uint32{0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19}
var blakePermutation = [16]int{2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8}

type blakeOutput struct {
	cv      [8]uints.U32
	block   [16]uints.U32
	counter uint64
	length  uint32
	flags   uint32
}

func blakeCompress(u *uints.BinaryField[uints.U32], out blakeOutput, counter uint64, flags uint32) [16]uints.U32 {
	var v [16]uints.U32
	copy(v[:8], out.cv[:])
	for i := 0; i < 4; i++ {
		v[8+i] = uints.NewU32(blakeIV[i])
	}
	v[12], v[13] = uints.NewU32(uint32(counter)), uints.NewU32(uint32(counter>>32))
	v[14], v[15] = uints.NewU32(out.length), uints.NewU32(flags)
	m := out.block
	g := func(a, b, c, d int, x, y uints.U32) {
		v[a] = u.Add(v[a], v[b], x)
		v[d] = u.Lrot(u.Xor(v[d], v[a]), -16)
		v[c] = u.Add(v[c], v[d])
		v[b] = u.Lrot(u.Xor(v[b], v[c]), -12)
		v[a] = u.Add(v[a], v[b], y)
		v[d] = u.Lrot(u.Xor(v[d], v[a]), -8)
		v[c] = u.Add(v[c], v[d])
		v[b] = u.Lrot(u.Xor(v[b], v[c]), -7)
	}
	for round := 0; round < 7; round++ {
		g(0, 4, 8, 12, m[0], m[1])
		g(1, 5, 9, 13, m[2], m[3])
		g(2, 6, 10, 14, m[4], m[5])
		g(3, 7, 11, 15, m[6], m[7])
		g(0, 5, 10, 15, m[8], m[9])
		g(1, 6, 11, 12, m[10], m[11])
		g(2, 7, 8, 13, m[12], m[13])
		g(3, 4, 9, 14, m[14], m[15])
		previous := m
		for i, index := range blakePermutation {
			m[i] = previous[index]
		}
	}
	for i := 0; i < 8; i++ {
		v[i] = u.Xor(v[i], v[i+8])
		v[i+8] = u.Xor(v[i+8], out.cv[i])
	}
	return v
}

func (out blakeOutput) chaining(u *uints.BinaryField[uints.U32]) [8]uints.U32 {
	v := blakeCompress(u, out, out.counter, out.flags)
	return [8]uints.U32(v[:8])
}

func blakeChunk(u *uints.BinaryField[uints.U32], input []uints.U8, counter uint64) blakeOutput {
	var cv [8]uints.U32
	for i := range cv {
		cv[i] = uints.NewU32(blakeIV[i])
	}
	blocks := max(1, (len(input)+63)/64)
	var out blakeOutput
	for i := 0; i < blocks; i++ {
		start, end := i*64, min((i+1)*64, len(input))
		var padded [64]uints.U8
		for j := range padded {
			padded[j] = uints.NewU8(0)
		}
		copy(padded[:], input[start:end])
		out = blakeOutput{cv: cv, counter: counter, length: uint32(end - start)}
		for j := range out.block {
			out.block[j] = u.PackLSB(padded[4*j : 4*j+4]...)
		}
		if i == 0 {
			out.flags |= 1
		}
		if i == blocks-1 {
			out.flags |= 2
		} else {
			cv = out.chaining(u)
		}
	}
	return out
}

func blakeParent(left, right [8]uints.U32) blakeOutput {
	out := blakeOutput{length: 64, flags: 4}
	for i := range out.cv {
		out.cv[i] = uints.NewU32(blakeIV[i])
	}
	copy(out.block[:8], left[:])
	copy(out.block[8:], right[:])
	return out
}

// blakeXOF implements unkeyed BLAKE3 for a circuit-fixed input and output length.
func blakeXOF(u *uints.BinaryField[uints.U32], input []uints.U8, length int) []uints.U8 {
	chunks := max(1, (len(input)+1023)/1024)
	stack := make([][8]uints.U32, 0)
	var out blakeOutput
	for i := 0; i < chunks; i++ {
		out = blakeChunk(u, input[i*1024:min((i+1)*1024, len(input))], uint64(i))
		if i == chunks-1 {
			break
		}
		cv := out.chaining(u)
		for count := i + 1; count&1 == 0; count >>= 1 {
			cv = blakeParent(stack[len(stack)-1], cv).chaining(u)
			stack = stack[:len(stack)-1]
		}
		stack = append(stack, cv)
	}
	for i := len(stack) - 1; i >= 0; i-- {
		out = blakeParent(stack[i], out.chaining(u))
	}
	result := make([]uints.U8, 0, length+63)
	for counter := uint64(0); len(result) < length; counter++ {
		block := blakeCompress(u, out, counter, out.flags|8)
		for _, word := range block {
			result = append(result, word[:]...)
		}
	}
	return result[:length]
}

type transcript struct {
	api    frontend.API
	u      *uints.BinaryField[uints.U32]
	state  []uints.U8
	buffer []uints.U8
}

func newTranscript(api frontend.API, u *uints.BinaryField[uints.U32], seed []byte) *transcript {
	return &transcript{api: api, u: u, state: uints.NewU8Array(make([]byte, 32)), buffer: uints.NewU8Array(seed)}
}

func (t *transcript) observe(v []uints.U8) { t.buffer = append(t.buffer, v...) }

func (t *transcript) sample() frontend.Variable {
	input := append(append([]uints.U8(nil), t.state...), t.buffer...)
	out := blakeXOF(t.u, input, 96)
	t.state, t.buffer = out[64:], nil
	var result frontend.Variable = 0
	for i := 63; i >= 0; i-- {
		result = t.api.Add(t.api.Mul(result, 256), t.u.Value(out[i]))
	}
	return result
}
