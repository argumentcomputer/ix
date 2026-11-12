package main

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/math/bits"
)

// Challenge expansion runs after the witness commitment. Bit constraints avoid
// creating lookup commitments that would depend on their own challenge.
type aiurBlakeWord [32]frontend.Variable

func aiurBlakeConstant(value uint32) (word aiurBlakeWord) {
	for i := range word {
		word[i] = (value >> i) & 1
	}
	return
}

func aiurBlakeXor(api frontend.API, a, b aiurBlakeWord) (word aiurBlakeWord) {
	for i := range word {
		word[i] = api.Xor(a[i], b[i])
	}
	return
}

func aiurBlakeAdd(api frontend.API, words ...aiurBlakeWord) (word aiurBlakeWord) {
	var sum frontend.Variable = 0
	for _, value := range words {
		sum = api.Add(sum, bits.FromBinary(api, value[:]))
	}
	width := 32
	for maximum := len(words) - 1; maximum > 0; maximum >>= 1 {
		width++
	}
	binary := bits.ToBinary(api, sum, bits.WithNbDigits(width))
	copy(word[:], binary[:32])
	return
}

func aiurBlakeRotate(a aiurBlakeWord, amount int) (word aiurBlakeWord) {
	for i := range word {
		word[i] = a[(i+amount)%32]
	}
	return
}

const aiurLookupDomain = "ix/aiur-plonk/logup/v1\x00"

// gamma is the native commitment challenge; BLAKE3 independently expands it
// to beta using 64 output bytes reduced in the scalar field.
func aiurLookupBeta(api frontend.API, gamma frontend.Variable) frontend.Variable {
	if len(aiurLookupDomain)+32 > 64 {
		panic("Aiur lookup challenge exceeds one BLAKE3 block")
	}
	input := make([]frontend.Variable, 0, 512)
	for _, value := range []byte(aiurLookupDomain) {
		for bit := 0; bit < 8; bit++ {
			input = append(input, (value>>bit)&1)
		}
	}
	input = append(input, bits.ToBinary(api, gamma, bits.WithNbDigits(256))...)
	length := len(input) / 8
	for len(input) < 512 {
		input = append(input, 0)
	}
	var block [16]aiurBlakeWord
	for i := range block {
		copy(block[i][:], input[32*i:32*i+32])
	}
	var state [16]aiurBlakeWord
	for i := range 8 {
		state[i] = aiurBlakeConstant(blakeIV[i])
	}
	for i := range 4 {
		state[8+i] = aiurBlakeConstant(blakeIV[i])
	}
	state[12], state[13] = aiurBlakeConstant(0), aiurBlakeConstant(0)
	state[14], state[15] = aiurBlakeConstant(uint32(length)), aiurBlakeConstant(1|2|8)
	g := func(a, b, c, d int, x, y aiurBlakeWord) {
		state[a] = aiurBlakeAdd(api, state[a], state[b], x)
		state[d] = aiurBlakeRotate(aiurBlakeXor(api, state[d], state[a]), 16)
		state[c] = aiurBlakeAdd(api, state[c], state[d])
		state[b] = aiurBlakeRotate(aiurBlakeXor(api, state[b], state[c]), 12)
		state[a] = aiurBlakeAdd(api, state[a], state[b], y)
		state[d] = aiurBlakeRotate(aiurBlakeXor(api, state[d], state[a]), 8)
		state[c] = aiurBlakeAdd(api, state[c], state[d])
		state[b] = aiurBlakeRotate(aiurBlakeXor(api, state[b], state[c]), 7)
	}
	for range 7 {
		g(0, 4, 8, 12, block[0], block[1])
		g(1, 5, 9, 13, block[2], block[3])
		g(2, 6, 10, 14, block[4], block[5])
		g(3, 7, 11, 15, block[6], block[7])
		g(0, 5, 10, 15, block[8], block[9])
		g(1, 6, 11, 12, block[10], block[11])
		g(2, 7, 8, 13, block[12], block[13])
		g(3, 4, 9, 14, block[14], block[15])
		previous := block
		for i, index := range blakePermutation {
			block[i] = previous[index]
		}
	}
	for i := range 8 {
		state[i] = aiurBlakeXor(api, state[i], state[i+8])
		state[i+8] = aiurBlakeXor(api, state[i+8], aiurBlakeConstant(blakeIV[i]))
	}
	var result frontend.Variable = 0
	for i := 15; i >= 0; i-- {
		result = api.Add(api.Mul(result, uint64(1)<<32), bits.FromBinary(api, state[i][:]))
	}
	return result
}
