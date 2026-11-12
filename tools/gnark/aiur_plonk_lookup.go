package main

import (
	"strconv"
	"strings"

	"github.com/consensys/gnark/frontend"
)

type aiurMessageGroup struct {
	count    frontend.Variable
	negative bool
	args     [][]frontend.Variable
}

// The polynomial is len(args)*gamma^len(args) + sum(args[i]*gamma^i).
// Constant coefficients and powers are shared across rows without changing
// the fingerprint or depending on any witness value after commitment.
func aiurLookupDenominator(api frontend.API, beta frontend.Variable, powers []frontend.Variable, args []frontend.Variable, bases map[string]frontend.Variable) frontend.Variable {
	var signature strings.Builder
	signature.WriteString(strconv.Itoa(len(args)))
	constants := make([]frontend.Variable, len(args))
	for i, value := range args {
		if constant, ok := api.Compiler().ConstantValue(value); ok {
			constants[i] = constant
			signature.WriteByte('|')
			signature.WriteString(strconv.Itoa(i))
			signature.WriteByte(':')
			signature.WriteString(constant.Text(16))
		}
	}
	key := signature.String()
	base, ok := bases[key]
	if !ok {
		base = api.Add(beta, api.Mul(len(args), powers[len(args)]))
		for i, value := range constants {
			if value != nil {
				base = api.Add(base, api.Mul(value, powers[i]))
			}
		}
		bases[key] = base
	}
	denominator := base
	for i, value := range args {
		if constants[i] == nil {
			denominator = api.Add(denominator, api.Mul(value, powers[i]))
		}
	}
	return denominator
}

func aiurLogUp(api frontend.API, gamma frontend.Variable, messages []aiurMessageGroup) error {
	beta := aiurLookupBeta(api, gamma)
	maximum := 0
	for _, group := range messages {
		for _, args := range group.args {
			maximum = max(maximum, len(args))
		}
	}
	powers := make([]frontend.Variable, maximum+1)
	powers[0] = 1
	if maximum > 0 {
		powers[1] = gamma
	}
	for i := 2; i < len(powers); i++ {
		powers[i] = api.Mul(powers[i-1], gamma)
	}
	bases := make(map[string]frontend.Variable)
	var denominators []frontend.Variable
	for _, group := range messages {
		for _, args := range group.args {
			denominators = append(denominators, aiurLookupDenominator(api, beta, powers, args, bases))
		}
	}
	// Both APIs constrain inverse*denominator=1. In particular, a zero
	// denominator cannot be admitted by zero multiplicity or by a hint value.
	var inverses []frontend.Variable
	if batch, ok := api.(frontend.BatchInverter); ok {
		inverses = batch.BatchInvert(denominators)
	} else {
		inverses = make([]frontend.Variable, len(denominators))
		for i, d := range denominators {
			inverses[i] = api.Inverse(d)
		}
	}
	var sum frontend.Variable = 0
	cursor := 0
	for _, group := range messages {
		var partial frontend.Variable = 0
		for range group.args {
			partial = api.Add(partial, inverses[cursor])
			cursor++
		}
		term := api.Mul(group.count, partial)
		if group.negative {
			sum = api.Sub(sum, term)
		} else {
			sum = api.Add(sum, term)
		}
	}
	api.AssertIsEqual(sum, 0)
	return nil
}
