//go:build plonk || !groth16

package main

// Prover-side values of the non-input wires of an `ix-aiur-scs-v1` circuit
// (over either BN254 Fr or BLS12-381 Fr).
//
// Every wire that is not an input is the output of a gnark hint, which adds
// no constraint: the file's gates, added by aiurScsCircuit.Define, are the
// only constraints on these wires, and a wrong hint value makes the solver
// fail on the gate it violates. Nothing here affects the compiled
// constraints; it only decides how the solver computes the witness.
//
// A solved wire u of gate qL·a + qR·b + qO·c + qM·a·b + qC = 0 is affine in
// u: A·u + B = 0. Where A is a constant, the hint receives the gate's known
// terms already scaled by −1/A (gnark hint inputs are single terms
// coefficient·wire), so it only adds them, or adds one product. After the
// commitment two kinds of wires are grouped, so that the solver runs one
// hint per group:
//   - quotients u·d = n (the log-derivative terms, whose A depends on a
//     wire), consecutive ones sharing one hint and one field inversion;
//   - chains u_k = u_{k−1} + t_k (the running sum of the log-derivative
//     argument, about one link per message, and the fingerprints' linear
//     steps), in segments that the solver runs in parallel.
//
// Hints are created when a gate first reads their wire, so hint
// instructions stay interleaved with the gates (gnark's constraint iterator
// recurses once per consecutive non-constraint instruction).

import (
	"fmt"
	"math/big"

	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
)

func init() {
	solver.RegisterHint(aiurScsSolveHint, aiurScsBitHint, aiurScsZeroHint, aiurScsSumHint, aiurScsProductHint,
		aiurScsChainHint, aiurScsDivHint)
}

// Quotients per division hint, and links per chain segment.
var aiurScsDivBatch = 1024
var aiurScsChainSegment = 1 << 14

type aiurScsElem[T any] interface {
	*T
	SetBigInt(*big.Int) *T
	BigInt(*big.Int) *big.Int
	SetInt64(int64) *T
	SetOne() *T
	IsZero() bool
	IsOne() bool
	Add(*T, *T) *T
	Mul(*T, *T) *T
	Neg(*T) *T
	Inverse(*T) *T
}

type aiurScsWireBuilder interface {
	wire(x uint32, gate int) (frontend.Variable, error)
	post(api frontend.API, gamma frontend.Variable) error
	stats() string
}

type aiurScsTerm[T any] struct {
	w uint32
	c T
}

// aiurScsForm is gate solved for u. With div unset, u = Σ c·w +
// pc·w[pa]·w[pb] (when prod) + k. With div set, u·(d0 + dc·w[dw]) = Σ c·w + k.
type aiurScsForm[T comparable, P aiurScsElem[T]] struct {
	terms  [3]aiurScsTerm[T]
	n      int
	prod   bool
	pa, pb uint32
	pc, k  T
	div    bool
	dw     uint32
	d0, dc T
}

func (f *aiurScsForm[T, P]) quotient() bool {
	return f.div && P(&f.d0).IsZero() && f.n == 1 && P(&f.k).IsZero()
}

// link is the term of coefficient 1 that a chain link adds its other term
// to, or −1.
func (f *aiurScsForm[T, P]) link() int {
	if f.div || f.prod || f.n != 2 || !P(&f.k).IsZero() {
		return -1
	}
	for i := range 2 {
		if P(&f.terms[i].c).IsOne() {
			return i
		}
	}
	return -1
}

// aiurScsUnit is a group of post-commitment wires created together: a
// quotient batch, or one segment of a chain (base: the wire the chain
// starts from; totals: one sum per earlier segment).
type aiurScsUnit struct {
	ws     []uint32
	chain  *aiurScsChain
	seg    int
	active bool
}

type aiurScsChain struct {
	base   uint32
	totals []frontend.Variable
	units  []int32
}

type aiurScsWires[T comparable, P aiurScsElem[T]] struct {
	api         frontend.API
	s           *aiurScs
	v           []frontend.Variable
	coeff       []T
	inverse     map[T]T
	afterCommit bool
	// unit[x] is the index of x's group in units, or −1.
	unit  []int32
	units []aiurScsUnit
	// active marks single wires whose dependencies are being created.
	active    map[uint32]bool
	dissolved int
}

func newAiurScsWires(api frontend.API, s *aiurScs, v []frontend.Variable) aiurScsWireBuilder {
	if api.Compiler().Field().Cmp(blsfr.Modulus()) == 0 {
		return newAiurScsWiresTyped[blsfr.Element, *blsfr.Element](api, s, v)
	}
	return newAiurScsWiresTyped[fr.Element, *fr.Element](api, s, v)
}

func newAiurScsWiresTyped[T comparable, P aiurScsElem[T]](api frontend.API, s *aiurScs, v []frontend.Variable) *aiurScsWires[T, P] {
	p := &aiurScsWires[T, P]{api: api, s: s, v: v, coeff: make([]T, len(s.Coeffs)), inverse: map[T]T{}}
	for i := range s.Coeffs {
		P(&p.coeff[i]).SetBigInt(&s.Coeffs[i])
	}
	return p
}

func aiurScsBig[T any, P aiurScsElem[T]](x P) *big.Int { return x.BigInt(new(big.Int)) }

func (p *aiurScsWires[T, P]) hint(f solver.Hint, n int, in ...frontend.Variable) ([]frontend.Variable, error) {
	return p.api.Compiler().NewHint(f, n, in...)
}

// wire is the variable of x as gate reads it. Before the commitment a
// solved wire is created at its solve gate; after it, any determined wire is
// created (with what it depends on) when first read.
func (p *aiurScsWires[T, P]) wire(x uint32, gate int) (frontend.Variable, error) {
	if p.v[x] != nil {
		return p.v[x], nil
	}
	kind, a, _ := p.s.hint(x)
	switch {
	case kind == aiurScsFree:
		out, err := p.hint(aiurScsZeroHint, 1)
		return p.setOut(x, out, err)
	case kind == aiurScsChallenge && !p.afterCommit:
		return nil, fmt.Errorf("Aiur SCS gate %d reads γ before the commitment", gate)
	case p.afterCommit && (kind == aiurScsSolve || kind == aiurScsBit):
		if err := p.need(x); err != nil {
			return nil, err
		}
		return p.v[x], nil
	case kind == aiurScsSolve && int(a) == gate:
		if err := p.single(x); err != nil {
			return nil, err
		}
		return p.v[x], nil
	}
	return nil, fmt.Errorf("Aiur SCS gate %d reads wire %d (kind %d) before it is determined", gate, x, kind)
}

func (p *aiurScsWires[T, P]) setOut(x uint32, out []frontend.Variable, err error) (frontend.Variable, error) {
	if err != nil {
		return nil, err
	}
	p.v[x] = out[0]
	return out[0], nil
}

func (p *aiurScsWires[T, P]) inv(a P) T {
	if r, ok := p.inverse[*a]; ok {
		return r
	}
	var r T
	P(&r).Inverse(a)
	p.inverse[*a] = r
	return r
}

func (p *aiurScsWires[T, P]) form(gate int, u uint32) (f aiurScsForm[T, P], err error) {
	g := p.s.gate(gate)
	al, be, om := P(&p.coeff[g.Al]), P(&p.coeff[g.Be]), P(&p.coeff[g.Om])
	sL, sR, sO, sM := g.Sel&1 != 0, g.Sel&2 != 0, g.Sel&4 != 0, g.Sel&8 != 0
	ua, ub, uc := g.A == u, g.B == u, g.C == u
	if !ua && !ub && !uc {
		return f, fmt.Errorf("Aiur SCS gate %d does not contain its solved wire %d", gate, u)
	}
	if sM && ua && ub {
		return f, fmt.Errorf("Aiur SCS gate %d is quadratic in wire %d", gate, u)
	}
	var A T
	if ua && sL {
		P(&A).Add(&A, al)
	}
	if ub && sR {
		P(&A).Add(&A, be)
	}
	if uc && sO {
		P(&A).Add(&A, om)
	}
	var qM T
	if sM {
		P(&qM).Mul(al, be)
	}
	P(&f.k).SetInt64(int64(g.QC))
	add := func(c P, w uint32) {
		f.terms[f.n] = aiurScsTerm[T]{w: w, c: *c}
		f.n++
	}
	if !ua && sL {
		add(al, g.A)
	}
	if !ub && sR {
		add(be, g.B)
	}
	if !uc && sO {
		add(om, g.C)
	}
	var scale T
	if sM && ua != ub {
		f.div, f.d0, f.dc, f.dw = true, A, qM, g.A
		if ua {
			f.dw = g.B
		}
		P(&scale).SetOne()
	} else {
		if P(&A).IsZero() {
			return f, fmt.Errorf("Aiur SCS gate %d does not determine wire %d", gate, u)
		}
		scale = p.inv(&A)
		if sM && !ua && !ub {
			f.prod, f.pa, f.pb, f.pc = true, g.A, g.B, qM
			P(&f.pc).Mul(&f.pc, &scale)
			P(&f.pc).Neg(&f.pc)
		}
	}
	P(&scale).Neg(&scale)
	for i := 0; i < f.n; i++ {
		P(&f.terms[i].c).Mul(&f.terms[i].c, &scale)
	}
	P(&f.k).Mul(&f.k, &scale)
	return f, nil
}

// term is c·w for an existing wire w (a hint input, no constraint).
func (p *aiurScsWires[T, P]) term(t aiurScsTerm[T]) frontend.Variable {
	return p.api.Mul(p.v[t.w], aiurScsBig[T, P](&t.c))
}

// single creates the hint of solved or bit wire x, all of whose inputs
// exist.
func (p *aiurScsWires[T, P]) single(x uint32) error {
	kind, a, b := p.s.hint(x)
	if kind == aiurScsBit {
		out, err := p.hint(aiurScsBitHint, 1, int(b), p.v[a])
		_, err = p.setOut(x, out, err)
		return err
	}
	f, err := p.form(int(a), x)
	if err != nil {
		return err
	}
	if f.div {
		return p.general(x, int(a))
	}
	var in []frontend.Variable
	h := aiurScsSumHint
	if f.prod {
		in, h = append(in, p.term(aiurScsTerm[T]{w: f.pa, c: f.pc}), p.v[f.pb]), aiurScsProductHint
	}
	for i := 0; i < f.n; i++ {
		in = append(in, p.term(f.terms[i]))
	}
	if !P(&f.k).IsZero() || len(in) == 0 {
		in = append(in, aiurScsBig[T, P](&f.k))
	}
	out, err := p.hint(h, 1, in...)
	_, err = p.setOut(x, out, err)
	return err
}

// general solves x through aiurScsSolveHint, which reads the gate's selector
// code and coefficients as inputs.
func (p *aiurScsWires[T, P]) general(x uint32, gate int) error {
	s := p.s
	g := s.gate(gate)
	mask := 0
	inputs := []frontend.Variable{0, &s.Coeffs[g.Al], &s.Coeffs[g.Be], &s.Coeffs[g.Om], 0, 0, 0, 0}
	for k, y := range []uint32{g.A, g.B, g.C} {
		if y == x {
			mask |= 1 << k
		} else if aiurScsSlotRead(g.Sel, k) {
			inputs[5+k] = p.v[y]
		}
	}
	code := int(g.Sel) | mask<<4 | (int(g.QC)+128)<<8
	inputs[0] = code
	if inv, ok := aiurScsSolveInverseFor[T, P](uint64(code), &s.Coeffs[g.Al], &s.Coeffs[g.Be], &s.Coeffs[g.Om]); ok {
		inputs[4] = inv
	}
	out, err := p.hint(aiurScsSolveHint, 1, inputs...)
	_, err = p.setOut(x, out, err)
	return err
}

// reads appends the wires whose values x's hint reads.
func (p *aiurScsWires[T, P]) reads(x uint32, out []uint32) ([]uint32, error) {
	kind, a, _ := p.s.hint(x)
	if kind == aiurScsBit {
		return append(out, a), nil
	}
	f, err := p.form(int(a), x)
	if err != nil {
		return out, err
	}
	if f.div && !f.quotient() {
		g := p.s.gate(int(a))
		for k, y := range []uint32{g.A, g.B, g.C} {
			if y != x && aiurScsSlotRead(g.Sel, k) {
				out = append(out, y)
			}
		}
		return out, nil
	}
	for i := 0; i < f.n; i++ {
		out = append(out, f.terms[i].w)
	}
	if f.prod {
		out = append(out, f.pa, f.pb)
	}
	if f.div {
		out = append(out, f.dw)
	}
	return out, nil
}

// aiurScsSlotRead reports whether a gate's value depends on slot k (a, b,
// c) under selector bits sel.
func aiurScsSlotRead(sel uint8, k int) bool {
	return sel&(1<<k) != 0 || (k < 2 && sel&8 != 0)
}

// deps appends the wires that x's group (or x alone) reads and that do not
// exist yet.
func (p *aiurScsWires[T, P]) deps(x uint32, out []uint32) ([]uint32, error) {
	u := p.unit[x]
	if u < 0 {
		reads, err := p.reads(x, nil)
		for _, w := range reads {
			if p.v[w] == nil {
				out = append(out, w)
			}
		}
		return out, err
	}
	unit := &p.units[u]
	var reads []uint32
	for _, w := range unit.ws {
		var err error
		if reads, err = p.reads(w, reads[:0]); err != nil {
			return out, err
		}
		for _, y := range reads {
			if p.v[y] == nil && p.unit[y] != u {
				out = append(out, y)
			}
		}
	}
	if ch := unit.chain; ch != nil {
		if p.v[ch.base] == nil {
			out = append(out, ch.base)
		}
		if unit.seg > 0 {
			prev := p.units[ch.units[unit.seg-1]].ws
			if last := prev[len(prev)-1]; p.v[last] == nil {
				out = append(out, last)
			}
		}
	}
	return out, nil
}

// dissolve turns x's group into single wires when one of its members
// depends on another through wires outside it; for a chain, from x's
// segment on (earlier segments may already exist).
func (p *aiurScsWires[T, P]) dissolve(x uint32) {
	u := p.unit[x]
	units := []int32{u}
	if ch := p.units[u].chain; ch != nil {
		units = ch.units[p.units[u].seg:]
		ch.units = ch.units[:p.units[u].seg]
	}
	for _, k := range units {
		for _, w := range p.units[k].ws {
			p.unit[w] = -1
		}
		p.units[k] = aiurScsUnit{}
	}
	p.dissolved++
}

// need creates x and, first, every wire it depends on that does not exist,
// with an explicit stack (dependency chains are millions of wires long).
func (p *aiurScsWires[T, P]) need(x uint32) error {
	stack := []uint32{x}
	var deps []uint32
	for len(stack) > 0 {
		y := stack[len(stack)-1]
		if p.v[y] != nil {
			stack = stack[:len(stack)-1]
			continue
		}
		switch kind, _, _ := p.s.hint(y); kind {
		case aiurScsFree:
			if _, err := p.wire(y, -1); err != nil {
				return err
			}
			continue
		case aiurScsSolve, aiurScsBit:
		default:
			return fmt.Errorf("Aiur SCS wire %d (kind %d) is read before it is determined", y, kind)
		}
		var err error
		if deps, err = p.deps(y, deps[:0]); err != nil {
			return err
		}
		if len(deps) > 0 {
			if p.isActive(y) {
				if p.unit[y] < 0 {
					return fmt.Errorf("Aiur SCS wire %d depends on itself", y)
				}
				p.dissolve(y)
				continue
			}
			p.setActive(y, true)
			stack = append(stack, deps...)
			continue
		}
		p.setActive(y, false)
		if err := p.create(y); err != nil {
			return err
		}
		stack = stack[:len(stack)-1]
	}
	return nil
}

func (p *aiurScsWires[T, P]) isActive(x uint32) bool {
	if u := p.unit[x]; u >= 0 {
		return p.units[u].active
	}
	return p.active[x]
}

func (p *aiurScsWires[T, P]) setActive(x uint32, on bool) {
	if u := p.unit[x]; u >= 0 {
		p.units[u].active = on
	} else if on {
		p.active[x] = true
	} else {
		delete(p.active, x)
	}
}

// create emits the hint of x's group (or of x alone); its inputs exist.
func (p *aiurScsWires[T, P]) create(x uint32) error {
	u := p.unit[x]
	if u < 0 {
		return p.single(x)
	}
	unit := &p.units[u]
	if unit.chain == nil {
		in := make([]frontend.Variable, 0, 2*len(unit.ws))
		for _, w := range unit.ws {
			_, a, _ := p.s.hint(w)
			f, err := p.form(int(a), w)
			if err != nil {
				return err
			}
			in = append(in, p.term(f.terms[0]), p.term(aiurScsTerm[T]{w: f.dw, c: f.dc}))
		}
		out, err := p.hint(aiurScsDivHint, len(unit.ws), in...)
		if err != nil {
			return err
		}
		for k, w := range unit.ws {
			p.v[w] = out[k]
		}
		return nil
	}
	ch := unit.chain
	in := append([]frontend.Variable{p.v[ch.base]}, ch.totals[:unit.seg]...)
	ts := make([]frontend.Variable, 0, len(unit.ws))
	for _, w := range unit.ws {
		_, a, _ := p.s.hint(w)
		f, err := p.form(int(a), w)
		if err != nil {
			return err
		}
		ts = append(ts, p.term(f.terms[1-f.link()]))
	}
	out, err := p.hint(aiurScsChainHint, len(ts), append(in, ts...)...)
	if err != nil {
		return err
	}
	for k, w := range unit.ws {
		p.v[w] = out[k]
	}
	if unit.seg+1 < len(ch.units) {
		total, err := p.hint(aiurScsSumHint, 1, ts...)
		if err != nil {
			return err
		}
		ch.totals = append(ch.totals, total[0])
	}
	return nil
}

// post groups the wires determined after the commitment γ: quotient batches
// in solve-gate order, and chains, each link being the first wire (in
// solve-gate order) that adds a term to its predecessor with coefficient 1.
// Wires are then created on first read.
func (p *aiurScsWires[T, P]) post(api frontend.API, gamma frontend.Variable) error {
	s := p.s
	p.api, p.afterCommit = api, true
	p.v[s.Gamma] = gamma
	p.active = map[uint32]bool{}
	p.unit = make([]int32, s.Wires)
	for i := range p.unit {
		p.unit[i] = -1
	}
	solvedBy := make([]uint32, s.Gates-s.Pre)
	const none = ^uint32(0)
	for i := range solvedBy {
		solvedBy[i] = none
	}
	for x := uint32(0); int(x) < s.Wires; x++ {
		if kind, a, _ := s.hint(x); kind == aiurScsSolve && int(a) >= s.Pre {
			if solvedBy[int(a)-s.Pre] != none {
				return fmt.Errorf("Aiur SCS gate %d solves two wires", a)
			}
			solvedBy[int(a)-s.Pre] = x
		}
	}
	next := map[uint32]uint32{}
	pred := map[uint32]uint32{}
	var quotients, links []uint32
	for i, x := range solvedBy {
		if x == none {
			continue
		}
		f, err := p.form(s.Pre+i, x)
		if err != nil {
			return err
		}
		if f.quotient() {
			quotients = append(quotients, x)
			continue
		}
		if l := f.link(); l >= 0 {
			w := f.terms[l].w
			if _, taken := next[w]; !taken {
				next[w] = x
			}
			pred[x] = w
			links = append(links, x)
		}
	}
	for start := 0; start < len(quotients); start += aiurScsDivBatch {
		ws := quotients[start:min(start+aiurScsDivBatch, len(quotients))]
		for _, w := range ws {
			p.unit[w] = int32(len(p.units))
		}
		p.units = append(p.units, aiurScsUnit{ws: ws})
	}
	for _, x := range links {
		w := pred[x]
		if _, linked := pred[w]; linked && next[w] == x {
			continue
		}
		// x starts a chain from w; it follows first successors.
		ch := &aiurScsChain{base: w}
		var ws []uint32
		for y, ok := x, true; ok; y, ok = next[y] {
			ws = append(ws, y)
		}
		for start := 0; start < len(ws); start += aiurScsChainSegment {
			seg := ws[start:min(start+aiurScsChainSegment, len(ws))]
			for _, w := range seg {
				p.unit[w] = int32(len(p.units))
			}
			ch.units = append(ch.units, int32(len(p.units)))
			p.units = append(p.units, aiurScsUnit{ws: seg, chain: ch, seg: len(ch.units) - 1})
		}
	}
	return nil
}

func (p *aiurScsWires[T, P]) stats() string {
	quotients, chains, links := 0, 0, 0
	for _, u := range p.units {
		switch {
		case u.chain != nil:
			links += len(u.ws)
			if u.seg == 0 {
				chains++
			}
		case len(u.ws) > 0:
			quotients += len(u.ws)
		}
	}
	return fmt.Sprintf("%d quotients in batches, %d chains with %d links, %d groups dissolved", quotients, chains, links, p.dissolved)
}

func aiurScsReduce(x, q *big.Int) {
	for x.Cmp(q) >= 0 {
		x.Sub(x, q)
	}
}

// aiurScsSumHint: out[0] = Σ in.
func aiurScsSumHint(q *big.Int, in []*big.Int, out []*big.Int) error {
	if len(out) != 1 || len(in) == 0 {
		return fmt.Errorf("aiurScsSumHint arity")
	}
	out[0].SetUint64(0)
	for _, x := range in {
		out[0].Add(out[0], x)
	}
	if len(in) > 8 {
		out[0].Mod(out[0], q)
	} else {
		aiurScsReduce(out[0], q)
	}
	return nil
}

// aiurScsProductHint: out[0] = in[0]·in[1] + Σ in[2:].
func aiurScsProductHint(q *big.Int, in []*big.Int, out []*big.Int) error {
	if len(out) != 1 || len(in) < 2 || len(in) > 8 {
		return fmt.Errorf("aiurScsProductHint arity")
	}
	out[0].Mul(in[0], in[1])
	for _, x := range in[2:] {
		out[0].Add(out[0], x)
	}
	out[0].Mod(out[0], q)
	return nil
}

// aiurScsChainHint: with b = len(in) − len(out) base inputs,
// out[k] = Σ in[:b] + in[b] + … + in[b+k].
func aiurScsChainHint(q *big.Int, in []*big.Int, out []*big.Int) error {
	b := len(in) - len(out)
	if len(out) == 0 || b < 1 {
		return fmt.Errorf("aiurScsChainHint arity")
	}
	acc := new(big.Int)
	for _, x := range in[:b] {
		acc.Add(acc, x)
	}
	acc.Mod(acc, q)
	for k, x := range in[b:] {
		acc.Add(acc, x)
		aiurScsReduce(acc, q)
		out[k].Set(acc)
	}
	return nil
}

// aiurScsDivHint: in = n_0, d_0, n_1, d_1, …; out[k] = n_k / d_k, with one
// field inversion for the batch.
func aiurScsDivHint(q *big.Int, in []*big.Int, out []*big.Int) error {
	if len(out) == 0 || len(in) != 2*len(out) {
		return fmt.Errorf("aiurScsDivHint arity")
	}
	if q != nil && q.Cmp(blsfr.Modulus()) == 0 {
		den := make([]blsfr.Element, len(out))
		for k := range den {
			den[k].SetBigInt(in[2*k+1])
			if den[k].IsZero() {
				return fmt.Errorf("Aiur SCS quotient with a zero denominator")
			}
		}
		den = blsfr.BatchInvert(den)
		var n blsfr.Element
		for k := range den {
			n.SetBigInt(in[2*k])
			n.Mul(&n, &den[k])
			n.BigInt(out[k])
		}
		return nil
	}
	if q != nil && q.Cmp(fr.Modulus()) != 0 {
		return fmt.Errorf("unsupported Aiur SCS division field modulus")
	}
	den := make([]fr.Element, len(out))
	for k := range den {
		den[k].SetBigInt(in[2*k+1])
		if den[k].IsZero() {
			return fmt.Errorf("Aiur SCS quotient with a zero denominator")
		}
	}
	den = fr.BatchInvert(den)
	var n fr.Element
	for k := range den {
		n.SetBigInt(in[2*k])
		n.Mul(&n, &den[k])
		n.BigInt(out[k])
	}
	return nil
}

// aiurScsSolveTerms splits gate qL·a + qR·b + qO·c + qM·a·b + qC, as a
// function of the wire u that fills the slots of mask, into A·u + B. code is
// sel | mask<<4 | (qC+128)<<8; w holds the gate's other wire values (masked
// slots ignored). A constant A (no qM·w term) is returned with w unused.
func aiurScsSolveTerms[T comparable, P aiurScsElem[T]](code uint64, al, be, om P, w *[3]T, withB bool) (A, B T, constant bool, err error) {
	sel, mask := code&15, (code>>4)&7
	ua, ub, uc := mask&1 != 0, mask&2 != 0, mask&4 != 0
	sL, sR, sO, sM := sel&1 != 0, sel&2 != 0, sel&4 != 0, sel&8 != 0
	if mask == 0 || (ua && ub && sM) {
		return A, B, false, fmt.Errorf("Aiur SCS gate is not affine in its unsolved wire")
	}
	var t T
	if ua && sL {
		P(&A).Add(&A, al)
	}
	if ub && sR {
		P(&A).Add(&A, be)
	}
	if uc && sO {
		P(&A).Add(&A, om)
	}
	var qM T
	if sM {
		P(&qM).Mul(al, be)
	}
	constant = !sM || ua == ub
	if !constant {
		if ua {
			P(&t).Mul(&qM, &w[1])
		} else {
			P(&t).Mul(&qM, &w[0])
		}
		P(&A).Add(&A, &t)
	}
	if !withB {
		return A, B, constant, nil
	}
	if !ua && sL {
		P(&t).Mul(al, &w[0])
		P(&B).Add(&B, &t)
	}
	if !ub && sR {
		P(&t).Mul(be, &w[1])
		P(&B).Add(&B, &t)
	}
	if !uc && sO {
		P(&t).Mul(om, &w[2])
		P(&B).Add(&B, &t)
	}
	if sM && !ua && !ub {
		P(&t).Mul(&w[0], &w[1])
		P(&t).Mul(&t, &qM)
		P(&B).Add(&B, &t)
	}
	P(&t).SetInt64(int64(code>>8) - 128)
	P(&B).Add(&B, &t)
	return A, B, constant, nil
}

// aiurScsSolveInverseFor is 1/A when A does not depend on the witness.
func aiurScsSolveInverseFor[T comparable, P aiurScsElem[T]](code uint64, al, be, om *big.Int) (*big.Int, bool) {
	var a, b, o T
	P(&a).SetBigInt(al)
	P(&b).SetBigInt(be)
	P(&o).SetBigInt(om)
	A, _, constant, err := aiurScsSolveTerms[T, P](code, &a, &b, &o, &[3]T{}, false)
	if err != nil || !constant || P(&A).IsZero() {
		return nil, false
	}
	P(&A).Inverse(&A)
	return P(&A).BigInt(new(big.Int)), true
}

// aiurScsSolveInverse is 1/A over BN254 Fr when A does not depend on the witness.
func aiurScsSolveInverse(code uint64, al, be, om *big.Int) (*big.Int, bool) {
	return aiurScsSolveInverseFor[fr.Element, *fr.Element](code, al, be, om)
}

func aiurScsSolveHintTyped[T comparable, P aiurScsElem[T]](in []*big.Int, out []*big.Int) error {
	var al, be, om, inv T
	var w [3]T
	P(&al).SetBigInt(in[1])
	P(&be).SetBigInt(in[2])
	P(&om).SetBigInt(in[3])
	P(&inv).SetBigInt(in[4])
	for k := range w {
		P(&w[k]).SetBigInt(in[5+k])
	}
	A, B, _, err := aiurScsSolveTerms[T, P](in[0].Uint64(), &al, &be, &om, &w, true)
	if err != nil {
		return err
	}
	if P(&inv).IsZero() {
		if P(&A).IsZero() {
			return fmt.Errorf("Aiur SCS gate does not determine its unsolved wire")
		}
		P(&inv).Inverse(&A)
	}
	P(&B).Mul(&B, &inv)
	P(&B).Neg(&B)
	P(&B).BigInt(out[0])
	return nil
}

// aiurScsSolveHint solves a gate for its one unsolved wire. Inputs: code
// (see aiurScsSolveTerms), α, β, ω, 1/A or 0, then a, b, c (zero in masked
// slots).
func aiurScsSolveHint(q *big.Int, in []*big.Int, out []*big.Int) error {
	if len(in) != 8 || len(out) != 1 {
		return fmt.Errorf("aiurScsSolveHint arity")
	}
	if q != nil && q.Cmp(blsfr.Modulus()) == 0 {
		return aiurScsSolveHintTyped[blsfr.Element, *blsfr.Element](in, out)
	}
	if q != nil && q.Cmp(fr.Modulus()) != 0 {
		return fmt.Errorf("unsupported Aiur SCS solve field modulus")
	}
	return aiurScsSolveHintTyped[fr.Element, *fr.Element](in, out)
}

// aiurScsBitHint returns bit in[0] of the canonical value in[1].
func aiurScsBitHint(_ *big.Int, in []*big.Int, out []*big.Int) error {
	if len(in) != 2 || len(out) != 1 {
		return fmt.Errorf("aiurScsBitHint arity")
	}
	out[0].SetUint64(uint64(in[1].Bit(int(in[0].Uint64()))))
	return nil
}

func aiurScsZeroHint(_ *big.Int, _ []*big.Int, out []*big.Int) error {
	for _, o := range out {
		o.SetUint64(0)
	}
	return nil
}
