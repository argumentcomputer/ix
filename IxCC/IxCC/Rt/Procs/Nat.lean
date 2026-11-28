import IxCC.Rt.Layout

/-! # `Nat` runtime procedures

`Nat.pow` and `Nat.gcd` loop, so they are Lir procedures rather than inline
sequences: internal functions over tagged words (`2n + 1`)
that `Rt.lower` calls. Their loops charge the clock at their back edges, as
every Lir loop does, so a run that calls them spends more Lir clock than its
Cfg run (the timeout clause still holds: runtime-procedure loops only add
charges).

* `rt_nat_pow a e`: `a^e`, or `fail natOverflow` when it is at least 2^63.
  `e = 0` gives 1 and a base of 0 or 1 itself; otherwise the base is at
  least 2, so an exponent above 62 overflows and at most six rounds of
  square-and-multiply remain. A round multiplies the accumulator when the
  exponent's low bit is set and squares the base only while exponent bits
  remain; each product is checked (by division, and below 2^63), and a
  product that is needed and too large means the result is too.
* `rt_nat_gcd a b`: Euclid over `urem` on the untagged values (`gcd a 0 =
  a`), as the synthetic `gcd` kernel of the backend tests. -/

namespace IxCC.Rt.Procs

open IxCC.Lir

private def v (x : VReg) : Arg := .v x
private def i (n : Nat) : Arg := .imm (UInt64.ofNat n)
private def to (l : Label) (args : List Arg := []) : Edge := ⟨l, args⟩
private def bin (x : VReg) (o : BinOp) (a b : Arg) : Stmt := .assign x (.bin o .w64 a b)
private def retag (x q : VReg) : Stmt := .assign x (.addr { base := some (.v q), index := some (q, .one), disp := 1 })

def powSymbol : String := "rt_nat_pow"
def gcdSymbol : String := "rt_nat_gcd"

/-- `rt_nat_pow`: `v0` the base, `v1` the exponent (tagged). -/
def natPow : Func where
  name := powSymbol
  params := [0, 1]
  results := 1
  blocks := #[
    -- b0: p, n untagged
    { body := #[bin 2 .shr (v 0) (i 1), bin 3 .shr (v 1) (i 1)]
      term := .br .eq .w64 (v 3) (i 0) (to 1) (to 2) },
    -- b1: p^0 = 1
    { term := .ret [i 3] },
    -- b2: 0^n = 0 and 1^n = 1 for n > 0
    { term := .br .ule .w64 (v 2) (i 1) (to 3) (to 4) },
    { term := .ret [v 0] },
    -- b4: p ≥ 2 and n ≥ 63 overflow
    { term := .br .ugt .w64 (v 3) (i 62) (to 5) (to 6) },
    { term := .fail .natOverflow, cold := true },
    -- b6: acc := 1
    { term := .jump (to 7 [i 1, v 2, v 3]) },
    -- b7(acc, base, n): acc · base when the low bit is set (acc ≥ 1, base ≥ 2)
    { params := [4, 5, 6]
      body := #[bin 7 .and (v 6) (i 1), bin 8 .mul (v 4) (v 5), bin 9 .udiv (v 8) (v 4),
        .assign 10 (.test .ne .w64 (v 9) (v 5)), .assign 11 (.test .slt .w64 (v 8) (i 0)),
        bin 12 .or (v 10) (v 11), bin 13 .and (v 12) (v 7)]
      term := .br .ne .w64 (v 13) (i 0) (to 8) (to 9) },
    { term := .fail .natOverflow, cold := true },
    -- b9: the new accumulator and exponent
    { body := #[.assign 14 (.select .eq .w64 (v 7) (i 0) (v 4) (v 8)), bin 15 .shr (v 6) (i 1)]
      term := .br .eq .w64 (v 15) (i 0) (to 10) (to 11) },
    { body := #[retag 16 14], term := .ret [v 16] },
    -- b11: bits remain, so the square is needed
    { body := #[bin 17 .mul (v 5) (v 5), bin 18 .udiv (v 17) (v 5),
        .assign 19 (.test .ne .w64 (v 18) (v 5)), .assign 20 (.test .slt .w64 (v 17) (i 0)),
        bin 21 .or (v 19) (v 20)]
      term := .br .ne .w64 (v 21) (i 0) (to 12) (to 13) },
    { term := .fail .natOverflow, cold := true },
    -- b13: back edge
    { term := .jump (to 7 [v 14, v 17, v 15]) }]

/-- `rt_nat_gcd`: `v0`, `v1` tagged. -/
def natGcd : Func where
  name := gcdSymbol
  params := [0, 1]
  results := 1
  blocks := #[
    { term := .jump (to 1 [v 0, v 1]) },
    -- b1(x, y): gcd x 0 = x
    { params := [2, 3], term := .br .eq .w64 (v 3) (i 1) (to 2) (to 3) },
    { term := .ret [v 2] },
    -- b3: untag, x % y, retag; back edge
    { body := #[bin 4 .shr (v 2) (i 1), bin 5 .shr (v 3) (i 1), bin 6 .urem (v 4) (v 5), retag 7 6]
      term := .jump (to 1 [v 3, v 7]) }]

/-! ## Phase 4 arbitrary-precision `Nat` procedures (`rt_nat_pow_big`, `rt_nat_gcd_big`)

Keep the tagged fixnum fast paths of `rt_nat_pow` and `rt_nat_gcd`, preceded by
a single low-bit tag check `test (v0 & v1), 1`, and replace every `fail natOverflow`
exit with a cold tail-call to the linked `BigNat` slow-path procedure (zero
`natOverflow`, zero critical edges). -/

def powBigSymbol : String := "rt_nat_pow_big"
def gcdBigSymbol : String := "rt_nat_gcd_big"

/-- `rt_nat_pow_big slowPow`: arbitrary-precision `Nat.pow` over unified `NatVal`
words (`v0` base, `v1` exponent). Dispatches via `.tail slowPow [v 0, v 1]` whenever
either operand is a big `LimbArray` pointer or any intermediate product reaches `2^63`. -/
def natPowBig (slowPow : FunId) : Func where
  name := powBigSymbol
  params := [0, 1]
  results := 1
  blocks := #[
    -- b0: single tag test on both operands' low bits
    { body := #[bin 22 .and (v 0) (v 1)]
      term := .br .tz .w64 (v 22) (i 1) (to 15) (to 1) },
    -- b1: both operands are odd tagged immediates; untag p, n
    { body := #[bin 2 .shr (v 0) (i 1), bin 3 .shr (v 1) (i 1)]
      term := .br .eq .w64 (v 3) (i 0) (to 2) (to 3) },
    -- b2: p^0 = 1
    { term := .ret [i 3] },
    -- b3: 0^n = 0 and 1^n = 1 for n > 0
    { term := .br .ule .w64 (v 2) (i 1) (to 4) (to 5) },
    -- b4
    { term := .ret [v 0] },
    -- b5: p ≥ 2 and n ≥ 63 overflow fixnums → slow path
    { term := .br .ugt .w64 (v 3) (i 62) (to 6) (to 7) },
    -- b6: cold slow path (exponent ≥ 63)
    { term := .tail slowPow [v 0, v 1], cold := true },
    -- b7: acc := 1
    { term := .jump (to 8 [i 1, v 2, v 3]) },
    -- b8(acc, base, n): acc · base when the low bit is set
    { params := [4, 5, 6]
      body := #[bin 7 .and (v 6) (i 1), bin 8 .mul (v 4) (v 5), bin 9 .udiv (v 8) (v 4),
        .assign 10 (.test .ne .w64 (v 9) (v 5)), .assign 11 (.test .slt .w64 (v 8) (i 0)),
        bin 12 .or (v 10) (v 11), bin 13 .and (v 12) (v 7)]
      term := .br .ne .w64 (v 13) (i 0) (to 9) (to 10) },
    -- b9: cold slow path (acc * base overflow)
    { term := .tail slowPow [v 0, v 1], cold := true },
    -- b10: new accumulator and halved exponent
    { body := #[.assign 14 (.select .eq .w64 (v 7) (i 0) (v 4) (v 8)), bin 15 .shr (v 6) (i 1)]
      term := .br .eq .w64 (v 15) (i 0) (to 11) (to 12) },
    -- b11: retag and return
    { body := #[retag 16 14], term := .ret [v 16] },
    -- b12: square base while bits remain
    { body := #[bin 17 .mul (v 5) (v 5), bin 18 .udiv (v 17) (v 5),
        .assign 19 (.test .ne .w64 (v 18) (v 5)), .assign 20 (.test .slt .w64 (v 17) (i 0)),
        bin 21 .or (v 19) (v 20)]
      term := .br .ne .w64 (v 21) (i 0) (to 13) (to 14) },
    -- b13: cold slow path (base * base overflow)
    { term := .tail slowPow [v 0, v 1], cold := true },
    -- b14: back edge to loop header b8
    { term := .jump (to 8 [v 14, v 17, v 15]) },
    -- b15: cold slow path (at least one operand is a big LimbArray pointer)
    { term := .tail slowPow [v 0, v 1], cold := true }]

/-- `rt_nat_gcd_big slowGcd`: arbitrary-precision `Nat.gcd` over unified `NatVal`
words (`v0`, `v1`). Fast-paths both-small tagged operands via Euclid on `urem`,
and tail-calls `slowGcd` whenever either operand is a big `LimbArray` pointer. -/
def natGcdBig (slowGcd : FunId) : Func where
  name := gcdBigSymbol
  params := [0, 1]
  results := 1
  blocks := #[
    -- b0: single tag test on both operands' low bits
    { body := #[bin 8 .and (v 0) (v 1)]
      term := .br .tz .w64 (v 8) (i 1) (to 5) (to 1) },
    -- b1: enter fast Euclid loop
    { term := .jump (to 2 [v 0, v 1]) },
    -- b2(x, y): gcd x 0 = x
    { params := [2, 3], term := .br .eq .w64 (v 3) (i 1) (to 3) (to 4) },
    -- b3
    { term := .ret [v 2] },
    -- b4: untag, x % y, retag; back edge
    { body := #[bin 4 .shr (v 2) (i 1), bin 5 .shr (v 3) (i 1), bin 6 .urem (v 4) (v 5), retag 7 6]
      term := .jump (to 2 [v 3, v 7]) },
    -- b5: cold slow path (at least one operand is a big LimbArray pointer)
    { term := .tail slowGcd [v 0, v 1], cold := true }]

end IxCC.Rt.Procs
