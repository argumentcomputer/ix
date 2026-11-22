/-! The fold guard's front-door input (`fixtures/fold`): roots whose bodies apply `Nat.pow`,
`Nat.shiftLeft`, `Nat.mul` and `Nat.mod` to literals, for the shrink walk's literal folding
(`IxCC.Anf.Walk.foldable`, with `foldBits` = 1024). Each root is `fun x => E + x`, so that it is a
function of one `Nat` whose executable runs on an argument.

Every root is `noncomputable`: Lean 4.34.1's own code generator folds `Nat.shiftLeft` on literals
without a bound and aborts `ix compile` (`Nat.shiftl exponent is too big`) on a computable
definition of that shape. The kernel's terms, and so the closure, are the same either way. -/

namespace IxCCTests.Fold

/-! ## Both sides of the bound -/

/-- `2 ^ 512` folds (`2 < 2 ^ (1024 / 512)`), and so does its remainder: `4 + x`. -/
noncomputable def powIn (x : Nat) : Nat := 2 ^ 512 % 7 + x
/-- `2 ^ 513` is not folded (`1024 / 513 = 1`): it runs natively and overflows. -/
noncomputable def powOut (x : Nat) : Nat := 2 ^ 513 % 7 + x
/-- `1 ^ 1024` folds to `1`. -/
noncomputable def powOneIn (x : Nat) : Nat := 1 ^ 1024 + x
/-- `1 ^ 1025` is not folded (the exponent is past 1024); natively it is `1`. -/
noncomputable def powOneOut (x : Nat) : Nat := 1 ^ 1025 + x
/-- `1 <<< 1023` folds (`1 < 2 ^ (1024 − 1023)`), and so does its remainder: `1 + x`. -/
noncomputable def shlIn (x : Nat) : Nat := (1 <<< 1023) % 7 + x
/-- `1 <<< 1024` is not folded: it runs natively and overflows. -/
noncomputable def shlOut (x : Nat) : Nat := (1 <<< 1024) % 7 + x
/-- A wide intermediate a later fold reduces, inside the bound: `2 ^ 100 % 7` folds to `2`. -/
noncomputable def powMod100 (x : Nat) : Nat := 2 ^ 100 % 7 + x

/-! ## Exponents at and past `2 ^ 32 − 1` (the runtime's `Nat.pow` aborts past it, whatever the base) -/

noncomputable def pow0At (x : Nat) : Nat := 0 ^ 4294967295 + x
noncomputable def pow0Past (x : Nat) : Nat := 0 ^ 4294967296 + x
noncomputable def pow1At (x : Nat) : Nat := 1 ^ 4294967295 + x
noncomputable def pow1Past (x : Nat) : Nat := 1 ^ 4294967296 + x
noncomputable def pow2At (x : Nat) : Nat := 2 ^ 4294967295 + x
noncomputable def pow2Past (x : Nat) : Nat := 2 ^ 4294967296 + x
/-- An exponent of `2 ^ 64`: past a native word as well. -/
noncomputable def pow1Far (x : Nat) : Nat := 1 ^ 18446744073709551616 + x
noncomputable def shl0Past (x : Nat) : Nat := 0 <<< 4294967296 + x
noncomputable def shl1At (x : Nat) : Nat := 1 <<< 4294967295 + x
noncomputable def shl1Past (x : Nat) : Nat := 1 <<< 4294967296 + x
noncomputable def shl2Past (x : Nat) : Nat := 2 <<< 4294967296 + x

/-! ## Chained squarings: each fold's result is the next one's operand -/

/-- Thirty-two squarings of `2 ^ 62`, then `% 7`. Unbounded, the folds build `62 · 2 ^ k` bits at
the `k`-th; bounded, the squarings stop folding once an operand reaches `2 ^ 1024`. -/
noncomputable def mulChain32 (x : Nat) : Nat :=
  let a0 := 4611686018427387904
  let a1 := a0 * a0
  let a2 := a1 * a1
  let a3 := a2 * a2
  let a4 := a3 * a3
  let a5 := a4 * a4
  let a6 := a5 * a5
  let a7 := a6 * a6
  let a8 := a7 * a7
  let a9 := a8 * a8
  let a10 := a9 * a9
  let a11 := a10 * a10
  let a12 := a11 * a11
  let a13 := a12 * a12
  let a14 := a13 * a13
  let a15 := a14 * a14
  let a16 := a15 * a15
  let a17 := a16 * a16
  let a18 := a17 * a17
  let a19 := a18 * a18
  let a20 := a19 * a19
  let a21 := a20 * a20
  let a22 := a21 * a21
  let a23 := a22 * a22
  let a24 := a23 * a23
  let a25 := a24 * a24
  let a26 := a25 * a25
  let a27 := a26 * a26
  let a28 := a27 * a27
  let a29 := a28 * a28
  let a30 := a29 * a29
  let a31 := a30 * a30
  let a32 := a31 * a31
  a32 % 7 + x

/-! ## A literal of the closure's own text -/

/-- `2 ^ 1000`, written out, below the bound: `2 + x`. -/
noncomputable def litIn (x : Nat) : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 % 7 + x
/-- `2 ^ 1100`, written out, past the bound: not folded, so natively an operand without a word. -/
noncomputable def litOut (x : Nat) : Nat := 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 % 7 + x

end IxCCTests.Fold
