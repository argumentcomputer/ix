import IxCCTests.Src.Support
import IxCC.Src.Word

/-! Fixed-width words: `WordOp.eval` against Lean's own `UInt8/16/32/64`.

Two independent oracles. Compiled evaluation (the `#guard`s at elaboration, and `run` in
`tests-src`) calls Lean's C implementations (`lean_uint64_add`, …); the kernel's `decide`
(`decide +kernel` below) reduces the reference bodies of Lean 4.34.1. Every operation of every
width is compared on every pair of ten or eleven boundary words per width (`0`, `1`, around the
shift widths, the top bit, the maximum), and `ofNat` on thirteen `Nat`s around every size; the
kernel compares every operation of widths 64 and 8 on five boundary words each. Then the attacks:
plausible variants of the meaning that are wrong, each refuted. -/

namespace IxCCTests.Src.Words

open IxCC IxCC.Src IxCCTests.Src

/-- Lean's operation of width 8 on words, the result as a number (a decision as `0` or `1`). -/
def lean8 : WordOp → UInt8 → UInt8 → Nat
  | .add, a, b => (a + b).toNat | .sub, a, b => (a - b).toNat | .mul, a, b => (a * b).toNat
  | .div, a, b => (a / b).toNat | .mod, a, b => (a % b).toNat | .land, a, b => (a &&& b).toNat
  | .lor, a, b => (a ||| b).toNat | .xor, a, b => (a ^^^ b).toNat
  | .shiftLeft, a, b => (a <<< b).toNat | .shiftRight, a, b => (a >>> b).toNat
  | .complement, a, _ => (~~~a).toNat | .neg, a, _ => (-a).toNat
  | .decEq, a, b => if a = b then 1 else 0 | .decLt, a, b => if a < b then 1 else 0
  | .decLe, a, b => if a ≤ b then 1 else 0
  | .ofNat, a, _ => (UInt8.ofNat a.toNat).toNat | .toNat, a, _ => a.toNat
  | .convert .w8, a, _ => a.toNat | .convert .w16, a, _ => a.toUInt16.toNat
  | .convert .w32, a, _ => a.toUInt32.toNat | .convert .w64, a, _ => a.toUInt64.toNat

def lean16 : WordOp → UInt16 → UInt16 → Nat
  | .add, a, b => (a + b).toNat | .sub, a, b => (a - b).toNat | .mul, a, b => (a * b).toNat
  | .div, a, b => (a / b).toNat | .mod, a, b => (a % b).toNat | .land, a, b => (a &&& b).toNat
  | .lor, a, b => (a ||| b).toNat | .xor, a, b => (a ^^^ b).toNat
  | .shiftLeft, a, b => (a <<< b).toNat | .shiftRight, a, b => (a >>> b).toNat
  | .complement, a, _ => (~~~a).toNat | .neg, a, _ => (-a).toNat
  | .decEq, a, b => if a = b then 1 else 0 | .decLt, a, b => if a < b then 1 else 0
  | .decLe, a, b => if a ≤ b then 1 else 0
  | .ofNat, a, _ => (UInt16.ofNat a.toNat).toNat | .toNat, a, _ => a.toNat
  | .convert .w8, a, _ => a.toUInt8.toNat | .convert .w16, a, _ => a.toNat
  | .convert .w32, a, _ => a.toUInt32.toNat | .convert .w64, a, _ => a.toUInt64.toNat

def lean32 : WordOp → UInt32 → UInt32 → Nat
  | .add, a, b => (a + b).toNat | .sub, a, b => (a - b).toNat | .mul, a, b => (a * b).toNat
  | .div, a, b => (a / b).toNat | .mod, a, b => (a % b).toNat | .land, a, b => (a &&& b).toNat
  | .lor, a, b => (a ||| b).toNat | .xor, a, b => (a ^^^ b).toNat
  | .shiftLeft, a, b => (a <<< b).toNat | .shiftRight, a, b => (a >>> b).toNat
  | .complement, a, _ => (~~~a).toNat | .neg, a, _ => (-a).toNat
  | .decEq, a, b => if a = b then 1 else 0 | .decLt, a, b => if a < b then 1 else 0
  | .decLe, a, b => if a ≤ b then 1 else 0
  | .ofNat, a, _ => (UInt32.ofNat a.toNat).toNat | .toNat, a, _ => a.toNat
  | .convert .w8, a, _ => a.toUInt8.toNat | .convert .w16, a, _ => a.toUInt16.toNat
  | .convert .w32, a, _ => a.toNat | .convert .w64, a, _ => a.toUInt64.toNat

def lean64 : WordOp → UInt64 → UInt64 → Nat
  | .add, a, b => (a + b).toNat | .sub, a, b => (a - b).toNat | .mul, a, b => (a * b).toNat
  | .div, a, b => (a / b).toNat | .mod, a, b => (a % b).toNat | .land, a, b => (a &&& b).toNat
  | .lor, a, b => (a ||| b).toNat | .xor, a, b => (a ^^^ b).toNat
  | .shiftLeft, a, b => (a <<< b).toNat | .shiftRight, a, b => (a >>> b).toNat
  | .complement, a, _ => (~~~a).toNat | .neg, a, _ => (-a).toNat
  | .decEq, a, b => if a = b then 1 else 0 | .decLt, a, b => if a < b then 1 else 0
  | .decLe, a, b => if a ≤ b then 1 else 0
  | .ofNat, a, _ => (UInt64.ofNat a.toNat).toNat | .toNat, a, _ => a.toNat
  | .convert .w8, a, _ => a.toUInt8.toNat | .convert .w16, a, _ => a.toUInt16.toNat
  | .convert .w32, a, _ => a.toUInt32.toNat | .convert .w64, a, _ => a.toNat

/-- Boundary words at each width: `0`, `1`, small, around the shift widths, the top bit, the
maximum. -/
def bnd8 : List UInt8 := [0, 1, 2, 7, 8, 9, 127, 128, 254, 255]
def bnd16 : List UInt16 := [0, 1, 15, 16, 17, 255, 256, 32767, 32768, 65535]
def bnd32 : List UInt32 := [0, 1, 31, 32, 33, 65535, 65536, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
def bnd64 : List UInt64 := [0, 1, 63, 64, 65, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
  0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]

/-- The comparisons of one width that disagree (operation, arguments). -/
def mismatches {α : Type} (w : Width) (bnd : List α) (toNat : α → Nat)
    (lean : WordOp → α → α → Nat) : List (WordOp × Nat × Nat) :=
  (WordOp.ofWidth w).flatMap fun op => bnd.flatMap fun a => bnd.filterMap fun b =>
    if lean op a b == (WordOp.eval w op (toNat a) (toNat b)).val then none
    else some (op, toNat a, toNat b)

/-- Every comparison, with Lean's C implementations when compiled: the number of cases and the
mismatches. -/
def checkAll : Nat × List (WordOp × Nat × Nat) :=
  let cases := fun (w : Width) (k : Nat) => (WordOp.ofWidth w).length * k * k
  let n := cases .w8 bnd8.length + cases .w16 bnd16.length + cases .w32 bnd32.length +
    cases .w64 bnd64.length
  (n, mismatches .w8 bnd8 UInt8.toNat lean8 ++ mismatches .w16 bnd16 UInt16.toNat lean16 ++
    mismatches .w32 bnd32 UInt32.toNat lean32 ++ mismatches .w64 bnd64 UInt64.toNat lean64)

#guard checkAll.2.isEmpty

/-- `ofNat` on `Nat`s around every width's size. -/
def ofNatProbe : List Nat :=
  [0, 1, 255, 256, 257, 65535, 65536, 4294967295, 4294967296, 18446744073709551615,
    18446744073709551616, 18446744073709551617, 36893488147419103232]

def ofNatOk : Bool :=
  ofNatProbe.all fun n =>
    (UInt8.ofNat n).toNat == (WordOp.eval .w8 .ofNat n 0).val &&
    (UInt16.ofNat n).toNat == (WordOp.eval .w16 .ofNat n 0).val &&
    (UInt32.ofNat n).toNat == (WordOp.eval .w32 .ofNat n 0).val &&
    (UInt64.ofNat n).toNat == (WordOp.eval .w64 .ofNat n 0).val

#guard ofNatOk

/-! ### The kernel: the reference bodies, reduced by `decide`, against `eval` -/

def kbnd64 : List UInt64 := [0, 1, 64, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]
def kbnd8 : List UInt8 := [0, 1, 8, 128, 255]

example : (WordOp.ofWidth .w64).all (fun op => kbnd64.all fun a => kbnd64.all fun b =>
    lean64 op a b == (WordOp.eval .w64 op a.toNat b.toNat).val) = true := by decide +kernel

example : (WordOp.ofWidth .w8).all (fun op => kbnd8.all fun a => kbnd8.all fun b =>
    lean8 op a b == (WordOp.eval .w8 op a.toNat b.toNat).val) = true := by decide +kernel

/-! ### Attacks: plausible variants of the meaning that are wrong, refuted by the kernel -/

/-- A shift by the width or more wraps the amount (`b % bits`); it does not clear the word. -/
example : (UInt64.ofNat 1 <<< UInt64.ofNat 64).toNat = 1 := by decide
example : (UInt8.ofNat 1 <<< UInt8.ofNat 8).toNat = 1 := by decide
example : (UInt64.ofNat 0xFFFFFFFFFFFFFFFF >>> UInt64.ofNat 65).toNat = 0x7FFFFFFFFFFFFFFF := by
  decide
/-- Subtraction wraps; a truncating `Nat` subtraction would give `0`. -/
example : (UInt64.ofNat 0 - UInt64.ofNat 1).toNat = 0xFFFFFFFFFFFFFFFF := by decide
/-- Division by zero is zero and remainder by zero the dividend (not a trap). -/
example : (UInt32.ofNat 7 / UInt32.ofNat 0).toNat = 0 := by decide
example : (UInt32.ofNat 7 % UInt32.ofNat 0).toNat = 7 := by decide
/-- Negation of zero is zero (`(2^n - 0) % 2^n`); the complement of zero is the maximum. -/
example : (-(UInt64.ofNat 0)).toNat = 0 := by decide
example : (~~~(UInt16.ofNat 0)).toNat = 65535 := by decide
/-- Narrowing reduces, widening keeps; comparisons are unsigned. -/
example : (UInt64.ofNat 300).toUInt8.toNat = 44 := by decide
example : (UInt8.ofNat 255).toUInt64.toNat = 255 := by decide
example : ¬ (UInt64.ofNat 0x8000000000000000 < UInt64.ofNat 1) := by decide
/-- `ofNat` wraps at the size, not at `2^63`. -/
example : (UInt64.ofNat 18446744073709551616).toNat = 0 := by decide

/-- The wrong variants, refuted on `eval`: a shift that clears at the width, a truncating
subtraction, a negation without the final reduction, a narrowing without reduction. -/
example : (WordOp.eval .w64 .shiftLeft 1 64).val ≠ (1 * 2 ^ 64) % 2 ^ 64 := by decide
example : (WordOp.eval .w64 .sub 0 1).val ≠ 0 - 1 := by decide
example : (WordOp.eval .w64 .neg 0 0).val ≠ 2 ^ 64 - 0 := by decide
example : (WordOp.eval .w64 (.convert .w8) 300 0).val ≠ 300 := by decide

/-! ### `eval_word_lt` on instances, and why each hypothesis is there

The theorem's hypotheses are the arguments F6w passes: words below the width's size (`asWord?`
reads no other), `ofNat`'s literal at any size, `0` as a unary operation's second argument. On
every operation of every width and every pair of numbers around the sizes, wherever the
hypotheses hold the word result is below its width's size; dropping either hypothesis has a
counterexample (a division of an out-of-range word by one, a disjunction with an out-of-range
second word). -/

/-- Numbers around every width's size, in range and not. -/
def rangeProbe : List Nat :=
  [0, 1, 255, 256, 65535, 65536, 4294967295, 4294967296, 18446744073709551615,
    18446744073709551616, 18446744073709551621, 36893488147419103235]

/-- The cases where `eval_word_lt`'s hypotheses hold, the failures of its conclusion among them,
and the failures among the cases that meet every hypothesis but `ha`, or every one but `hb`. -/
def rangeCases : Nat × List (Width × WordOp × Nat × Nat) × Nat × Nat := Id.run do
  let mut n := 0
  let mut bad : List (Width × WordOp × Nat × Nat) := []
  let mut withoutA := 0
  let mut withoutB := 0
  for w in Width.all do
    for op in WordOp.ofWidth w do
      for a in rangeProbe do
        for b in rangeProbe do
          let ha := op == .ofNat || a < w.size
          let hb := b < w.size
          let ok := match WordOp.eval w op a b with
            | .word w' r => r < w'.size
            | _ => true
          if ha && hb then
            n := n + 1
            if !ok then bad := bad ++ [(w, op, a, b)]
          if !ha && hb && !ok then withoutA := withoutA + 1
          if ha && !hb && !ok then withoutB := withoutB + 1
  return (n, bad, withoutA, withoutB)

#guard rangeCases.2.1.isEmpty && rangeCases.2.2.1 > 0 && rangeCases.2.2.2 > 0

/-- The two counterexamples, decided. -/
example : WordOp.eval .w64 .div (2 ^ 64) 1 = .word .w64 (2 ^ 64) ∧ ¬ 2 ^ 64 < Width.size .w64 := by
  decide
example : WordOp.eval .w8 .lor 0 256 = .word .w8 256 ∧ ¬ 256 < Width.size .w8 := by decide
/-- `ofNat` at and above every size: in range, no bound needed. -/
example : [2 ^ 64, 2 ^ 64 + 5, 2 ^ 65 + 3].all (fun a => Width.all.all fun w =>
    match WordOp.eval w .ofNat a 0 with
    | .word w' r => w' == w && decide (r < w'.size)
    | _ => false) = true := by decide

/-! ### The bridge the model fact rests on, on instances (`wordAccel_of_eqns`, stage W1)

The grounding's model fact for words takes what a pinned operation computes from its stored
theorems, `ofNat`'s being the bridge to the tower. The data-types plan's bridge,
`∀ x (h : x < size), ofNat x = tower x h`, constrains nothing at or above the size, so its
`WordAccel` (`ofNat (lit a)` is the tower of `a % size` for every literal `a`) was false: a key
`bogus` that agrees with `UInt64.ofNat` below the size and returns `5` above satisfies that bridge,
and `bogus (2^64)` is not the tower of `0`. The corrected premise is the *reducing* bridge (the
statement `Ix.Compile.WordEquations` stores and `Table.wordEqnType` checks),
`∀ x (h : Nat.le (Nat.succ (x % size)) size), ofNat x = tower (x % size) h`: `bogus` fails it at
`2^64`, and Lean's `UInt64.ofNat` satisfies it (by `rfl`), at every literal the corrected
`WordAccel` speaks of. -/

/-- The plan's counter-instance. -/
def bogus (x : Nat) : UInt64 := if x < 2 ^ 64 then UInt64.ofNat x else 5

/-- The tower of `n`, the proof a hypothesis. -/
abbrev tower64 (n : Nat) (h : Nat.le (Nat.succ n) 18446744073709551616) : UInt64 :=
  UInt64.ofBitVec (@BitVec.ofFin 64 (@Fin.mk 18446744073709551616 n h))

/-- `bogus` satisfies the plan's bridge (below the size it is `UInt64.ofNat`)… -/
example (x : Nat) (h : x < 2 ^ 64) : bogus x = tower64 x h := by
  unfold bogus; rw [if_pos h]
  apply UInt64.toNat_inj.mp
  show Nat.mod x 18446744073709551616 = x
  exact Nat.mod_eq_of_lt h

/-- …and the plan's `WordAccel` fails for it at `2^64`: not the tower of `2^64 % 2^64 = 0`. -/
example : bogus (2 ^ 64) ≠ tower64 0 (Nat.le_of_ble_eq_true rfl) := by decide

/-- The reducing bridge refutes `bogus` as an `ofNat` key: it fails at `2^64`. -/
example : ¬ ∀ x (h : Nat.le (Nat.succ (Nat.mod x 18446744073709551616)) 18446744073709551616),
    bogus x = tower64 (Nat.mod x 18446744073709551616) h :=
  fun hb => absurd (hb (2 ^ 64) (Nat.le_of_ble_eq_true rfl)) (by decide)

/-- Lean's `UInt64.ofNat` satisfies the reducing bridge, definitionally (as the stored theorem
`IxWordEquations.UInt64_ofNat` is proved), and so do the other widths' (here `UInt8`). -/
example (x : Nat) (h : Nat.le (Nat.succ (Nat.mod x 18446744073709551616)) 18446744073709551616) :
    UInt64.ofNat x = tower64 (Nat.mod x 18446744073709551616) h := rfl
example (x : Nat) (h : Nat.le (Nat.succ (Nat.mod x 256)) 256) :
    UInt8.ofNat x = UInt8.ofBitVec (@BitVec.ofFin 8 (@Fin.mk 256 (Nat.mod x 256) h)) := rfl

/-- The corrected `WordAccel`'s `ofNat` clause at literals at and above the size, where the plan's
failed: `ofNat a` is the tower of `a % size`. -/
example : (UInt64.ofNat (2 ^ 64)) = tower64 0 (Nat.le_of_ble_eq_true rfl) := by decide
example : (UInt64.ofNat (2 ^ 64 + 5)) = tower64 5 (Nat.le_of_ble_eq_true rfl) := by decide
example : (UInt64.ofNat (2 ^ 65 + 3)) = tower64 3 (Nat.le_of_ble_eq_true rfl) := by decide
example : (UInt8.ofNat 300) = UInt8.ofBitVec (@BitVec.ofFin 8 (@Fin.mk 256 44 (by decide))) := by
  decide

/-- `tests-src`: the same comparisons in the compiled test program, with Lean's C
implementations, so a runtime that disagreed with the elaborator's evaluation is caught too. -/
def run (a : Assert) : IO Unit := do
  let (n, bad) := checkAll
  expect a bad.isEmpty s!"words: {bad.length} of {n} comparisons disagree with Lean: {reprStr (bad.take 5)}"
  expect a ofNatOk "words: ofNat around every size"
  expectEq a n 8420 s!"words: {n} comparisons"
  let (rn, rbad, withoutA, withoutB) := rangeCases
  expect a rbad.isEmpty s!"words: eval_word_lt's conclusion fails on {reprStr (rbad.take 5)}"
  expect a (withoutA > 0 && withoutB > 0)
    s!"words: without either hypothesis of eval_word_lt a counterexample ({withoutA}, {withoutB})"
  -- per width, 19 operations on in-range pairs and `ofNat` on every probe with an in-range second
  -- argument: 3, 5, 7 and 9 of the 12 probes are below the sizes of widths 8 to 64
  expectEq a rn 3404 "words: the cases that meet eval_word_lt's hypotheses"

end IxCCTests.Src.Words
