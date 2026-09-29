import Compilatrix.Lir.Syntax

/-!
# Hand-written Lir kernels (MEAS-4 inputs)

Synthetic kernels over 04's tagged `Nat` words (`n ↦ 2n+1`, n < 2^63), written
as `Rt.lower` should emit them for K1 (04 §2), with every edge already
non-critical. M1.B6 runs them through selection, allocation and emission and
measures them against C twins; they are never reported as real-program
results (roadmap §9).

- `fib`: K1's `fib` (`0 ↦ 0`, `1 ↦ 1`, `n+2 ↦ fib n + fib (n+1)`): two
  recursive calls and a tagged add, `lea t,[a-1]; add t,b; jc` as
  `t := a - 1; brOvf addC s t b`, with the carry edge to `fail natOverflow`.
- `sumLoop`: K1's `sum-loop` (`s := 0; for i in [0:n] do s := s + i`) as one
  loop whose header carries `i` and `s`; `sumFrom` starts from `s₀`, so tests
  reach the overflow boundary without 2^32 iterations.
- `gcd`: K1's `gcd` (`if b = 0 then a else gcd b (a % b)`) as a loop: untag,
  `urem`, retag.
- `natAdd`, `natSub` (truncated, `jb`), `natDiv` and `natMod` (with their
  zero tests, `n/0 = 0` and `n%0 = n`): the primitive sequences on their own,
  for boundary tests.

Label order puts each loop's header before its body, so exactly the back
edges charge the clock; `fib` charges one unit per recursive call.
-/

namespace CompilatrixTests.Lir.Kernels

open Compilatrix Compilatrix.Lir

/-! ## Tagged words -/

/-- The largest `Nat` with an immediate word. -/
def natMax : Nat := 2 ^ 63 - 1

def tag (n : Nat) : Word := UInt64.ofNat (2 * n + 1)

def untag (w : Word) : Nat := w.toNat / 2

private def v (x : VReg) : Arg := .v x
private def i (w : Word) : Arg := .imm w
private def to (l : Label) (args : List Arg := []) : Edge := ⟨l, args⟩
private def bin (x : VReg) (o : BinOp) (a b : Arg) : Stmt := .assign x (.bin o .w64 a b)

/-! ## Kernels -/

/-- `fib n`, with `n` in `v0`. -/
def fib : Func where
  name := "fib"
  params := [0]
  results := 1
  blocks := #[
    -- b0: n ≤ 1 ⇔ 2n+1 ≤ 3
    { term := .br .ule .w64 (v 0) (i 3) (to 1) (to 2) },
    -- b1: fib 0 = 0 and fib 1 = 1: the argument itself
    { term := .ret [v 0] },
    -- b2: fib (n-2) + fib (n-1)
    { body := #[bin 1 .sub (v 0) (i 4), .call [2] 0 [v 1],
        bin 3 .sub (v 0) (i 2), .call [4] 0 [v 3],
        bin 5 .sub (v 2) (i 1)]
      term := .brOvf .addC 6 (v 5) (v 4) (to 3) (to 4) },
    { term := .ret [v 6] },
    { term := .fail .natOverflow, cold := true }]

/-- The counting loop from `s₀` (`v1`) over `i < n` (`n` in `v0`). -/
private def sumBlocks (init : Arg) : Array Block := #[
    -- b0: i := 0, s := init
    { term := .jump (to 1 [i (tag 0), init]) },
    -- b1(i, s): i < n (tagging is monotone)
    { params := [2, 3], term := .br .ult .w64 (v 2) (v 0) (to 2) (to 3) },
    -- b2: s + i
    { body := #[bin 4 .sub (v 3) (i 1)]
      term := .brOvf .addC 5 (v 4) (v 2) (to 4) (to 5) },
    -- b3
    { term := .ret [v 3] },
    -- b4: i + 1 cannot overflow, since i < n; back edge
    { body := #[bin 6 .add (v 2) (i 2)], term := .jump (to 1 [v 6, v 5]) },
    { term := .fail .natOverflow, cold := true }]

/-- `sumLoop n = Σ i < n, i`, with `n` in `v0`. -/
def sumLoop : Func where
  name := "sumLoop"
  params := [0]
  results := 1
  blocks := sumBlocks (i (tag 0))

/-- `sumFrom n s₀ = s₀ + Σ i < n, i`, with `n` in `v0` and `s₀` in `v1`. -/
def sumFrom : Func where
  name := "sumFrom"
  params := [0, 1]
  results := 1
  blocks := sumBlocks (v 1)

/-- `gcd a b`, with `a` in `v0` and `b` in `v1`. -/
def gcd : Func where
  name := "gcd"
  params := [0, 1]
  results := 1
  blocks := #[
    { term := .jump (to 1 [v 0, v 1]) },
    -- b1(x, y): y = 0 ⇔ y = tag 0
    { params := [2, 3], term := .br .eq .w64 (v 3) (i (tag 0)) (to 2) (to 3) },
    { term := .ret [v 2] },
    -- b3: untag, x % y, retag; back edge
    { body := #[bin 4 .shr (v 2) (i 1), bin 5 .shr (v 3) (i 1), bin 6 .urem (v 4) (v 5),
        bin 7 .shl (v 6) (i 1), bin 8 .or (v 7) (i 1)]
      term := .jump (to 1 [v 3, v 8]) }]

/-- `a + b` (04 §2: `lea rax,[rdi-1]; add rax,rsi; jc`). -/
def natAdd : Func where
  name := "natAdd"
  params := [0, 1]
  results := 1
  blocks := #[
    { body := #[bin 2 .sub (v 0) (i 1)], term := .brOvf .addC 3 (v 2) (v 1) (to 1) (to 2) },
    { term := .ret [v 3] },
    { term := .fail .natOverflow, cold := true }]

/-- Truncated `a - b` (04 §2: `sub rax,rsi; jb .Lzero; or rax,1`). -/
def natSub : Func where
  name := "natSub"
  params := [0, 1]
  results := 1
  blocks := #[
    { term := .brOvf .subB 2 (v 0) (v 1) (to 1) (to 2) },
    { body := #[bin 3 .or (v 2) (i 1)], term := .ret [v 3] },
    { term := .ret [i (tag 0)] }]

/-- `a / b` or `a % b` with the zero test (`n/0 = 0`, `n%0 = n`). -/
private def divMod (o : BinOp) (zero : Arg) : Array Block := #[
    { term := .br .eq .w64 (v 1) (i (tag 0)) (to 1) (to 2) },
    { term := .ret [zero] },
    { body := #[bin 2 .shr (v 0) (i 1), bin 3 .shr (v 1) (i 1), bin 4 o (v 2) (v 3),
        bin 5 .shl (v 4) (i 1), bin 6 .or (v 5) (i 1)]
      term := .ret [v 6] }]

def natDiv : Func where
  name := "natDiv"
  params := [0, 1]
  results := 1
  blocks := divMod .udiv (i (tag 0))

def natMod : Func where
  name := "natMod"
  params := [0, 1]
  results := 1
  blocks := divMod .urem (v 0)

/-- A one-function program exported under the kernel's name. -/
def program (f : Func) : Program :=
  { funcs := #[{ f with conv := .sysvExport s!"lir_{f.name}" }], main := 0 }

/-! ## Reference results -/

/-- Kernel outcomes, as `Nat`s or natOverflow. -/
inductive Expect where
  | nat (n : Nat)
  | natOverflow
  deriving DecidableEq, Repr

def Expect.ofNat (n : Nat) : Expect := if n ≤ natMax then .nat n else .natOverflow

def fibNat (n : Nat) : Nat := Id.run do
  let mut (a, b) := (0, 1)
  for _ in [:n] do (a, b) := (b, a + b)
  return a

/-- Charges `fib n` spends: one per recursive call, `2·fib(n+1) − 2`. -/
def fibCharges (n : Nat) : Nat := 2 * fibNat (n + 1) - 2

structure Case where
  kernel : String
  func : Func
  args : List Nat
  expect : Expect
  /-- The smallest clock that does not time out, when known. -/
  charges : Option Nat := none

def sumTo (n : Nat) : Nat := n * (n - 1) / 2

def cases : List Case :=
  ((List.range 21).map fun n =>
    { kernel := "fib", func := fib, args := [n], expect := .nat (fibNat n), charges := some (fibCharges n) }) ++
  ([0, 1, 2, 3, 10, 100, 1000, 5000].map fun n =>
    { kernel := "sumLoop", func := sumLoop, args := [n], expect := .nat (sumTo n), charges := some n }) ++
  -- The last additions of `sumFrom` land exactly on, and just past, 2^63 − 1.
  ([(4, natMax - 6), (4, natMax - 5), (3, natMax - 3), (3, natMax - 2), (1, natMax), (0, natMax)].map
    fun (n, s) =>
      { kernel := "sumFrom", func := sumFrom, args := [n, s], expect := Expect.ofNat (s + sumTo n) }) ++
  ([(0, 0), (0, 5), (5, 0), (12, 18), (18, 12), (17, 5), (1071, 462),
      (fibNat 91, fibNat 90), (natMax, 2 ^ 62), (natMax, natMax), (natMax, 7 * 73 * 127 * 337),
      (2 ^ 62, 2 ^ 40)].map fun (a, b) =>
    { kernel := "gcd", func := gcd, args := [a, b], expect := .nat (Nat.gcd a b) }) ++
  ([(0, 0), (1, 2), (natMax, 0), (0, natMax), (2 ^ 62, 2 ^ 62 - 1), (2 ^ 62, 2 ^ 62),
      (natMax, 1), (natMax, natMax), (fibNat 91, fibNat 92)].map fun (a, b) =>
    { kernel := "natAdd", func := natAdd, args := [a, b], expect := Expect.ofNat (a + b) }) ++
  ([(5, 3), (3, 5), (0, 0), (natMax, 0), (natMax, natMax), (0, natMax), (natMax, 1)].map fun (a, b) =>
    { kernel := "natSub", func := natSub, args := [a, b], expect := .nat (a - b) }) ++
  ([(7, 2), (7, 0), (0, 5), (natMax, 1), (natMax, 2 ^ 62), (natMax, natMax), (6, 7)].map fun (a, b) =>
    { kernel := "natDiv", func := natDiv, args := [a, b], expect := .nat (a / b) }) ++
  ([(7, 2), (7, 0), (0, 5), (natMax, 1), (natMax, 2 ^ 62), (natMax, natMax), (6, 7)].map fun (a, b) =>
    { kernel := "natMod", func := natMod, args := [a, b], expect := .nat (a % b) })

end CompilatrixTests.Lir.Kernels
