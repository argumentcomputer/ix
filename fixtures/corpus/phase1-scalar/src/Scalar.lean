/-!
# The Phase 1 scalar corpus (MT.2)

First-order, total programs over `Nat` and `Bool`, written for Compilatr.ix
(Apache-2.0 OR MIT). Several are re-derivations of classic benchmark
programs: the algorithm is reimplemented in fresh Lean, no upstream text is
copied, and `corpus.json` records each origin and its licence.

Every `Scalar.*` definition named in `corpus.json` is a closure root (at most
five `Nat` parameters, a `Nat` or `Bool` result). `main` is the oracle
driver for `lean --run`: each stdin line `ROOT ARG…` prints that root's
value on those arguments.
-/

namespace Scalar

/-! ## Recursion shapes -/

/-- MLton `tailfib.sml`: accumulator tail recursion, `fib' (n, a, b) =
fib' (n - 1, a + b, a)` from `fib' (n, 0, 1)`. -/
def tailfibGo : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => tailfibGo n (a + b) a

def tailfib (n : Nat) : Nat := tailfibGo n 0 1

/-- nofib `rfib`, over `Nat`: binary recursion counting its calls
(`nfib n = 2 fib (n + 1) - 1`). -/
def nfib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => nfib n + nfib (n + 1) + 1

mutual
/-- MLton `even-odd.sml`: mutual structural recursion, sibling tail calls. -/
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n

def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

/-- McCarthy's 91 function, total through fuel: nested non-tail recursion.
`91` for `n ≤ 100`, otherwise `n - 10`. -/
def f91Go : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n > 100 then n - 10 else f91Go fuel (f91Go fuel (n + 11))

def f91 (n : Nat) : Nat := f91Go 1000 n

/-- Factorial: `20!` is the largest with a word. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-! ## Loops -/

/-- MLton `imp-for.sml`, three levels: nested `for` loops over a mutable
counter (`k³`). -/
def impFor (k : Nat) : Nat := Id.run do
  let mut x := 0
  for _ in [0:k] do
    for _ in [0:k] do
      for _ in [0:k] do
        x := x + 1
  return x

/-- Koka `pyth.kk`: nested loops with an early exit, counting the triples
`x < y < z` with `x² + y² = z²` that the upstream search visits. -/
def pyth (n : Nat) : Nat := Id.run do
  let mut count := 0
  for x in [1:n / 3 + 1] do
    for y in [x + 1:n / 2 + 1] do
      for z in [y + 1:n / 2 + 1] do
        if x * x + y * y == z * z then count := count + 1
        else if x * x + y * y ≥ z * z && x + y + z ≤ n then pure ()
        else break
  return count

/-- Koka `sfib-int.kk`: a tail loop on `x² + x + 2`, restarted above `10⁹`,
so every value stays below `2⁶³`. -/
def sfibGo : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => if x > 1000000000 then sfibGo n 1 else sfibGo n (x * x + x + 2)

def sfib (n : Nat) : Nat := sfibGo n 1

/-- Collatz steps to reach 1 (fuel bounds the loop; OEIS A006577 below
`10⁶` needs at most 524). -/
def collatzGo : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | fuel + 1, n, s =>
    if n ≤ 1 then s else collatzGo fuel (if n % 2 == 0 then n / 2 else 3 * n + 1) (s + 1)

def collatz (n : Nat) : Nat := collatzGo 1000 n 0

/-- The start below `limit` with the most Collatz steps (the first one). -/
def collatzBest (limit : Nat) : Nat := Id.run do
  let mut best := 1
  let mut most := 0
  for n in [1:limit] do
    let s := collatz n
    if s > most then
      best := n
      most := s
  return best

/-- Trial division by `d` while `d² ≤ n` (fuel `n`). -/
def primeGo (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if d * d > n then true else if n % d == 0 then false else primeGo n fuel (d + 1)

def isPrime (n : Nat) : Bool := n ≥ 2 && primeGo n n 2

/-- `π(n)`, the primes up to `n`, by trial division. -/
def primeCount (n : Nat) : Nat := Id.run do
  let mut c := 0
  for i in [2:n + 1] do
    if isPrime i then c := c + 1
  return c

/-- The sum of the proper divisors of `n`. -/
def sigma (n : Nat) : Nat := Id.run do
  let mut s := 0
  for d in [1:n] do
    if n % d == 0 then s := s + d
  return s

def isPerfect (n : Nat) : Bool := n > 0 && sigma n == n

/-- Perfect numbers below `limit` (6, 28, 496, 8128). -/
def perfectCount (limit : Nat) : Nat := Id.run do
  let mut c := 0
  for n in [1:limit] do
    if isPerfect n then c := c + 1
  return c

/-- Binomial coefficients, multiplicatively: `c (n - i) / (i + 1)` is exact
at every step, but `c (n - i)` can pass `2⁶³` before the division. -/
def chooseMul (n k : Nat) : Nat := Id.run do
  let mut c := 1
  for i in [0:k] do
    c := c * (n - i) / (i + 1)
  return c

/-- `lcm(1, …, n)` with the library's `Nat.lcm` (`m * n / gcd m n`). -/
def lcmUpTo (n : Nat) : Nat := Id.run do
  let mut l := 1
  for i in [1:n + 1] do
    l := Nat.lcm l i
  return l

/-! ## Structural and well-founded recursion on values -/

/-- Pascal's rule (exponential; small arguments only). -/
def choosePascal : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choosePascal n k + choosePascal n (k + 1)

/-- Integer square root by Newton's iteration from above (fuel 200). -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + n / x) / 2
    if y ≥ x then x else isqrtGo n fuel y

def isqrt (n : Nat) : Nat := if n < 2 then n else isqrtGo n 200 (n / 2 + 1)

/-- Square and multiply, by well-founded recursion on `e / 2`. Moduli below
`3037000500` keep `(m - 1)²` below `2⁶³`. -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    let r := powMod b (e / 2) m
    let r2 := r * r % m
    if e % 2 == 0 then r2 else r2 * (b % m) % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- The decimal digit sum, by well-founded recursion on `n / 10`. -/
def digitSum (n : Nat) : Nat :=
  if h : n < 10 then n else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Koka `hamming.kk`'s gcd by subtraction (`termination_by x + y`). -/
def gcdSub (x y : Nat) : Nat :=
  if hx : x = 0 then y
  else if hy : y = 0 then x
  else if x < y then gcdSub x (y - x) else gcdSub (x - y) y
termination_by x + y
decreasing_by all_goals omega

end Scalar

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Scalar.tailfib", [n] => toString (Scalar.tailfib n)
        | "Scalar.nfib", [n] => toString (Scalar.nfib n)
        | "Scalar.isEven", [n] => toString (Scalar.isEven n)
        | "Scalar.isOdd", [n] => toString (Scalar.isOdd n)
        | "Scalar.f91", [n] => toString (Scalar.f91 n)
        | "Scalar.factorial", [n] => toString (Scalar.factorial n)
        | "Scalar.impFor", [k] => toString (Scalar.impFor k)
        | "Scalar.pyth", [n] => toString (Scalar.pyth n)
        | "Scalar.sfib", [n] => toString (Scalar.sfib n)
        | "Scalar.collatz", [n] => toString (Scalar.collatz n)
        | "Scalar.collatzBest", [n] => toString (Scalar.collatzBest n)
        | "Scalar.isPrime", [n] => toString (Scalar.isPrime n)
        | "Scalar.primeCount", [n] => toString (Scalar.primeCount n)
        | "Scalar.sigma", [n] => toString (Scalar.sigma n)
        | "Scalar.isPerfect", [n] => toString (Scalar.isPerfect n)
        | "Scalar.perfectCount", [n] => toString (Scalar.perfectCount n)
        | "Scalar.chooseMul", [n, k] => toString (Scalar.chooseMul n k)
        | "Scalar.lcmUpTo", [n] => toString (Scalar.lcmUpTo n)
        | "Scalar.choosePascal", [n, k] => toString (Scalar.choosePascal n k)
        | "Scalar.isqrt", [n] => toString (Scalar.isqrt n)
        | "Scalar.powMod", [b, e, m] => toString (Scalar.powMod b e m)
        | "Scalar.digitSum", [n] => toString (Scalar.digitSum n)
        | "Scalar.gcdSub", [x, y] => toString (Scalar.gcdSub x y)
        | _, _ => s!"unknown root {root} {args}"
