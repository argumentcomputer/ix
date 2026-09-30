import CompilatrixTests.Sem.Toy.Pipeline

/-!
# Toy pipeline cases

Elaboration-time checks of the three toy levels and the composed pipeline:
`fib 10 = 55` at every level (with the exact clocks where each level stops
timing out: depth 9 in the source, `9·3 + 2` after two ticks per body, and
530 total charges on the machine), divergence (with its proof at the source
and the pipeline's corollary at the target), an `add` that overflows only
on the machine, a stuck call, and a rejected program.
-/

namespace CompilatrixTests.Sem.Toy.Cases

open Compilatrix.Sem CompilatrixTests.Sem.Toy

def fib : Prog :=
  [.ifz (.sub .arg (.lit 1)) .arg
    (.add (.call 0 (.sub .arg (.lit 1))) (.call 0 (.sub .arg (.lit 2))))]

/-- `f x = f x`. -/
def loop : Prog := [.call 0 .arg]

/-- `2^64 - 1 + x`: exact in the source, an overflow on the machine for
`x > 0`. -/
def overflow : Prog := [.add (.lit (2 ^ 64 - 1)) .arg]

/-- Calls a function that does not exist. -/
def unknown : Prog := [.call 7 .arg]

/-- The machine run of the pipeline's output, or `stuck` if it rejects. -/
def target (p : Prog) (n x k : Nat) : Result Nat :=
  match compile p n with
  | some q => Stack.run q x k
  | none => .stuck

/-! ## `fib 10 = 55` -/

#guard Big.run fib 10 9 == .ok 55
#guard Big.run fib 10 8 == .timeout
#guard Big.run (Tick.pass fib 2) 10 29 == .ok 55
#guard Big.run (Tick.pass fib 2) 10 28 == .timeout
#guard target fib 2 10 530 == .ok 55
#guard target fib 2 10 529 == .timeout
#guard target fib 0 10 176 == .ok 55
#guard target fib 0 10 175 == .timeout
#guard (List.range 12).all fun x =>
  Big.run fib x 20 == target fib 3 x 100000

-- Each level is clock monotone on `fib 10`.
#guard (List.range 600).all fun k =>
  (Big.run fib 10 k == .timeout || Big.run fib 10 k == .ok 55) &&
  (Big.run (Tick.pass fib 2) 10 k == .timeout || Big.run (Tick.pass fib 2) 10 k == .ok 55) &&
  (target fib 2 10 k == .timeout || target fib 2 10 k == .ok 55)

/-! ## Divergence -/

#guard (List.range 200).all fun k =>
  Big.run loop 0 k == .timeout && Big.run (Tick.pass loop 3) 0 k == .timeout &&
    target loop 3 0 k == .timeout

theorem loop_timeout (x : Nat) : ∀ k, Big.run loop x k = .timeout
  | 0 => rfl
  | k + 1 => loop_timeout x k

/-- The pipeline preserves the loop's divergence. -/
theorem loop_target {n x : Nat} {q : Stack.Program} (h : compile loop n = some q) :
    (∀ k, Stack.run q x k = .timeout) ∨ ∃ k failure, Stack.run q x k = .resource failure :=
  compile_diverges h (loop_timeout x)

/-! ## Overflow: a resource failure only the machine has -/

#guard Big.run overflow 1 0 == .ok (2 ^ 64)
#guard Big.run (Tick.pass overflow 1) 1 1 == .ok (2 ^ 64)
#guard target overflow 1 1 10 == .resource .natOverflow
#guard target overflow 1 0 10 == .ok (2 ^ 64 - 1)

/-! ## Stuck and rejected programs -/

#guard Big.run unknown 0 5 == .stuck
#guard Big.run (Tick.pass unknown 2) 0 5 == .stuck
#guard target unknown 2 0 5 == .stuck
#guard (compile [] 1).isNone

end CompilatrixTests.Sem.Toy.Cases
