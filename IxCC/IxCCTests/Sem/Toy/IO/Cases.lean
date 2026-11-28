import IxCCTests.Sem.Toy.IO.Pipeline

/-!
# IO toy cases

The IO toy's clause check on concrete programs. `count x = out x;
count (x + 1)` never returns and keeps producing output: its source run at
depth `k` times out after `out x, …, out (x + k)` (`count_run`), so its
traced behaviour is a divergence whose finite traces are those prefixes
(`count_tbehaviour`). The toy's `TSim` specialises to it for each pass and
composes (`count_sim`), with progress, and gives the traced refinement
(`count_refines`); through the pipeline, the machine performs every one of
those prefixes unless it fails for a resource (`count_live`: it does
overflow at 2^64), and never returns (`count_never_returns`).

Elaboration-time checks under a concrete oracle (the answer is ten times
the number of events so far): outputs, an echo loop whose inputs depend on
the history, a terminating program that reads twice, an `add` that
overflows on the machine before the event the source performs, and a stuck
call after an output that both levels perform.
-/

namespace IxCCTests.Sem.Toy.IO.Cases

open IxCC.Sem IxCCTests.Sem.Toy.IO

/-- `count x = out x; count (x + 1)`. -/
def countBody : Expr := .out .arg (.call 0 (.add .arg (.lit 1)))

def count : Prog := [countBody]

/-- `echo x = out (inp); echo x`. -/
def echo : Prog := [.out .inp (.call 0 .arg)]

/-- Read two numbers and return their sum. -/
def sum2 : Prog := [.add .inp .inp]

/-- Output `2^64 - 1 + x`, then return `x`: an overflow on the machine for
`x > 0`, before the event. -/
def big : Prog := [.out (.add (.lit (2 ^ 64 - 1)) .arg) .arg]

/-- Output `x`, then call a function that does not exist. -/
def unknown : Prog := [.out .arg (.call 7 .arg)]

/-- A concrete oracle: ten times the number of events so far. -/
def tens : Oracle := fun h => h.length * 10

/-- The machine run of the pipeline's output, or `stuck` if it rejects. -/
def target (p : Prog) (n x : Nat) (o : Oracle) (k : Nat) : Traced Ev Nat :=
  match compile p n with
  | some q => Stack.run q x o k
  | none => ⟨.stuck, []⟩

/-! ## Concrete runs -/

#guard Big.run count 0 tens 3 == ⟨.timeout, [.out 0, .out 1, .out 2, .out 3]⟩
#guard Big.run (Tick.pass count 2) 0 tens 11 == ⟨.timeout, [.out 0, .out 1, .out 2, .out 3]⟩
#guard target count 2 0 tens 11 == ⟨.timeout, [.out 0, .out 1, .out 2, .out 3]⟩
-- The machine's trace grows with the clock (three charges per call).
#guard ((List.range 12).map fun k => (target count 2 0 tens k).trace.length) ==
  [0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4]
#guard (List.range 40).all fun k =>
  (target count 2 5 tens k).result == .timeout &&
    (target count 2 5 tens k).trace.isPrefixOf (target count 2 5 tens (k + 1)).trace

#guard Big.run echo 0 tens 2 ==
  ⟨.timeout, [.inp 0, .out 0, .inp 20, .out 20, .inp 40, .out 40]⟩
#guard target echo 1 0 tens 5 ==
  ⟨.timeout, [.inp 0, .out 0, .inp 20, .out 20, .inp 40, .out 40]⟩

#guard Big.run sum2 0 tens 0 == ⟨.ok 10, [.inp 0, .inp 10]⟩
#guard target sum2 0 0 tens 0 == ⟨.ok 10, [.inp 0, .inp 10]⟩

#guard Big.run big 1 tens 0 == ⟨.ok 1, [.out (2 ^ 64)]⟩
#guard target big 0 1 tens 5 == ⟨.resource .natOverflow, []⟩
#guard target big 0 0 tens 5 == ⟨.ok 0, [.out (2 ^ 64 - 1)]⟩

#guard Big.run unknown 3 tens 4 == ⟨.stuck, [.out 3]⟩
#guard target unknown 1 3 tens 4 == ⟨.stuck, [.out 3]⟩

/-! ## A program that never returns and keeps producing output -/

/-- `out x, …, out (x + k)`. -/
def countTrace (x : Nat) : Nat → List Ev
  | 0 => [.out x]
  | k + 1 => .out x :: countTrace (x + 1) k

theorem count_eval (o : Oracle) :
    ∀ k x h, Big.eval o count k x countBody h = ⟨.timeout, countTrace x k⟩
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have ih := count_eval o k (x + 1)
    simp only [countBody, count] at ih
    simp [Big.eval, Big.evalAt, countBody, M.bind, M.pure, M.emit, Big.callAt, count, ih,
      countTrace]

/-- Under every oracle, the source at depth `k` times out after
`out x, …, out (x + k)`. -/
theorem count_run (x : Nat) (o : Oracle) (k : Nat) :
    Big.run count x o k = ⟨.timeout, countTrace x k⟩ :=
  count_eval o k x []

/-- The source's traced behaviour: a divergence performing those
prefixes. -/
theorem count_tbehaviour (x : Nat) (o : Oracle) :
    tbehaviour (Big.run count x o) = .diverges (countTrace x) := by
  rw [tbehaviour_of_forall_timeout fun k => by rw [count_run]]
  simp only [count_run]

/-- The traced simulation of both passes on `count`, composed: forward,
timeout after a prefix, and progress, for every oracle. -/
theorem count_sim (n x : Nat) :
    TSim (RelComp Eq Eq) (fun k => id (id k)) (Big.run count x)
      (Stack.run (Stack.compileProg (Tick.pass count n)) x) :=
  (Tick.sim count n x).comp (fun o => Stack.run_mono _ x o) (Stack.sim (Tick.pass count n) x)

/-- The traced refinement on `count`: the machine diverges performing
the source's prefixes, or fails for a resource after one of them. -/
theorem count_refines (n x : Nat) (o : Oracle) :
    TBehaviour.Refines (RelComp Eq Eq) (.diverges (countTrace x))
      (tbehaviour (Stack.run (Stack.compileProg (Tick.pass count n)) x o)) := by
  rw [← count_tbehaviour x o]
  exact (count_sim n x).refines (fun o => Big.run_mono count x o)
    (fun o => Stack.run_mono _ x o) o

/-- Through the pipeline, under every oracle, the machine performs
`out x, …, out (x + k)` at some clock for every `k`, unless it fails for a
resource. -/
theorem count_live {n : Nat} {q : Stack.Program} (h : compile count n = some q) (x : Nat)
    (o : Oracle) (k : Nat) :
    (∃ k', countTrace x k <+: (Stack.run q x o k').trace) ∨
      ∃ k' failure, (Stack.run q x o k').result = .resource failure := by
  rcases compile_live h x o k with ⟨k', hp⟩ | hf | ⟨k', hs⟩
  · rw [count_run] at hp
    exact .inl ⟨k', hp⟩
  · exact .inr hf
  · rw [count_run] at hs
    cases hs

/-- Through the pipeline the machine never returns: it runs out of clock
at every clock or fails for a resource. -/
theorem count_never_returns {n : Nat} {q : Stack.Program} (h : compile count n = some q)
    (x : Nat) (o : Oracle) :
    (∀ k, (Stack.run q x o k).result = .timeout) ∨
      ∃ k failure, (Stack.run q x o k).result = .resource failure :=
  compile_diverges h fun k => by rw [count_run]

end IxCCTests.Sem.Toy.IO.Cases
