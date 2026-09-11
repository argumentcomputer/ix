import Ix.Compiler.IxIR2.Borrow.Rewrite
import Ix.Compiler.IxIR2.Eval

/-! Closed-program translation validation for borrowed calls. Structural
validation is necessary but does not prove that moving a release preserves
results or peak space. This boundary therefore derives finite execution
certificates internally for the exact baseline and reconstructed program.
Only scalar results, complete reclamation, a strict RC improvement, and no
increase in peak live heap nodes can select the optional rewrite. It makes
no claim about open functions on arbitrary runtime arguments. -/

namespace Ix.Compiler.IxIR2.Borrow

structure Budget where
  control : Nat := 1000
  heap : Nat := 1000
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

inductive ReplayError where
  | execution (error : Eval.Error)
  | nonScalar
  | notClosed
  | resultMismatch
  | reclamation
  | noImprovement
  | peakIncrease
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def run (context : Validate.Context) (budget : Budget) (program : Program) :
    Except Eval.Error Eval.Result :=
  Eval.runMain (Eval.Context.ofProgram program context.schemas) .physical
    program budget.control budget.heap

structure Execution (context : Validate.Context) (budget : Budget) (program : Program) where
  result : Eval.Result
  number : Nat
  ran : run context budget program = .ok result
  scalar : result.value = .lit (.nat number)
  arity : program.main.signature.params.size = 0
  nonempty : program.main.blocks.isEmpty = false

def execute (context : Validate.Context) (budget : Budget) (program : Program) :
    Except ReplayError (Execution context budget program) := do
  if arity : program.main.signature.params.size = 0 then
    if nonempty : program.main.blocks.isEmpty = false then
      match ran : run context budget program with
      | .error error => .error (.execution error)
      | .ok result =>
          match scalar : result.value with
          | .lit (.nat number) => pure ⟨result, number, ran, scalar, arity, nonempty⟩
          | _ => .error .nonScalar
    else .error .notClosed
  else .error .notClosed

/-- Reclamation checks actual slots as well as counters. -/
def Reclaimed (store : Eval.Store) : Prop :=
  store.heap.live = 0 ∧ store.heap.allocs = store.heap.frees ∧
    store.heap.nodes.all Option.isNone = true

instance (store : Eval.Store) : Decidable (Reclaimed store) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Improved (limits : Limits) (context : Validate.Context)
    (budget : Budget) (baseline : Program) where
  rewrite : Checked limits context baseline
  before : Execution context budget baseline
  after : Execution context budget rewrite.program
  same : before.number = after.number
  beforeReclaimed : Reclaimed before.result.store
  afterReclaimed : Reclaimed after.result.store
  fewerRC : after.result.store.heap.rcops < before.result.store.heap.rcops
  peak : after.result.store.peakLiveNodes ≤ before.result.store.peakLiveNodes

def replay {limits : Limits} (context : Validate.Context) (budget : Budget)
    {baseline : Program} (rewrite : Checked limits context baseline) :
    Except ReplayError (Improved limits context budget baseline) := do
  let before ← execute context budget baseline
  let after ← execute context budget rewrite.program
  if same : before.number = after.number then
    if beforeReclaimed : Reclaimed before.result.store then
      if afterReclaimed : Reclaimed after.result.store then
        if fewerRC : after.result.store.heap.rcops < before.result.store.heap.rcops then
          if peak : after.result.store.peakLiveNodes ≤ before.result.store.peakLiveNodes then
            pure ⟨rewrite, before, after, same, beforeReclaimed, afterReclaimed, fewerRC, peak⟩
          else .error .peakIncrease
        else .error .noImprovement
      else .error .reclamation
    else .error .reclamation
  else .error .resultMismatch

inductive Fallback where
  | noCandidates
  | rewrite (error : Error)
  | replay (error : ReplayError)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

inductive Decision (limits : Limits) (context : Validate.Context)
    (budget : Budget) (baseline : Program) where
  | baseline (reason : Fallback)
  | improved (result : Improved limits context budget baseline)

structure Selection (limits : Limits) (context : Validate.Context)
    (budget : Budget) (baseline : Program) where
  baselineChecked : Validate.Checked limits.validator context baseline
  inference : Inference
  decision : Decision limits context budget baseline

def Selection.program {limits context budget baseline}
    (selected : Selection limits context budget baseline) : Program :=
  match selected.decision with
  | .baseline _ => baseline
  | .improved result => result.rewrite.program

def optimize {limits : Limits} {context : Validate.Context} {baseline : Program}
    (baselineChecked : Validate.Checked limits.validator context baseline)
    (budget : Budget := {}) : Selection limits context budget baseline :=
  let inference := infer limits context baseline
  let decision := if inference.summaries.isEmpty then .baseline .noCandidates else
    match check limits context baseline inference.summaries with
    | .error error => .baseline (.rewrite error)
    | .ok rewrite =>
        match replay context budget rewrite with
        | .error error => .baseline (.replay error)
        | .ok result => .improved result
  ⟨baselineChecked, inference, decision⟩

theorem Execution.steps {context budget program} (execution : Execution context budget program) :
    ∃ count,
      budget.control = count + execution.result.controlRemaining ∧
      Eval.Steps (Eval.Context.ofProgram program context.schemas) .physical count
        (Eval.initialMachine program.main #[] budget.heap)
        { store := execution.result.store, heapFuel := execution.result.heapRemaining
          control := .halted (.lit (.nat execution.number)) } := by
  have ran := execution.ran
  unfold run at ran
  rw [Eval.runMain_eq_runMachine execution.arity execution.nonempty] at ran
  simpa only [execution.scalar] using Eval.runMachine_steps ran

theorem Improved.preservation {limits context budget baseline}
    (result : Improved limits context budget baseline) :
    result.before.result.value = result.after.result.value := by
  rw [result.before.scalar, result.after.scalar, result.same]

theorem Improved.resources {limits context budget baseline}
    (result : Improved limits context budget baseline) :
    Reclaimed result.before.result.store ∧ Reclaimed result.after.result.store ∧
    result.after.result.store.heap.rcops < result.before.result.store.heap.rcops ∧
    result.after.result.store.peakLiveNodes ≤ result.before.result.store.peakLiveNodes :=
  ⟨result.beforeReclaimed, result.afterReclaimed, result.fewerRC, result.peak⟩

theorem Selection.valid {limits context budget baseline}
    (selected : Selection limits context budget baseline) :
    Validate.ValidWith limits.validator context selected.program := by
  cases h : selected.decision with
  | baseline _ =>
      simpa [Selection.program, h] using
        (show Validate.ValidWith limits.validator context baseline from
          ⟨selected.baselineChecked.stats, selected.baselineChecked.accepted⟩)
  | improved result => simpa [Selection.program, h] using result.rewrite.valid

theorem Selection.fallbackExact {limits context budget baseline}
    (selected : Selection limits context budget baseline) {reason : Fallback}
    (fallback : selected.decision = .baseline reason) : selected.program = baseline := by
  simp [Selection.program, fallback]

end Ix.Compiler.IxIR2.Borrow
