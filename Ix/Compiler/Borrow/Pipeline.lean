import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR2.Borrow.Replay

/-! Attach the optional borrowed-call pass to the actual validated Ixon
compiler. In addition to the exact baseline/rewrite replay, selection checks
the source evaluation internally. A failed optional check retains the entire
checked baseline attachment. Invalid source is still a compiler error. -/

namespace Ix.Compiler.Borrow

open Ix.Compiler.Ixon (Address Owned)

structure Options where
  maxCandidates : Nat := 32
  maxRounds : Nat := 16
  maxAttempts : Nat := 256
  sourceFuel : Nat := 1000
  budget : IxIR2.Borrow.Budget := {}
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Options.limits (options : Options) : IxIR2.Borrow.Limits :=
  { maxCandidates := options.maxCandidates, maxRounds := options.maxRounds
    maxAttempts := options.maxAttempts }

structure SourceExecution (constants : List (Address × Ixon.Constant))
    (root : Address) (config : Pipeline.Config) (fuel : Nat) where
  number : Nat
  ran : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
    (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource =
      .ok (.litV (.natL number))

def executeSource (constants : List (Address × Ixon.Constant))
    (root : Address) (config : Pipeline.Config) (fuel : Nat) :
    Except String (SourceExecution constants root config fuel) :=
  match ran : Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) fuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource with
  | .ok (.litV (.natL number)) => .ok ⟨number, ran⟩
  | .ok _ => .error "source result is outside the closed scalar borrow boundary"
  | .error error => .error s!"source replay failed: {repr error}"

structure Improved {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (options : Options) where
  target : IxIR2.Borrow.Improved options.limits attached.target.artifact.validationContext
    options.budget attached.target.artifact.program
  source : SourceExecution constants root config options.sourceFuel
  agrees : source.number = target.before.number

inductive Fallback where
  | target (reason : IxIR2.Borrow.Fallback)
  | source (message : String)
  | sourceMismatch
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Selection {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (options : Options) where
  inference : IxIR2.Borrow.Inference
  attempt : Except Fallback (Improved attached options)

def select {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (options : Options := {}) : Selection attached options :=
  let baselineChecked : IxIR2.Validate.Checked options.limits.validator
      attached.target.artifact.validationContext attached.target.artifact.program :=
    ⟨attached.target.stats, attached.target.accepted⟩
  let selected := IxIR2.Borrow.optimize baselineChecked options.budget
  let attempt := match selected.decision with
    | .baseline reason => .error (.target reason)
    | .improved target =>
        match executeSource constants root config options.sourceFuel with
        | .error message => .error (.source message)
        | .ok source =>
            if agrees : source.number = target.before.number then
              .ok ⟨target, source, agrees⟩
            else .error .sourceMismatch
  ⟨selected.inference, attempt⟩

def Selection.program {constants root config world eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel}
    (selection : Selection attached options) : IxIR2.Program :=
  match selection.attempt with
  | .error _ => attached.target.artifact.program
  | .ok improved => improved.target.rewrite.program

structure Compilation (constants : List (Address × Ixon.Constant)) (root : Address)
    (config : Pipeline.Config) (world : Owned) (eraseFuel lowerFuel : Nat)
    (options : Options) where
  baseline : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel
  selection : Selection baseline options

def compileValidated (constants : List (Address × Ixon.Constant)) (root : Address)
    (config : Pipeline.Config) (world : Owned) (checkFuel eraseFuel validateFuel lowerFuel maxDepth : Nat)
    (options : Options := {}) :
    Except IxIR2.Pipeline.Error (Compilation constants root config world eraseFuel lowerFuel options) := do
  let baseline ← IxIR2.Pipeline.compileValidated constants root config world
    checkFuel eraseFuel validateFuel lowerFuel maxDepth
  pure ⟨baseline, select baseline options⟩

theorem Improved.sourcePreservation {constants root config world eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel}
    (result : Improved attached options) :
    Ixon.Eval.eval (Pipeline.validatedEvalCtx constants config) options.sourceFuel
      (Pipeline.validatedMainFrame root) [] Pipeline.validatedMainSource =
        .ok (.litV (.natL result.source.number)) ∧
    IxIR2.Borrow.run attached.target.artifact.validationContext options.budget
        result.target.rewrite.program = .ok result.target.after.result ∧
    result.target.after.result.value = .lit (.nat result.source.number) := by
  refine ⟨result.source.ran, result.target.after.ran, ?_⟩
  rw [result.target.after.scalar, result.agrees, result.target.same]

theorem Improved.resources {constants root config world eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel}
    (result : Improved attached options) :
    IxIR2.Borrow.Reclaimed result.target.before.result.store ∧
    IxIR2.Borrow.Reclaimed result.target.after.result.store ∧
    result.target.after.result.store.heap.rcops < result.target.before.result.store.heap.rcops ∧
    result.target.after.result.store.peakLiveNodes ≤ result.target.before.result.store.peakLiveNodes :=
  result.target.resources

theorem Selection.valid {constants root config world eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel}
    (selection : Selection attached options) :
    IxIR2.Validate.Valid attached.target.artifact.validationContext selection.program := by
  cases h : selection.attempt with
  | error _ =>
      simpa [Selection.program, h] using
        (show IxIR2.Validate.Valid attached.target.artifact.validationContext
            attached.target.artifact.program from ⟨attached.target.stats, attached.target.accepted⟩)
  | ok improved =>
      simpa [Selection.program, h, Options.limits, IxIR2.Validate.Valid] using
        improved.target.rewrite.valid

theorem Selection.fallbackExact {constants root config world eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel}
    (selection : Selection attached options) {reason : Fallback}
    (fallback : selection.attempt = .error reason) :
    selection.program = attached.target.artifact.program := by
  simp [Selection.program, fallback]

end Ix.Compiler.Borrow
