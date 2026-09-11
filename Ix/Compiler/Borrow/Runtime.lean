import Ix.Compiler.Borrow.RuntimeSource

/-! Ordinary validated source compilation followed by optional structural
borrow certification. Options contain only compiler/checker work limits;
runtime arguments and evaluation fuel are absent from selection. -/

namespace Ix.Compiler.Borrow.Runtime

open Ix.Compiler.Ixon (Address)

structure Options where
  maxCandidates : Nat := 32
  maxRounds : Nat := 16
  maxAttempts : Nat := 256
  maxSourceDepth : Nat := 32
  policy : IxIR2.Borrow.Open.Policy := {}
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Options.limits (options : Options) : IxIR2.Borrow.Limits :=
  { maxCandidates := options.maxCandidates, maxRounds := options.maxRounds, maxAttempts := options.maxAttempts }

structure Certified {constants root config eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel) (options : Options) where
  target : IxIR2.Borrow.Open.Certificate options.limits attached.target.artifact.validationContext attached.target.artifact.program
  source : Source.Shape attached.source.erasure.result.raw (.ref root) target.schema.zeroResult target.schema.succResult
  sameDepth : source.chain.depth = target.entry.beforeBody.depth

inductive Rejection where
  | target (reason : IxIR2.Borrow.Open.Rejection)
  | source
  | depth
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Selection {constants root config eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel) (options : Options) where
  inference : IxIR2.Borrow.Inference
  attempt : Except Rejection (Certified attached options)

def select {constants root config eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel)
    (options : Options := {}) : Selection attached options :=
  let checked : IxIR2.Validate.Checked options.limits.validator
      attached.target.artifact.validationContext attached.target.artifact.program :=
    ⟨attached.target.stats, attached.target.accepted⟩
  let target := IxIR2.Borrow.Open.optimize checked options.policy
  let attempt := do
    let target ← target.attempt.mapError Rejection.target
    let some source := Source.recognize attached.source.erasure.result.raw (.ref root)
        target.schema.zeroResult target.schema.succResult options.maxSourceDepth | throw .source
    if sameDepth : source.chain.depth = target.entry.beforeBody.depth then
      pure (⟨target, source, sameDepth⟩ : Certified attached options)
    else throw .depth
  ⟨target.inference, attempt⟩

def Selection.program {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (selection : Selection attached options) : IxIR2.Program :=
  match selection.attempt with
  | .ok certified => certified.target.rewrite.program
  | .error _ => attached.target.artifact.program

structure Compilation (constants : List (Address × Ixon.Constant)) (root : Address) (config : Pipeline.Config)
    (eraseFuel lowerFuel : Nat) (options : Options) where
  baseline : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel
  selection : Selection baseline options

def compileValidated (constants : List (Address × Ixon.Constant)) (root : Address) (config : Pipeline.Config)
    (checkFuel eraseFuel validateFuel lowerFuel maxDepth : Nat) (options : Options := {}) :
    Except IxIR2.Pipeline.Error (Compilation constants root config eraseFuel lowerFuel options) := do
  let baseline ← IxIR2.Pipeline.compileValidated constants root config .shared
    checkFuel eraseFuel validateFuel lowerFuel maxDepth
  return ⟨baseline, select baseline options⟩

theorem Selection.valid {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (selection : Selection attached options) :
    IxIR2.Validate.Valid attached.target.artifact.validationContext selection.program := by
  cases h : selection.attempt with
  | error _ =>
      simpa [Selection.program, h] using
        (show IxIR2.Validate.Valid attached.target.artifact.validationContext attached.target.artifact.program from
          ⟨attached.target.stats, attached.target.accepted⟩)
  | ok result =>
      simpa [Selection.program, h, Options.limits, IxIR2.Validate.Valid] using result.target.rewrite.valid

theorem Selection.fallbackExact {constants root config eraseFuel lowerFuel options}
    {attached : IxIR2.Pipeline.Attached constants root config .shared eraseFuel lowerFuel}
    (selection : Selection attached options) {reason : Rejection}
    (fallback : selection.attempt = .error reason) : selection.program = attached.target.artifact.program := by
  simp [Selection.program, fallback]

end Ix.Compiler.Borrow.Runtime
