import Ix.Compiler.IxIR2.Validate
import Ix.Compiler.IxIR2.Eval
import Ix.Compiler.X86.Eval
import Ix.Compiler.X86.ScalarApply
import Ix.Compiler.IxIR2.EvalFuel

/-!
# First IxIR₂ to x86-64 scalar selection slice

The selector accepts two exact source graphs: a literal/alias/return leaf and
the closed application graph emitted by the validated synthetic Ixon scalar.
The latter retains both addressed declarations, its PAP/application path, and
the main tail call. Selection folds either graph's bounded Nat observation to
an x86 immediate move and returns it in System V's `rax` result register.

The executable selector always runs the ordinary bounded IxIR₂ validator
before reflecting exact source equality. `Output.refinesSuccessfulRun` relates
any successful physical execution to the actual selected typed local x86
result, independently of execution budgets. `PipelineSim` composes this with
validated Ixon evaluation. The E0 bytes implementing the typed machine remain
the separately ledgered encoder/local-ISA boundary.
-/

namespace Ix.Compiler.X86.Select

open Ix.Compiler

def validationContext : IxIR2.Validate.Context := {}

def scalarSignature : IxIR2.Signature :=
  { params := #[]
    result := .unique
    papSafe := false }

def scalarMoveBlock (word : Word) : IxIR2.Block :=
  { valueParams := #[]
    creditParams := #[]
    instructions := #[
      .move (.lit (.nat word.toNat)),
      .move (.reg 0)]
    terminator := .ret (.reg 1) }

/-- The first selected IxIR₂ family.  The second move is intentional: it
exercises block-local SSA register resolution instead of selecting a literal
return directly. -/
def scalarMoveProgram (word : Word) : IxIR2.Program :=
  { declarations := []
    main :=
      { signature := scalarSignature
        blocks := #[scalarMoveBlock word] } }

private def moveCandidate? (source : IxIR2.Program) : Option Word := do
  let block ← source.main.blocks[0]?
  let .move (.lit (.nat number)) ← block.instructions[0]? | none
  return UInt64.ofNat number

/-- Recognize the bounded literal/alias family by reflecting exact program
equality. The comparison also rejects a Nat that wraps at the word boundary. -/
def sourceWord? (source : IxIR2.Program) : Option Word := do
  let word ← moveCandidate? source
  if source == scalarMoveProgram word then some word else none

@[simp] theorem sourceWord?_scalarMoveProgram (word : Word) :
    sourceWord? (scalarMoveProgram word) = some word := by
  simp [sourceWord?, moveCandidate?, scalarMoveProgram, scalarMoveBlock,
    scalarSignature, UInt64.ofNat_toNat]

theorem sourceWord?_sound {source : IxIR2.Program} {word : Word}
    (found : sourceWord? source = some word) : source = scalarMoveProgram word := by
  obtain ⟨candidate, _, selected⟩ := Option.bind_eq_some_iff.mp found
  split at selected
  · rename_i matched
    cases Option.some.inj selected
    exact beq_iff_eq.mp matched
  · contradiction

/-- Both recognized graphs retain exact source equations. The closed
application family is the actual validated Ixon compiler output. -/
inductive SourceShape (source : IxIR2.Program) (word : Word) : Prop where
  | moves (exactSource : source = scalarMoveProgram word)
  | closedApply (workerAddress entryAddress : Ixon.Address)
      (distinct : workerAddress ≠ entryAddress)
      (exactSource : source = ScalarApply.program word workerAddress entryAddress)

private structure Recognized (source : IxIR2.Program) where
  word : Word
  shape : SourceShape source word

private def applyCandidate? (source : IxIR2.Program) :
    Option (Word × Ixon.Address × Ixon.Address) := do
  let [(workerAddress, .fn worker), (entryAddress, .fn _)] := source.declarations | none
  let block ← worker.blocks[0]?
  let .ret (.lit (.nat number)) := block.terminator | none
  return (UInt64.ofNat number, workerAddress, entryAddress)

private def recognize (source : IxIR2.Program) : Option (Recognized source) :=
  match found : sourceWord? source with
  | some word => some { word, shape := .moves (sourceWord?_sound found) }
  | none => do
      let (word, workerAddress, entryAddress) ← applyCandidate? source
      if distinct : workerAddress = entryAddress then none
      else if matched : source == ScalarApply.program word workerAddress entryAddress then
        some { word, shape := .closedApply workerAddress entryAddress distinct (beq_iff_eq.mp matched) }
      else none

private theorem recognize_scalarMoveProgram (word : Word) :
    recognize (scalarMoveProgram word) = some { word, shape := .moves rfl } := by
  unfold recognize
  split
  · rename_i candidate found
    have same : candidate = word := Option.some.inj
      (found.symm.trans (sourceWord?_scalarMoveProgram word))
    subst candidate
    rfl
  · rename_i found
    simp at found

/-- Initial scalar calling convention: a nullary leaf returns its machine word
in `rax`; it needs no frame and does not touch the entry stack pointer. -/
def targetProgram (word : Word) : X86.Program :=
  { entry := 0
    blocks := #[
      { instructions := #[.mov .w64 SysV.resultRegister (.imm word)]
        terminator := .ret }] }

theorem targetProgram_wellFormed (word : Word) :
    (targetProgram word).wellFormed = true := by
  simp [targetProgram, X86.Program.wellFormed, X86.Program.hasBlock,
    X86.Block.offsetsFit, X86.Block.targetsValid,
    X86.Instr.targetsValid, X86.Terminator.targetsValid]

def targetChecked (word : Word) : X86.Checked :=
  { program := targetProgram word
    valid := targetProgram_wellFormed word }

inductive Error where
  | invalidSource (error : IxIR2.Validate.Error)
  | unsupportedScalarShape
  deriving Repr

/-- A selected target carries the exact successful source-validation equation
that authorized selection. -/
structure Output (source : IxIR2.Program) where
  sourceStats : IxIR2.Validate.Stats
  sourceAccepted :
    IxIR2.Validate.validate validationContext source = .ok sourceStats
  word : Word
  shape : SourceShape source word
  target : X86.Checked
  targetProduced : target = targetChecked word

theorem Output.sourceValid {source : IxIR2.Program} (output : Output source) :
    IxIR2.Validate.Valid validationContext source :=
  ⟨output.sourceStats, output.sourceAccepted⟩

/-- Validator-gated selection for the first scalar slice. -/
def select (source : IxIR2.Program) : Except Error (Output source) :=
  match accepted : IxIR2.Validate.validate validationContext source with
  | .error error => .error (.invalidSource error)
  | .ok stats =>
      match recognize source with
      | none => .error .unsupportedScalarShape
      | some recognized =>
          .ok
            { sourceStats := stats
              sourceAccepted := accepted
              word := recognized.word
              shape := recognized.shape
              target := targetChecked recognized.word
              targetProduced := rfl }

/-- Any validated member of the canonical scalar family is accepted by the
selector, and the selected word and typed target are definitionally the ones
used by the semantic refinement theorem below. -/
theorem select_scalarMoveProgram (word : Word)
    (stats : IxIR2.Validate.Stats)
    (accepted : IxIR2.Validate.validate validationContext
      (scalarMoveProgram word) = .ok stats) :
    ∃ output, select (scalarMoveProgram word) = .ok output ∧
      output.word = word ∧ output.target = targetChecked word := by
  unfold select
  split
  · rename_i error invalid
    simp_all
  · rename_i selectedStats valid
    have same : selectedStats = stats := Except.ok.inj (valid.symm.trans accepted)
    subst selectedStats
    rw [recognize_scalarMoveProgram]
    exact ⟨_, rfl, rfl, rfl⟩

def sourceContext (word : Word) : IxIR2.Eval.Context :=
  IxIR2.Eval.Context.ofProgram (scalarMoveProgram word) (fun _ _ => none)

private def sourceFrame0 (word : Word) : IxIR2.Eval.Frame :=
  { definition := (scalarMoveProgram word).main }

private def sourceFrame1 (word : Word) : IxIR2.Eval.Frame :=
  { definition := (scalarMoveProgram word).main
    pc := 1
    values := #[.lit (.nat word.toNat)] }

private def sourceFrame2 (word : Word) : IxIR2.Eval.Frame :=
  { definition := (scalarMoveProgram word).main
    pc := 2
    values := #[.lit (.nat word.toNat), .lit (.nat word.toNat)] }

private def sourceMachine0 (word : Word) : IxIR2.Eval.Machine :=
  { heapFuel := 0
    control := .running (sourceFrame0 word) [] }

private def sourceMachine1 (word : Word) : IxIR2.Eval.Machine :=
  { heapFuel := 0
    control := .running (sourceFrame1 word) [] }

private def sourceMachine2 (word : Word) : IxIR2.Eval.Machine :=
  { heapFuel := 0
    control := .running (sourceFrame2 word) [] }

private def sourceHalted (word : Word) : IxIR2.Eval.Machine :=
  { heapFuel := 0
    control := .halted (.lit (.nat word.toNat)) }

theorem scalarMoveSteps (word : Word) (context : IxIR2.Eval.Context := sourceContext word) :
    IxIR2.Eval.Steps context .physical 3
      (sourceMachine0 word) (sourceHalted word) := by
  have first : IxIR2.Eval.Step context .physical
      (sourceMachine0 word) (sourceMachine1 word) := by
    simpa [sourceMachine0, sourceMachine1, sourceFrame0, sourceFrame1]
      using
        (IxIR2.Eval.Step.move
          (context := context) (interpretation := .physical)
          (machine := sourceMachine0 word) (frame := sourceFrame0 word)
          (stack := []) (block := scalarMoveBlock word)
          (atom := .lit (.nat word.toNat))
          (value := .lit (.nat word.toNat))
          (control := rfl)
          (blockAt := by
            simp [sourceFrame0, scalarMoveProgram, scalarMoveBlock])
          (pc := by simp [sourceFrame0, scalarMoveBlock])
          (instruction := by simp [sourceFrame0, scalarMoveBlock])
          (resolved := rfl))
  have second : IxIR2.Eval.Step context .physical
      (sourceMachine1 word) (sourceMachine2 word) := by
    simpa [sourceMachine1, sourceMachine2, sourceFrame1, sourceFrame2]
      using
        (IxIR2.Eval.Step.move
          (context := context) (interpretation := .physical)
          (machine := sourceMachine1 word) (frame := sourceFrame1 word)
          (stack := []) (block := scalarMoveBlock word)
          (atom := .reg 0) (value := .lit (.nat word.toNat))
          (control := rfl)
          (blockAt := by
            simp [sourceFrame1, scalarMoveProgram, scalarMoveBlock])
          (pc := by simp [sourceFrame1, scalarMoveBlock])
          (instruction := by simp [sourceFrame1, scalarMoveBlock])
          (resolved := by simp [sourceFrame1, IxIR2.Eval.resolveAtom]))
  have third : IxIR2.Eval.Step context .physical
      (sourceMachine2 word) (sourceHalted word) := by
    simpa [sourceMachine2, sourceHalted, sourceFrame2]
      using
        (IxIR2.Eval.Step.retHalt
          (context := context) (interpretation := .physical)
          (machine := sourceMachine2 word) (frame := sourceFrame2 word)
          (block := scalarMoveBlock word) (atom := .reg 1)
          (value := .lit (.nat word.toNat))
          (control := rfl)
          (blockAt := by
            simp [sourceFrame2, scalarMoveProgram, scalarMoveBlock])
          (pc := by simp [sourceFrame2, scalarMoveBlock])
          (terminator := rfl)
          (resolved := by simp [sourceFrame2, IxIR2.Eval.resolveAtom])
          (noCredits := rfl)
          (world := rfl))
  exact .cons rfl first (.cons rfl second (.cons rfl third (.refl _)))

theorem scalarMoveSourceRuns (word : Word) (context : IxIR2.Eval.Context := sourceContext word) :
    IxIR2.Eval.runMain context .physical
        (scalarMoveProgram word) 3 0 =
      .ok
        { store := {}
          value := .lit (.nat word.toNat)
          controlRemaining := 0
          heapRemaining := 0 } := by
  rw [IxIR2.Eval.runMain_eq_runMachine (arity := rfl)
    (nonempty := by simp [scalarMoveProgram])]
  exact (scalarMoveSteps word context).runMachine_halted

theorem scalarMoveTargetRuns (word : Word) (core : X86.Core) :
    let result := X86.runFrom X86.Runtime.rejecting (targetChecked word) 2
      core
    result.status = .halted word ∧
      result.core.readReg .rsp = core.readReg .rsp := by
  simp [X86.runFrom, X86.run, X86.step, X86.Machine.initial,
    targetChecked, targetProgram, X86.executeInstr, X86.executeTerminator,
    X86.Machine.advanceWith, X86.PC.next?,
    X86.MoveSource.eval, X86.Core.writeReg, X86.Core.setReg,
    X86.Core.readReg, X86.Registers.set, SysV.resultRegister]

/-- Semantic refinement for the complete first slice.  The source observation
is the Nat literal corresponding exactly to the target word, and the target
additionally preserves the System V entry stack pointer. -/
theorem scalarMoveRefines (word : Word) :
    IxIR2.Eval.runMain (sourceContext word) .physical
        (scalarMoveProgram word) 3 0 =
      .ok
        { store := {}
          value := .lit (.nat word.toNat)
          controlRemaining := 0
          heapRemaining := 0 } ∧
    (X86.runFrom X86.Runtime.rejecting (targetChecked word) 2
      (X86.Core.empty 0x1008)).status = .halted word := by
  exact ⟨scalarMoveSourceRuns word,
    (scalarMoveTargetRuns word (X86.Core.empty 0x1008)).1⟩

/-- Flagship validator-to-semantics statement for this first slice: once the
ordinary IxIR₂ validator accepts a canonical member, the executable selector
returns a checked target and both machines return the same 64-bit scalar. -/
theorem selectScalarMoveRefines (word : Word)
    (stats : IxIR2.Validate.Stats)
    (accepted : IxIR2.Validate.validate validationContext
      (scalarMoveProgram word) = .ok stats) :
    ∃ output, select (scalarMoveProgram word) = .ok output ∧
      output.word = word ∧
      IxIR2.Eval.runMain (sourceContext word) .physical
          (scalarMoveProgram word) 3 0 =
        .ok
          { store := {}
            value := .lit (.nat word.toNat)
            controlRemaining := 0
            heapRemaining := 0 } ∧
      (X86.runFrom X86.Runtime.rejecting output.target 2
        (X86.Core.empty 0x1008)).status = .halted word := by
  obtain ⟨output, selected, result, target⟩ :=
    select_scalarMoveProgram word stats accepted
  refine ⟨output, selected, result, scalarMoveSourceRuns word, ?_⟩
  rw [target]
  exact (scalarMoveTargetRuns word (X86.Core.empty 0x1008)).1

theorem SourceShape.entryFacts {source : IxIR2.Program} {word : Word}
    (shape : SourceShape source word) :
    source.main.signature.params.size = 0 ∧ source.main.blocks.isEmpty = false := by
  cases shape with
  | moves exactSource => subst source; exact ⟨rfl, rfl⟩
  | closedApply workerAddress entryAddress distinct exactSource =>
      subst source; exact ⟨rfl, rfl⟩

/-- Shape reflection produces a physical run of the exact accepted graph.
Schemas and the oracle are arbitrary because neither supported graph uses
constructor layouts or extern calls. -/
theorem SourceShape.sourceRuns {source : IxIR2.Program} {word : Word}
    (shape : SourceShape source word)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List IxIR1.RVal → Option IxIR1.RVal) :
    ∃ controlFuel heapFuel result,
      IxIR2.Eval.runMain (IxIR2.Eval.Context.ofProgram source schemas oracle)
        .physical source controlFuel heapFuel = .ok result ∧
      result.value = .lit (.nat word.toNat) := by
  cases shape with
  | moves exactSource =>
      subst source
      exact ⟨3, 0, _, scalarMoveSourceRuns word _, rfl⟩
  | closedApply workerAddress entryAddress distinct exactSource =>
      subst source
      exact ⟨6, 2, _, ScalarApply.runs word workerAddress entryAddress distinct
        .physical 0 0 schemas oracle, rfl⟩

/-- Correctness of the actual returned selector artifact. Every successful
physical execution of its source returns the selected scalar, independently
of both evaluator budgets, and the exact selected typed x86 target returns
that word while preserving the entry stack pointer. -/
theorem Output.refinesSuccessfulRun {source : IxIR2.Program}
    (output : Output source)
    {schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema}
    {oracle : Ixon.Address → List IxIR1.RVal → Option IxIR1.RVal}
    {controlFuel heapFuel : Nat} {result : IxIR2.Eval.Result}
    (run : IxIR2.Eval.runMain (IxIR2.Eval.Context.ofProgram source schemas oracle)
      .physical source controlFuel heapFuel = .ok result)
    (core : X86.Core) :
    result.value = .lit (.nat output.word.toNat) ∧
      (X86.runFrom X86.Runtime.rejecting output.target 2 core).status = .halted output.word ∧
      (X86.runFrom X86.Runtime.rejecting output.target 2 core).core.readReg .rsp = core.readReg .rsp := by
  obtain ⟨_, _, expected, expectedRun, value⟩ := output.shape.sourceRuns schemas oracle
  have same := IxIR2.Eval.runMain_success_unique output.shape.entryFacts.1
    output.shape.entryFacts.2 run expectedRun
  refine ⟨same.2.trans value, ?_⟩
  rw [output.targetProduced]
  exact scalarMoveTargetRuns output.word core

end Ix.Compiler.X86.Select
