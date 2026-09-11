import Ix.Compiler.UniqueReuse.Pipeline
import Ix.Compiler.X86.UniqueTarget

/-! Optional native selection from the actual checked unique-reversal
compilation. Selection requires static reuse, exact Word representation, and
the bounded native shape. A skip retains the existing compiler artifact. -/

namespace Ix.Compiler.UniqueReuse.Native

open Ix.Compiler.Ixon (Address Constant)
open Ix.Compiler.X86 (Word Checked)

variable {constants : List (Address × Constant)} {entry : Pipeline.ClosedEntry}
  {config : Pipeline.Config} {checkFuel eraseFuel : Nat} {limits : IxIR2.Validate.Limits}

structure Output (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  sourceTarget : CompiledTarget compilation.plan limits
  backendProduced : compilation.backend = .translated sourceTarget
  reuseSelected : sourceTarget.selection.reused = true
  words : List Word
  valuesExact : words.map UInt64.toNat = compilation.plan.values
  lengthBound : words.length ≤ X86.UniqueABI.maxLength
  main : Checked
  mainProduced : main.program = X86.UniqueTarget.program words
  release : Checked
  releaseProduced : release.program = X86.UniqueTarget.releaseProgram

inductive Selection (compilation : Compilation constants entry config checkFuel eraseFuel limits) where
  | skipped (reason : String)
  | native (output : Output compilation)

/-- Native objects can only be requested through the successful certificate.
The representability comparison rejects large Nats instead of truncating them. -/
def select (compilation : Compilation constants entry config checkFuel eraseFuel limits) : Selection compilation :=
  match backend : compilation.backend with
  | .ownedOnly reason => .skipped s!"native requires a translated target: {reason}"
  | .translated target =>
      if reused : target.selection.reused = true then
        let words := compilation.plan.values.map UInt64.ofNat
        if exactValues : words.map UInt64.toNat = compilation.plan.values then
          if bounded : words.length ≤ X86.UniqueABI.maxLength then
            if mainValid : (X86.UniqueTarget.program words).wellFormed = true then
              if releaseValid : X86.UniqueTarget.releaseProgram.wellFormed = true then
                .native
                  { sourceTarget := target
                    backendProduced := backend
                    reuseSelected := reused
                    words
                    valuesExact := exactValues
                    lengthBound := bounded
                    main := ⟨X86.UniqueTarget.program words, mainValid⟩
                    mainProduced := rfl
                    release := ⟨X86.UniqueTarget.releaseProgram, releaseValid⟩
                    releaseProduced := rfl }
              else .skipped "native release control validation failed"
            else .skipped "native main control validation failed"
          else .skipped "native unique reversal exceeds 64 scalar elements"
        else .skipped "native unique reversal contains a Nat outside the 64-bit Word range"
      else .skipped "native unique reversal requires selected static reuse"

theorem Output.sourceProgram {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) :
    output.sourceTarget.selection.program = IxIR2.UniqueLower.program compilation.plan true := by
  simp only [IxIR2.UniqueLower.Selection.program, output.reuseSelected]

def Output.sourceChecked {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) :
    IxIR2.Validate.Checked limits (IxIR2.UniqueLower.context compilation.plan.schema)
      (IxIR2.UniqueLower.program compilation.plan true) :=
  output.sourceProgram ▸ output.sourceTarget.selection.checked

theorem Output.sourceLength {compilation : Compilation constants entry config checkFuel eraseFuel limits}
    (output : Output compilation) : compilation.plan.values.length = output.words.length := by
  rw [← output.valuesExact, List.length_map]

end Ix.Compiler.UniqueReuse.Native
