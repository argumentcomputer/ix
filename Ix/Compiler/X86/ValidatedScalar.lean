import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.Ixon.Sharing
import Ix.Compiler.X86.Select
import Ix.Compiler.X86.ELF

/-! A reproducible synthetic Ixon input for the source-to-native scalar slice.
The erased-argument application returns the configured Nat in the Ixon
evaluator and emits the exact `ScalarApply.program` graph. All addresses are
computed from bytes; the fixture supplies no hand-written intermediate IR. -/

namespace Ix.Compiler.X86.ValidatedScalar

open Ix.Compiler Ix.Compiler.Ixon

/-- The fixture's literal resolver is pinned to a versioned Nat preimage.
This is a synthetic resolver input, not a catalog blob-format claim. -/
def literalAddress (number : Nat) : Address :=
  Address.blake3 ("compilatrix/native-scalar-literal/1\x00".toUTF8 ++ IxIR.Encoding.nat number)

def constant (number : Nat) (ghostApplication : Bool := true) : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0, typ := .sort 0
        value := if ghostApplication then .app (.lam .erased (.sort 0) (.nat 0)) (.sort 0)
          else .nat 0 }
    sharing := #[], refs := #[literalAddress number], univs := #[.zero] }

/-- Conservative, explicit source budgets for this one-constant fixture. -/
def config (number : Nat) : Pipeline.Config :=
  { blobs := fun address => if address == literalAddress number then some (.natB number) else none
    natBlock := none
    limits :=
      { maxConstants := 1, maxExpressionUnits := 32, maxExpandedExpressionUnits := 32
        maxLayer1NodeVisits := 128, maxErasedDeclarations := 8, maxErasureAppendCells := 64
        maxCertificateCandidates := 8, maxCertificateValidationAttempts := 64
        maxCertificateSourceNodeWork := 1024, maxUsageFuel := 100, maxErasureFuel := 100
        maxValidationFuel := 100, maxLoweringFuel := 100 } }

/-- Version 1 pins shared-result baseline lowering and the two exact scalar
selection families. No optional IxIR₁ or IxIR₂ optimizer is invoked. -/
def loweringVersion : UInt32 := 1
def passPolicyVersion : UInt32 := 1

inductive Error where
  | sourceAddress
  | compilation (error : IxIR2.Pipeline.Error)
  | selection (error : Select.Error)
  deriving Repr

structure Compiled (number : Nat) where
  sourceRoot : Address
  addressed : (constant number).address? = some sourceRoot
  attached : IxIR2.Pipeline.Attached [(sourceRoot, constant number)] sourceRoot
    (config number) .shared 100 100
  compiled : IxIR2.Pipeline.compileValidated [(sourceRoot, constant number)] sourceRoot
    (config number) .shared 100 100 100 100 100 = .ok attached
  selected : Select.Output attached.target.artifact.program
  selection : Select.select attached.target.artifact.program = .ok selected

/-- One executable call crosses every real compiler and selector gate,
retaining the exact successful equations used by the semantic endpoint. -/
def compile (number : Nat) : Except Error (Compiled number) :=
  match addressed : (constant number).address? with
  | none => .error .sourceAddress
  | some sourceRoot =>
      match compiled : IxIR2.Pipeline.compileValidated [(sourceRoot, constant number)] sourceRoot
          (config number) .shared 100 100 100 100 100 with
      | .error error => .error (.compilation error)
      | .ok attached =>
          match selection : Select.select attached.target.artifact.program with
          | .error error => .error (.selection error)
          | .ok selected => .ok { sourceRoot, addressed, attached, compiled, selected, selection }

def Compiled.ir1Root {number : Nat} (compiled : Compiled number) : Address :=
  IxIR1.Optimizer.graphRoot compiled.attached.source.artifact.targetArtifacts
    compiled.attached.source.artifact.main

def Compiled.provenance {number : Nat} (compiled : Compiled number) : ELF.Provenance :=
  .ixir1Policy compiled.ir1Root loweringVersion passPolicyVersion

private def scalar (value : IxIR1.RVal) : Except String Word :=
  match value with
  | .lit (.nat number) =>
      let word := UInt64.ofNat number
      if word.toNat == number then .ok word else .error "scalar result exceeds 64 bits"
  | _ => .error "intermediate execution returned a non-Nat value"

/-- Execute the source and every intermediate observation used by the native
gate. These operational checks accompany the generic theorem in PipelineSim. -/
def Compiled.observe {number : Nat} (compiled : Compiled number) : Except String Word := do
  let constants := [(compiled.sourceRoot, constant number)]
  let sourceNumber ← match Ixon.Eval.eval (Pipeline.validatedEvalCtx constants (config number))
      100 (Pipeline.validatedMainFrame compiled.sourceRoot) [] Pipeline.validatedMainSource with
    | .ok (.litV (.natL result)) => pure result
    | _ => throw "Ixon scalar execution failed"
  let artifact := compiled.attached.source.artifact
  let rawValue ← match IxIR0.eval { env := IxIR0.Env.ofList artifact.rawErasedDecls }
      100 [] (.ref compiled.sourceRoot) with
    | .ok (.lit (.nat result)) => pure result
    | _ => throw "raw IxIR₀ scalar execution failed"
  let addressedValue ← match IxIR0.eval { env := IxIR0.Env.ofList artifact.erasedDecls }
      100 [] compiled.attached.source.erasure.result.main with
    | .ok (.lit (.nat result)) => pure result
    | _ => throw "addressed IxIR₀ scalar execution failed"
  let (ir1Store, ir1Value) ← match IxIR1.runOwnedMain
      { decls := artifact.targetDeclEnv } .shared artifact.main 100 with
    | .ok output => pure output
    | .error _ => throw "addressed IxIR₁ scalar execution failed"
  let ir1Word ← scalar ir1Value
  let program := compiled.attached.target.artifact.program
  let context := IxIR2.Eval.Context.ofProgram program
    compiled.attached.target.artifact.validationContext.schemas
  for interpretation in [IxIR2.Eval.Interpretation.logical, .physical] do
    let result ← match IxIR2.Eval.runMain context interpretation program 6 2 with
      | .ok result => pure result
      | .error error => throw s!"IxIR₂ scalar execution failed: {repr error}"
    let word ← scalar result.value
    if word != ir1Word || result.controlRemaining != 0 || result.heapRemaining != 0 ||
        result.store.heap.allocs != 1 || result.store.heap.frees != 1 ||
        result.store.heap.rcops != 1 || result.store.heap.reuses != 0 ||
        result.store.live != 0 || result.store.peakLiveNodes != 1 ||
        result.store.resetAttempts != 0 || result.store.hotResets != 0 ||
        result.store.coldResets != 0 || result.store.reusedPayloadUnits != 0 then
      throw "IxIR₂ scalar observation or counters drifted"
  if sourceNumber != number || rawValue != number || addressedValue != number ||
      ir1Word.toNat != number || compiled.selected.word != ir1Word ||
      ir1Store.allocs != 1 || ir1Store.frees != 1 || ir1Store.rcops != 1 ||
      ir1Store.reuses != 0 || ir1Store.live != 0 then
    throw "source and intermediate scalar observations disagree"
  let localResult := X86.runFrom X86.Runtime.rejecting compiled.selected.target 2 (X86.Core.empty 0x1008)
  if localResult.status != .halted ir1Word || localResult.core.readReg .rsp != 0x1008 then
    throw "selected local x86 execution disagrees with the source"
  return ir1Word

/-- A bare unique literal cannot satisfy the existing shared constant result
policy. Keep the exact source rejection visible before selection. -/
def rejectsBareLiteral (number : Nat) : Bool :=
  let source := constant number false
  match source.address? with
  | none => false
  | some root =>
      match IxIR2.Pipeline.compileValidated [(root, source)] root
          (config number) .shared 100 100 100 100 100 with
      | .error (.pipeline (.usage address .freezeNeeded)) => address == root
      | _ => false

def rejectsOverflow : Bool :=
  match compile UInt64.size with
  | .error (.selection .unsupportedScalarShape) => true
  | _ => false

end Ix.Compiler.X86.ValidatedScalar
