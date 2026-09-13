import Compilatrix.Ixby.SymbolicCertificate
import Compilatrix.Ixby.Wire

namespace Compilatrix.Ixby

namespace WireEquality

mutual
  def value : Ix.Ixby.Value → Ix.Ixby.Value → Bool
    | .scalar a, .scalar b => decide (a = b)
    | .ctor a xs, .ctor b ys => decide (a = b) && array xs ys
    | .pap a xs, .pap b ys => a == b && array xs ys
    | .erased, .erased => true
    | _, _ => false
  def array : Array Ix.Ixby.Value → Array Ix.Ixby.Value → Bool
    | ⟨xs⟩, ⟨ys⟩ => list xs ys
  def list : List Ix.Ixby.Value → List Ix.Ixby.Value → Bool
    | [], [] => true
    | x :: xs, y :: ys => value x y && list xs ys
    | _, _ => false
end

theorem value_eq (a : Ix.Ixby.Value) : ∀ b, value a b = true → a = b := by
  induction a using Ix.Ixby.Value.rec
      (motive_2 := fun xs => ∀ ys, array xs ys = true → xs = ys)
      (motive_3 := fun xs => ∀ ys, list xs ys = true → xs = ys) with
  | scalar scalar => intro b h; cases b <;> simp_all [value]
  | ctor id fields ih =>
      intro b h
      cases b <;> simp_all [value]
      exact ih _ h.2
  | pap function captured ih =>
      intro b h
      cases b <;> simp_all [value]
      exact ih _ h.2
  | erased => intro b h; cases b <;> simp_all [value]
  | mk xs ih =>
      rename_i ys h
      cases ys with
      | mk ys => exact congrArg Array.mk (ih ys h)
  | nil => rename_i ys h; cases ys <;> simp_all [list]
  | cons x xs ihHead ihTail =>
      rename_i ys h
      cases ys <;> simp_all [list]
      exact ⟨ihHead _ h.1, ihTail _ h.2⟩

theorem list_eq {xs ys : List Ix.Ixby.Value} (accepted : list xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [list]
  | cons x xs ih =>
      cases ys with
      | nil => simp [list] at accepted
      | cons y ys =>
          simp only [list, Bool.and_eq_true] at accepted
          cases value_eq _ _ accepted.1
          cases ih accepted.2
          rfl

theorem array_eq {xs ys : Array Ix.Ixby.Value} (accepted : array xs ys = true) : xs = ys := by
  cases xs with
  | mk xs =>
      cases ys with
      | mk ys => exact congrArg Array.mk (list_eq accepted)

end WireEquality

/-- Canonical input bytes admitted for the exact exported program. No guest
execution is performed when reconstructing this input binding. -/
structure ExportedArguments {source config compiled profile inputDepth}
    (exported : @Exported source config compiled profile)
    (args : Arguments source config inputDepth) where
  bytes : Ix.Ixby.Codec.Bytes
  encoded : Ix.Ixby.Codec.encodeInput profile exported.program.value args.raw = .ok bytes
  input : Ix.Ixby.Codec.Decoded (Ix.Ixby.Codec.encodeInput profile exported.program.value) bytes
  decoded : Ix.Ixby.Codec.decodeInput profile exported.program.value bytes = .ok input
  exactInput : input.value = args.raw

def Arguments.read {source config compiled profile inputDepth}
    (args : Arguments source config inputDepth) (exported : @Exported source config compiled profile)
    (bytes : Ix.Ixby.Codec.Bytes) :
    Except String (ExportedArguments exported args) := do
  match decoded : Ix.Ixby.Codec.decodeInput profile exported.program.value bytes with
  | .error error => throw s!"Ixby reusable input decoding: {reprStr error}"
  | .ok input =>
      if equal : WireEquality.array input.value args.raw then
        have same := WireEquality.array_eq equal
        return { bytes, encoded := same ▸ input.canonical, input, decoded, exactInput := same }
      else throw "Ixby canonical input differs from the admitted argument array"

def Arguments.export {source config compiled profile inputDepth}
    (args : Arguments source config inputDepth) (exported : @Exported source config compiled profile) :
    Except String (ExportedArguments exported args) := do
  match Ix.Ixby.Codec.encodeInput profile exported.program.value args.raw with
  | .error error => throw s!"Ixby reusable input encoding: {reprStr error}"
  | .ok bytes => args.read exported bytes

theorem ExportedArguments.reference_evaluates {source config compiled profile inputDepth}
    {exported : @Exported source config compiled profile} {args : Arguments source config inputDepth}
    (input : ExportedArguments exported args) {outputBytes}
    (executed : Ix.Ixby.Codec.Evaluates profile exported.programBytes input.bytes outputBytes) :
    ∃ output, Ix.Ixby.Evaluates config.limits compiled.program args.raw output ∧
      Ix.Ixby.Codec.encodeOutput profile compiled.program output = .ok outputBytes := by
  obtain ⟨fuel, executed⟩ := executed
  cases execution : Ix.Ixby.Codec.execute profile exported.programBytes input.bytes fuel with
  | error error => simp [execution, Except.map] at executed
  | ok result =>
      have outputEq : result.outputBytes = outputBytes := by
        simpa [execution, Except.map] using executed
      simp only [Ix.Ixby.Codec.execute, exported.readProgram, input.decoded,
        Bind.bind, Except.bind] at execution
      split at execution
      · contradiction
      · rename_i output evaluated
        split at execution
        · contradiction
        · rename_i bytes encoded
          have same := Except.ok.inj execution
          have bytesEq : bytes = outputBytes := (congrArg (·.outputBytes) same).trans outputEq
          refine ⟨output, ⟨fuel, ?_⟩, ?_⟩
          · simpa only [exported.exactProgram, exported.exactLimits, input.exactInput] using
              Ix.Ixby.Profile.execute_refines evaluated
          · simpa only [exported.exactProgram, bytesEq] using encoded

/-- Canonical execution inherits the reusable program theorem for every
admitted argument array. Output encoding binds the complete returned bytes;
the source interpreter is never invoked to certify a new runtime input. -/
theorem SymbolicCertificate.byte_refinement {source config compiled profile inputDepth}
    (certificate : @SymbolicCertificate source config compiled)
    {exported : @Exported source config compiled profile} {args : Arguments source config inputDepth}
    (input : ExportedArguments exported args) {outputBytes}
    (executed : Ix.Ixby.Codec.Evaluates profile exported.programBytes input.bytes outputBytes) :
    ∃ result output, source.EvaluatesData args.data result ∧
      decodeData source (inputDepth + certificate.dataDepth) output = some result ∧
      Ix.Ixby.Codec.encodeOutput profile compiled.program output = .ok outputBytes := by
  obtain ⟨output, evaluated, encoded⟩ := input.reference_evaluates executed
  obtain ⟨result, decoded, sourceRun⟩ := certificate.refinement inputDepth args output evaluated
  exact ⟨result, output, sourceRun, decoded, encoded⟩

end Compilatrix.Ixby
