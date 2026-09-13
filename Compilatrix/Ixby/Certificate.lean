import Compilatrix.Ixby.Lower

/-! Checked execution certificates for the first Ixby backend. Compilation
itself is independent of evaluation. This checker certifies one supplied input,
then target determinism covers every successful run on that same input. It is
not an unbounded structural compiler-correctness theorem. -/

namespace Compilatrix.Ixby

def Source.EvaluatesData (source : Source) (input : Array Data) (result : Data) : Prop :=
  ∃ sourceFuel value observationFuel,
    IxIR0.eval source.ctx sourceFuel (input.toList.reverse.map Data.toValue)
      source.main = .ok value ∧ observe observationFuel value = some result

structure RunCertificate {source config} (compiled : Compiled source config)
    (input : Array Data) (decodeFuel : Nat) where
  encodedInput : Array Ix.Ixby.Value
  inputEncoded : input.mapM (encodeData source config config.depth) = .ok encodedInput
  result : Data
  sourceEvaluated : source.EvaluatesData input result
  output : Ix.Ixby.Value
  targetFuel : Nat
  targetEvaluated : Ix.Ixby.execute config.limits compiled.program encodedInput targetFuel = .ok output
  decoded : decodeData source decodeFuel output = some result

/-- Evaluate the two exact semantic objects and compare complete data trees.
Failure, resource exhaustion, and higher-order outputs produce no certificate. -/
def Compiled.certify {source config} (compiled : Compiled source config)
    (input : Array Data := #[]) (sourceFuel : Nat := 100000)
    (targetFuel : Nat := 1000000) (decodeFuel : Nat := 10000) :
    Except String (RunCertificate compiled input decodeFuel) := do
  if input.size != source.parameters then throw "Ixby input arity mismatch"
  admitData config.limits config.limits.inputNodes input.toList
  match inputEncoded : input.mapM (encodeData source config config.depth) with
  | .error error => throw error
  | .ok encodedInput =>
    match targetEvaluated : Ix.Ixby.execute config.limits compiled.program encodedInput targetFuel with
    | .error error => throw s!"Ixby certificate target execution: {reprStr error}"
    | .ok output =>
      let _ ← (Ix.Ixby.validateInputValues config.limits compiled.program
        config.limits.inputNodes [output]).mapError (fun error => s!"Ixby output limit: {reprStr error}")
      match decoded : decodeData source decodeFuel output with
      | none => throw "Ixby output is outside the bounded data ABI"
      | some result =>
        match evaluated : IxIR0.eval source.ctx sourceFuel
            (input.toList.reverse.map Data.toValue) source.main with
        | .error error => throw s!"Ixby certificate source execution: {reprStr error}"
        | .ok value =>
          match observed : observe decodeFuel value with
          | none => throw "IxIR0 output is outside the bounded data ABI"
          | some expected =>
            if equal : Data.equal expected result then
              have same := Data.eq_of_equal expected result equal
              return {
                encodedInput, inputEncoded, result
                sourceEvaluated := ⟨sourceFuel, value, decodeFuel, evaluated, same ▸ observed⟩
                output, targetFuel, targetEvaluated, decoded }
            else throw "Ixby compiler/source result disagreement"

def RunCertificate.abi {source config compiled input decodeFuel}
    (certificate : @RunCertificate source config compiled input decodeFuel) :
    Ix.Ixby.ABI Unit Data :=
  { encodeInput := fun _ => certificate.encodedInput,
    decodeOutput := decodeData source decodeFuel }

/-- The upstream contract, with the input fixed by this checked certificate.
The source result is inferred from ANY successful target run, at any fuel. -/
theorem RunCertificate.refinement {source config compiled input decodeFuel}
    (certificate : @RunCertificate source config compiled input decodeFuel) :
    Ix.Ixby.ExecutionRefinement
      (fun source (_ : Unit) result => source.EvaluatesData input result)
      source config.limits compiled.program certificate.abi := by
  intro _ output evaluated
  have same : output = certificate.output :=
    Ix.Ixby.evaluates_deterministic evaluated
      ⟨certificate.targetFuel, certificate.targetEvaluated⟩
  exact ⟨certificate.result, same.symm ▸ certificate.decoded, certificate.sourceEvaluated⟩

end Compilatrix.Ixby
