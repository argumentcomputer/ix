import Compilatrix.Ixby.Wire
namespace Compilatrix.Ixby
open Ix.Ixby
open Ix.Ixby.Codec
/-- Successful canonical executions of the same image/input agree across fuels. -/
theorem byte_execute_deterministic {profile : Profile} {programBytes inputBytes : Bytes}
    {fuel1 fuel2 : Nat} {one two : Execution profile programBytes inputBytes}
    (first : Codec.execute profile programBytes inputBytes fuel1 = .ok one)
    (second : Codec.execute profile programBytes inputBytes fuel2 = .ok two) :
    one.outputBytes = two.outputBytes := by
  unfold Codec.execute at first second
  simp only [Bind.bind, Except.bind] at first second
  cases hp : decodeProgram profile programBytes with
  | error err => simp [hp] at first
  | ok program =>
    simp only [hp] at first second
    cases hi : decodeInput profile program.value inputBytes with
    | error err => simp [hi] at first
    | ok input =>
      simp only [hi] at first second
      split at first
      next err h1 => contradiction
      next v1 h1 =>
        split at second
        next err h2 => contradiction
        next v2 h2 =>
          have same : v1 = v2 := evaluates_deterministic
            ⟨fuel1, Profile.execute_refines h1⟩ ⟨fuel2, Profile.execute_refines h2⟩
          split at first
          next err he1 => contradiction
          next bytes1 he1 =>
            split at second
            next err he2 => contradiction
            next bytes2 he2 =>
              have e1 := Except.ok.inj first
              have e2 := Except.ok.inj second
              have encodedSame : bytes1 = bytes2 := by
                rw [← same] at he2
                exact Except.ok.inj (he1.symm.trans he2)
              exact (congrArg (·.outputBytes) e1).symm.trans
                (encodedSame.trans (congrArg (·.outputBytes) e2))

/-- Byte execution also has a unique complete canonical output. -/
theorem byte_evaluates_deterministic {profile : Profile} {programBytes inputBytes out1 out2 : Bytes}
    (first : Codec.Evaluates profile programBytes inputBytes out1)
    (second : Codec.Evaluates profile programBytes inputBytes out2) : out1 = out2 := by
  obtain ⟨fuel1, first⟩ := first
  obtain ⟨fuel2, second⟩ := second
  cases h1 : Codec.execute profile programBytes inputBytes fuel1 with
  | error error => simp [h1, Except.map] at first
  | ok one =>
    cases h2 : Codec.execute profile programBytes inputBytes fuel2 with
    | error error => simp [h2, Except.map] at second
    | ok two =>
      have e1 : one.outputBytes = out1 := by simpa [h1, Except.map] using first
      have e2 : two.outputBytes = out2 := by simpa [h2, Except.map] using second
      exact e1.symm.trans ((byte_execute_deterministic h1 h2).trans e2)

/-- Any successful canonical byte run has the output tied to this checked
source execution. All source/image/input/profile equalities remain explicit. -/
theorem ByteCertificate.execution_refines {source config compiled profile exported input depth}
    (certificate : @ByteCertificate source config compiled profile exported input depth)
    {outputBytes : Bytes}
    (evaluated : Codec.Evaluates profile exported.programBytes certificate.inputBytes outputBytes) :
    outputBytes = certificate.execution.outputBytes ∧
      source.EvaluatesData input certificate.reference.result := by
  have recorded : Codec.Evaluates profile exported.programBytes certificate.inputBytes
      certificate.execution.outputBytes :=
    ⟨certificate.reference.targetFuel, by rw [certificate.executed]; rfl⟩
  exact ⟨byte_evaluates_deterministic evaluated recorded, certificate.reference.sourceEvaluated⟩

end Compilatrix.Ixby
