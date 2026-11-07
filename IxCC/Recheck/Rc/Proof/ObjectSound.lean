import IxCC.Recheck.Rc.Bytes
import IxCC.Recheck.Rc.Proof.SourceSound
import IxCC.Recheck.Rc.Proof.LoadedRun
import IxCC.Recheck.Rc.Proof.Back

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Lang Obs)
open IxCC.Lam.Erase.Proof (CheckedProgram)

variable {cfg : Config} {P : Src.Program} {cert : Cert} {artifact : Artifact}

theorem object_refines (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size) :
    Sem.Refines artifact.front.source (artifact.linked driver) :=
  (front_refines_lir (run_parts accepted).1 (model := Recheck.model driver)
    (X86.Driver.regionOk valid) (X86.Driver.lirRegion valid)).trans
    (back_refines accepted valid)

theorem object_refines_traced (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size) :
    Sem.TRefines artifact.front.source (artifact.linked driver) :=
  Sem.Refines.ofPure (object_refines accepted driver valid)

/-- The driver premise is inhabited for every object actually emitted by
the accepted replay path, using the assembler's checked text bound. -/
theorem driver_exists (accepted : run cfg P cert = .ok artifact) :
    ∃ driver : X86.Driver, driver.Ok artifact.backend.encoded.text.size := by
  obtain ⟨_, _, _, _, _, emitted, _⟩ := run_parts accepted
  obtain ⟨input, emitted⟩ := Backend.emit_parts emitted
  apply X86.Driver.exists_ok
  rw [← emitted.encoded, emitted.stream.textLength]
  exact emitted.stream.textBound

/-- Complete soundness, safety and divergence clauses for the admitted heap
fragment, preserving the existing source GoesWrong and driver contracts. -/
theorem sound (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    (input : Nat × List Nat) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value,
        Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
          input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input →
      ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
        input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock resource, Lang.run (artifact.linked driver) input clock = .resource resource) :=
  have refinement := object_refines accepted driver valid
  ⟨fun _ _ success => Front.sound_of refinement success,
    fun safe clock => Front.safe_of refinement safe clock,
    fun diverging => Front.diverges_of refinement diverging⟩


theorem sound_bytes {bytes : List UInt8}
    (accepted : (run cfg P cert).map Artifact.bytes = .ok bytes) :
    ∃ artifact, run cfg P cert = .ok artifact ∧ artifact.bytes = bytes ∧
      ∀ driver : X86.Driver, (artifact.linked driver).object.data.toList = bytes := by
  cases result : run cfg P cert with
  | error error => rw [result] at accepted; cases accepted
  | ok artifact =>
    rw [result] at accepted
    simp only [Except.map, Except.ok.injEq] at accepted
    exact ⟨artifact, rfl, accepted, fun _ => accepted⟩

theorem compile_sound_linked (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    {input : Nat × List Nat} {clock : Nat} {output : Option Obs}
    (success : Lang.run (artifact.linked driver) input clock = .ok output) :
    (∃ sourceClock value,
      Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
        input sourceClock = .ok value ∧ artifact.front.view input.1 (Lang.obs value) = some output) ∨
      artifact.front.GoesWrong input :=
  (sound accepted driver valid input).1 clock output success

theorem compile_safe_linked (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    {input : Nat × List Nat} (safe : ¬ artifact.front.GoesWrong input) (clock : Nat) :
    ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong :=
  (sound accepted driver valid input).2.1 safe clock

theorem compile_diverges_linked (accepted : run cfg P cert = .ok artifact)
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size)
    {input : Nat × List Nat}
    (diverging : ∀ clock, Lang.run (⟨artifact.front.src, artifact.front.checked⟩ : CheckedProgram)
      input clock = .timeout) :
    (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
      ∃ clock resource, Lang.run (artifact.linked driver) input clock = .resource resource :=
  (sound accepted driver valid input).2.2 diverging

end IxCC.Recheck.RcReplay
