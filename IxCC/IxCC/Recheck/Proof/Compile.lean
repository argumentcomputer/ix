import IxCC.Recheck.Produce
import IxCC.Recheck.Proof.Soundness

/-! The actual compiler returns only artifacts accepted by certificate replay.

These results connect `compileInput` and byte-input `compile` to the existing
SrcEval-relative object theorem. The source is the checked program recorded in
the artifact. Authentic input/model adequacy and source safety remain separate
obligations; the driver contract is retained. Because their statements mention
the actual producer and ingress, these theorems expose the existing native
BLAKE3 dependency. They do not change the ordinary recheck theorem's axiom set.
-/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)

theorem compileInput_parts {cfg : Config} {inp : Input} {cert : Cert} {artifact : Artifact}
    (accepted : compileInput cfg inp = .ok (cert, artifact)) :
    produce (cfg.forInput inp) inp = .ok cert ∧ run (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold compileInput at accepted
  simp only [bind, Except.bind] at accepted
  cases produced : produce (cfg.forInput inp) inp with
  | error error => simp [produced] at accepted
  | ok candidate =>
    simp only [produced] at accepted
    cases replayed : run (cfg.forInput inp) inp.program candidate with
    | error error => simp [replayed] at accepted
    | ok actual =>
      simp only [replayed, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨rfl, replayed⟩

theorem compile_parts {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {typecheck : Bool} {cert : Cert} {artifact : Artifact}
    (accepted : compile cfg bytes equations roots typecheck = .ok (cert, artifact)) :
    ∃ inp, ingress bytes equations roots typecheck = .ok inp ∧
      produce (cfg.forInput inp) inp = .ok cert ∧ run (cfg.forInput inp) inp.program cert = .ok artifact := by
  unfold compile at accepted
  simp only [bind, Except.bind] at accepted
  cases ingested : ingress bytes equations roots typecheck with
  | error error => simp [ingested] at accepted
  | ok inp =>
    simp only [ingested] at accepted
    exact ⟨inp, rfl, compileInput_parts accepted⟩

theorem compileInput_object_refines {cfg : Config} {inp : Input} {cert : Cert} {artifact : Artifact}
    (accepted : compileInput cfg inp = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size) :
    Sem.Refines artifact.front.source (artifact.linked driver) :=
  object_refines (compileInput_parts accepted).2 driver valid

theorem compile_object_refines {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {typecheck : Bool} {cert : Cert} {artifact : Artifact}
    (accepted : compile cfg bytes equations roots typecheck = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size) :
    Sem.Refines artifact.front.source (artifact.linked driver) := by
  obtain ⟨inp, _, _, replayed⟩ := compile_parts accepted
  exact object_refines replayed driver valid

theorem compile_driver_exists {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {typecheck : Bool} {cert : Cert} {artifact : Artifact}
    (accepted : compile cfg bytes equations roots typecheck = .ok (cert, artifact)) :
    ∃ driver : X86.Driver, driver.Ok artifact.backend.encoded.text.size := by
  obtain ⟨inp, _, _, replayed⟩ := compile_parts accepted
  exact driver_exists replayed

/-- The three existing object guarantees now follow from success of the actual
byte-input compiler, including its default or explicit typechecking choice.
The typechecking switch does not discharge the stronger model/safety boundary. -/
theorem compiled_sound {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {typecheck : Bool} {cert : Cert} {artifact : Artifact}
    (accepted : compile cfg bytes equations roots typecheck = .ok (cert, artifact))
    (driver : X86.Driver) (valid : driver.Ok artifact.backend.encoded.text.size) (input : Nat × List Nat) :
    (∀ clock output, Lang.run (artifact.linked driver) input clock = .ok output →
      (∃ sourceClock value, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input sourceClock = .ok value ∧
        artifact.front.view input.1 (Lang.obs value) = some output) ∨ artifact.front.GoesWrong input) ∧
    (¬ artifact.front.GoesWrong input → ∀ clock, ¬ (Lang.run (artifact.linked driver) input clock).GoesWrong) ∧
    ((∀ clock, Lang.run (⟨artifact.src, artifact.checked⟩ : CheckedProgram) input clock = .timeout) →
      (∀ clock, Lang.run (artifact.linked driver) input clock = .timeout) ∨
        ∃ clock failure, Lang.run (artifact.linked driver) input clock = .resource failure) := by
  obtain ⟨inp, _, _, replayed⟩ := compile_parts accepted
  exact sound replayed driver valid input

/-- Emitted bytes are those of the actual rechecked object, including the
certificate and successful ingress/producer/replay that supplied that object. -/
theorem compile_bytes {cfg : Config} {bytes : ByteArray} {equations : Lean.Json}
    {roots : List String} {typecheck : Bool} {output : List UInt8}
    (accepted : (compile cfg bytes equations roots typecheck).map (fun result => result.2.bytes) = .ok output) :
    ∃ inp cert artifact, ingress bytes equations roots typecheck = .ok inp ∧
      produce (cfg.forInput inp) inp = .ok cert ∧ run (cfg.forInput inp) inp.program cert = .ok artifact ∧
      artifact.bytes = output ∧ ∀ driver : X86.Driver, (artifact.linked driver).object.data.toList = output := by
  cases compiled : compile cfg bytes equations roots typecheck with
  | error error => simp [compiled, Except.map] at accepted
  | ok result =>
    obtain ⟨cert, artifact⟩ := result
    simp only [compiled, Except.map, Except.ok.injEq] at accepted
    obtain ⟨inp, ingested, produced, replayed⟩ := compile_parts compiled
    exact ⟨inp, cert, artifact, ingested, produced, replayed, accepted, fun _ => accepted⟩

end IxCC.Recheck
