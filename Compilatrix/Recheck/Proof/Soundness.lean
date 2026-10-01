import Compilatrix.Recheck.Proof.Object
import Compilatrix.Recheck.Produce

/-!
# `Recheck.sound` (M2.8)

Roadmap §1.1 at stage S for the recheck path: for every object
`Recheck.run` makes (`a.object`, the bytes the kernel gate evaluates,
`Artifact.bytes`) and every driver that keeps its contract
(`X86.Driver.Ok`), on every input,

- a value the object returns is the view of a value SrcEval returns
  (relabelled by tag at the root's readback type), or the source goes
  wrong (`Front.GoesWrong`);
- if the source does not go wrong, the object goes wrong at no clock;
- a diverging source has an object that runs at every clock or fails for a
  resource (`sound`).

Such a driver exists for every object (`driver_exists`). The compiler
(`Recheck.compile`: ingress, `produce`, `run`) inherits the statement for
its artifact (`compiled_sound`, `compiled_safe`), and so does an object
the kernel gate evaluates (`sound_bytes`).
-/

set_option autoImplicit false

namespace Compilatrix.Recheck

open Compilatrix.Sem (Obs Lang)
open Compilatrix.Lam.Erase.Proof (CheckedProgram)

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- The driver's contract can be kept for every object `Recheck.run` makes. -/
theorem driver_exists (h : run cfg P c = .ok a) : ∃ D : X86.Driver, D.Ok a.backend.encoded.text.size := by
  obtain ⟨-, -, -, -, he, -⟩ := run_parts h
  obtain ⟨input, em⟩ := Backend.emit_parts he
  apply X86.Driver.exists_ok
  rw [← em.encoded, em.stream.textLength]
  exact em.stream.textBound

/-- **`Recheck.sound`** (M2.8): roadmap §1.1 at stage S for the object
`Recheck.run` makes, run by any driver that keeps its contract, on every
input: the object's values are the source's viewed at the roots' readback
types unless the source goes wrong; a source that does not go wrong has an
object that never goes wrong; a diverging source has an object that runs
or fails for a resource. -/
theorem sound (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i) ∧
    (¬ a.front.GoesWrong i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  have href := object_refines h D hD
  ⟨fun _ _ hw => Front.sound_of href hw, fun hs k => Front.safe_of href hs k, fun hs => Front.diverges_of href hs⟩

/-- An object the kernel gate evaluates (`(run cfg P c).map Artifact.bytes =
.ok bytes`) is an artifact's, whose linked object has those bytes. -/
theorem sound_bytes {bytes : List UInt8} (h : (run cfg P c).map Artifact.bytes = .ok bytes) :
    ∃ a, run cfg P c = .ok a ∧ a.bytes = bytes ∧ ∀ D : X86.Driver, (a.linked D).object.data.toList = bytes := by
  cases hr : run cfg P c with
  | error e => rw [hr] at h; cases h
  | ok a =>
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨a, rfl, h, fun _ => h⟩

/-- The compiler's artifact is `Recheck.run`'s, on the certificate `produce` made. -/
theorem compile_run {cfg : Config} {bytes : ByteArray} {equations : Lean.Json} {roots : List String} {tc : Bool}
    {cert : Cert} {a : Artifact} (h : compile cfg bytes equations roots tc = .ok (cert, a)) :
    ∃ cfg' P, run cfg' P cert = .ok a := by
  unfold compile at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i inp _
    unfold compileInput at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i c' _
      split at h
      · cases h
      · rename_i a' ha
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, ha⟩

/-- **`compile_sound` for the compiler** (roadmap §1.1, stage S): a value
the compiled object returns, run by a driver that keeps its contract, is
the view of a value SrcEval returns, or the source goes wrong. -/
theorem compiled_sound {cfg : Config} {bytes : ByteArray} {equations : Lean.Json} {roots : List String} {tc : Bool}
    {cert : Cert} {a : Artifact} (h : compile cfg bytes equations roots tc = .ok (cert, a)) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) {i : Nat × List Nat} {k : Nat} {w : Option Obs}
    (hw : Lang.run (a.linked D) i k = .ok w) :
    (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
      a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i := by
  obtain ⟨cfg', P, hr⟩ := compile_run h
  exact (sound hr D hD i).1 k w hw

/-- **`compile_safe` for the compiler**: a source that does not go wrong
has a compiled object that goes wrong at no clock. -/
theorem compiled_safe {cfg : Config} {bytes : ByteArray} {equations : Lean.Json} {roots : List String} {tc : Bool}
    {cert : Cert} {a : Artifact} (h : compile cfg bytes equations roots tc = .ok (cert, a)) (D : X86.Driver)
    (hD : D.Ok a.backend.encoded.text.size) {i : Nat × List Nat} (hs : ¬ a.front.GoesWrong i) (k : Nat) :
    ¬ (Lang.run (a.linked D) i k).GoesWrong := by
  obtain ⟨cfg', P, hr⟩ := compile_run h
  exact (sound hr D hD i).2.1 hs k

end Compilatrix.Recheck
