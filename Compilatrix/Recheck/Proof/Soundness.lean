import Compilatrix.Recheck.Proof.Object

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

Such a driver exists for every object (`driver_exists`). Its three clauses
are `compile_sound_linked`, `compile_safe_linked` and
`compile_diverges_linked`; an object the kernel gate evaluates is such an
artifact's (`sound_bytes`). (Theorems about `Recheck.compile` or
`compileInput` are not stated: their definitions reach Blake3 lemmas
proved by native evaluation, through ingress and `produce`, which are not
on the recheck path, so their axiom sets are not the standard three.)
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

/-- **`compile_sound` for the object** (roadmap §1.1, stage S), from
`Recheck.sound`: a value the object returns is the view of a value SrcEval
returns, or the source goes wrong. -/
theorem compile_sound_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} {k : Nat} {w : Option Obs} (hw : Lang.run (a.linked D) i k = .ok w) :
    (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
      a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i :=
  (sound h D hD i).1 k w hw

/-- **`compile_safe` for the object**, from `Recheck.sound`: if the source
does not go wrong, the object goes wrong at no clock. -/
theorem compile_safe_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hs : ¬ a.front.GoesWrong i) (k : Nat) : ¬ (Lang.run (a.linked D) i k).GoesWrong :=
  (sound h D hD i).2.1 hs k

/-- **Divergence for the object**, from `Recheck.sound`: a diverging source
has an object that runs at every clock or fails for a resource. -/
theorem compile_diverges_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hs : ∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure :=
  (sound h D hD i).2.2 hs

end Compilatrix.Recheck
