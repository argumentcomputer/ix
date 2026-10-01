import Compilatrix.Recheck.Proof.Back
import Compilatrix.Recheck.Proof.Sound

/-!
# `compile_sound`, `compile_safe` and `compile_diverges` for the object (M2.7b)

The front half (`front_refines_lir`, on the part of the region Lir uses)
and the backend half (`back_refines`) compose: for an artifact
`Recheck.run` returns and every driver that keeps its contract
(`X86.Driver.Ok`), the object run by the driver refines the checked source
viewed at the roots' readback types (`object_refines`). Roadmap §1.1 at
stage S follows for the object, with no hypothesis beyond the driver's
contract:

- `compile_sound_linked`: a value the object returns is the view of a
  value SrcEval returns (relabelled by tag at the root's type), or the
  source goes wrong (`Front.GoesWrong`: stuck, a trap, or a result its
  root's readback type does not read back);
- `compile_safe_linked`: if the source does not go wrong, the object goes
  wrong at no clock: it returns, is still running, or fails for a resource;
- `compile_diverges_linked`: a diverging source has an object that runs at
  every clock or fails for a resource.

`Front.sound_of`, `Front.safe_of` and `Front.diverges_of` derive the three
from any refinement of the viewed source.
-/

set_option autoImplicit false

namespace Compilatrix.Recheck

open Compilatrix.Sem (Obs Lang)
open Compilatrix.Lam.Erase.Proof (CheckedProgram)

section Of

variable {f : Front} {O : Type} [Lang (Nat × List Nat) O] {obj : O}

/-- Roadmap §1.1's `compile_sound` from a refinement of the viewed source. -/
theorem Front.sound_of (href : Sem.Refines f.source obj) {i : Nat × List Nat} {k : Nat} {w : Lang.Val O}
    (hw : Lang.run obj i k = .ok w) :
    (∃ k' v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k' = .ok v ∧
      f.view i.1 (Lang.obs v) = some (Lang.obs w)) ∨ f.GoesWrong i := by
  rcases href.backward hw with ⟨k', o, ho, hobs⟩ | ⟨k', hst⟩
  · obtain ⟨v, hv, hview⟩ := Sem.Viewed.run_ok ho
    exact .inl ⟨k', v, hv, hview.trans (congrArg some hobs)⟩
  · exact .inr (source_goesWrong (k := k') (by rw [hst]; trivial))

/-- Roadmap §1.1's `compile_safe` from a refinement of the viewed source. -/
theorem Front.safe_of (href : Sem.Refines f.source obj) {i : Nat × List Nat} (hs : ¬ f.GoesWrong i) (k : Nat) :
    ¬ (Lang.run obj i k).GoesWrong :=
  href.safe (fun _ hk' => hs (source_goesWrong hk')) k

/-- Divergence from a refinement of the viewed source. -/
theorem Front.diverges_of (href : Sem.Refines f.source obj) {i : Nat × List Nat}
    (hs : ∀ k, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run obj i k = .timeout) ∨ ∃ k failure, Lang.run obj i k = .resource failure :=
  href.diverges fun k => by
    show (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).bind _ = _
    rw [hs k]
    rfl

end Of

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- **The object refines the source** (M2.7b): for an artifact
`Recheck.run` returns and a driver that keeps its contract, the object run
by the driver refines the checked source viewed at the roots' readback
types. -/
theorem object_refines (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) :
    Sem.Refines a.front.source (a.linked D) :=
  (front_refines_lir (run_parts h).1 (M := model D) (X86.Driver.regionOk hD) (X86.Driver.lirRegion hD)).trans
    (back_refines h hD)

/-- `object_refines` in the traced shape (decision D-1). -/
theorem object_refines_traced (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size) :
    Sem.TRefines a.front.source (a.linked D) :=
  Sem.Refines.ofPure (object_refines h D hD)

/-- **`compile_sound` for the object** (roadmap §1.1, stage S): a value the
object returns is the view of a value SrcEval returns, or the source goes
wrong. -/
theorem compile_sound_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} {k : Nat} {w : Option Obs} (hw : Lang.run (a.linked D) i k = .ok w) :
    (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
      a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrong i :=
  Front.sound_of (object_refines h D hD) hw

/-- **`compile_safe` for the object**: if the source does not go wrong, the
object goes wrong at no clock. -/
theorem compile_safe_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hs : ¬ a.front.GoesWrong i) (k : Nat) : ¬ (Lang.run (a.linked D) i k).GoesWrong :=
  Front.safe_of (object_refines h D hD) hs k

/-- **Divergence for the object**: a diverging source has an object that
runs at every clock or fails for a resource. -/
theorem compile_diverges_linked (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    {i : Nat × List Nat} (hs : ∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) :
    (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure :=
  Front.diverges_of (object_refines h D hD) hs

end Compilatrix.Recheck
