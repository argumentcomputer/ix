import Compilatrix.Recheck.Proof.Back
import Compilatrix.Recheck.Proof.Sound

/-!
# The object refines the source (M2.7b)

The front half (`front_refines_lir`, on the part of the region Lir uses)
and the backend half (`back_refines`) compose: for an artifact
`Recheck.run` returns and every driver that keeps its contract
(`X86.Driver.Ok`), the object run by the driver refines the checked source
viewed at the roots' readback types (`object_refines`), with no
hypothesis beyond the driver's contract. Roadmap §1.1 at stage S follows
(`Recheck.sound`): `Front.sound_of`, `Front.safe_of` and
`Front.diverges_of` derive its three clauses from any refinement of the
viewed source (a value the object returns is the view of one SrcEval
returns, or the source goes wrong, `Front.GoesWrong`: stuck, a trap, or a
result its root's readback type does not read back; a source that does not
go wrong has an object that goes wrong at no clock; a diverging source has
an object that runs or fails for a resource).
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


end Compilatrix.Recheck
