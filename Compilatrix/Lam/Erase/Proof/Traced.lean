import Compilatrix.Lam.Erase.Proof.Correct
import Compilatrix.Sem.TracedTransform

/-! # Erasure's correctness in the traced vocabulary

`erase_correct` and `erase_refines` restated in the traced shape of
decision D-1 through the lifts, with no new proof: SrcEval and Lam are pure
in Phase 1, so their runs are traced runs under the environment `Unit` that
perform no event (`E := Empty`). `erase_correct_traced` is a `TSim` per
root (`TSim.ofPure`); `erase_refines_traced` is `TRefines` of the lifted
languages (`Refines.ofPure`). When the levels gain IO, these statements
keep their shape and their proofs change. -/

set_option autoImplicit false

namespace Compilatrix.Lam.Erase.Proof

open Compilatrix.Sem (TSim TRefines Traced)

/-- `erase_correct` as a traced simulation: every root of a successfully
erased program simulates, under every environment, from related
arguments. -/
theorem erase_correct_traced {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) :
    ∃ G : Key.GKey → GlobalId → Prop, Forall2 (fun c g => ∀ (xs : List Src.Value) (xs' : List Val),
        Forall2 (VR (Input.ofProgram p ch) G) xs xs' →
          TSim (Env := Unit) (E := Empty) (VR (Input.ofProgram p ch) G) id
            (fun _ k => Traced.lift (Src.run p k c xs)) (fun _ k => Traced.lift (Lam.run L k g xs')))
      (p.roots.map (·.2)) L.roots := by
  obtain ⟨G, hroots⟩ := erase_correct h
  exact ⟨G, Forall2.imp (fun _ _ hr xs xs' hx => TSim.ofPure (hr xs xs' hx)) hroots⟩

/-- `erase_refines` as traced refinement: on every root, `Nat` arguments
and environment, the erased program's traced behaviour refines SrcEval's
up to equal first-order observations. -/
theorem erase_refines_traced {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) :
    TRefines (⟨p, ch⟩ : CheckedProgram) L :=
  Sem.Refines.ofPure (erase_refines h)

end Compilatrix.Lam.Erase.Proof
