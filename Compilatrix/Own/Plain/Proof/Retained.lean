import Compilatrix.Fir.Proof.Retained

set_option autoImplicit false
namespace Compilatrix.Own.Plain
open Compilatrix.Sem (Result ClockMono Obs Lang Sim Forall2)

theorem checked_retained {F : Fir.Program} {candidate : Src.NatMap Code}
    (checked : checkPlainMap F candidate = true)
    (exports : ∀ f, f ∈ F.exports → f < F.size) :
    ∀ i, Sim (fun w p => Proof.Den p.2 p.1 w) id
      (Fir.firRun F i) (plainRun {source := F, bodies := candidate} i) := by
  intro i
  obtain ⟨r, ns⟩ := i
  show Sim _ _ (Fir.firRun F (r, ns))
    (plainRun { source := F, bodies := candidate } (r, ns))
  unfold Fir.firRun plainRun
  simp only
  cases hr : F.exports[r]? with
  | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
  | some f =>
    simp only
    have hf := exports f (List.mem_of_getElem? hr)
    cases hfd : F.fun? f with
    | none => exact { forward := fun _ _ => ⟨0, .stuck⟩, timeout := fun _ h => nomatch h }
    | some fd =>
      simp only
      by_cases he : ns.length = fd.params.length
      · simp only [Sem.entryRun, he, ↓reduceIte]
        exact checked_call_sim checked hf ns
      · by_cases hlt : ns.length < fd.params.length
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          by_cases hn : ns = []
          · simp only [hn, ↓reduceIte]
            exact Sim.okConst (R := fun w (p : Own.RVal × Own.Heap) => Proof.Den p.2 p.1 w)
              (Proof.den_erased {})
          · simp only [hn, ↓reduceIte]
            exact Sim.laterConst (R := fun w (p : Own.RVal × Own.Heap) => Proof.Den p.2 p.1 w)
              (Proof.den_erased {}) (fun k h => h)
        · simp only [Sem.entryRun, he, hlt, ↓reduceIte]
          exact Sim.bindStuck (checked_call_sim checked hf (ns.take fd.params.length))
            fun _ _ _ => rfl



end Compilatrix.Own.Plain
