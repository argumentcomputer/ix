import Compilatrix.Cfg.Rc.Proof.Simulation
import Compilatrix.Cfg.Rc.Proof.Fuel
import Compilatrix.Sem.TracedSim

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc

theorem step_ret_nil (P : Program) (v : Own.RVal) (H : Own.Heap) :
    step P (.ret v [] H) = .done (v, H) := rfl

/-- A checked candidate executes the actual Plain program, including RC actions,
with exactly the same returned value and abstract heap. The depth-to-total-clock
simulation uses the original structural Cfg fuel bound. Native physical-memory
representation and release-loop costs are separate obligations. -/
theorem checked_correct {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (f : Nat) (vs : List Own.RVal)
    (H : Own.Heap) :
    Sem.Sim Eq id (fun k => Own.Plain.evalCall {source := F, bodies} k f vs H)
      (fun k => run P k f vs H) := by
  refine Sem.Sim.ofStar (runs_run (checked_ordered (checkScopedProgram_parts checked).1) f vs H)
    (fun k hk hs => ?_) (fun k hk => ?_)
  · have hr := checked_call_reach checked k f vs [] H
    generalize Own.Plain.evalCall {source := F, bodies} k f vs H = r at hr hk hs ⊢
    match r, hr with
    | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n, _, _, hn, step_ret_nil P v H' ▸ .done, .ok rfl⟩
    | .trap, ⟨n, s', hn, ht⟩ => exact ⟨n, s', _, hn, ht ▸ .trap, .trap⟩
    | .timeout, _ => exact absurd rfl hk
    | .stuck, _ => exact absurd rfl hs
    | .resource _, h => exact h.elim
  · have hr := checked_call_reach checked k f vs [] H
    simp only [id] at hk
    rw [hk] at hr
    obtain ⟨n, s', hn, hlt⟩ := hr
    exact ⟨n, s', hn, .inl hlt⟩

theorem checked_correct_traced {Env E : Type} {F : Fir.Program}
    {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true) (f : Nat) (vs : List Own.RVal)
    (H : Own.Heap) :
    Sem.TSim (Env := Env) (E := E) Eq id
      (fun _ k => Sem.Traced.lift (Own.Plain.evalCall {source := F, bodies} k f vs H))
      (fun _ k => Sem.Traced.lift (run P k f vs H)) :=
  Sem.TSim.ofPure (checked_correct checked f vs H)



end Compilatrix.Cfg.Rc
