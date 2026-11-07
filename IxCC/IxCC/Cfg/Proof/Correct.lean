import IxCC.Cfg.Proof.Sim
import IxCC.Sem.TracedSim

/-! # `Cfg.lower_correct`

The Own → Cfg lowering is correct (design note 03 §7, M2.4): for an Own
program whose functions are below its size, whose signatures are as long as
their parameters and whose names are bound above the environments in scope
(`Good`), under either allocation policy, from every function, argument
list and heap,

`Sem.Sim Eq id (Own.run pol q · f vs H) (Cfg.run pol (Cfg.lower q) · f vs H)`:

* **forward:** an Own value (and heap) at depth clock `k` is the same value
  and heap at some total clock `k'` of Cfg, a trap a trap;
* **timeout, identity clock map:** an Own timeout at depth `k` is a Cfg
  timeout at total clock `k` (a depth-`k` timeout forces more than `k`
  charges).

It crosses from big-step to small-step by `Sim.ofStar`: the CPS forward
lemma (`run_reach`) gives the final step or the charges, and Cfg's step
bound covers every clock (`Cfg.runs_run`, M2.5's `Potential`) because
`Cfg.lower` keeps forward edges going up (`lower_ordered`). The result
relation is equality on plain values and heaps, so it composes with
`Rt.lower_correct`'s argument and heap relations. The traced form (decision
D-1) follows by `TSim.ofPure`. -/

set_option autoImplicit false

namespace IxCC.Cfg

open IxCC.Sem (Result Sim TSim Star)
open IxCC.Own (RVal Heap AllocPol)
open IxCC.Fir (FunId)
open IxCC.Cfg.Proof

/-- **`Cfg.lower_correct`** (03 §7, M2.4). -/
theorem lower_correct {pol : AllocPol} {q : Own.Program} (G : Good q) (f : FunId) (vs : List RVal)
    (H : Heap) :
    Sim Eq id (fun k => Own.run pol q k f vs H) (fun k => run pol (lower q) k f vs H) := by
  refine Sem.Sim.ofStar (runs_run pol (lower_ordered q) f vs H) (fun k hk hs => ?_) (fun k hk => ?_)
  · have hr := run_reach (pol := pol) G k f vs H
    generalize Own.run pol q k f vs H = r at hr hk hs ⊢
    match r, hr with
    | .ok (v, H'), ⟨n, hn⟩ => exact ⟨n, _, _, hn, step_ret_nil ▸ .done, .ok rfl⟩
    | .trap, ⟨n, s', hn, ht⟩ => exact ⟨n, s', _, hn, ht ▸ .trap, .trap⟩
    | .timeout, _ => exact absurd rfl hk
    | .stuck, _ => exact absurd rfl hs
    | .resource _, h => exact h.elim
  · have hr := run_reach (pol := pol) G k f vs H
    simp only [id] at hk
    rw [hk] at hr
    obtain ⟨n, s', hn, hlt⟩ := hr
    exact ⟨n, s', hn, .inl hlt⟩

/-- `Cfg.lower_correct` in the traced shape (decision D-1). -/
theorem lower_correct_traced {Env E : Type} {pol : AllocPol} {q : Own.Program} (G : Good q) (f : FunId)
    (vs : List RVal) (H : Heap) :
    TSim (Env := Env) (E := E) Eq id (fun _ k => Sem.Traced.lift (Own.run pol q k f vs H))
      (fun _ k => Sem.Traced.lift (run pol (lower q) k f vs H)) :=
  TSim.ofPure (lower_correct G f vs H)

end IxCC.Cfg
