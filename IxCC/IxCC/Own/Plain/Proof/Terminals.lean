import IxCC.Own.Plain.Proof.Results
import IxCC.Own.Plain.Proof.Transfers
import IxCC.Own.Plain.Proof.Scope
import IxCC.Own.Plain.Proof.Unfold
import IxCC.Fir.Proof.Unfold

/-! Terminal cases of the canonical producer's refinement. These proofs use
the actual copies/drops evaluator and concrete live roots; no execution
simulation is a caller premise. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

theorem retained_empty (live : List Fir.Var) : retained [] live = [] := by
  simp [retained]

theorem return_refines (P : Program) (k : Nat) (ρf : Fir.Env) (ρo : Own.Env)
    (Jf : List Fir.JEntry) (Jo : List JEntry) (H : Heap)
    (live : List Fir.Var) (joins : Joins) (a : Fir.Arg)
    {external : Nat → Nat} {roots : List RVal}
    (he : EnvDen H live ρf ρo) (hr : EnvRoots ρo live roots)
    (hb : Balance H external roots) (hs : argIn live a = true) :
    ResultRel H external (Fir.eval P.source k ρf Jf (.ret a))
      (eval P k ρo Jo H (lowerCode live joins (.ret a))) := by
  obtain ⟨v, w, hvo, hwf, hd⟩ := arg_den he hs
  have has : [a].all (argIn live) = true := by simpa using hs
  have hav : Own.evalArgs ρo [a] = some [v] := by simp [Own.evalArgs, hvo]
  obtain ⟨H', kept, hrun, hk, hb', _, hv, hext⟩ :=
    transfer_sound P k ρo Jo H live [] [a] (.ret a) hr hb
      (argsOwned_of_scope he hr has) hav
  have hk' : kept = [] := by
    simpa [EnvRoots, retained_empty, Own.evalArgs] using hk.symm
  subst kept
  have hd' : Proof.Den H' v w := by
    change H'.value? v = some w
    rw [← hv v (by simp)]
    exact hd
  rw [lowerCode, hrun, eval_ret, Fir.eval_ret, hwf, hvo]
  simp only [Result.ofOption, Result.bind_ok]
  refine .ok hd' (by simpa using hb') ?_
  intro root value hroot hden
  change H'.value? root = some value
  rw [← hext root hroot]
  exact hden

theorem trap_refines (P : Program) (k : Nat) (ρf : Fir.Env) (ρo : Own.Env)
    (Jf : List Fir.JEntry) (Jo : List JEntry) (H : Heap)
    (live : List Fir.Var) (joins : Joins)
    {external : Nat → Nat} {roots : List RVal}
    (hr : EnvRoots ρo live roots) (hb : Balance H external roots) :
    ResultRel H external (Fir.eval P.source k ρf Jf .trap)
      (eval P k ρo Jo H (lowerCode live joins .trap)) := by
  obtain ⟨H', _, hrun, _, _, _, _, _⟩ :=
    drops_sound ρo H [] live (carry := []) hr (by simpa using hb)
  rw [lowerCode, eval_actionPrefix, hrun, Result.bind_ok, eval_trap, Fir.eval_trap]
  exact .trap


end IxCC.Own.Plain
