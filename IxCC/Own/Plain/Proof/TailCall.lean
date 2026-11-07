import IxCC.Own.Plain.Proof.Terminals

/-! Actual tail-call argument transfer. The output supplies the concrete
callee state to the whole-program induction; this lemma assumes no callee
simulation. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

theorem dens_transport {H H' : Heap} {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws)
    (hv : ∀ v, v ∈ vs → H.value? v = H'.value? v) :
    Sem.Forall2 (Proof.Den H') vs ws := by
  revert hv
  induction hd with
  | nil => intro _; exact .nil
  | @cons v w vs ws hd hds ih =>
    intro hv
    refine .cons ?_ (ih (fun root hm => hv root (List.mem_cons_of_mem _ hm)))
    change H'.value? v = some w
    rw [← hv v List.mem_cons_self]
    exact hd

theorem tailCall_transfer (P : Program) (k : Nat) (ρf : Fir.Env) (ρo : Own.Env)
    (Jf : List Fir.JEntry) (Jo : List JEntry) (H : Heap)
    (live : List Fir.Var) (joins : Joins) (f : Fir.FunId) (args : List Fir.Arg)
    {external : Nat → Nat} {roots : List RVal}
    (he : EnvDen H live ρf ρo) (hr : EnvRoots ρo live roots)
    (hb : Balance H external roots) (hs : args.all (argIn live) = true) :
    ∃ H' vs ws,
      Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Fir.eval P.source k ρf Jf (.tcall f args) = Fir.evalCall P.source k f ws ∧
      eval P k ρo Jo H (lowerCode live joins (.tcall f args)) = evalCall P k f vs H' ∧
      Balance H' external vs ∧ Sem.Forall2 (Proof.Den H') vs ws ∧
      ∀ root, ExternalRoot external root → H.value? root = H'.value? root := by
  obtain ⟨vs, ws, hvo, hwf, hd⟩ := args_den he args hs
  obtain ⟨H', kept, hrun, hk, hb', _, hv, hext⟩ :=
    transfer_sound P k ρo Jo H live [] args (.tcall f args) hr hb
      (argsOwned_of_scope he hr hs) hvo
  have hk' : kept = [] := by
    simpa [EnvRoots, retained_empty, Own.evalArgs] using hk.symm
  subst kept
  refine ⟨H', vs, ws, hvo, hwf, ?_, ?_, by simpa using hb', ?_, hext⟩
  · rw [Fir.eval_tcall, hwf]
    rfl
  · rw [lowerCode, hrun, eval_tcall, hvo]
    rfl
  · exact dens_transport hd (by simpa using hv)


end IxCC.Own.Plain
