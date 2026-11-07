import IxCC.Own.Plain.Proof.Environment
import IxCC.Own.Plain.Proof.Prefixes

/-! Derive argument evaluation and ownership permissions from the actual
checked lexical scope and related live environments. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

theorem argsOwned_of_scope {H : Heap} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal} {args : List Fir.Arg}
    (he : EnvDen H live ρf ρo) (hr : EnvRoots ρo live roots)
    (hs : args.all (argIn live) = true) : ArgsOwned ρo args roots := by
  intro x hx
  have ha : argIn live (.var x) = true := (List.all_eq_true.mp hs) _ hx
  have hm : x ∈ live := by simpa [argIn] using ha
  obtain ⟨v, _, ho, _, _⟩ := he x hm
  exact ⟨v, ho, hr.member hm ho⟩

theorem args_den {H : Heap} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (he : EnvDen H live ρf ρo) (args : List Fir.Arg)
    (hs : args.all (argIn live) = true) :
    ∃ vs ws, Own.evalArgs ρo args = some vs ∧ Fir.evalArgs ρf args = some ws ∧
      Sem.Forall2 (Proof.Den H) vs ws := by
  induction args with
  | nil => exact ⟨[], [], rfl, rfl, .nil⟩
  | cons a args ih =>
    have ha : argIn live a = true ∧ args.all (argIn live) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hs
    obtain ⟨v, w, ho, hf, hd⟩ := arg_den he ha.1
    obtain ⟨vs, ws, hos, hfs, hds⟩ := ih ha.2
    refine ⟨v :: vs, w :: ws, ?_, ?_, .cons hd hds⟩
    · simp [Own.evalArgs, ho, hos]
    · simp [Fir.evalArgs, hf, hfs]


end IxCC.Own.Plain
