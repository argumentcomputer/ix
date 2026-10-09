import Compilatrix.Own.Plain.Proof.CaptureIdentity
import Compilatrix.Own.Plain.Proof.Drops

/-! Connect lexical capture identity to actual retained heap-root tokens. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem retained_eq {captured live : List Fir.Var} (hs : captured.Sublist live)
    (hn : live.Nodup) : retained captured live = captured := by
  have hself : captured.filter captured.contains = captured :=
    List.filter_eq_self.mpr (by intro x hx; simpa using hx)
  have hsub : captured.Sublist (retained captured live) := by
    simpa [retained, hself] using hs.filter captured.contains
  have hnodup : (retained captured live).Nodup := List.filter_sublist.nodup hn
  have hmem : retained captured live ⊆ captured := by
    intro x hx
    have hc := (List.mem_filter.mp hx).2
    simpa using hc
  exact (hsub.eq_of_length_le (hnodup.length_le_of_subset hmem)).symm

theorem evalVars_congr (saved current : Own.Env) (live : List Fir.Var)
    (he : ∀ x, x ∈ live → saved.get? x = current.get? x) :
    Own.evalArgs saved (live.map Fir.Arg.var) = Own.evalArgs current (live.map Fir.Arg.var) := by
  induction live with
  | nil => rfl
  | cons x xs ih =>
    have hh := he x (by simp)
    have ht := ih (fun y hy => he y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, Own.evalArgs, Own.evalArg]
    rw [hh, ht]

theorem EnvRoots.restrict {ρ : Own.Env} {live captured : List Fir.Var} {roots : List RVal}
    (hr : EnvRoots ρ live roots) (hs : captured.Sublist live) :
    ∃ kept, EnvRoots ρ captured kept ∧ kept.Sublist roots := by
  induction hs generalizing roots with
  | slnil =>
    have he : roots = [] := by simpa [EnvRoots, Own.evalArgs] using hr.symm
    subst roots
    exact ⟨[], rfl, .refl _⟩
  | cons x hs ih =>
    obtain ⟨v, vs, hx, ht, he⟩ := envRoots_cons hr
    subst roots
    obtain ⟨kept, hk, hsub⟩ := ih ht
    exact ⟨kept, hk, hsub.cons v⟩
  | cons_cons x hs ih =>
    obtain ⟨v, vs, hx, ht, he⟩ := envRoots_cons hr
    subst roots
    obtain ⟨kept, hk, hsub⟩ := ih ht
    refine ⟨v :: kept, ?_, hsub.cons_cons v⟩
    change Own.evalArgs ρ ((x :: _).map Fir.Arg.var) = some (v :: kept)
    unfold EnvRoots at hk
    simp only [List.map_cons, Own.evalArgs, Own.evalArg, hx, hk]

theorem CaptureView.roots {saved current : Own.Env} {captured live : List Fir.Var}
    {roots : List RVal} (hv : CaptureView saved current captured live)
    (hr : EnvRoots current live roots) :
    ∃ kept, EnvRoots saved captured kept ∧ kept.Sublist roots := by
  obtain ⟨kept, hk, hs⟩ := hr.restrict hv.order
  refine ⟨kept, ?_, hs⟩
  change Own.evalArgs saved (captured.map Fir.Arg.var) = some kept
  rw [evalVars_congr saved current captured hv.agree]
  exact hk

theorem CaptureView.retained_roots {saved current : Own.Env} {captured live : List Fir.Var}
    {kept : List RVal} (hv : CaptureView saved current captured live)
    (hr : EnvRoots current (retained captured live) kept) : EnvRoots saved captured kept := by
  rw [retained_eq hv.order hv.distinct] at hr
  change Own.evalArgs saved (captured.map Fir.Arg.var) = some kept
  rw [evalVars_congr saved current captured hv.agree]
  exact hr


end Compilatrix.Own.Plain
