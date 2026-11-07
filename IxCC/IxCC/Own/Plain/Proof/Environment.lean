import IxCC.Own.Plain.Check
import IxCC.Own.Plain.Proof.Actions

/-! Live-scope environment denotations. Released stale entries may remain in
the persistent maps; only variables in the producer's live scope are related.
Concrete root lists come from actual variable evaluation, not a caller's
assertion that the source and target executions simulate one another. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc

def EnvDen (H : Heap) (live : List Fir.Var) (ρf : Fir.Env) (ρo : Own.Env) : Prop :=
  ∀ x, x ∈ live → ∃ v w, ρo.get? x = some v ∧ ρf.get? x = some w ∧ Proof.Den H v w

def EnvRoots (ρo : Own.Env) (live : List Fir.Var) (roots : List RVal) : Prop :=
  Own.evalArgs ρo (live.map Fir.Arg.var) = some roots

def RootedEnv (H : Heap) (external : Nat → Nat) (live : List Fir.Var)
    (ρf : Fir.Env) (ρo : Own.Env) : Prop :=
  EnvDen H live ρf ρo ∧ ∃ roots, EnvRoots ρo live roots ∧ Balance H external roots

theorem EnvDen.insert {H : Heap} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (h : EnvDen H live ρf ρo) (x : Fir.Var) {v : RVal} {w : Fir.Val}
    (hd : Proof.Den H v w) : EnvDen H (live ++ [x]) (ρf.insert x w) (ρo.insert x v) := by
  intro y hy
  by_cases he : y = x
  · subst y
    exact ⟨v, w, Src.NatMap.get?_insert_self .., Src.NatMap.get?_insert_self .., hd⟩
  · have hm : y ∈ live := by simpa [he] using hy
    obtain ⟨v', w', ho, hf, hd'⟩ := h y hm
    exact ⟨v', w', by rw [Src.NatMap.get?_insert_ne _ _ he]; exact ho,
      by rw [Src.NatMap.get?_insert_ne _ _ he]; exact hf, hd'⟩

theorem EnvRoots.member {ρo : Own.Env} {live : List Fir.Var} {roots : List RVal}
    (h : EnvRoots ρo live roots) {x : Fir.Var} (hx : x ∈ live) {v : RVal}
    (hv : ρo.get? x = some v) : v ∈ roots := by
  induction live generalizing roots with
  | nil => simp at hx
  | cons y ys ih =>
    unfold EnvRoots at h
    cases hy : ρo.get? y with
    | none => simp [List.map_cons, Own.evalArgs, Own.evalArg, hy] at h
    | some u =>
      cases hs : Own.evalArgs ρo (ys.map Fir.Arg.var) with
      | none => simp [List.map_cons, Own.evalArgs, Own.evalArg, hy, hs] at h
      | some us =>
        have hr : u :: us = roots := by
          simpa [List.map_cons, Own.evalArgs, Own.evalArg, hy, hs] using h
        subst roots
        rcases List.mem_cons.mp hx with he | hx
        · subst x
          have he : u = v := Option.some.inj (hy.symm.trans hv)
          subst v
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem u (ih hs hx)

theorem EnvDen.transport {H H' : Heap} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal}
    (h : EnvDen H live ρf ρo) (hr : EnvRoots ρo live roots)
    (hv : ∀ v, v ∈ roots → H.value? v = H'.value? v) : EnvDen H' live ρf ρo := by
  intro x hx
  obtain ⟨v, w, ho, hf, hd⟩ := h x hx
  refine ⟨v, w, ho, hf, ?_⟩
  change H'.value? v = some w
  rw [← hv v (hr.member hx ho)]
  exact hd

theorem arg_den {H : Heap} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (h : EnvDen H live ρf ρo) {a : Fir.Arg} (ha : argIn live a = true) :
    ∃ v w, Own.evalArg ρo a = some v ∧ a.eval ρf = some w ∧ Proof.Den H v w := by
  cases a with
  | var x =>
    have hx : x ∈ live := by simpa [argIn] using ha
    exact h x hx
  | lit l => exact ⟨.lit l, .lit l, rfl, rfl, Proof.den_lit H l⟩
  | erased => exact ⟨.erased, .erased, rfl, rfl, Proof.den_erased H⟩


end IxCC.Own.Plain
