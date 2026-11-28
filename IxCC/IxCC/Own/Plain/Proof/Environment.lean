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

def ImmVal (v : RVal) : Prop := ∀ l, v ≠ .loc l

def ImmEnv (ρ : Own.Env) (imm : List Fir.Var) : Prop :=
  ∀ x, x ∈ imm → ∃ v, ρ.get? x = some v ∧ ImmVal v

theorem value?_eq_of_immVal (H₁ H₂ : Heap) {v : RVal} (h : ImmVal v) :
    H₁.value? v = H₂.value? v := by
  cases v with
  | loc l => exact False.elim (h l rfl)
  | lit _ | ctor0 _ | erased => simp [Heap.value?, toFir]

theorem immVal_of_isImmArg {ρ : Own.Env} {imm : List Fir.Var} {a : Fir.Arg} {v : RVal}
    (himm : ImmEnv ρ imm) (ha : isImmArg imm a = true) (hev : Own.evalArg ρ a = some v) :
    ImmVal v := by
  cases a with
  | var x =>
    have hx : x ∈ imm := List.contains_iff_mem.mp ha
    obtain ⟨v', hv', himm_v⟩ := himm x hx
    have heq : v' = v := Option.some.inj (hv'.symm.trans hev)
    exact heq ▸ himm_v
  | lit _ =>
    have heq : .lit _ = v := Option.some.inj hev
    subst heq
    intro l hloc
    cases hloc
  | erased =>
    have heq : .erased = v := Option.some.inj hev
    subst heq
    intro l hloc
    cases hloc

theorem ImmEnv.insert_keep {ρ : Own.Env} {live imm : List Fir.Var}
    (h : ImmEnv ρ imm) (hsub : ∀ y, y ∈ imm → y ∈ live)
    (x : Fir.Var) (v : RVal) (hx : x ∉ live) :
    ImmEnv (ρ.insert x v) imm := by
  intro y hy
  have hne : y ≠ x := fun he => hx (he ▸ hsub y hy)
  obtain ⟨v', ho, himm⟩ := h y hy
  exact ⟨v', by rw [Src.NatMap.get?_insert_ne _ _ hne]; exact ho, himm⟩

theorem ImmEnv.insert_imm {ρ : Own.Env} {live imm : List Fir.Var}
    (h : ImmEnv ρ imm) (hsub : ∀ y, y ∈ imm → y ∈ live)
    (x : Fir.Var) (v : RVal) (hx : x ∉ live) (hv : ImmVal v) :
    ImmEnv (ρ.insert x v) (imm ++ [x]) := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact (h.insert_keep hsub x v hx) y hy
  · have he : y = x := by simpa using hy
    subst y
    exact ⟨v, Src.NatMap.get?_insert_self .., hv⟩

theorem ImmEnv.insert_rhs {ρ : Own.Env} {live imm : List Fir.Var}
    (h : ImmEnv ρ imm) (hsub : ∀ y, y ∈ imm → y ∈ live)
    (x : Fir.Var) (r : Fir.Rhs) (v : RVal) (hx : x ∉ live)
    (hv : isImmRhs imm r = true → ImmVal v)
    (hnotPrim : ∀ op args, r ≠ .prim op args := by intro op args h; cases h) :
    (∀ y, y ∈ nextImm imm x r → y ∈ live ++ [x]) ∧
      ImmEnv (ρ.insert x v) (nextImm imm x r) := by
  have hnext : nextImm imm x r = if isImmRhs imm r then imm ++ [x] else imm := by
    cases r with
    | prim op args => exact False.elim (hnotPrim op args rfl)
    | _ => rfl
  rw [hnext]
  cases hr : isImmRhs imm r with
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact ⟨fun y hy => List.mem_append_left _ (hsub y hy), h.insert_keep hsub x v hx⟩
  | true =>
    rw [if_pos rfl]
    refine ⟨fun y hy => ?_, h.insert_imm hsub x v hx (hv hr)⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_append_left _ (hsub y hy)
    · exact List.mem_append_right _ hy

theorem argVars_sub_live : ∀ {live : List Fir.Var} {args : List Fir.Arg},
    args.all (argIn live) = true → ∀ x ∈ argVars args, x ∈ live
  | _, [], _, x, hx => by simp [argVars] at hx
  | live, a :: args, hs, x, hx => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    cases a with
    | var y =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa [argIn] using hs.1
      · exact argVars_sub_live (args := args) hs.2 x hx
    | lit _ | erased => exact argVars_sub_live (args := args) hs.2 x hx

theorem immEnv_argVars : ∀ {ρ : Own.Env} {args : List Fir.Arg} {vs : List RVal},
    Own.evalArgs ρ args = some vs → (∀ v ∈ vs, ImmVal v) → ImmEnv ρ (argVars args)
  | _, [], _, _, _ => by intro x hx; simp [argVars] at hx
  | ρ, a :: args, vs, hev, himm => by
    cases ha : Own.evalArg ρ a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v =>
      cases has : Own.evalArgs ρ args with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have heq : v :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst vs
        cases a with
        | var y =>
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨v, ha, himm v List.mem_cons_self⟩
          · exact immEnv_argVars has (fun u hu => himm u (List.mem_cons_of_mem v hu)) x hx
        | lit _ | erased =>
          exact immEnv_argVars (args := args) has (fun u hu => himm u (List.mem_cons_of_mem v hu))

theorem ImmEnv.append {ρ : Own.Env} {xs ys : List Fir.Var}
    (hx : ImmEnv ρ xs) (hy : ImmEnv ρ ys) : ImmEnv ρ (xs ++ ys) := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hx z hz
  · exact hy z hz

end IxCC.Own.Plain
