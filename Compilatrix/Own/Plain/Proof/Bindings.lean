import Compilatrix.Own.Plain.Proof.CaptureRoots

/-! Fresh binder and parameter entry rules for concrete environment roots.
Source and target parameter lists are bound in the same order; existing
captured tokens are preserved rather than duplicated. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

theorem evalArgs_append (ρ : Own.Env) (as bs : List Fir.Arg) :
    Own.evalArgs ρ (as ++ bs) =
      (Own.evalArgs ρ as).bind (fun vs => (Own.evalArgs ρ bs).map (vs ++ ·)) := by
  induction as with
  | nil => simp [Own.evalArgs]
  | cons a as ih =>
    simp only [List.cons_append, Own.evalArgs]
    rw [ih]
    cases Own.evalArg ρ a <;> cases Own.evalArgs ρ as <;> cases Own.evalArgs ρ bs <;> rfl

theorem EnvRoots.append {ρ : Own.Env} {xs ys : List Fir.Var} {vs ws : List RVal}
    (hx : EnvRoots ρ xs vs) (hy : EnvRoots ρ ys ws) : EnvRoots ρ (xs ++ ys) (vs ++ ws) := by
  change Own.evalArgs ρ ((xs ++ ys).map Fir.Arg.var) = some (vs ++ ws)
  rw [List.map_append, evalArgs_append, hx, hy]
  rfl

theorem EnvRoots.insert {ρ : Own.Env} {live : List Fir.Var} {roots : List RVal}
    (h : EnvRoots ρ live roots) (x : Fir.Var) (v : RVal) (hx : x ∉ live) :
    EnvRoots (ρ.insert x v) (live ++ [x]) (roots ++ [v]) := by
  have hold : EnvRoots (ρ.insert x v) live roots := by
    change Own.evalArgs (ρ.insert x v) (live.map Fir.Arg.var) = some roots
    rw [evalVars_congr (ρ.insert x v) ρ live (fun y hy =>
      Src.NatMap.get?_insert_ne _ _ (by intro he; subst y; exact hx hy))]
    exact h
  apply hold.append
  simp [EnvRoots, Own.evalArgs, Own.evalArg, Src.NatMap.get?_insert_self]

theorem EnvRoots.bindAll {ρ : Own.Env} {live : List Fir.Var} {roots : List RVal}
    (h : EnvRoots ρ live roots) (params : List Fir.Var) (values : List RVal)
    (hl : values.length = params.length) (hf : fresh live params = true) :
    EnvRoots (Own.bindAll ρ params values) (live ++ params) (roots ++ values) := by
  induction params generalizing ρ live roots values with
  | nil =>
    cases values with
    | nil => simpa [Own.bindAll] using h
    | cons => simp at hl
  | cons x xs ih =>
    cases values with
    | nil => simp at hl
    | cons v vs =>
      have hp : (!live.contains x) = true ∧ fresh (live ++ [x]) xs = true := by
        simpa only [fresh, Bool.and_eq_true] using hf
      have hx : x ∉ live := by simpa using hp.1
      have ht : vs.length = xs.length := by simpa using hl
      have result := ih (h.insert x v hx) vs ht hp.2
      simpa [Own.bindAll, List.append_assoc] using result

theorem EnvDen.bindAll {H : Heap} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (h : EnvDen H live ρf ρo) (params : List Fir.Var) {vs : List RVal} {ws : List Fir.Val}
    (hd : Sem.Forall2 (Proof.Den H) vs ws) (hl : vs.length = params.length) :
    EnvDen H (live ++ params) (Fir.bindAll ρf params ws) (Own.bindAll ρo params vs) := by
  induction params generalizing live ρf ρo vs ws with
  | nil =>
    cases hd with
    | nil => simpa [Fir.bindAll, Own.bindAll] using h
    | cons => simp at hl
  | cons x xs ih =>
    cases hd with
    | nil => simp at hl
    | @cons v w vs ws hv hvs =>
      have ht : vs.length = xs.length := by simpa using hl
      have result := ih (h.insert x hv) hvs ht
      simpa [Fir.bindAll, Own.bindAll, List.append_assoc] using result

theorem balance_append_comm {H : Heap} {external : Nat → Nat} {xs ys : List RVal}
    (h : Rc.Balance H external (xs ++ ys)) : Rc.Balance H external (ys ++ xs) := by
  intro l
  have he := h l
  simp only [Rc.refsIn_append] at *
  omega


end Compilatrix.Own.Plain
