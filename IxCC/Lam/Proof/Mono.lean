import IxCC.Lam.Proof.Unfold
import IxCC.Sem.Agrees

/-! # Lam: clock monotonicity

`Lam.eval_mono` (design note 02 §4.3, M2.2): an outcome of `eval` other
than `timeout` is the outcome at every larger clock, and likewise for
`apply`, `force`, `evalList`, `evalAlts`, `applyAll` and `run`; so each is a
`Sem.ClockMono` computation. Strong induction on the clock; within one
clock, structural recursion on the term (every call at the same clock is on
a subterm, every other call is one clock down). -/

namespace IxCC.Lam

open IxCC.Sem (Result ClockMono)
open IxCC.Sem.Result (Agrees)

variable (P : Program)

section

set_option linter.unusedSectionVars false

variable {k : Nat}
  (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ t, Agrees (eval P j' ρ t) (eval P j ρ t))
include ih

theorem force_agrees_of {k' : Nat} (hk : k ≤ k') (s : Slot) :
    Agrees (force P k' s) (force P k s) := by
  cases s with
  | val v => rw [force_val, force_val]; exact .refl _
  | name ρ' t =>
    rw [force_name, force_name]
    cases k with
    | zero => exact .of_timeout
    | succ j =>
      obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
      exact ih j (by omega) j' (by omega) ρ' t

theorem apply_agrees_of {k' : Nat} (hk : k ≤ k') (f : Val) (s : Slot) :
    Agrees (apply P k' f s) (apply P k f s) := by
  cases f with
  | clos ρ' b =>
    rw [apply_clos, apply_clos]
    cases k with
    | zero => exact .of_timeout
    | succ j =>
      obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
      exact ih j (by omega) j' (by omega) _ b
  | _ =>
    rw [apply_not_clos P k' _ s (by intros; nofun), apply_not_clos P k _ s (by intros; nofun)]
    exact .refl _

mutual

theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) :
    ∀ t : Term, Agrees (eval P k' ρ t) (eval P k ρ t)
  | .var i => by
    rw [eval_var, eval_var]
    cases ρ[i]? with
    | some s => exact force_agrees_of P ih hk s
    | none => exact .refl _
  | .glob g => by
    rw [eval_glob, eval_glob]
    cases P.global? g with
    | some gl =>
      cases k with
      | zero => exact .of_timeout
      | succ j =>
        obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
        exact ih j (by omega) j' (by omega) [] gl.body
    | none => exact .refl _
  | .lam m c b => by rw [eval_lam, eval_lam]; exact .refl _
  | .app f a m => by
    rw [eval_app, eval_app]
    refine .bind (eval_agrees_of hk ρ f) fun fv _ => ?_
    cases m with
    | strict =>
      exact .bind (eval_agrees_of hk ρ a) fun av _ => apply_agrees_of P ih hk fv _
    | name => exact apply_agrees_of P ih hk fv _
  | .letE c v b => by
    rw [eval_letE, eval_letE]
    exact .bind (eval_agrees_of hk ρ v) fun x _ => eval_agrees_of hk _ b
  | .con c fs => by
    rw [eval_con, eval_con]
    exact .bind (evalList_agrees_of hk ρ fs) fun _ _ => .refl _
  | .case s alts d => by
    rw [eval_case, eval_case]
    refine .bind (eval_agrees_of hk ρ s) fun v _ => ?_
    cases v.asCtor P.known with
    | some cf =>
      exact evalAlts_agrees_of hk ρ cf.1 cf.2 d (evalOpt_agrees_of hk ρ d) alts
    | none => exact .refl _
  | .proj c i s => by
    rw [eval_proj, eval_proj]
    exact .bind (eval_agrees_of hk ρ s) fun _ _ => .refl _
  | .lit l => by rw [eval_lit, eval_lit]; exact .refl _
  | .prim p args => by
    rw [eval_prim, eval_prim]
    exact .bind (evalList_agrees_of hk ρ args) fun _ _ => .refl _
  | .tick t => by
    rw [eval_tick, eval_tick]
    cases k with
    | zero => exact .of_timeout
    | succ j =>
      obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
      exact ih j (by omega) j' (by omega) ρ t
  | .box => by rw [eval_box', eval_box']; exact .refl _
  | .trap => by rw [eval_trap', eval_trap']; exact .refl _

theorem evalList_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) :
    ∀ ts : List Term, Agrees (evalList P k' ρ ts) (evalList P k ρ ts)
  | [] => by rw [evalList_nil, evalList_nil]; exact .refl _
  | t :: ts => by
    rw [evalList_cons, evalList_cons]
    exact .bind (eval_agrees_of hk ρ t) fun _ _ =>
      .bind (evalList_agrees_of hk ρ ts) fun _ _ => .refl _

theorem evalOpt_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) :
    ∀ d : Option Term, ∀ t, d = some t → Agrees (eval P k' ρ t) (eval P k ρ t)
  | none => fun _ h => nomatch h
  | some t => fun _ h => by cases h; exact eval_agrees_of hk ρ t

theorem evalAlts_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) (c : Key.CtorKey) (fs : List Val)
    (d : Option Term) (hd : ∀ t, d = some t → Agrees (eval P k' ρ t) (eval P k ρ t)) :
    ∀ alts : List Alt, Agrees (evalAlts P k' ρ c fs alts d) (evalAlts P k ρ c fs alts d)
  | [] => by
    rw [evalAlts_nil, evalAlts_nil]
    cases d with
    | some t => exact hd t rfl
    | none => exact .refl _
  | .mk key n body :: rest => by
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_agrees_of hk _ body
    · exact evalAlts_agrees_of hk ρ c fs d hd rest

end

end

/-- Every clock level agrees upward. -/
theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ t, Agrees (eval P k' ρ t) (eval P k ρ t) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ t; exact eval_agrees_of P ih hk ρ t

theorem apply_agrees {k k' : Nat} (hk : k ≤ k') (f : Val) (s : Slot) :
    Agrees (apply P k' f s) (apply P k f s) :=
  apply_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk f s

theorem force_agrees {k k' : Nat} (hk : k ≤ k') (s : Slot) :
    Agrees (force P k' s) (force P k s) :=
  force_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk s

theorem evalList_agrees {k k' : Nat} (hk : k ≤ k') (ρ : Env) (ts : List Term) :
    Agrees (evalList P k' ρ ts) (evalList P k ρ ts) :=
  evalList_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk ρ ts

theorem applyAll_agrees {k k' : Nat} (hk : k ≤ k') :
    ∀ (f : Val) (ss : List Slot), Agrees (applyAll P k' f ss) (applyAll P k f ss)
  | f, [] => by rw [applyAll_nil, applyAll_nil]; exact .refl _
  | f, s :: ss => by
    rw [applyAll_cons, applyAll_cons]
    exact .bind (apply_agrees P hk f s) fun v _ => applyAll_agrees hk v ss

theorem run_agrees {k k' : Nat} (hk : k ≤ k') (root : GlobalId) (xs : List Val) :
    Agrees (run P k' root xs) (run P k root xs) := by
  unfold run
  have h := eval_agrees P k k' hk [] (.glob root)
  intro hne
  cases he : eval P k [] (.glob root) with
  | ok f =>
    rw [he] at hne h
    rw [h (by simp)]
    exact applyAll_agrees P hk f _ hne
  | timeout => rw [he] at hne; exact absurd rfl hne
  | _ => rw [he] at h; rw [h (by simp)]

/-- **Clock monotonicity** of Lam evaluation (M2.2). -/
theorem eval_mono (ρ : Env) (t : Term) : ClockMono fun k => eval P k ρ t :=
  Result.Agrees.clockMono fun k k' hk => eval_agrees P k k' hk ρ t

theorem apply_mono (f : Val) (s : Slot) : ClockMono fun k => apply P k f s :=
  Result.Agrees.clockMono fun _ _ hk => apply_agrees P hk f s

theorem force_mono (s : Slot) : ClockMono fun k => force P k s :=
  Result.Agrees.clockMono fun _ _ hk => force_agrees P hk s

theorem evalList_mono (ρ : Env) (ts : List Term) : ClockMono fun k => evalList P k ρ ts :=
  Result.Agrees.clockMono fun _ _ hk => evalList_agrees P hk ρ ts

theorem applyAll_mono (f : Val) (ss : List Slot) : ClockMono fun k => applyAll P k f ss :=
  Result.Agrees.clockMono fun _ _ hk => applyAll_agrees P hk f ss

theorem run_mono (root : GlobalId) (xs : List Val) : ClockMono fun k => run P k root xs :=
  Result.Agrees.clockMono fun _ _ hk => run_agrees P hk root xs

end IxCC.Lam
