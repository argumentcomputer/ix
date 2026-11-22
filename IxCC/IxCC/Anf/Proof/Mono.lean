import IxCC.Anf.Proof.Unfold
import IxCC.Sem.SimUpTo

/-! # Anf: clock monotonicity

`Anf.eval_mono`: an outcome of `eval` other
than `timeout` is the outcome at every larger clock, and likewise for
`evalBind`, `applyN`, `evalAlts`, the jump and call helpers, and `run`; so
each is a `Sem.ClockMono` computation. Strong induction on the clock; within
one clock, structural recursion on the term, and for `applyN` induction on
the number of arguments (an over-saturated application enters the body one
clock down, then applies the rest at the same clock). The proofs read the
evaluator only through its bind-form equations (`Anf.Proof.Unfold`). -/

set_option autoImplicit false

namespace IxCC.Anf

open IxCC.Sem (Result ClockMono later)
open IxCC.Sem.Result (Agrees)

variable (P : Program)

theorem Agrees.later {α : Type} {k k' : Nat} (hk : k ≤ k') {f f' : Nat → Result α}
    (h : ∀ j j', j + 1 = k → j' + 1 = k' → Agrees (f' j') (f j)) :
    Agrees (later k' f') (later k f) := by
  cases k with
  | zero => exact .of_timeout
  | succ j =>
    obtain ⟨j', rfl⟩ : ∃ j', k' = j' + 1 := ⟨k' - 1, by omega⟩
    exact h j j' rfl rfl

theorem Agrees.ofOption {α β : Type} (o : Option α) {f f' : α → Result β}
    (h : ∀ a, o = some a → Agrees (f' a) (f a)) :
    Agrees ((Result.ofOption o).bind f') ((Result.ofOption o).bind f) := by
  cases o with
  | none => exact .refl _
  | some a => exact h a rfl

section

set_option linter.unusedSectionVars false

variable {k : Nat}
  (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J e, Agrees (eval P j' ρ J e) (eval P j ρ J e))
include ih

theorem applyN_agrees_of {k' : Nat} (hk : k ≤ k') :
    ∀ (m : Nat) (f : Val) (vs : List Val), vs.length ≤ m → Agrees (applyN P k' f vs) (applyN P k f vs)
  | _, f, [], _ => by rw [applyN_nil', applyN_nil']; exact .refl _
  | m, f, v :: rest, hm => by
    cases f with
    | clos ρ' n b got =>
      rw [applyN_clos, applyN_clos]
      refine Agrees.later hk fun j j' hj hj' => ?_
      by_cases hg : got.length < n
      · simp only [hg, if_true]
        by_cases hs : got.length + (v :: rest).length < n
        · simp only [hs, if_true]; exact .refl _
        · simp only [hs, if_false, enter]
          refine .bind (ih j (by omega) j' (by omega) _ _ b) fun r _ => ?_
          rw [hj, hj']
          cases m with
          | zero => simp at hm
          | succ m =>
            exact applyN_agrees_of hk m r _ (by simp at hm ⊢; omega)
      · simp only [hg, if_false]; exact .refl _
    | _ =>
      rw [applyN_not_clos P k' _ v rest (by intros; nofun),
        applyN_not_clos P k _ v rest (by intros; nofun)]
      exact .refl _

theorem globVal_agrees_of {k' : Nat} (hk : k ≤ k') (gd : GDef) :
    Agrees (globVal P k' gd) (globVal P k gd) := by
  unfold globVal
  cases gd.ps with
  | nil => exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) [] [] gd.body
  | cons _ _ => exact .refl _

theorem callVal_agrees_of {k' : Nat} (hk : k ≤ k') (gd : GDef) (vs : List Val) :
    Agrees (callVal P k' gd vs) (callVal P k gd vs) := by
  unfold callVal
  split
  · exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ [] gd.body
  · exact .refl _

theorem jumpTo_agrees_of {k' : Nat} (hk : k ≤ k') (jc : JClo) (vs : List Val) :
    Agrees (jumpTo P k' jc vs) (jumpTo P k jc vs) := by
  obtain ⟨ρ', J', n, b, r⟩ := jc
  simp only [jumpTo]
  by_cases h : vs.length = n
  · simp only [h, if_true]
    exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ _ b
  · simp only [h, if_false]; exact .refl _

mutual

theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : List Val) (J : List JClo) :
    ∀ e : Exp, Agrees (eval P k' ρ J e) (eval P k ρ J e)
  | .bind c b e => by
    rw [eval_bind, eval_bind]
    exact .bind (evalBind_agrees_of hk ρ b) fun v _ => eval_agrees_of hk (v :: ρ) J e
  | .join n r b e => by
    rw [eval_join', eval_join']
    exact eval_agrees_of hk ρ _ e
  | .jump j as => by
    rw [eval_jump, eval_jump]
    exact Agrees.ofOption _ fun jc _ => Agrees.ofOption _ fun vs _ =>
      jumpTo_agrees_of P ih hk jc vs
  | .case x alts d => by
    rw [eval_case, eval_case]
    refine Agrees.ofOption _ fun v _ => ?_
    cases v.asCtor P.known with
    | some cf => exact evalAlts_agrees_of hk ρ J cf.1 cf.2 d (evalOpt_agrees_of hk ρ J d) alts
    | none => exact .refl _
  | .ret a => by rw [eval_ret', eval_ret']; exact .refl _
  | .tick e => by
    rw [eval_tick, eval_tick]
    exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) ρ J e
  | .trap => by rw [eval_trap', eval_trap']; exact .refl _

theorem evalBind_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : List Val) :
    ∀ b : Bind, Agrees (evalBind P k' ρ b) (evalBind P k ρ b)
  | .atom a => by rw [evalBind_atom, evalBind_atom]; exact .refl _
  | .con c as => by rw [evalBind_con, evalBind_con]; exact .refl _
  | .proj c i x => by rw [evalBind_proj, evalBind_proj]; exact .refl _
  | .prim p as => by rw [evalBind_prim, evalBind_prim]; exact .refl _
  | .glob g => by
    rw [evalBind_glob, evalBind_glob]
    exact Agrees.ofOption _ fun gd _ => globVal_agrees_of P ih hk gd
  | .call g as => by
    rw [evalBind_call, evalBind_call]
    exact Agrees.ofOption _ fun gd _ => Agrees.ofOption _ fun vs _ =>
      callVal_agrees_of P ih hk gd vs
  | .app f as => by
    rw [evalBind_app, evalBind_app]
    exact Agrees.ofOption _ fun fv _ => Agrees.ofOption _ fun vs _ =>
      applyN_agrees_of P ih hk vs.length fv vs (Nat.le_refl _)
  | .fn ps b => by
    cases ps with
    | nil => rw [evalBind_fn_nil, evalBind_fn_nil]; exact .refl _
    | cons p ps =>
      rw [evalBind_fn P k' ρ _ b (List.cons_ne_nil _ _), evalBind_fn P k ρ _ b (List.cons_ne_nil _ _)]
      exact .refl _

theorem evalOpt_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : List Val) (J : List JClo) :
    ∀ d : Option Exp, ∀ e, d = some e → Agrees (eval P k' ρ J e) (eval P k ρ J e)
  | none => fun _ h => nomatch h
  | some e => fun _ h => by cases h; exact eval_agrees_of hk ρ J e

theorem evalAlts_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : List Val) (J : List JClo)
    (c : Key.CtorKey) (fs : List Val) (d : Option Exp)
    (hd : ∀ e, d = some e → Agrees (eval P k' ρ J e) (eval P k ρ J e)) :
    ∀ alts : List Alt, Agrees (evalAlts P k' ρ J c fs alts d) (evalAlts P k ρ J c fs alts d)
  | [] => by
    rw [evalAlts_nil, evalAlts_nil]
    cases d with
    | some e => exact hd e rfl
    | none => exact .refl _
  | .mk key n body :: rest => by
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_agrees_of hk _ J body
    · exact evalAlts_agrees_of hk ρ J c fs d hd rest

end

end

/-- Every clock level agrees upward. -/
theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ J e, Agrees (eval P k' ρ J e) (eval P k ρ J e) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ J e; exact eval_agrees_of P ih hk ρ J e

theorem evalBind_agrees {k k' : Nat} (hk : k ≤ k') (ρ : List Val) (b : Bind) :
    Agrees (evalBind P k' ρ b) (evalBind P k ρ b) :=
  evalBind_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk ρ b

theorem applyN_agrees {k k' : Nat} (hk : k ≤ k') (f : Val) (vs : List Val) :
    Agrees (applyN P k' f vs) (applyN P k f vs) :=
  applyN_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk vs.length f vs (Nat.le_refl _)

theorem evalAlts_agrees {k k' : Nat} (hk : k ≤ k') (ρ : List Val) (J : List JClo)
    (c : Key.CtorKey) (fs : List Val) (alts : List Alt) (d : Option Exp) :
    Agrees (evalAlts P k' ρ J c fs alts d) (evalAlts P k ρ J c fs alts d) :=
  evalAlts_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk ρ J c fs d
    (fun e _ => eval_agrees P k k' hk ρ J e) alts

theorem run_agrees {k k' : Nat} (hk : k ≤ k') (root : GlobalId) (xs : List Val) :
    Agrees (run P k' root xs) (run P k root xs) := by
  rw [run_eq, run_eq]
  exact .bind (evalBind_agrees P hk [] _) fun f _ => applyN_agrees P hk f xs

/-- **Clock monotonicity** of Anf evaluation. -/
theorem eval_mono (ρ : List Val) (J : List JClo) (e : Exp) : ClockMono fun k => eval P k ρ J e :=
  Result.Agrees.clockMono fun k k' hk => eval_agrees P k k' hk ρ J e

theorem evalBind_mono (ρ : List Val) (b : Bind) : ClockMono fun k => evalBind P k ρ b :=
  Result.Agrees.clockMono fun _ _ hk => evalBind_agrees P hk ρ b

theorem applyN_mono (f : Val) (vs : List Val) : ClockMono fun k => applyN P k f vs :=
  Result.Agrees.clockMono fun _ _ hk => applyN_agrees P hk f vs

theorem evalAlts_mono (ρ : List Val) (J : List JClo) (c : Key.CtorKey) (fs : List Val)
    (alts : List Alt) (d : Option Exp) : ClockMono fun k => evalAlts P k ρ J c fs alts d :=
  Result.Agrees.clockMono fun _ _ hk => evalAlts_agrees P hk ρ J c fs alts d

theorem globVal_mono (gd : GDef) : ClockMono fun k => globVal P k gd :=
  Result.Agrees.clockMono fun _ _ hk =>
    globVal_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk gd

theorem callVal_mono (gd : GDef) (vs : List Val) : ClockMono fun k => callVal P k gd vs :=
  Result.Agrees.clockMono fun _ _ hk =>
    callVal_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk gd vs

theorem jumpTo_mono (jc : JClo) (vs : List Val) : ClockMono fun k => jumpTo P k jc vs :=
  Result.Agrees.clockMono fun _ _ hk =>
    jumpTo_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk jc vs

theorem enter_mono (ρ' : List Val) (n : Nat) (b : Exp) (all : List Val) :
    ClockMono fun k => enter P k ρ' n b all := by
  unfold enter
  intro k k' hle hk
  exact (Agrees.bind (eval_agrees P k k' hle _ [] b) fun r _ =>
    applyN_agrees P (by omega) r (all.drop n)) hk

theorem run_mono (root : GlobalId) (xs : List Val) : ClockMono fun k => run P k root xs :=
  Result.Agrees.clockMono fun _ _ hk => run_agrees P hk root xs

end IxCC.Anf
