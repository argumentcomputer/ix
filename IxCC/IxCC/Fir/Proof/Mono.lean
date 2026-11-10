import IxCC.Fir.Proof.Unfold
import IxCC.Sem.SimUpTo

/-! # Fir: clock monotonicity

`Fir.eval_mono`: an outcome of `eval` other than `timeout` is the
outcome at every larger clock, and likewise for `evalAlts`, `evalCall`,
the call and jump helpers and `run`; so each is a `Sem.ClockMono`
computation. Strong induction on the clock; within one clock, well-founded
induction on the evaluator's own measure (the size of the code plus the
sizes of the uncharged join bodies on the stack), since a free jump runs a
join body at the same clock. The proofs read the evaluator only through its
bind-form equations (`Fir.Proof.Unfold`). -/

set_option autoImplicit false

namespace IxCC.Fir

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

/-- The measure of a free jump: the body of an uncharged entry, under the
stack below it, is smaller than the stack it was found in. -/
theorem jump_measure {j : JoinId} {J : List JEntry} {e : JEntry} {rest : List JEntry}
    (h : lookupJ j J = some (e, rest)) (hc : e.charged = false) :
    e.body.size + jweight (e.after rest) < (Code.jmp j []).size + jweight J := by
  have hw := lookupJ_weight j h
  rw [JEntry.jweight_after]
  simp only [JEntry.weight, hc, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [Code.size]
  omega

section

set_option linter.unusedSectionVars false

variable {k : Nat}
  (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J c, Agrees (eval P j' ρ J c) (eval P j ρ J c))
include ih

theorem callFun_agrees_of {k' : Nat} (hk : k ≤ k') (fd : Fun) (vs : List Val) :
    Agrees (callFun P k' fd vs) (callFun P k fd vs) := by
  unfold callFun
  split
  · exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ [] fd.body
  · exact .refl _

theorem evalCall_agrees_of {k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List Val) :
    Agrees (evalCall P k' f vs) (evalCall P k f vs) := by
  rw [evalCall_eq, evalCall_eq]
  exact Agrees.ofOption _ fun fd _ => callFun_agrees_of P ih hk fd vs

mutual

theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry) (c : Code) :
    Agrees (eval P k' ρ J c) (eval P k ρ J c) := by
  match c with
  | .bind x (.call f as) c' =>
    rw [eval_bindCall, eval_bindCall]
    exact Agrees.ofOption _ fun vs _ => .bind (evalCall_agrees_of P ih hk f vs) fun v _ =>
      eval_agrees_of hk (ρ.insert x v) J c'
  | .bind x (.arg a) c' =>
    rw [eval_bind_arg, eval_bind_arg]
    exact .bind (.refl _) fun v _ => eval_agrees_of hk (ρ.insert x v) J c'
  | .bind x (.ctor ci as) c' =>
    rw [eval_bind_ctor, eval_bind_ctor]
    exact .bind (.refl _) fun v _ => eval_agrees_of hk (ρ.insert x v) J c'
  | .bind x (.proj y ci i) c' =>
    rw [eval_bind_proj, eval_bind_proj]
    exact .bind (.refl _) fun v _ => eval_agrees_of hk (ρ.insert x v) J c'
  | .bind x (.prim op as) c' =>
    rw [eval_bind_prim, eval_bind_prim]
    exact .bind (.refl _) fun v _ => eval_agrees_of hk (ρ.insert x v) J c'
  | .jp j ps r b c' =>
    rw [eval_jp, eval_jp]
    exact eval_agrees_of hk ρ _ c'
  | .jmp j as =>
    rw [eval_jmp, eval_jmp]
    refine Agrees.ofOption _ fun p hp => Agrees.ofOption _ fun vs _ => ?_
    obtain ⟨e, rest⟩ := p
    unfold jumpTo
    split
    · split
      · exact Agrees.later hk fun i i' hi hi' => ih i (by omega) i' (by omega) _ _ e.body
      · next hc =>
        have := jump_measure hp (by simpa using hc)
        exact eval_agrees_of hk _ (e.after rest) e.body
    · exact .refl _
  | .case x alts d =>
    rw [eval_case, eval_case]
    refine Agrees.ofOption _ fun v _ => ?_
    cases v.asCtor P.known with
    | some kf => exact evalAlts_agrees_of hk ρ J kf.1 alts d
    | none => exact .refl _
  | .ret a => rw [eval_ret, eval_ret]; exact .refl _
  | .tcall f as =>
    rw [eval_tcall, eval_tcall]
    exact Agrees.ofOption _ fun vs _ => evalCall_agrees_of P ih hk f vs
  | .trap => rw [eval_trap, eval_trap]; exact .refl _
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

theorem evalAlts_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    Agrees (evalAlts P k' ρ J key alts d) (evalAlts P k ρ J key alts d) := by
  match alts, d with
  | [], some c =>
    rw [evalAlts_nil, evalAlts_nil]
    exact eval_agrees_of hk ρ J c
  | [], none => rw [evalAlts_nil, evalAlts_nil]; exact .refl _
  | .mk key' body :: rest, d =>
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_agrees_of hk ρ J body
    · exact evalAlts_agrees_of hk ρ J key rest d
termination_by Code.altsSize alts + Code.optSize d + jweight J + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)

end

end

/-- Every clock level agrees upward. -/
theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ J c, Agrees (eval P k' ρ J c) (eval P k ρ J c) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ J c; exact eval_agrees_of P ih hk ρ J c

theorem evalCall_agrees {k k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List Val) :
    Agrees (evalCall P k' f vs) (evalCall P k f vs) :=
  evalCall_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk f vs

theorem evalAlts_agrees {k k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    Agrees (evalAlts P k' ρ J key alts d) (evalAlts P k ρ J key alts d) :=
  evalAlts_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk ρ J key alts d

/-- **Clock monotonicity** of Fir evaluation. -/
theorem eval_mono (ρ : Env) (J : List JEntry) (c : Code) : ClockMono fun k => eval P k ρ J c :=
  Result.Agrees.clockMono fun k k' hk => eval_agrees P k k' hk ρ J c

theorem evalAlts_mono (ρ : Env) (J : List JEntry) (key : Key.CtorKey) (alts : List Alt)
    (d : Option Code) : ClockMono fun k => evalAlts P k ρ J key alts d :=
  Result.Agrees.clockMono fun _ _ hk => evalAlts_agrees P hk ρ J key alts d

theorem evalCall_mono (f : FunId) (vs : List Val) : ClockMono fun k => evalCall P k f vs :=
  Result.Agrees.clockMono fun _ _ hk => evalCall_agrees P hk f vs

theorem callFun_mono (fd : Fun) (vs : List Val) : ClockMono fun k => callFun P k fd vs :=
  Result.Agrees.clockMono fun _ _ hk =>
    callFun_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk fd vs

theorem jumpTo_mono (e : JEntry) (rest : List JEntry) (vs : List Val) :
    ClockMono fun k => jumpTo P k e rest vs := by
  refine Result.Agrees.clockMono fun k k' hk => ?_
  unfold jumpTo
  split
  · split
    · exact Agrees.later hk fun j j' hj hj' => eval_agrees P j j' (by omega) _ _ e.body
    · exact eval_agrees P k k' hk _ _ e.body
  · exact .refl _

/-- **Clock monotonicity** of a Fir run. -/
theorem run_mono (f : FunId) (args : List Val) : ClockMono fun k => run P k f args :=
  evalCall_mono P f args

end IxCC.Fir
