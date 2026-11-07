import IxCC.Own.Plain.Proof.Unfold
import IxCC.Sem.SimUpTo

/-! Clock monotonicity of the actual scratch RC evaluator, including action
stuttering and the first-free/recursive-charged join discipline. -/

set_option autoImplicit false
namespace IxCC.Own.Plain
open IxCC.Sem (Result ClockMono later)
open IxCC.Sem.Result (Agrees)
open IxCC.Fir (Var FunId JoinId Arg)

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
  (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J H c, Agrees (eval P j' ρ J H c) (eval P j ρ J H c))
include ih

theorem callFun_agrees_of {k' : Nat} (hk : k ≤ k') (fd : Fir.Fun) (body : Code)
    (vs : List RVal) (H : Heap) :
    Agrees (callFun P k' fd body vs H) (callFun P k fd body vs H) := by
  unfold callFun
  split
  · exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ [] H body
  · exact .refl _

theorem evalCall_agrees_of {k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List RVal) (H : Heap) :
    Agrees (evalCall P k' f vs H) (evalCall P k f vs H) := by
  rw [evalCall_eq, evalCall_eq]
  exact Agrees.ofOption _ fun fd _ => Agrees.ofOption _ fun body _ =>
    callFun_agrees_of P ih hk fd body vs H

mutual
theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Own.Env) (J : List JEntry) (H : Heap) (c : Code) :
    Agrees (eval P k' ρ J H c) (eval P k ρ J H c) := by
  match c with
  | .act a c' =>
    rw [eval_act, eval_act]
    exact .bind (.refl _) fun H' _ => eval_agrees_of hk ρ J H' c'
  | .bind x r c' =>
    by_cases hr : ∃ f args, r = .call f args
    · obtain ⟨f, args, rfl⟩ := hr
      rw [eval_bindCall, eval_bindCall]
      exact Agrees.ofOption _ fun vs _ => .bind (evalCall_agrees_of P ih hk f vs H) fun p _ =>
        eval_agrees_of hk (ρ.insert x p.1) J p.2 c'
    · have hr' : ∀ f args, r ≠ .call f args := fun f args h => hr ⟨f, args, h⟩
      rw [eval_bindRhs _ _ _ _ _ _ _ _ hr', eval_bindRhs _ _ _ _ _ _ _ _ hr']
      exact .bind (.refl _) fun p _ => eval_agrees_of hk (ρ.insert x p.1) J p.2 c'
  | .jp j ps captured rec body c' =>
    rw [eval_jp, eval_jp]
    exact eval_agrees_of hk ρ _ H c'
  | .jmp j args =>
    rw [eval_jmp, eval_jmp]
    refine Agrees.ofOption _ fun p hp => Agrees.ofOption _ fun vs _ => ?_
    obtain ⟨e, rest⟩ := p
    unfold jumpTo
    split
    · split
      · exact Agrees.later hk fun i i' hi hi' => ih i (by omega) i' (by omega) _ _ H e.body
      · next hc =>
        have := jump_measure hp (by simpa using hc)
        exact eval_agrees_of hk _ (e.after rest) H e.body
    · exact .refl _
  | .case x alts d =>
    rw [eval_case, eval_case]
    refine Agrees.ofOption _ fun v _ => ?_
    cases v.asCtor P.source.known H with
    | some kf => exact evalAlts_agrees_of hk ρ J H kf.1 alts d
    | none => exact .refl _
  | .ret a => rw [eval_ret, eval_ret]; exact .refl _
  | .tcall f args =>
    rw [eval_tcall, eval_tcall]
    exact Agrees.ofOption _ fun vs _ => evalCall_agrees_of P ih hk f vs H
  | .trap => rw [eval_trap, eval_trap]; exact .refl _
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

theorem evalAlts_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Own.Env) (J : List JEntry) (H : Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    Agrees (evalAlts P k' ρ J H key alts d) (evalAlts P k ρ J H key alts d) := by
  match alts, d with
  | [], some c =>
    rw [evalAlts_nil, evalAlts_nil]
    exact eval_agrees_of hk ρ J H c
  | [], none => rw [evalAlts_nil, evalAlts_nil]; exact .refl _
  | .mk key' body :: rest, d =>
    rw [evalAlts_cons, evalAlts_cons]
    split
    · exact eval_agrees_of hk ρ J H body
    · exact evalAlts_agrees_of hk ρ J H key rest d
termination_by Code.altsSize alts + Code.optSize d + jweight J + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [Code.altsSize, Code.optSize]
  all_goals first
    | omega
    | (have := Code.size_pos body; omega)
end
end

theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ J H c,
    Agrees (eval P k' ρ J H c) (eval P k ρ J H c) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ J H c; exact eval_agrees_of P ih hk ρ J H c

theorem evalCall_agrees {k k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List RVal) (H : Heap) :
    Agrees (evalCall P k' f vs H) (evalCall P k f vs H) :=
  evalCall_agrees_of P (fun j _ j' hj => eval_agrees P j j' hj) hk f vs H

theorem eval_mono (ρ : Own.Env) (J : List JEntry) (H : Heap) (c : Code) :
    ClockMono fun k => eval P k ρ J H c :=
  Result.Agrees.clockMono fun k k' hk => eval_agrees P k k' hk ρ J H c

theorem run_mono (f : FunId) (args : List RVal) (H : Heap) :
    ClockMono fun k => run P k f args H :=
  Result.Agrees.clockMono fun _ _ hk => evalCall_agrees P hk f args H


end IxCC.Own.Plain
