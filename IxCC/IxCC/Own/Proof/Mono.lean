import IxCC.Own.Proof.Unfold
import IxCC.Sem.SimUpTo

/-! # Own: clock monotonicity

`Own.eval_mono`: under either allocation policy, an outcome of `eval`
other than `timeout` is the outcome at every larger clock, and likewise for
`evalAlts`, `evalCall`, the call and jump helpers and `run`. Strong
induction on the clock; within one clock, well-founded induction on the
evaluator's measure (code size plus the uncharged join bodies on the
stack), as for Fir (`Fir.Proof.Mono`). The proofs read the evaluator only
through its bind-form equations (`Own.Proof.Unfold`). -/

set_option autoImplicit false

namespace IxCC.Own

open IxCC.Sem (Result ClockMono later)
open IxCC.Sem.Result (Agrees)
open IxCC.Fir (Var FunId JoinId Arg)

variable (pol : AllocPol) (P : Program)

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

/-- The measure of a free jump (as `Fir.jump_measure`). -/
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
  (ih : ∀ j < k, ∀ j', j ≤ j' → ∀ ρ J H c, Agrees (eval pol P j' ρ J H c) (eval pol P j ρ J H c))
include ih

theorem callFun_agrees_of {k' : Nat} (hk : k ≤ k') (fd : Fun) (vs : List RVal) (H : Heap) :
    Agrees (callFun pol P k' fd vs H) (callFun pol P k fd vs H) := by
  unfold callFun
  split
  · exact Agrees.later hk fun j j' hj hj' => ih j (by omega) j' (by omega) _ [] H fd.body
  · exact .refl _

theorem evalCall_agrees_of {k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List RVal) (H : Heap) :
    Agrees (evalCall pol P k' f vs H) (evalCall pol P k f vs H) := by
  rw [evalCall_eq, evalCall_eq]
  exact Agrees.ofOption _ fun fd _ => callFun_agrees_of pol P ih hk fd vs H

mutual

theorem eval_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry) (H : Heap) (c : Code) :
    Agrees (eval pol P k' ρ J H c) (eval pol P k ρ J H c) := by
  match c with
  | .bind x r c' =>
    by_cases hr : ∃ f as, r = .fir (.call f as)
    · obtain ⟨f, as, rfl⟩ := hr
      rw [eval_bindCall, eval_bindCall]
      exact Agrees.ofOption _ fun vs _ => .bind (evalCall_agrees_of pol P ih hk f vs H) fun p _ =>
        eval_agrees_of hk (ρ.insert x p.1) J p.2 c'
    · have hr' : ∀ f as, r ≠ .fir (.call f as) := fun f as h => hr ⟨f, as, h⟩
      rw [eval_bindRhs _ _ _ _ _ _ _ _ _ hr', eval_bindRhs _ _ _ _ _ _ _ _ _ hr']
      exact .bind (.refl _) fun p _ => eval_agrees_of hk (ρ.insert x p.1) J p.2 c'
  | .jp j ps φ r b c' =>
    rw [eval_jp, eval_jp]
    exact eval_agrees_of hk ρ _ H c'
  | .jmp j as =>
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
    cases v.asCtor P.known H with
    | some kf => exact evalAlts_agrees_of hk ρ J H kf.1 alts d
    | none => exact .refl _
  | .ret a => rw [eval_ret, eval_ret]; exact .refl _
  | .tcall f as =>
    rw [eval_tcall, eval_tcall]
    exact Agrees.ofOption _ fun vs _ => evalCall_agrees_of pol P ih hk f vs H
  | .trap => rw [eval_trap, eval_trap]; exact .refl _
termination_by c.size + jweight J
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Code.size]; omega)
    | (simp only [Code.size, jweight, JEntry.weight, Bool.false_eq_true, ↓reduceIte]; omega)
    | (simp only [Code.size] at this ⊢; omega)

theorem evalAlts_agrees_of {k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry) (H : Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    Agrees (evalAlts pol P k' ρ J H key alts d) (evalAlts pol P k ρ J H key alts d) := by
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

/-- Every clock level agrees upward. -/
theorem eval_agrees : ∀ k k', k ≤ k' → ∀ ρ J H c,
    Agrees (eval pol P k' ρ J H c) (eval pol P k ρ J H c) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih => intro k' hk ρ J H c; exact eval_agrees_of pol P ih hk ρ J H c

theorem evalCall_agrees {k k' : Nat} (hk : k ≤ k') (f : FunId) (vs : List RVal) (H : Heap) :
    Agrees (evalCall pol P k' f vs H) (evalCall pol P k f vs H) :=
  evalCall_agrees_of pol P (fun j _ j' hj => eval_agrees pol P j j' hj) hk f vs H

theorem evalAlts_agrees {k k' : Nat} (hk : k ≤ k') (ρ : Env) (J : List JEntry) (H : Heap)
    (key : Key.CtorKey) (alts : List Alt) (d : Option Code) :
    Agrees (evalAlts pol P k' ρ J H key alts d) (evalAlts pol P k ρ J H key alts d) :=
  evalAlts_agrees_of pol P (fun j _ j' hj => eval_agrees pol P j j' hj) hk ρ J H key alts d

/-- **Clock monotonicity** of Own evaluation, under either policy. -/
theorem eval_mono (ρ : Env) (J : List JEntry) (H : Heap) (c : Code) :
    ClockMono fun k => eval pol P k ρ J H c :=
  Result.Agrees.clockMono fun k k' hk => eval_agrees pol P k k' hk ρ J H c

theorem evalAlts_mono (ρ : Env) (J : List JEntry) (H : Heap) (key : Key.CtorKey) (alts : List Alt)
    (d : Option Code) : ClockMono fun k => evalAlts pol P k ρ J H key alts d :=
  Result.Agrees.clockMono fun _ _ hk => evalAlts_agrees pol P hk ρ J H key alts d

theorem evalCall_mono (f : FunId) (vs : List RVal) (H : Heap) :
    ClockMono fun k => evalCall pol P k f vs H :=
  Result.Agrees.clockMono fun _ _ hk => evalCall_agrees pol P hk f vs H

theorem callFun_mono (fd : Fun) (vs : List RVal) (H : Heap) :
    ClockMono fun k => callFun pol P k fd vs H :=
  Result.Agrees.clockMono fun _ _ hk =>
    callFun_agrees_of pol P (fun j _ j' hj => eval_agrees pol P j j' hj) hk fd vs H

theorem jumpTo_mono (e : JEntry) (rest : List JEntry) (vs : List RVal) (H : Heap) :
    ClockMono fun k => jumpTo pol P k e rest vs H := by
  refine Result.Agrees.clockMono fun k k' hk => ?_
  unfold jumpTo
  split
  · split
    · exact Agrees.later hk fun j j' hj hj' => eval_agrees pol P j j' (by omega) _ _ H e.body
    · exact eval_agrees pol P k k' hk _ _ H e.body
  · exact .refl _

/-- **Clock monotonicity** of an Own run, under either policy. -/
theorem run_mono (f : FunId) (args : List RVal) (H : Heap) :
    ClockMono fun k => run pol P k f args H :=
  evalCall_mono pol P f args H

end IxCC.Own
