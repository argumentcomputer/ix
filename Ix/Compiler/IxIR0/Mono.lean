import Ix.Compiler.Fuel
import Ix.Compiler.IxIR0.Eval

/-!
# Fuel monotonicity for the IxIR₀ interpreter

The workhorse lemma of the erasure-simulation work: a successful
evaluation stays successful (with the same value) under more fuel.
This is what lets a proof combine sub-derivations obtained at
different fuels — lift everything to the max. Proved for all four
mutual functions at once by induction on fuel; the uniform
decrement-at-entry discipline keeps the induction shape trivial.
-/

namespace Ix.Compiler.IxIR0

/-- `Except`-bind reduction on a success (definitional; core has no
named lemma for it). -/
private theorem bindOk {α β : Type} (a : α) (f : α → Except Err β) :
    (Except.ok a >>= f) = f a := rfl

/-- `Except`-bind reduction on an error. -/
private theorem bindErr {α β : Type} (e : Err) (f : α → Except Err β) :
    ((Except.error e : Except Err α) >>= f) = Except.error e := rfl

private def MonoAt (fuel : Nat) : Prop :=
  (∀ ctx ρ e v, eval ctx fuel ρ e = .ok v → eval ctx (fuel + 1) ρ e = .ok v) ∧
  (∀ ctx f a v, apply ctx fuel f a = .ok v → apply ctx (fuel + 1) f a = .ok v) ∧
  (∀ ctx h args v, saturate ctx fuel h args = .ok v →
    saturate ctx (fuel + 1) h args = .ok v) ∧
  (∀ ctx h args v, fire ctx fuel h args = .ok v →
    fire ctx (fuel + 1) h args = .ok v)

private theorem monoAt : ∀ fuel, MonoAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx ρ e v h; rw [eval.eq_def] at h; simp at h
    · intro ctx f a v h; rw [apply.eq_def] at h; simp at h
    · intro ctx hd args v h; rw [saturate.eq_def] at h; simp at h
    · intro ctx hd args v h; rw [fire.eq_def] at h; simp at h
  | succ n ihn =>
    obtain ⟨ihE, ihA, ihS, ihF⟩ := ihn
    refine ⟨?_, ?_, ?_, ?_⟩
    -- eval
    · intro ctx ρ e v h
      cases e with
      | var i =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢; exact h
      | lit l =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢; exact h
      | erased =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢; exact h
      | lam u body =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢; exact h
      | letE u val body =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢
        cases hval : eval ctx n ρ val with
        | error err => rw [hval, bindErr] at h; simp at h
        | ok w =>
          rw [hval, bindOk] at h
          rw [ihE _ _ _ _ hval, bindOk]
          exact ihE _ _ _ _ h
      | app fn arg =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢
        cases hf : eval ctx n ρ fn with
        | error err => rw [hf, bindErr] at h; simp at h
        | ok fv =>
          rw [hf, bindOk] at h
          rw [ihE _ _ _ _ hf, bindOk]
          cases ha : eval ctx n ρ arg with
          | error err => rw [ha, bindErr] at h; simp at h
          | ok av =>
            rw [ha, bindOk] at h
            rw [ihE _ _ _ _ ha, bindOk]
            exact ihA _ _ _ _ h
      | proj i s =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢
        cases hs : eval ctx n ρ s with
        | error err => rw [hs, bindErr] at h; simp at h
        | ok w =>
          rw [hs, bindOk] at h
          rw [ihE _ _ _ _ hs, bindOk]
          exact h
      | ref a =>
        rw [eval.eq_def] at h; rw [eval.eq_def]; dsimp only at h ⊢
        split at h
        · exact h
        · exact ihE _ _ _ _ h
        · exact ihS _ _ _ _ h
        · exact h
        · exact ihS _ _ _ _ h
    -- apply
    · intro ctx f a v h
      cases f with
      | clos u ρ body =>
        rw [apply.eq_def] at h; rw [apply.eq_def]; dsimp only at h ⊢
        exact ihE _ _ _ _ h
      | pap hd args =>
        rw [apply.eq_def] at h; rw [apply.eq_def]; dsimp only at h ⊢
        exact ihS _ _ _ _ h
      | erased =>
        rw [apply.eq_def] at h; rw [apply.eq_def]; dsimp only at h ⊢; exact h
      | ctor adr tag args =>
        rw [apply.eq_def] at h; rw [apply.eq_def]; dsimp only at h ⊢; exact h
      | lit l =>
        rw [apply.eq_def] at h; rw [apply.eq_def]; dsimp only at h ⊢; exact h
    -- saturate
    · intro ctx hd args v h
      rw [saturate.eq_def] at h; rw [saturate.eq_def]; dsimp only at h ⊢
      cases hc : args.length == hd.arity
      · simp only [hc] at h ⊢
        simp at h ⊢
        exact h
      · simp only [hc] at h ⊢
        simp at h ⊢
        exact ihF _ _ _ _ h
    -- fire
    · intro ctx hd args v h
      cases hd with
      | ctor a tag ar =>
        rw [fire.eq_def] at h; rw [fire.eq_def]; dsimp only at h ⊢; exact h
      | ext a ar =>
        rw [fire.eq_def] at h; rw [fire.eq_def]; dsimp only at h ⊢; exact h
      | rec_ a ar =>
        rw [fire.eq_def] at h; rw [fire.eq_def]; dsimp only at h ⊢
        split at h
        · rename_i natLit rules heq
          split at h
          · exact h
          · rename_i major heq'
            cases hmc : majorCtor natLit major with
            | error err => rw [hmc, bindErr] at h; simp at h
            | ok tf =>
              obtain ⟨tag, fields⟩ := tf
              rw [hmc, bindOk] at h
              rw [bindOk]
              dsimp only at h ⊢
              split at h
              · exact h
              · rename_i rule heq''
                split at h
                · rename_i hc
                  rw [if_pos hc]
                  exact h
                · rename_i hc
                  rw [if_neg hc]
                  exact ihE _ _ _ _ h
        · exact h

/-- Success is stable under raising fuel (`eval`). -/
theorem eval_mono {ctx : Ctx} {fuel fuel' : Nat} {ρ : List Value} {e : Expr}
    {v : Value} (hle : fuel ≤ fuel') (h : eval ctx fuel ρ e = .ok v) :
    eval ctx fuel' ρ e = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).1 _ _ _ _ hrun) hle h

/-- Success is stable under raising fuel (`apply`). -/
theorem apply_mono {ctx : Ctx} {fuel fuel' : Nat} {f a v : Value}
    (hle : fuel ≤ fuel') (h : apply ctx fuel f a = .ok v) :
    apply ctx fuel' f a = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.1 _ _ _ _ hrun) hle h

end Ix.Compiler.IxIR0
