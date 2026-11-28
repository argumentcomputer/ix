import IxCC.Xv.Validate.Proof.Match

/-!
# Calls, and instructions by form

The validator's call check decoded (`call_check`): arguments and results
exactly where the convention puts them, distinct results, and the argument
registers known at their locations; so the Xl call reads the same argument
values (`readAll_of_holds`). `inst_sound` dispatches a non-call
instruction to its form's lemma.
-/

namespace IxCC.Xv.Validate

open IxCC.Lir (VReg Word Env Label FunId)
open IxCC.Xv.Alloc (Edit Output BlockOut)
open IxCC.Xv

set_option linter.unusedSimpArgs false in
/-- What the validator checks of a call. -/
theorem call_check {c : Ctx} {a a' : AState} {g : FunId} {args rets : List VReg} {ls : List Loc}
    (h : stepInst c a (.call g args rets) ls = .ok a') :
    ls.length = args.length + rets.length ∧ rets.length ≤ Xl.nResultRegs ∧ rets.Nodup ∧
      ls.take args.length = argLocs args.length ∧ ls.drop args.length = resultLocs rets.length ∧
      (args.zip (argLocs args.length)).all (fun p => a.holds p.2 p.1) = true ∧
      a' = (a.clearOutArgs).define (rets.zip (resultLocs rets.length)) ((c.env.clobbers g).map Loc.reg) := by
  simp only [stepInst, bind, Except.bind] at h
  cases h₁ : ((Inst.call g args rets).operands.length == ls.length) <;>
    simp only [h₁, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  by_cases h₂ : rets.length ≤ Xl.nResultRegs <;>
    simp only [h₂, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq, decide_true, decide_false] at h
  cases h₃ : nodup rets <;>
    simp only [h₃, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₄ : (ls.take args.length == argLocs args.length && ls.drop args.length == resultLocs rets.length) <;>
    simp only [h₄, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  cases h₅ : (args.zip (argLocs args.length)).all (fun p => a.holds p.2 p.1) <;>
    simp only [h₅, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw, reduceCtorEq, Except.ok.injEq] at h
  simp only [Inst.operands, conUses, conDefs, List.length_append, List.length_map, List.length_zipIdx,
    beq_iff_eq] at h₁
  simp only [Bool.and_eq_true, beq_iff_eq] at h₄
  exact ⟨h₁.symm, h₂, nodup_iff.1 h₃, h₄.1, h₄.2, rfl, h.symm⟩

theorem argLocs_length (n : Nat) : (argLocs n).length = n := by simp [argLocs]

theorem resultLocs_length {n : Nat} (h : n ≤ Xl.nResultRegs) : (resultLocs n).length = n := by
  have : n ≤ 2 := h
  rcases n with _ | _ | _ | n <;> first | rfl | omega

/-- A call's arguments read at their convention locations. -/
theorem readAll_of_holds {a : AState} {ρ : Env} {regs : Xl.Regs} {fr : Xl.Frame}
    (hag : a.Agree ρ (Xl.read regs fr)) :
    ∀ {vs : List VReg} {ls : List Loc} {vals : List Word}, vs.length = ls.length →
      (vs.zip ls).all (fun p => a.holds p.2 p.1) = true → vs.mapM (ρ[·]?) = some vals →
      Xl.readAll regs fr ls = some vals
  | [], [], vals, _, _, h => by simp at h; subst h; rfl
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | v :: vs, l :: ls, vals, hl, hh, hm => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hh
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at hm
      obtain ⟨w, hw, ws, hws, rfl⟩ := hm
      obtain ⟨w', hw', hr⟩ := hag.holds hh.1
      rw [hw] at hw'
      cases hw'
      have := readAll_of_holds hag (by simpa using hl) hh.2 hws
      simp only [Xl.readAll, List.mapM_cons] at this ⊢
      simp [hr, this]

theorem conventionArgs_argLocs (n : Nat) : Xl.conventionArgs (argLocs n) = true := by
  simp [Xl.conventionArgs, argLocs]

theorem conventionResults_resultLocs {n : Nat} (h : n ≤ Xl.nResultRegs) :
    Xl.conventionResults (resultLocs n) = true := by
  simp only [Xl.conventionResults, resultLocs_length h, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨h, rfl⟩

/-- A call's substituted form. -/
theorem call_substitute {g : FunId} {args rets : List VReg} {ls : List Loc} {x : Inst Loc}
    (h : (Inst.call g args rets).substitute ls = some x) :
    x = .call g (ls.take args.length) (ls.drop args.length) := by
  simp only [Inst.substitute] at h
  split at h
  · simpa using h.symm
  · simp at h

/-- A non-call instruction under the validator's transfer. -/
theorem inst_sound {c : Ctx} {a a' : AState} {inst : Inst VReg} {ls : List Loc} {x : Inst Loc}
    (hnc : ∀ g args rets, inst ≠ .call g args rets)
    (hv : stepInst c a inst ls = .ok a') (hsub : inst.substitute ls = some x)
    {ρ ρ' : Env} {regs : Xl.Regs} {fr : Xl.Frame} {mem mem' : X86.Memory} {ctx : Word}
    (hagree : a.Agree ρ (Xl.read regs fr)) (hsize : regs.size = 16) (hin : fr.inArgs.size = c.stackParams)
    (hxv : inst.exec ρ mem ctx = some (ρ', mem')) :
    (∀ g args rets, x ≠ .call g args rets) ∧
    ∃ regs' fr', Xl.execInst regs fr mem ctx x = some (regs', fr', mem') ∧ regs'.size = 16 ∧
      Xl.Frame.SameCtl fr fr' ∧ a'.Agree ρ' (Xl.read regs' fr') := by
  have hshape : ∀ g args rets, x ≠ .call g args rets := by
    intro g args rets e
    subst e
    cases inst with
    | call g' a r => exact hnc g' a r rfl
    | op o d r =>
      simp only [Inst.substitute, Option.bind_eq_bind, Option.bind_eq_some_iff] at hsub
      obtain ⟨_, -, h⟩ := hsub
      simp [guard, pure] at h
      try (split at h <;> simp_all [failure])
    | fused p pa c' d ca =>
      simp only [Inst.substitute, Option.bind_eq_bind, Option.bind_eq_some_iff] at hsub
      obtain ⟨_, -, _, -, h⟩ := hsub
      simp [guard, pure] at h
      try (split at h <;> simp_all [failure])
    | move d s => rcases ls with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp [Inst.substitute] at hsub
    | zero y => rcases ls with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp [Inst.substitute] at hsub
  refine ⟨hshape, ?_⟩
  cases inst with
  | call g' a r => exact absurd rfl (hnc g' a r)
  | op o d r => exact op_sound hv hsub hagree hsize hin hxv
  | fused p pa c' d ca => exact fused_sound hv hsub hagree hsize hin hxv
  | move d s => exact move_sound hv hsub hagree hsize hin hxv
  | zero y => exact zero_sound hv hsub hagree hsize hxv

end IxCC.Xv.Validate
