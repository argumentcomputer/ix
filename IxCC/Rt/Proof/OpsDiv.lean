import IxCC.Rt.Proof.Ops

/-!
# `natDiv` and `natMod`

`Rt.lower`'s `divMod` untags both operands, divides by a nonzero divisor
(`1` in place of a zero one), retags, and selects `n / 0 = 0`
(`n % 0 = n`) for a zero divisor; an immediate divisor folds (a zero one
gives the result directly). One lemma per operation covers every operand
shape.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

theorem untag_ne_zero {q : Nat} {wb : Word} (hb : natWord q = some wb) (hq : q ≠ 0) : wb >>> 1 ≠ 0 := by
  intro h
  have := untag_toNat hb
  rw [h] at this
  exact hq (by simpa using this.symm)

theorem word_one_ne_zero : (1 : Word) ≠ 0 := by decide

theorem mod_word0 {p : Nat} {wa : Word} (h : natWord p = some wa) :
    natWord (if (0 : Nat) = 0 then p else p % 0) = some wa := by
  simpa using h

theorem div_word0 {p : Nat} : natWord (if (0 : Nat) = 0 then 0 else p / 0) = some 1 := by
  simp; exact natWord_of_lt (by decide)

theorem div_word {p q : Nat} {wa wb : Word} (hwa : natWord p = some wa) (hwb : natWord q = some wb) (hq : q ≠ 0) :
    natWord (if q = 0 then 0 else p / q) = some ((wa >>> 1) / (wb >>> 1) + (wa >>> 1) / (wb >>> 1) + 1) := by
  simp only [hq, ↓reduceIte]; exact natDiv_word hwa hwb hq

theorem mod_word {p q : Nat} {wa wb : Word} (hwa : natWord p = some wa) (hwb : natWord q = some wb) (hq : q ≠ 0) :
    natWord (if q = 0 then p else p % q) = some ((wa >>> 1) % (wb >>> 1) + (wa >>> 1) % (wb >>> 1) + 1) := by
  simp only [hq, ↓reduceIte]; exact natMod_word hwa hwb hq

theorem prim_natDiv {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natDiv [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natDiv as)) := by
  have hsem := sem_nat2 .natDiv (by decide)
  cases lb with
  | imm wbi =>
    by_cases hw : wbi = 1
    · subst hw
      lower_run at hrun
      simp only [beq_self_eq_true, ↓reduceIte] at hrun
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign x (.arg (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
        hlive (by decide) (fun p q => if q = 0 then 0 else p / q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra _
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
      subst hb
      have hq0 : q = 0 := (natWord_eq_one hwb).1 rfl
      subst hq0
      exact ⟨_, _, by (simp only [lir_eval]; try rfl), div_word0, by simp, fun y hy hyx => by regs_ne⟩
    · have hw' : (wbi == 1) = false := by simpa using hw
      cases la with
      | v ya =>
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
            .assign (st.fresh + 1) (.bin .udiv .w64 (.v st.fresh) (.imm (wbi >>> 1))),
            .assign x (.addr { base := some (.v (st.fresh + 1)), index := some (st.fresh + 1, .one), disp := 1 })])
          hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
          (fun p q => if q = 0 then 0 else p / q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
        have ha' : ρl[ya]? = some wa := ha
        have hya := hra ya rfl
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', untag_ne_zero hwb hq, ↓reduceIte, if_neg,
          UInt64.mul_one]; try rfl), div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
      | imm wai =>
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign st.fresh (.bin .udiv .w64 (.imm (wai >>> 1)) (.imm (wbi >>> 1))),
            .assign x (.addr { base := some (.v st.fresh), index := some (st.fresh, .one), disp := 1 })])
          hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
          (fun p q => if q = 0 then 0 else p / q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb _ _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
        subst ha hb
        have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, untag_ne_zero hwb hq, ↓reduceIte, if_neg,
          UInt64.mul_one]; try rfl), div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
  | v yb =>
    cases la with
    | v ya =>
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
          .assign (st.fresh + 1) (.bin .shr .w64 (.v yb) (.imm 1)),
          .assign (st.fresh + 1 + 1) (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v (st.fresh + 1))),
          .assign (st.fresh + 1 + 1 + 1) (.bin .udiv .w64 (.v st.fresh) (.v (st.fresh + 1 + 1))),
          .assign (st.fresh + 1 + 1 + 1 + 1) (.addr { base := some (.v (st.fresh + 1 + 1 + 1)), index := some (st.fresh + 1 + 1 + 1, .one), disp := 1 }),
          .assign x (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v (st.fresh + 1 + 1 + 1 + 1)))])
        hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
        (fun p q => if q = 0 then 0 else p / q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra hrb
      have ha' : ρl[ya]? = some wa := ha
      have hb' : ρl[yb]? = some wb := hb
      have hya := hra ya rfl
      have hyb := hrb yb rfl
      by_cases hq : q = 0
      · subst hq
        have hw1 : wb = 1 := (natWord_eq_one hwb).2 rfl
        subst hw1
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', hb', ↓reduceIte, if_neg, UInt64.mul_one, word_one_ne_zero]
          <;> try rfl), div_word0, by simp, fun y hy hyx => by regs_ne⟩
      · have hw1 : wb ≠ 1 := fun h => hq ((natWord_eq_one hwb).1 h)
        have hne := untag_ne_zero hwb hq
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', hb', ↓reduceIte, if_neg, UInt64.mul_one, hw1, hne]
          <;> try rfl), div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
    | imm wai =>
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v yb) (.imm 1)),
          .assign (st.fresh + 1) (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v st.fresh)),
          .assign (st.fresh + 1 + 1) (.bin .udiv .w64 (.imm (wai >>> 1)) (.v (st.fresh + 1))),
          .assign (st.fresh + 1 + 1 + 1) (.addr { base := some (.v (st.fresh + 1 + 1)), index := some (st.fresh + 1 + 1, .one), disp := 1 }),
          .assign x (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v (st.fresh + 1 + 1 + 1)))])
        hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
        (fun p q => if q = 0 then 0 else p / q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra hrb
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
      subst ha
      have hb' : ρl[yb]? = some wb := hb
      have hyb := hrb yb rfl
      by_cases hq : q = 0
      · subst hq
        have hw1 : wb = 1 := (natWord_eq_one hwb).2 rfl
        subst hw1
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, hb', ↓reduceIte, if_neg, UInt64.mul_one, word_one_ne_zero]
          <;> try rfl), div_word0, by simp, fun y hy hyx => by regs_ne⟩
      · have hw1 : wb ≠ 1 := fun h => hq ((natWord_eq_one hwb).1 h)
        have hne := untag_ne_zero hwb hq
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, hb', ↓reduceIte, if_neg, UInt64.mul_one, hw1, hne]; try rfl),
          div_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩

theorem prim_natMod {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natMod [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natMod as)) := by
  have hsem := sem_nat2 .natMod (by decide)
  cases lb with
  | imm wbi =>
    by_cases hw : wbi = 1
    · subst hw
      lower_run at hrun
      simp only [beq_self_eq_true, ↓reduceIte] at hrun
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
        hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra _
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
      subst hb
      have hq0 : q = 0 := (natWord_eq_one hwb).1 rfl
      subst hq0
      exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod_word0 hwa, by simp, fun y hy hyx => by regs_ne⟩
    · have hw' : (wbi == 1) = false := by simpa using hw
      cases la with
      | v ya =>
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
            .assign (st.fresh + 1) (.bin .urem .w64 (.v st.fresh) (.imm (wbi >>> 1))),
            .assign x (.addr { base := some (.v (st.fresh + 1)), index := some (st.fresh + 1, .one), disp := 1 })])
          hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
          (fun p q => if q = 0 then p else p % q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
        have ha' : ρl[ya]? = some wa := ha
        have hya := hra ya rfl
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', untag_ne_zero hwb hq, ↓reduceIte, if_neg,
          UInt64.mul_one]; try rfl), mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
      | imm wai =>
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign st.fresh (.bin .urem .w64 (.imm (wai >>> 1)) (.imm (wbi >>> 1))),
            .assign x (.addr { base := some (.v st.fresh), index := some (st.fresh, .one), disp := 1 })])
          hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
          (fun p q => if q = 0 then p else p % q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb _ _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
        subst ha hb
        have hq : q ≠ 0 := fun h => hw ((natWord_eq_one hwb).2 h)
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, untag_ne_zero hwb hq, ↓reduceIte, if_neg,
          UInt64.mul_one]; try rfl), mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
  | v yb =>
    cases la with
    | v ya =>
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
          .assign (st.fresh + 1) (.bin .shr .w64 (.v yb) (.imm 1)),
          .assign (st.fresh + 1 + 1) (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v (st.fresh + 1))),
          .assign (st.fresh + 1 + 1 + 1) (.bin .urem .w64 (.v st.fresh) (.v (st.fresh + 1 + 1))),
          .assign (st.fresh + 1 + 1 + 1 + 1) (.addr { base := some (.v (st.fresh + 1 + 1 + 1)), index := some (st.fresh + 1 + 1 + 1, .one), disp := 1 }),
          .assign x (.select .eq .w64 (.v yb) (.imm 1) (.v ya) (.v (st.fresh + 1 + 1 + 1 + 1)))])
        hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
        (fun p q => if q = 0 then p else p % q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra hrb
      have ha' : ρl[ya]? = some wa := ha
      have hb' : ρl[yb]? = some wb := hb
      have hya := hra ya rfl
      have hyb := hrb yb rfl
      by_cases hq : q = 0
      · subst hq
        have hw1 : wb = 1 := (natWord_eq_one hwb).2 rfl
        subst hw1
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', hb', ↓reduceIte, if_neg, UInt64.mul_one, word_one_ne_zero]
          <;> try rfl), mod_word0 hwa, by simp, fun y hy hyx => by regs_ne⟩
      · have hw1 : wb ≠ 1 := fun h => hq ((natWord_eq_one hwb).1 h)
        have hne := untag_ne_zero hwb hq
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', hb', ↓reduceIte, if_neg, UInt64.mul_one, hw1, hne]
          <;> try rfl), mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩
    | imm wai =>
      lower_run at hrun
      subst hrun
      refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v yb) (.imm 1)),
          .assign (st.fresh + 1) (.select .eq .w64 (.v yb) (.imm 1) (.imm 1) (.v st.fresh)),
          .assign (st.fresh + 1 + 1) (.bin .urem .w64 (.imm (wai >>> 1)) (.v (st.fresh + 1))),
          .assign (st.fresh + 1 + 1 + 1) (.addr { base := some (.v (st.fresh + 1 + 1)), index := some (st.fresh + 1 + 1, .one), disp := 1 }),
          .assign x (.select .eq .w64 (.v yb) (.imm 1) (.imm wai) (.v (st.fresh + 1 + 1 + 1)))])
        hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
        (fun p q => if q = 0 then p else p % q) hsem ?_
      intro ρl mem p q wa wb ha hb hwa hwb hra hrb
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
      subst ha
      have hb' : ρl[yb]? = some wb := hb
      have hyb := hrb yb rfl
      by_cases hq : q = 0
      · subst hq
        have hw1 : wb = 1 := (natWord_eq_one hwb).2 rfl
        subst hw1
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, hb', ↓reduceIte, if_neg, UInt64.mul_one, word_one_ne_zero]
          <;> try rfl), mod_word0 hwa, by simp, fun y hy hyx => by regs_ne⟩
      · have hw1 : wb ≠ 1 := fun h => hq ((natWord_eq_one hwb).1 h)
        have hne := untag_ne_zero hwb hq
        exact ⟨_, _, by (simp (disch := omega) only [lir_eval, hb', ↓reduceIte, if_neg, UInt64.mul_one, hw1, hne]; try rfl),
          mod_word hwa hwb hq, by simp, fun y hy hyx => by regs_ne⟩

end IxCC.Rt.Proof
