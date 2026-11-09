import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarBasic
import IxCC.Rt.Proof.OpsDiv

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

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
      by_cases hw3 : wbi = 3
      · subst hw3
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign x (.arg la)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
          hlive (by decide) (fun p q => if q = 0 then 0 else p / q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq1 : q = 1 := (natWord_eq_three hwb).1 rfl
        subst hq1
        exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), div1_word hwa, by simp, fun y hy hyx => by regs_ne⟩
      · have hw3' : (wbi == 3) = false := by simpa using hw3
        by_cases hw5 : wbi = 5
        · subst hw5
          cases la with
          | v ya =>
            lower_run at hrun
            simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v ya) (.imm 1)),
                .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
            subst hq2
            have ha' : ρl[ya]? = some wa := ha
            have hya := hra ya rfl
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha', ↓reduceIte, if_neg]; try rfl),
              div2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          | imm wai =>
            lower_run at hrun
            simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign x (.bin .or .w64 (.imm (wai >>> 1)) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb _ _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
            subst ha hb
            have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
            subst hq2
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg]; try rfl),
              div2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
        · have hw5' : (wbi == 5) = false := by simpa using hw5
          by_cases hw9 : wbi = 9
          · subst hw9
            lower_run at hrun
            simp only [hw', hw3', hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 la (.imm 2)),
                .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))])
              hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide)
              (fun p q => if q = 0 then 0 else p / q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq4 : q = 4 := (natWord_eq_nine hwb).1 rfl
            subst hq4
            exact ⟨_, _, by (simp (disch := omega) only [lir_eval, ha, show (2 &&& 63 : Word) = 2 from rfl, ↓reduceIte]; try rfl),
              div4_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          · have hw9' : (wbi == 9) = false := by simpa using hw9
            cases la with
            | v ya =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
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
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
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
      by_cases hw3 : wbi = 3
      · subst hw3
        lower_run at hrun
        simp only [hw', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine prim2_sim (ss := [.assign x (.arg (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
          hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
        intro ρl mem p q wa wb ha hb hwa hwb hra _
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
        subst hb
        have hq1 : q = 1 := (natWord_eq_three hwb).1 rfl
        subst hq1
        exact ⟨_, _, by (simp only [lir_eval]; try rfl), mod1_word, by simp, fun y hy hyx => by regs_ne⟩
      · have hw3' : (wbi == 3) = false := by simpa using hw3
        by_cases hw5 : wbi = 5
        · subst hw5
          lower_run at hrun
          simp only [hw', hw3', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
          lower_run at hrun
          subst hrun
          refine prim2_sim (ss := [.assign x (.bin .and .w64 la (.imm 3))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
            hsup hx hops hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
          intro ρl mem p q wa wb ha hb hwa hwb hra _
          simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
          subst hb
          have hq2 : q = 2 := (natWord_eq_five hwb).1 rfl
          subst hq2
          exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod2_word hwa, by simp, fun y hy hyx => by regs_ne⟩
        · have hw5' : (wbi == 5) = false := by simpa using hw5
          by_cases hw9 : wbi = 9
          · subst hw9
            lower_run at hrun
            simp only [hw', hw3', hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
            lower_run at hrun
            subst hrun
            refine prim2_sim (ss := [.assign x (.bin .and .w64 la (.imm 7))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
              hsup hx hops hlive (by decide) (fun p q => if q = 0 then p else p % q) hsem ?_
            intro ρl mem p q wa wb ha hb hwa hwb hra _
            simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
            subst hb
            have hq4 : q = 4 := (natWord_eq_nine hwb).1 rfl
            subst hq4
            exact ⟨_, _, by (simp only [lir_eval, ha]; try rfl), mod4_word hwa, by simp, fun y hy hyx => by regs_ne⟩
          · have hw9' : (wbi == 9) = false := by simpa using hw9
            cases la with
            | v ya =>
              lower_run at hrun
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
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
              simp only [hw', hw3', hw5', hw9', Bool.false_eq_true, ↓reduceIte] at hrun
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


end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
