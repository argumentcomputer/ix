import IxCC.Rt.Proof.Check

/-!
# The checked primitives: `natAdd`, `natMul`, `natShl`

* `natAdd`: `brOvf addC x (a − 1) b`, with an immediate operand folded into
  `imm (w − 1)`; no carry means the sum is the word of `p + q`.
* `natMul`: `p · (b − 1)` checked by division (`Words.natMul_word`).
* `natShl`: `(a − 1) <<< y` checked by shifting back (`Words.natShl_word`).
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

theorem prim_natAdd {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natAdd [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natAdd as)) := by
  have hsem := sem_nat2 .natAdd (by decide)
  have hnb := sem_not_bool .natAdd (by decide)
  cases lb with
  | imm wbi =>
    lower_run at hrun
    subst hrun
    refine check_ovf_sim (ss1 := []) hF hH hC hl ho (by simp) ?_
    intro P H ρ ρl mem v H' _ hρ hr
    obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, _⟩⟩ := bin2_of hρ hops hlive hnb hr
    rw [hsem] at hs
    cases hs
    simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
    subst hb
    refine ⟨rfl, ρl, wa, wbi - 1, rfl, ha, rfl, fun hc => hρ.insert hx ?_⟩
    exact natAdd_word (natAdd_operands hwa hwb).2 hc
  | v yb =>
    cases la with
    | imm wai =>
      lower_run at hrun
      subst hrun
      refine check_ovf_sim (ss1 := []) hF hH hC hl ho (by simp) ?_
      intro P H ρ ρl mem v H' _ hρ hr
      obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, _, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
      rw [hsem] at hs
      cases hs
      simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
      subst ha
      refine ⟨rfl, ρl, wb, wai - 1, rfl, hb, rfl, fun hc => hρ.insert hx ?_⟩
      have := (natAdd_operands hwa hwb).1
      exact natAdd_word (by omega) hc
    | v ya =>
      lower_run at hrun
      subst hrun
      refine check_ovf_sim (ss1 := [.assign st.fresh (.bin .sub .w64 (.v ya) (.imm 1))]) hF hH hC hl ho
        (by simp [Lir.Stmt.isCall]) ?_
      intro P H ρ ρl mem v H' _ hρ hr
      obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
      rw [hsem] at hs
      cases hs
      have ha' : ρl[ya]? = some wa := ha
      have hb' : ρl[yb]? = some wb := hb
      have hyb := hrb yb rfl
      refine ⟨rfl, ρl.insert st.fresh (wa - 1), wa - 1, wb, by simp only [lir_eval, ha'], by simp, ?_,
        fun hc => (hρ.temp hsup _).insert hx ?_⟩
      · simp (disch := omega) only [Lir.Arg.eval_v, Lir.env_insert_get, if_neg, hb']
      · exact natAdd_word (natAdd_operands hwa hwb).1 hc

/-! ## `natMul` -/

theorem mul_flag {q t u : Word} :
    ((if q ≠ t then (1 : Word) else 0) &&& (if u ≠ 0 then (1 : Word) else 0)) = 0 ↔ (q = t ∨ u = 0) := by
  by_cases h1 : q = t <;> by_cases h2 : u = 0 <;> simp [h1, h2]

theorem prim_natMul {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natMul [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natMul as)) := by
  have hsem := sem_nat2 .natMul (by decide)
  have hnb := sem_not_bool .natMul (by decide)
  cases la with
  | v ya =>
    have hgen : ∀ {lb : Lir.Arg}, operands f as = .ok (some [.v ya, lb]) →
        (do
          let u ← untag (.v ya)
          let t ← bin .sub lb (.imm 1)
          let p ← bin .mul u t
          let u1 ← temp (.select .eq .w64 u (.imm 0) (.imm 1) u)
          let q ← bin .udiv p u1
          let c1 ← temp (.test .ne .w64 q t)
          let c2 ← temp (.test .ne .w64 u (.imm 0))
          let c ← bin .and c1 c2
          check .natOverflow fun ok bad => .br .ne c (.imm 0) bad ok
          assign x (.bin .or .w64 p (.imm 1))).run st = .ok ((), st') →
        RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
          (.fir (.prim .natMul as)) := by
      intro lb hops hrun
      lower_run at hrun
      subst hrun
      let f0 := st.fresh
      refine check_br_sim (ss1 := [.assign f0 (.bin .shr .w64 (.v ya) (.imm 1)),
          .assign (f0 + 1) (.bin .sub .w64 lb (.imm 1)),
          .assign (f0 + 1 + 1) (.bin .mul .w64 (.v f0) (.v (f0 + 1))),
          .assign (f0 + 1 + 1 + 1) (.select .eq .w64 (.v f0) (.imm 0) (.imm 1) (.v f0)),
          .assign (f0 + 1 + 1 + 1 + 1) (.bin .udiv .w64 (.v (f0 + 1 + 1)) (.v (f0 + 1 + 1 + 1))),
          .assign (f0 + 1 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v (f0 + 1 + 1 + 1 + 1)) (.v (f0 + 1))),
          .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v f0) (.imm 0)),
          .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
            (.bin .and .w64 (.v (f0 + 1 + 1 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1 + 1 + 1)))])
        (ss2 := [.assign x (.bin .or .w64 (.v (f0 + 1 + 1)) (.imm 1))])
        hF hH hC hl ho (by simp [Lir.Stmt.isCall]) (by simp [Lir.Stmt.isCall]) ?_
      intro P H ρ ρl mem v H' hheap hρ hr
      obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
      rw [hsem] at hs
      cases hs
      have ha' : ρl[ya]? = some wa := ha
      have hya := hra ya rfl
      have hu1 : (if wa >>> 1 = 0 then (1 : Word) else wa >>> 1) ≠ 0 := by
        split
        · decide
        · assumption
      refine ⟨_, mem, _, 0, by
        simp (disch := omega) only [lir_eval, ha', arg_eval_temp hrb (t := st.fresh) hsup, hb, ↓reduceIte, if_neg,
          hu1, f0]; try rfl, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, rfl, ?_⟩
      intro hfl
      simp only [Lir.holds_ne, decide_eq_false_iff_not, Decidable.not_not] at hfl
      refine ⟨_, mem, P, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, hheap,
        List.prefix_refl _, ?_⟩
      refine ((((((((hρ.temp hsup _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp
        (by omega) _).temp (by omega) _).temp (by omega) _).insert hx ?_
      show natWord (p * q) = some _
      have := natMul_word hwa hwb (mul_flag.1 hfl)
      simpa using this
    cases lb with
    | imm wbi => exact hgen hops hrun
    | v yb =>
      by_cases hy : ya = yb
      · subst hy
        lower_run at hrun
        simp only [beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        let f0 := st.fresh
        refine check_br_sim (ss1 := [])
          (ss2 := [.assign f0 (.bin .shr .w64 (.v ya) (.imm 1)),
            .assign (f0 + 1) (.bin .sub .w64 (.v ya) (.imm 1)),
            .assign (f0 + 1 + 1) (.bin .mul .w64 (.v f0) (.v (f0 + 1))),
            .assign x (.bin .or .w64 (.v (f0 + 1 + 1)) (.imm 1))])
          hF hH hC hl ho (by simp) (by simp [Lir.Stmt.isCall]) ?_
        intro P H ρ ρl mem v H' hheap hρ hr
        obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, _⟩⟩ := bin2_of hρ hops hlive hnb hr
        rw [hsem] at hs
        cases hs
        have ha' : ρl[ya]? = some wa := ha
        have hb' : ρl[ya]? = some wb := hb
        have hya := hra ya rfl
        refine ⟨ρl, mem, wa, 0x16a09e667, rfl, ha, rfl, ?_⟩
        intro hfl
        simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hfl
        refine ⟨_, mem, P, by simp (disch := omega) only [lir_eval, ha', ↓reduceIte, if_neg, f0]; try rfl, hheap,
          List.prefix_refl _, ?_⟩
        refine (((hρ.temp hsup _).temp (by omega) _).temp (by omega) _).insert hx ?_
        have hwab : wa = wb := Option.some.inj (ha'.symm.trans hb')
        exact natMulSq_word hwa hwb hwab hfl
      · have hbeq : (ya == yb) = false := beq_eq_false_iff_ne.mpr hy
        lower_run at hrun
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hrun
        exact hgen hops hrun
  | imm wai =>
    by_cases hw5 : wai = 5
    · subst hw5
      cases lb with
      | v yb =>
        lower_run at hrun
        simp only [beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine check_br_sim (ss1 := [])
          (ss2 := [.assign x (.addr { base := some (.v yb), index := some (yb, .one), disp := -1 })])
          hF hH hC hl ho (by simp) (by simp [Lir.Stmt.isCall]) ?_
        intro P H ρ ρl mem v H' hheap hρ hr
        obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, _, _⟩⟩ := bin2_of hρ hops hlive hnb hr
        rw [hsem] at hs
        cases hs
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
        subst ha
        have hp2 : p = 2 := (natWord_eq_five hwa).1 rfl
        subst hp2
        have hb' : ρl[yb]? = some wb := hb
        refine ⟨ρl, mem, wb, 0x7fffffffffffffff, rfl, hb, rfl, ?_⟩
        intro hfl
        simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hfl
        refine ⟨_, mem, P, by simp only [lir_eval, hb']; try rfl, hheap, List.prefix_refl _, hρ.insert hx ?_⟩
        exact natMul2_addr_word hwb hfl
      | imm wbi =>
        lower_run at hrun
        simp only [beq_self_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        refine check_br_sim (ss1 := [])
          (ss2 := [.assign x (.arg (.imm (2 * wbi - 1)))])
          hF hH hC hl ho (by simp) (by simp [Lir.Stmt.isCall]) ?_
        intro P H ρ ρl mem v H' hheap hρ hr
        obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, _, _⟩⟩ := bin2_of hρ hops hlive hnb hr
        rw [hsem] at hs
        cases hs
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
        subst ha hb
        have hp2 : p = 2 := (natWord_eq_five hwa).1 rfl
        subst hp2
        refine ⟨ρl, mem, wbi, 0x7fffffffffffffff, rfl, rfl, rfl, ?_⟩
        intro hfl
        simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hfl
        refine ⟨_, mem, P, by simp only [lir_eval]; try rfl, hheap, List.prefix_refl _, hρ.insert hx ?_⟩
        exact natMul2_word hwb hfl
    · have hw5' : (wai == 5) = false := by simpa using hw5
      by_cases hw7 : wai = 7
      · subst hw7
        cases lb with
        | v yb =>
          lower_run at hrun
          simp only [hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
          lower_run at hrun
          subst hrun
          refine check_br_sim (ss1 := [])
            (ss2 := [.assign x (.addr { base := some (.v yb), index := some (yb, .two), disp := -2 })])
            hF hH hC hl ho (by simp) (by simp [Lir.Stmt.isCall]) ?_
          intro P H ρ ρl mem v H' hheap hρ hr
          obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, _, _⟩⟩ := bin2_of hρ hops hlive hnb hr
          rw [hsem] at hs
          cases hs
          simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
          subst ha
          have hp3 : p = 3 := (natWord_eq_seven hwa).1 rfl
          subst hp3
          have hb' : ρl[yb]? = some wb := hb
          refine ⟨ρl, mem, wb, 0x5555555555555555, rfl, hb, rfl, ?_⟩
          intro hfl
          simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hfl
          refine ⟨_, mem, P, by simp only [lir_eval, hb']; try rfl, hheap, List.prefix_refl _, hρ.insert hx ?_⟩
          exact natMul3_addr_word hwb hfl
        | imm wbi =>
          lower_run at hrun
          simp only [hw5', Bool.false_eq_true, beq_self_eq_true, ↓reduceIte] at hrun
          lower_run at hrun
          subst hrun
          refine check_br_sim (ss1 := [])
            (ss2 := [.assign x (.arg (.imm (3 * wbi - 2)))])
            hF hH hC hl ho (by simp) (by simp [Lir.Stmt.isCall]) ?_
          intro P H ρ ρl mem v H' hheap hρ hr
          obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, _, _⟩⟩ := bin2_of hρ hops hlive hnb hr
          rw [hsem] at hs
          cases hs
          simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha hb
          subst ha hb
          have hp3 : p = 3 := (natWord_eq_seven hwa).1 rfl
          subst hp3
          refine ⟨ρl, mem, wbi, 0x5555555555555555, rfl, rfl, rfl, ?_⟩
          intro hfl
          simp only [Lir.holds_ugt, decide_eq_false_iff_not] at hfl
          refine ⟨_, mem, P, by simp only [lir_eval]; try rfl, hheap, List.prefix_refl _, hρ.insert hx ?_⟩
          exact natMul3_word hwb hfl
      · have hw7' : (wai == 7) = false := by simpa using hw7
        lower_run at hrun
        simp only [hw5', hw7', Bool.false_eq_true, ↓reduceIte] at hrun
        lower_run at hrun
        subst hrun
        let f0 := st.fresh
        refine check_br_sim (ss1 := [.assign f0 (.bin .sub .w64 lb (.imm 1)),
            .assign (f0 + 1) (.bin .mul .w64 (.imm (wai >>> 1)) (.v f0)),
            .assign (f0 + 1 + 1) (.select .eq .w64 (.imm (wai >>> 1)) (.imm 0) (.imm 1) (.imm (wai >>> 1))),
            .assign (f0 + 1 + 1 + 1) (.bin .udiv .w64 (.v (f0 + 1)) (.v (f0 + 1 + 1))),
            .assign (f0 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v (f0 + 1 + 1 + 1)) (.v f0)),
            .assign (f0 + 1 + 1 + 1 + 1 + 1) (.test .ne .w64 (.imm (wai >>> 1)) (.imm 0)),
            .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1) (.bin .and .w64 (.v (f0 + 1 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1 + 1)))])
          (ss2 := [.assign x (.bin .or .w64 (.v (f0 + 1)) (.imm 1))])
          hF hH hC hl ho (by simp [Lir.Stmt.isCall]) (by simp [Lir.Stmt.isCall]) ?_
        intro P H ρ ρl mem v H' hheap hρ hr
        obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
        rw [hsem] at hs
        cases hs
        simp only [Lir.Arg.eval_imm, Option.some.injEq] at ha
        subst ha
        have hu1 : (if wai >>> 1 = 0 then (1 : Word) else wai >>> 1) ≠ 0 := by
          split
          · decide
          · assumption
        refine ⟨_, mem, _, 0, by
          simp (disch := omega) only [lir_eval, hb, ↓reduceIte, if_neg, hu1, f0]; try rfl,
          by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, rfl, ?_⟩
        intro hfl
        simp only [Lir.holds_ne, decide_eq_false_iff_not, Decidable.not_not] at hfl
        refine ⟨_, mem, P, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, hheap,
          List.prefix_refl _, ?_⟩
        refine (((((((hρ.temp hsup _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp
          (by omega) _).temp (by omega) _).insert hx ?_
        show natWord (p * q) = some _
        have := natMul_word hwa hwb (mul_flag.1 hfl)
        simpa using this

/-! ## `natShl` -/

theorem shl_flag {back t y : Word} :
    (((if back ≠ t then (1 : Word) else 0) ||| (if (63 : Word) < y then (1 : Word) else 0)) &&&
        (if t ≠ 0 then (1 : Word) else 0)) = 0 ↔ (back = t ∧ ¬ (63 : Word) < y) ∨ t = 0 := by
  by_cases h1 : back = t <;> by_cases h2 : (63 : Word) < y <;> by_cases h3 : t = 0 <;> simp [h1, h2, h3]

theorem prim_natShl {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natShl [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (hl : Labels st)
    (ho : Open st) (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natShl as)) := by
  have hsem := sem_nat2 .natShl (by decide)
  have hnb := sem_not_bool .natShl (by decide)
  cases lb with
  | v yb =>
    lower_run at hrun
    subst hrun
    let f0 := st.fresh
    refine check_br_sim (ss1 := [.assign f0 (.bin .shr .w64 (.v yb) (.imm 1)),
        .assign (f0 + 1) (.bin .sub .w64 la (.imm 1)),
        .assign (f0 + 1 + 1) (.bin .shl .w64 (.v (f0 + 1)) (.v f0)),
        .assign (f0 + 1 + 1 + 1) (.bin .shr .w64 (.v (f0 + 1 + 1)) (.v f0)),
        .assign (f0 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v (f0 + 1 + 1 + 1)) (.v (f0 + 1))),
        .assign (f0 + 1 + 1 + 1 + 1 + 1) (.test .ugt .w64 (.v f0) (.imm 63)),
        .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1) (.bin .or .w64 (.v (f0 + 1 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1 + 1))),
        .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v (f0 + 1)) (.imm 0)),
        .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
          (.bin .and .w64 (.v (f0 + 1 + 1 + 1 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)))])
      (ss2 := [.assign x (.bin .or .w64 (.v (f0 + 1 + 1)) (.imm 1))])
      hF hH hC hl ho (by simp [Lir.Stmt.isCall]) (by simp [Lir.Stmt.isCall]) ?_
    intro P H ρ ρl mem v H' hheap hρ hr
    obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
    rw [hsem] at hs
    cases hs
    have hb' : ρl[yb]? = some wb := hb
    have hyb := hrb yb rfl
    refine ⟨_, mem, _, 0, by
      simp (disch := omega) only [lir_eval, hb', arg_eval_temp hra (t := st.fresh) hsup, ha, ↓reduceIte, if_neg,
        f0]; try rfl, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, rfl, ?_⟩
    intro hfl
    simp only [Lir.holds_ne, decide_eq_false_iff_not, Decidable.not_not] at hfl
    refine ⟨_, mem, P, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, hheap,
      List.prefix_refl _, ?_⟩
    refine (((((((((hρ.temp hsup _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp
      (by omega) _).temp (by omega) _).temp (by omega) _).temp (by omega) _).insert hx ?_
    show natWord (p * 2 ^ q) = some _
    have := natShl_word hwa hwb (shl_flag.1 hfl)
    simpa using this
  | imm wbi =>
    lower_run at hrun
    subst hrun
    let f0 := st.fresh
    refine check_br_sim (ss1 := [.assign f0 (.bin .sub .w64 la (.imm 1)),
        .assign (f0 + 1) (.bin .shl .w64 (.v f0) (.imm (wbi >>> 1))),
        .assign (f0 + 1 + 1) (.bin .shr .w64 (.v (f0 + 1)) (.imm (wbi >>> 1))),
        .assign (f0 + 1 + 1 + 1) (.test .ne .w64 (.v (f0 + 1 + 1)) (.v f0)),
        .assign (f0 + 1 + 1 + 1 + 1) (.test .ugt .w64 (.imm (wbi >>> 1)) (.imm 63)),
        .assign (f0 + 1 + 1 + 1 + 1 + 1) (.bin .or .w64 (.v (f0 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1))),
        .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1) (.test .ne .w64 (.v f0) (.imm 0)),
        .assign (f0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
          (.bin .and .w64 (.v (f0 + 1 + 1 + 1 + 1 + 1)) (.v (f0 + 1 + 1 + 1 + 1 + 1 + 1)))])
      (ss2 := [.assign x (.bin .or .w64 (.v (f0 + 1)) (.imm 1))])
      hF hH hC hl ho (by simp [Lir.Stmt.isCall]) (by simp [Lir.Stmt.isCall]) ?_
    intro P H ρ ρl mem v H' hheap hρ hr
    obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hs, rfl, hra, hrb⟩⟩ := bin2_of hρ hops hlive hnb hr
    rw [hsem] at hs
    cases hs
    simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
    subst hb
    refine ⟨_, mem, _, 0, by
      simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg, f0]; try rfl,
      by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, rfl, ?_⟩
    intro hfl
    simp only [Lir.holds_ne, decide_eq_false_iff_not, Decidable.not_not] at hfl
    refine ⟨_, mem, P, by simp (disch := omega) only [lir_eval, ↓reduceIte, if_neg, f0]; try rfl, hheap,
      List.prefix_refl _, ?_⟩
    refine ((((((((hρ.temp hsup _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp (by omega) _).temp
      (by omega) _).temp (by omega) _).temp (by omega) _).insert hx ?_
    show natWord (p * 2 ^ q) = some _
    have := natShl_word hwa hwb (shl_flag.1 hfl)
    simpa using this

end IxCC.Rt.Proof
