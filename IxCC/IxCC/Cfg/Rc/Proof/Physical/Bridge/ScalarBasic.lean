import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarSem

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

theorem prim_natSub {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natSub [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natSub as)) := by
  lower_run at hrun
  subst hrun
  apply straight_sim (ss := [.assign st.fresh (.bin .sub .w64 la lb),
      .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
      .assign x (.select .ult .w64 la lb (.imm 1) (.v (st.fresh + 1)))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hsem, rfl, hra, hrb⟩⟩ :=
    bin2_of hρ hops hlive (sem_not_bool_sub) hr
  have hn : n = p - q := by
    simp [Lam.Prim.sem, Lam.Prim.sem.srcOp, Src.PrimOp.eval2] at hsem; omega
  subst hn
  refine ⟨rfl, ((ρl.insert st.fresh (wa - wb)).insert (st.fresh + 1) ((wa - wb) ||| 1)).insert x
    (if wa < wb then 1 else (wa - wb) ||| 1), ?_, ?_⟩
  · simp only [lir_eval, ha, hb, arg_eval_temp hra (t := st.fresh) hsup, arg_eval_temp hrb (t := st.fresh) hsup,
      arg_eval_temp hra (t := st.fresh + 1) (by omega), arg_eval_temp hrb (t := st.fresh + 1) (by omega),
      ↓reduceIte, Nat.add_one_ne_zero]
  · exact ((hρ.temp hsup _).temp (by omega) _).insert hx (by
      show natWord (p - q) = some _
      rw [natSub_word hwa hwb])

theorem prim2_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {ss : List Lir.Stmt} {f' : Nat}
    (hC : Ext C { st with acc := ss.reverse ++ st.acc, fresh := f' }) (ho : Open st)
    (hnc : ∀ s ∈ ss, s.isCall = false) (hsup : sup ≤ st.fresh) {x : Nat} (hx : x < sup) {la lb : Lir.Arg}
    {as : List Fir.Arg} (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a)
    {op : Lam.Prim} (hop : op ≠ .natBeq ∧ op ≠ .natBle ∧ op ≠ .natBlt ∧ op ≠ .natPred) (g : Nat → Nat → Nat)
    (hg : ∀ p q, op.sem [p, q] = some (.nat (g p q)))
    (hexec : ∀ (ρl : Lir.Env) (mem : X86.Memory) (p q : Nat) (wa wb : Word), la.eval ρl = some wa →
      lb.eval ρl = some wb → natWord p = some wa → natWord q = some wb → ArgReads sup la → ArgReads sup lb →
      ∃ ρl' w, Lir.execList ρl mem ctx ss = some (ρl', mem) ∧ natWord (g p q) = some w ∧ ρl'[x]? = some w ∧
        ∀ y, y < sup → y ≠ x → ρl'[y]? = ρl[y]?) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur) (ss.reverse ++ st.acc).length x
      (.fir (.prim op as)) := by
  apply straight_sim hF hH hC ho hnc
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, ⟨p, q, n, wa, wb, ha, hb, hwa, hwb, hsem, rfl, hra, hrb⟩⟩ :=
    bin2_of hρ hops hlive (sem_not_bool op ⟨hop.1, hop.2.1, hop.2.2.1⟩) hr
  rw [hg] at hsem
  cases hsem
  obtain ⟨ρl', w, hx', hw, hρx, hρy⟩ := hexec ρl mem p q wa wb ha hb hwa hwb hra hrb
  refine ⟨rfl, ρl', hx', ?_, ?_⟩
  · intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact hρ.dom hy
  · intro y v' hy hD
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx
      subst hyx
      cases hy
      exact ⟨w, hρx, hw⟩
    · rename_i hyx
      obtain ⟨w', hw', hv'⟩ := hρ.val hy hD
      exact ⟨w', by rw [hρy y (hρ.dom hy) hyx]; exact hw', hv'⟩

/-! ## `natLand`, `natLor`, `natXor` -/

theorem prim_natLand {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natLand [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natLand as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign x (.bin .and .w64 la lb)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· &&& ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨ρl.insert x (wa &&& wb), wa &&& wb, by simp only [lir_eval, ha, hb], natLand_word hwa hwb, by simp,
    fun y hy hyx => by regs_ne⟩

theorem prim_natLor {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natLor [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natLor as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign x (.bin .or .w64 la lb)]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· ||| ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨ρl.insert x (wa ||| wb), wa ||| wb, by simp only [lir_eval, ha, hb], natLor_word hwa hwb, by simp,
    fun y hy hyx => by regs_ne⟩

theorem prim_natXor {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natXor [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natXor as)) := by
  lower_run at hrun
  subst hrun
  refine prim2_sim (ss := [.assign st.fresh (.bin .xor .w64 la lb),
      .assign x (.bin .or .w64 (.v st.fresh) (.imm 1))]) hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops
    hlive (by decide) (· ^^^ ·) (sem_nat2 _ (by decide)) ?_
  intro ρl mem p q wa wb ha hb hwa hwb _ _
  exact ⟨(ρl.insert st.fresh (wa ^^^ wb)).insert x ((wa ^^^ wb) ||| 1), (wa ^^^ wb) ||| 1,
    by simp only [lir_eval, ha, hb, ↓reduceIte], natXor_word hwa hwb, by simp, fun y hy hyx => by regs_ne⟩

theorem prim_cmp {T : Tables} (hT : BoolsOk T) {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop}
    {sup : Nat} {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hF : lp.funcs[fn]? = some F) (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg}
    {as : List Fir.Arg} {op : Lam.Prim} {c : Lir.Cond} (hc : compareOf op = some c)
    (hrun : (primitive f T x op [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hops : operands f as = .ok (some [la, lb])) (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim op as)) := by
  cases hte : T.bools with
  | none =>
    rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · lower_run at hrun
      simp [hte, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, Functor.map, Except.map] at hrun
  | some te =>
    obtain ⟨t, e⟩ := te
    have hrun' : st' = { st with
        acc := [.assign x (.select c .w64 la lb (.imm t) (.imm e))].reverse ++ st.acc, fresh := st.fresh } := by
      rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · lower_run at hrun
        simp only [hte] at hrun
        lower_run at hrun
        exact hrun.symm
    subst hrun'
    apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
    intro P H ρ ρl mem v H' hρ hr
    obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
    obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
    simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
    cases ha : la.eval ρl with
    | none => simp [ha] at hws
    | some wa =>
      cases hb : lb.eval ρl with
      | none => simp [ha, hb] at hws
      | some wb =>
        simp [ha, hb] at hws
        subst hws
        rcases hrel with _ | ⟨hva, hrel'⟩
        rcases hrel' with _ | ⟨hvb, hnil⟩
        rcases hnil
        rename_i va vb
        simp only [Own.primResult] at hres
        cases hn : Own.natArgs [va, vb] with
        | none => simp [hn] at hres
        | some ns =>
          obtain ⟨p, q, rfl, rfl, rfl⟩ := natArgs_two hn
          simp only [hn] at hres
          rw [cmp_sem hc hva hvb] at hres
          refine ⟨rfl, ρl.insert x (if c.holds .w64 wa wb then t else e), ?_, ?_⟩
          · rcases compareOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp only [lir_eval, ha, hb, ↓reduceIte]
          · exact hρ.insert hx (bool_rel hT hte hres)

/-! ## `natPred` -/

theorem prim_natPred {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natPred [la]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natPred as)) := by
  lower_run at hrun
  subst hrun
  apply straight_sim (ss := [.assign st.fresh (.bin .sub .w64 la (.imm 2)),
      .assign x (.select .eq .w64 la (.imm 1) (.imm 1) (.v st.fresh))]) hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, vs, hvs, hres⟩ := evalRhs_prim hr
  obtain ⟨ws, hws, hrel, hreads⟩ := operands_rel hρ hops hlive hvs
  simp only [Lir.evalArgs_cons, Lir.evalArgs_nil, Option.bind_eq_bind] at hws
  cases ha : la.eval ρl with
  | none => simp [ha] at hws
  | some wa =>
    simp [ha] at hws
    subst hws
    rcases hrel with _ | ⟨hva, hnil⟩
    rcases hnil
    rename_i va
    simp only [Own.primResult] at hres
    cases hn : Own.natArgs [va] with
    | none => simp [hn] at hres
    | some ns =>
      obtain ⟨p, rfl, rfl⟩ := natArgs_one hn
      simp only [hn, Lam.Prim.sem, Src.PrimOp.eval2, Sem.Result.ok.injEq] at hres
      subst hres
      have hra := hreads la (by simp)
      refine ⟨rfl, (ρl.insert st.fresh (wa - 2)).insert x (if wa = 1 then 1 else wa - 2), ?_, ?_⟩
      · simp only [lir_eval, ha, arg_eval_temp hra (t := st.fresh) hsup, ↓reduceIte]
      · exact (hρ.temp hsup _).insert hx (natPred_word hva)

/-! ## `natShr` -/

theorem prim_natShr {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x : Nat} {la lb : Lir.Arg} {as : List Fir.Arg}
    (hrun : (primitive f T x .natShr [la, lb]).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hsup : sup ≤ st.fresh) (hx : x < sup) (hops : operands f as = .ok (some [la, lb]))
    (hlive : ∀ a ∈ as, LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x
      (.fir (.prim .natShr as)) := by
  cases lb with
  | v yb =>
    lower_run at hrun
    subst hrun
    refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 (.v yb) (.imm 1)),
        .assign (st.fresh + 1) (.bin .shr .w64 la (.v st.fresh)),
        .assign (st.fresh + 1 + 1) (.bin .or .w64 (.v (st.fresh + 1)) (.imm 1)),
        .assign x (.select .ugt .w64 (.v st.fresh) (.imm 63) (.imm 1) (.v (st.fresh + 1 + 1)))])
      hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide) (fun p q => p / 2 ^ q)
      (sem_nat2 _ (by decide)) ?_
    intro ρl mem p q wa wb ha hb hwa hwb hra _
    have hb' : ρl[yb]? = some wb := hb
    refine ⟨(((ρl.insert st.fresh (wb >>> 1)).insert (st.fresh + 1) (wa >>> ((wb >>> 1) &&& 63))).insert
        (st.fresh + 1 + 1) ((wa >>> ((wb >>> 1) &&& 63)) ||| 1)).insert x
        (if (63 : Word) < wb >>> 1 then (1 : Word) else (wa >>> ((wb >>> 1) &&& 63)) ||| 1),
      (if (63 : Word) < wb >>> 1 then (1 : Word) else (wa >>> ((wb >>> 1) &&& 63)) ||| 1), ?_, natShr_word hwa hwb, by simp,
      fun y hy hyx => by regs_ne⟩
    simp (disch := omega) only [lir_eval, hb', ha, arg_eval_temp hra (t := st.fresh) hsup, ↓reduceIte, if_neg]
  | imm wbi =>
    lower_run at hrun
    subst hrun
    refine prim2_sim (ss := [.assign st.fresh (.bin .shr .w64 la (.imm (wbi >>> 1))),
        .assign (st.fresh + 1) (.bin .or .w64 (.v st.fresh) (.imm 1)),
        .assign x (.select .ugt .w64 (.imm (wbi >>> 1)) (.imm 63) (.imm 1) (.v (st.fresh + 1)))])
      hF hH hC ho (by simp [Lir.Stmt.isCall]) hsup hx hops hlive (by decide) (fun p q => p / 2 ^ q)
      (sem_nat2 _ (by decide)) ?_
    intro ρl mem p q wa wb ha hb hwa hwb hra _
    simp only [Lir.Arg.eval_imm, Option.some.injEq] at hb
    subst hb
    refine ⟨((ρl.insert st.fresh (wa >>> ((wbi >>> 1) &&& 63))).insert
        (st.fresh + 1) ((wa >>> ((wbi >>> 1) &&& 63)) ||| 1)).insert x
        (if (63 : Word) < wbi >>> 1 then (1 : Word) else (wa >>> ((wbi >>> 1) &&& 63)) ||| 1),
      (if (63 : Word) < wbi >>> 1 then (1 : Word) else (wa >>> ((wbi >>> 1) &&& 63)) ||| 1), ?_, natShr_word hwa hwb, by simp,
      fun y hy hyx => by regs_ne⟩
    simp (disch := omega) only [lir_eval, ha, ↓reduceIte, if_neg]










end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
