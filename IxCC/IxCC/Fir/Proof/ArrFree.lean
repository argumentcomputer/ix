import IxCC.Fir.Proof.Lowering

/-! # `Fir.lower` binds no array primitive

`Fir.lower` declines an array primitive (`fir.arrays`, `exp_prim_arr`), so every body it produces
is `Code.arrFree`. The immortal route needs it below Own: Cfg's instructions run `Own.evalRhs`,
which has no array case, while Own's code evaluator gives array primitives their meaning
(`Cfg.Proof.Good.arrFree`, proved in `Cfg.Proof.immortal_good`). -/

set_option autoImplicit false

namespace IxCC.Fir.Proof

open IxCC.Fir.Lower

theorem projections_arrFree (x : Var) (key : Key.CtorKey) (body : Anf.Exp) :
    ∀ (fs : List Var) (i : Nat) (k : Code), k.arrFree = true →
      (projections x key body fs i k).arrFree = true
  | [], _, _, h => h
  | _ :: fs, i, k, h => by
    simp only [projections]
    split
    · simp only [Code.arrFree, Rhs.isArrPrim, Bool.not_false, Bool.true_and]
      exact projections_arrFree x key body fs (i + 1) k h
    · exact projections_arrFree x key body fs (i + 1) k h

mutual

/-- **A lowered body binds no array primitive.** -/
theorem exp_arrFree {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {st : St} {e : Anf.Exp} {code : Code} {st' : St},
      exp A g ρ J st e = .ok (code, st') → code.arrFree = true
  | _, _, _, .bind c b e, _, _, h => by
    cases b with
    | call h0 as =>
      obtain ⟨_, _, _, ⟨_, rfl, rfl⟩ | ⟨_, k, hk, rfl⟩⟩ := exp_call h
      · rfl
      · simpa [Code.arrFree, Rhs.isArrPrim] using exp_arrFree hk
    | glob h0 =>
      obtain ⟨_, _, _, _, ⟨_, rfl, rfl⟩ | ⟨_, k, hk, rfl⟩⟩ := exp_glob h
      · rfl
      · simpa [Code.arrFree, Rhs.isArrPrim] using exp_arrFree hk
    | atom a =>
      obtain ⟨_, k, _, hk, rfl⟩ := exp_atom h
      simpa [Code.arrFree, Rhs.isArrPrim] using exp_arrFree hk
    | con key as =>
      obtain ⟨_, _, k, _, _, _, hk, rfl⟩ := exp_con h
      simpa [Code.arrFree, Rhs.isArrPrim] using exp_arrFree hk
    | proj key i a =>
      obtain ⟨y, pre, st₁, k, hav, hk, rfl⟩ := exp_proj h
      have hk' := exp_arrFree hk
      rcases atomVar_inv hav with ⟨_, _, _, rfl, rfl⟩ | ⟨arg, _, _, _, rfl, rfl⟩
      · simpa [Code.arrFree, Rhs.isArrPrim] using hk'
      · simpa [Code.arrFree, Rhs.isArrPrim] using hk'
    | prim p as =>
      have hp := exp_prim_arr h
      obtain ⟨_, k, _, _, hk, rfl⟩ := exp_prim h
      simpa [Code.arrFree, Rhs.isArrPrim, hp] using exp_arrFree hk
    | app f as => exact (exp_app h).elim
    | fn ps b => exact (exp_fn h).elim
  | _, _, _, .join n r b e, _, _, h => by
    obtain ⟨_, _, _, _, _, -, hb, hk, rfl⟩ := exp_join h
    simp only [Code.arrFree, exp_arrFree hb, exp_arrFree hk, Bool.and_self]
  | _, _, _, .jump j as, _, _, h => by
    obtain ⟨_, _, _, _, rfl, -⟩ := exp_jump h
    rfl
  | _, _, _, .case x alts d, _, _, h => by
    obtain ⟨y, pre, st₁, alts', st₂, d', hav, has, hd, rfl⟩ := exp_case h
    have hcase : (Code.case y alts' d').arrFree = true := by
      simp only [Code.arrFree, exps_arrFree has, opt_arrFree hd, Bool.and_self]
    rcases atomVar_inv hav with ⟨_, _, _, rfl, rfl⟩ | ⟨arg, _, _, _, rfl, rfl⟩
    · exact hcase
    · simpa [Code.arrFree, Rhs.isArrPrim] using hcase
  | _, _, _, .ret a, _, _, h => by
    obtain ⟨_, _, rfl, -⟩ := exp_ret h
    rfl
  | _, _, _, .tick e, _, _, h => exp_arrFree (exp_tick h)
  | _, _, _, .trap, _, _, h => by
    obtain ⟨rfl, -⟩ := exp_trap h
    rfl

theorem exps_arrFree {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {y : Var} {st : St} {alts : List Anf.Alt} {alts' : List Alt}
      {st' : St}, exps A g ρ J y st alts = .ok (alts', st') → Code.altsArrFree alts' = true
  | _, _, _, _, [], _, _, h => by
    obtain ⟨rfl, -⟩ := exps_nil h
    rfl
  | _, _, _, _, .mk key n body :: as, _, _, h => by
    obtain ⟨-, b, _, rest, hb, hr, rfl⟩ := exps_cons h
    simp only [Code.altsArrFree, projections_arrFree _ _ _ _ _ _ (exp_arrFree hb), exps_arrFree hr,
      Bool.and_self]

theorem opt_arrFree {A : Anf.Program} {g : Anf.GlobalId} :
    ∀ {ρ : List Var} {J : List JoinId} {st : St} {d : Option Anf.Exp} {d' : Option Code} {st' : St},
      opt A g ρ J st d = .ok (d', st') → Code.optArrFree d' = true
  | _, _, _, none, _, _, h => by
    obtain ⟨rfl, -⟩ := opt_none h
    rfl
  | _, _, _, some _, _, _, h => by
    obtain ⟨_, hc, rfl⟩ := opt_some h
    exact exp_arrFree hc

end

end IxCC.Fir.Proof
