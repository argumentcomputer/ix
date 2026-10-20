module

public import IxC.Kernel.Verify.Rename.Core4

@[expose] public section

/-!
# The renaming walk through the core, part 5: inference

`inferBody` and `inferBodyIO` at renamed arguments over related core
records and environments. The checker's `unless c do throw e` guards
compile to conditionals whose failing branch is `throw e >>= k`
(`SimE.throw_bind`).
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

theorem ProjEntry.typeAt_good {e : ProjEntry md} (he : e.Good P) (us : List Level)
    {targs : List (Expr md)} (ht : Expr.GoodList P targs) {pe : Expr md} (hpe : pe.Good P) :
    (e.typeAt us targs pe).Good P := by
  unfold ProjEntry.typeAt
  refine Expr.Good.instantiateList (Expr.Good.instantiateLevelParams he.2.2 _ _) ?_ 0
  simp only [Expr.goodList_cons]
  exact ⟨hpe, fun x hx => ht x (List.mem_reverse.mp hx)⟩

/-- The cases shared by both inference bodies: everything but `λ` and the
application. -/
theorem inferBody_const_sim (hE : EnvRelG P f L env env') {n : Key md} (hn : n.Good P)
    (us : List Level) :
    SimX P f
      (match env.find? n with
        | none => throw (unknownConstError n)
        | some ci => do
          unless !ci.isTowerEntry do
            throw (.invalid msg!"projection table entry used as a constant {n}")
          let cv := ci.toConstantVal
          unless us.length = cv.levelParams.length do
            throw (.invalid msg!"incorrect number of universe levels for {n}")
          pure (cv.type.instantiateLevelParams cv.levelParams us) : CheckM md (Expr md))
      (match env'.find? (n.map f) with
        | none => throw (unknownConstError (n.map f))
        | some ci => do
          unless !ci.isTowerEntry do
            throw (.invalid msg!"projection table entry used as a constant {n.map f}")
          let cv := ci.toConstantVal
          unless us.length = cv.levelParams.length do
            throw (.invalid msg!"incorrect number of universe levels for {n.map f}")
          pure (cv.type.instantiateLevelParams cv.levelParams us) : CheckM md' (Expr md')) := by
  rw [hE.find n hn]
  cases hc : env.find? n with
  | none => exact SimE.throw'
  | some ci =>
    have hg := hE.good n ci hn hc
    simp only [Option.map_some, ConstantInfo.isTowerEntry_mapKeys,
      ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_levelParams,
      ConstantVal.mapKeys_type]
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    exact SimE.pure' (Expr.Good.instantiateLevelParams hg.toConstantVal.2 _ _) (by simp)

theorem inferBody_sim (mode : CheckMode) (hE : EnvRelG P f L env env') (hr : CoreSim P f r r')
    (d : Nat) {e : Expr md} (he : e.Good P) :
    SimX P f (inferBody mode r env d e) (inferBody mode r' env' d (e.mapKeys f)) := by
  cases e with
  | sort u => exact SimE.pure' trivial rfl
  | fvar idx ty =>
    simp only [inferBody, Expr.mapKeys]
    exact SimE.ite Iff.rfl (fun _ => SimE.pure' he rfl) (fun _ => SimE.throw')
  | const n us =>
    simp only [inferBody, Expr.mapKeys]
    exact inferBody_const_sim hE he us
  | lit l =>
    cases l with
    | natVal n =>
      simp only [inferBody, Expr.mapKeys, natLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
    | strVal s =>
      simp only [inferBody, Expr.mapKeys, strLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
  | forallE ty body mb =>
    have hty : ty.Good P := he.1
    have hbody : body.Good P := he.2
    simp only [inferBody, Expr.mapKeys]
    refine SimE.bind (hr.infer d ty hty) (fun tt htt => ?_)
    refine SimE.bind (hr.whnf d tt htt) (fun w _ => ?_)
    cases w with
    | sort u =>
      have hb : (body.instantiate1 (.fvar d ty)).Good P :=
        Expr.Good.instantiate1 (v := .fvar d ty) hbody hty 0
      refine SimE.bind (SimE.congr (by simp) (hr.infer (d + 1) _ hb)) (fun tb htb => ?_)
      refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr (d + 1) htb)
        (fun v _ => ?_)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' trivial rfl)
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | lam ty body mb =>
    have hty : ty.Good P := he.1
    have hbody : body.Good P := he.2
    simp only [inferBody, Expr.mapKeys]
    refine SimE.bind (hr.infer d ty hty) (fun tt htt => ?_)
    refine SimE.bind (hr.whnf d tt htt) (fun w _ => ?_)
    cases w with
    | sort u =>
      have hb : (body.instantiate1 (.fvar d ty)).Good P :=
        Expr.Good.instantiate1 (v := .fvar d ty) hbody hty 0
      refine SimE.bind (SimE.congr (by simp) (hr.infer (d + 1) _ hb)) (fun bt hbt => ?_)
      have hR : (Expr.forallE ty (bt.abstract1 d) mb).Good P := ⟨hty, Expr.Good.abstract1 hbt d 0⟩
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hR (by simp))
      rw [Expr.lamPw_mapKeys]
      cases body.lamPw with
      | some pwI =>
        exact SimE.ite Iff.rfl (fun _ => SimE.pure' hR (by simp)) (fun _ => SimE.throw_bind)
      | none =>
        refine SimE.bind (hr.inferIO (d + 1) bt hbt) (fun btt hbtt => ?_)
        refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr (d + 1) hbtt)
          (fun vb _ => ?_)
        exact SimE.ite Iff.rfl (fun _ => SimE.pure' hR (by simp)) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | app fn a =>
    have hfn : fn.Good P := he.1
    have ha : a.Good P := he.2
    simp only [inferBody, Expr.mapKeys]
    refine SimE.bind (hr.infer d fn hfn) (fun tf htf => ?_)
    refine SimE.bind (hr.whnf d tf htf) (fun w hw => ?_)
    cases w with
    | forallE ty body mt =>
      refine SimE.bind (hr.infer d a ha) (fun ta hta => ?_)
      refine SimE.bind (hr.defeq d ta ty hta hw.1) (fun ok _ => ?_)
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' (Expr.Good.instantiate1 hw.2 ha 0) (by simp))
        (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | proj sn i pe =>
    have hsn : sn.Good P := he.1
    have hpe : pe.Good P := he.2
    simp only [inferBody, Expr.mapKeys]
    refine SimE.bind (hr.infer d pe hpe) (fun tp htp => ?_)
    refine SimE.bind (hr.whnf d tp htp) (fun te hte => ?_)
    rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
    have hg := Expr.Good.getAppFn hte
    have hargs := Expr.Good.getAppArgs hte
    generalize te.getAppFn = g at hg ⊢
    generalize te.getAppArgs = args at hargs ⊢
    cases g with
    | const T us =>
      simp only [Expr.mapKeys]
      rw [hE.findProj? hg i]
      cases hent : env.findProj? T i with
      | none => exact SimE.throw'
      | some entry =>
        have hge := hE.findProj?_good hg hent
        have hX := ProjEntry.typeAt_good hge us hargs hpe
        simp only [Option.map_some, Key.map_eq_map_iff hE.inj hg hsn, List.length_map]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw')
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hX (by simp))
        exact SimE.ite Iff.rfl (fun _ => SimE.pure' hX (by simp)) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | letE t v b l => exact SimE.throw'
  | bvar i => exact SimE.throw'

theorem inferBodyIO_sim (mode : CheckMode) (hE : EnvRelG P f L env env') (hr : CoreSim P f r r')
    (d : Nat) {e : Expr md} (he : e.Good P) :
    SimX P f (inferBodyIO mode r env d e) (inferBodyIO mode r' env' d (e.mapKeys f)) := by
  cases e with
  | sort u => exact SimE.pure' trivial rfl
  | fvar idx ty =>
    simp only [inferBodyIO, Expr.mapKeys]
    exact SimE.ite Iff.rfl (fun _ => SimE.pure' he rfl) (fun _ => SimE.throw')
  | const n us =>
    simp only [inferBodyIO, Expr.mapKeys]
    exact inferBody_const_sim hE he us
  | lit l =>
    cases l with
    | natVal n =>
      simp only [inferBodyIO, Expr.mapKeys, natLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
    | strVal s =>
      simp only [inferBodyIO, Expr.mapKeys, strLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
  | forallE ty body mb =>
    have hty : ty.Good P := he.1
    have hbody : body.Good P := he.2
    simp only [inferBodyIO, Expr.mapKeys]
    refine SimE.bind (hr.infer d ty hty) (fun tt htt => ?_)
    refine SimE.bind (hr.whnf d tt htt) (fun w _ => ?_)
    cases w with
    | sort u =>
      have hb : (body.instantiate1 (.fvar d ty)).Good P :=
        Expr.Good.instantiate1 (v := .fvar d ty) hbody hty 0
      refine SimE.bind (SimE.congr (by simp) (hr.infer (d + 1) _ hb)) (fun tb htb => ?_)
      refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr (d + 1) htb)
        (fun v _ => ?_)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' trivial rfl)
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | lam ty body mb =>
    have hty : ty.Good P := he.1
    have hbody : body.Good P := he.2
    simp only [inferBodyIO, Expr.mapKeys]
    have hb : (body.instantiate1 (.fvar d ty)).Good P :=
      Expr.Good.instantiate1 (v := .fvar d ty) hbody hty 0
    refine SimE.bind (SimE.congr (by simp) (hr.infer (d + 1) _ hb)) (fun bt hbt => ?_)
    have hR : (Expr.forallE ty (bt.abstract1 d) mb).Good P := ⟨hty, Expr.Good.abstract1 hbt d 0⟩
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hR (by simp))
    rw [Expr.lamPw_mapKeys]
    cases body.lamPw with
    | some pwI =>
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' hR (by simp)) (fun _ => SimE.throw_bind)
    | none =>
      refine SimE.bind (hr.infer (d + 1) bt hbt) (fun btt hbtt => ?_)
      refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr (d + 1) hbtt)
        (fun vb _ => ?_)
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' hR (by simp)) (fun _ => SimE.throw_bind)
  | app fn a =>
    have hfn : fn.Good P := he.1
    have ha : a.Good P := he.2
    simp only [inferBodyIO, Expr.mapKeys]
    refine SimE.bind (hr.infer d fn hfn) (fun tf htf => ?_)
    refine SimE.bind (hr.whnf d tf htf) (fun w hw => ?_)
    cases w with
    | forallE ty body mt =>
      have hX := Expr.Good.instantiate1 hw.2 ha 0
      refine SimE.ite Iff.rfl (fun _ => SimE.pure' hX (by simp)) (fun _ => ?_)
      refine SimE.bind (hr.infer d a ha) (fun ta hta => ?_)
      refine SimE.bind (hr.defeq d ta ty hta hw.1) (fun ok _ => ?_)
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' hX (by simp)) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | proj sn i pe =>
    have hsn : sn.Good P := he.1
    have hpe : pe.Good P := he.2
    simp only [inferBodyIO, Expr.mapKeys]
    refine SimE.bind (hr.infer d pe hpe) (fun tp htp => ?_)
    refine SimE.bind (hr.whnf d tp htp) (fun te hte => ?_)
    rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
    have hg := Expr.Good.getAppFn hte
    have hargs := Expr.Good.getAppArgs hte
    generalize te.getAppFn = g at hg ⊢
    generalize te.getAppArgs = args at hargs ⊢
    cases g with
    | const T us =>
      simp only [Expr.mapKeys]
      rw [hE.findProj? hg i]
      cases hent : env.findProj? T i with
      | none => exact SimE.throw'
      | some entry =>
        have hge := hE.findProj?_good hg hent
        have hX := ProjEntry.typeAt_good hge us hargs hpe
        simp only [Option.map_some, Key.map_eq_map_iff hE.inj hg hsn, List.length_map]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw')
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' hX (by simp))
        exact SimE.ite Iff.rfl (fun _ => SimE.pure' hX (by simp)) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'
  | letE t v b l => exact SimE.throw'
  | bvar i => exact SimE.throw'

end Ix.Kernel
