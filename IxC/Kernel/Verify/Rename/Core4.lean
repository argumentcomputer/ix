module

public import IxC.Kernel.Verify.Rename.Core3

@[expose] public section

/-!
# The renaming walk through the core, part 4: reduction

The projection certificate (`projCert`, `projCertAt`), head normalization
(`whnfCoreBody`), the reduction loop (`whnfStep`, `whnfLoop`, `whnfBody`)
and `ensureSort`, at renamed arguments over related core records and
environments.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

theorem projCert_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat) (lic : Bool)
    {c : Key md} (hc : c.Good P) (us : List Level) {args : List (Expr md)}
    (hargs : Expr.GoodList P args) :
    SimV (projCert r env d lic c us args)
      (projCert r' env' d lic (c.map f) us (args.map (Expr.mapKeys f))) := by
  unfold projCert
  rw [hE.find c hc]
  cases hcc : env.find? c with
  | none => exact SimV.pureT false
  | some cc =>
    have hg := hE.good c cc hc hcc
    cases cc with
    | ctorInfo cvC nP nF =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type]
      exact iotaCerts_sim' hr d lic (Expr.Good.instantiateLevelParams hg.2 _ _) hargs (by simp) rfl
    | _ => exact SimV.pureT false

theorem projCertAt_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    (verified lic : Bool) {c : Key md} (hc : c.Good P) (us : List Level)
    {args : List (Expr md)} (hargs : Expr.GoodList P args) :
    SimV (projCertAt r env d verified lic c us args)
      (projCertAt r' env' d verified lic (c.map f) us (args.map (Expr.mapKeys f))) := by
  unfold projCertAt
  exact SimE.ite Iff.rfl (fun _ => projCert_sim hE hr d lic hc us hargs) (fun _ => SimV.pureT true)

/-! ## Head normalization -/

theorem whnfCoreBody_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) {e : Expr md} (he : e.Good P) :
    SimX P f (whnfCoreBody mode r env d e) (whnfCoreBody mode r' env' d (e.mapKeys f)) := by
  cases e with
  | sort u => exact SimE.pure' he rfl
  | fvar idx ty => exact SimE.pure' he rfl
  | forallE ty body bi => exact SimE.pure' he rfl
  | lam ty body mb => exact SimE.pure' he rfl
  | const n us => exact SimE.pure' he rfl
  | lit l => exact SimE.pure' he rfl
  | letE t v b l => exact SimE.throw'
  | bvar i => exact SimE.throw'
  | app fn a =>
    have hfn : fn.Good P := he.1
    have ha : a.Good P := he.2
    simp only [whnfCoreBody, Expr.mapKeys]
    refine SimE.bind (hr.whnfCore d fn hfn) (fun w hw => ?_)
    cases w
    case lam ty body mb =>
      simp only [Expr.mapKeys]
      have hb : (body.instantiate1 a).Good P := Expr.Good.instantiate1 hw.2 ha 0
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · exact SimE.congr (by simp) (hr.whnfCore d _ hb)
      · refine SimE.bind (hr.inferIO d a ha) (fun ta hta => ?_)
        refine SimE.bind (hr.defeq d ta ty hta hw.1) (fun ok _ => ?_)
        exact SimE.ite Iff.rfl (fun _ => SimE.congr (by simp) (hr.whnfCore d _ hb))
          (fun _ => SimE.pure' ⟨hw, ha⟩ rfl)
    all_goals
      simp only [Expr.mapKeys]
      refine SimE.bind (SimE.congr (by simp) (iotaRec_sim mode hE hr d (And.intro hw ha)))
        (fun o ho => ?_)
      cases o with
      | none => exact SimE.pure' ⟨hw, ha⟩ (by simp)
      | some e'' => exact hr.whnfCore d e'' (ho e'' rfl)
  | proj sn i pe =>
    have hsn : sn.Good P := he.1
    have hpe : pe.Good P := he.2
    simp only [whnfCoreBody, Expr.mapKeys]
    refine SimE.bind (hr.whnf d pe hpe) (fun w hw => ?_)
    refine SimE.bind (projLitToCtor_sim hE hr d hw) (fun w' hw' => ?_)
    rw [hE.findProj? hsn i]
    cases hent : env.findProj? sn i with
    | none => exact SimE.pure' he rfl
    | some entry =>
      have hge := hE.findProj?_good hsn hent
      simp only [Option.map_some]
      rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
      have hg := Expr.Good.getAppFn hw'
      have hargs := Expr.Good.getAppArgs hw'
      generalize w'.getAppFn = g at hg ⊢
      generalize w'.getAppArgs = args at hargs ⊢
      cases g with
      | const c us =>
        simp only [Expr.mapKeys, ProjEntry.mapKeys, ProjEntry.fireOk_mapKeys, List.length_map,
          Key.map_eq_map_iff hE.inj hg hge.2.1]
        refine SimE.ite (by simp [ProjEntry.fireOk, ProjEntry.mapKeys]) (fun _ => ?_)
          (fun _ => SimE.pure' he rfl)
        refine SimE.bind (projCertAt_sim hE hr d _ _ hg us hargs) (fun ok _ => ?_)
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.pure' he rfl)
        exact SimE.congr (by rw [List.getD_map_bvar]) (hr.whnfCore d _ (hargs.getD _))
      | _ => exact SimE.pure' he rfl

/-! ## The reduction loop -/

theorem whnfStep_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {k : Expr md → CheckM md (Expr md)} {k' : Expr md' → CheckM md' (Expr md')}
    (hk : ∀ e, e.Good P → SimX P f (k e) (k' (e.mapKeys f))) {e : Expr md} (he : e.Good P) :
    SimX P f (whnfStep r env d k e) (whnfStep r' env' d k' (e.mapKeys f)) := by
  unfold whnfStep
  refine SimE.bind (hr.whnfCore d e he) (fun e₁ he₁ => ?_)
  refine SimE.bind (reduceNat_sim hE hr d he₁) (fun o ho => ?_)
  cases o with
  | some e₂ => exact hk e₂ (ho e₂ rfl)
  | none =>
    simp only [Option.map_none]
    rw [unfoldDefinition_ren hE he₁]
    cases hu : unfoldDefinition env e₁ with
    | none => exact SimE.pure' he₁ rfl
    | some e₂ => exact hk e₂ (unfoldDefinition_good hE he₁ hu)

theorem whnfLoop_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat) :
    ∀ (n : Nat) {e : Expr md}, e.Good P →
      SimX P f (whnfLoop r env d n e) (whnfLoop r' env' d n (e.mapKeys f))
  | 0, _, _ => SimE.throw'
  | n + 1, _, he => by
    simp only [whnfLoop]
    exact whnfStep_sim hE hr d (fun e he => whnfLoop_sim hE hr d n he) he

theorem whnfBody_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {e : Expr md} (he : e.Good P) :
    SimX P f (whnfBody r env d e) (whnfBody r' env' d (e.mapKeys f)) :=
  whnfLoop_sim hE hr d _ he

theorem ensureSort_sim (hr : CoreSim P f r r') (d : Nat) {e : Expr md} (he : e.Good P) :
    SimV (ensureSort r env d e) (ensureSort r' env' d (e.mapKeys f)) := by
  unfold ensureSort
  refine SimE.bind (hr.whnf d e he) (fun w _ => ?_)
  cases w with
  | sort u => exact SimV.pureT u
  | _ => exact SimE.throw'

end Ix.Kernel
