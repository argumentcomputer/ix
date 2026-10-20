module

public import IxC.Kernel.Verify.Rename.Core6
public import IxC.Kernel.CheckerBase

@[expose] public section

/-!
# The renaming walk through the core, part 7: annotation and the knot

The annotation pass (`isPropType`, `annotPwPi`, `annotPwLam`,
`annotateBody`), then the knot: at every fuel, the core records over
related environments are related (`coreKnot_sim`), and so are the fueled
entry points and the declaration checker's operation record
(`fueledOps_sim`).
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

theorem isPropType_sim (hr : CoreSim P f r r') (d : Nat) {ty : Expr md} (hty : ty.Good P) :
    SimV (isPropType r env d ty) (isPropType r' env' d (ty.mapKeys f)) := by
  unfold isPropType
  refine SimE.bind (hr.annotate d ty hty) (fun ty' hty' => ?_)
  refine SimE.bind (hr.inferIO d ty' hty') (fun t ht => ?_)
  refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr d ht) (fun s _ => ?_)
  exact SimE.liftFueled _ _

theorem annotPwPi_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {body : Expr md} (hb : body.Good P) :
    SimV (annotPwPi r env d body) (annotPwPi r' env' d (body.mapKeys f)) := by
  unfold annotPwPi
  rw [typeSortPW_ren hE hb]
  cases typeSortPW env.find? body with
  | some pw => exact SimV.pureT pw
  | none =>
    refine SimE.bind (hr.inferIO d body hb) (fun t ht => ?_)
    refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr d ht) (fun v _ => ?_)
    exact SimV.pureT _

theorem annotPwLam_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {body : Expr md} (hb : body.Good P) :
    SimV (annotPwLam r env d body) (annotPwLam r' env' d (body.mapKeys f)) := by
  unfold annotPwLam
  rw [proofPW_ren hE hb]
  cases proofPW env.find? body with
  | some pw => exact SimV.pureT pw
  | none =>
    refine SimE.bind (hr.inferIO d body hb) (fun bt hbt => ?_)
    refine SimE.bind (hr.inferIO d bt hbt) (fun t ht => ?_)
    refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr d ht) (fun v _ => ?_)
    exact SimV.pureT _

theorem annotateBody_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {e : Expr md} (he : e.Good P) :
    SimX P f (annotateBody r env d e) (annotateBody r' env' d (e.mapKeys f)) := by
  cases e with
  | bvar i => exact SimE.pure' trivial rfl
  | fvar idx ty =>
    simp only [annotateBody, Expr.mapKeys]
    exact SimE.ite Iff.rfl (fun _ => SimE.pure' he rfl) (fun _ => SimE.throw')
  | sort u => exact SimE.pure' trivial rfl
  | const n us => exact SimE.pure' he rfl
  | lit l =>
    cases l with
    | natVal n =>
      simp only [annotateBody, Expr.mapKeys, natLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
    | strVal s =>
      simp only [annotateBody, Expr.mapKeys, strLitSupported_ren hE]
      exact SimE.ite Iff.rfl (fun _ => SimE.pure' trivial rfl) (fun _ => SimE.throw')
  | app fn a =>
    simp only [annotateBody, Expr.mapKeys]
    refine SimE.bind (hr.annotate d fn he.1) (fun fn' hfn' => ?_)
    refine SimE.bind (hr.annotate d a he.2) (fun a' ha' => ?_)
    exact SimE.pure' ⟨hfn', ha'⟩ rfl
  | forallE ty body mb =>
    simp only [annotateBody, Expr.mapKeys]
    refine SimE.bind (hr.annotate d ty he.1) (fun ty' hty' => ?_)
    refine SimE.bind (SimE.congr (by simp) (hr.annotate (d + 1) _
      (Expr.Good.instantiate1 (v := .fvar d ty') he.2 hty' 0))) (fun body' hbody' => ?_)
    have hR := Expr.Good.abstract1 hbody' d 0
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · exact SimE.bind (annotPwPi_sim hE hr (d + 1) hbody')
        (fun _ _ => SimE.pure' ⟨hty', hR⟩ (by simp))
    · exact SimE.bind (SimV.pureT _) (fun _ _ => SimE.pure' ⟨hty', hR⟩ (by simp))
  | lam ty body mb =>
    simp only [annotateBody, Expr.mapKeys]
    refine SimE.bind (hr.annotate d ty he.1) (fun ty' hty' => ?_)
    refine SimE.bind (SimE.congr (by simp) (hr.annotate (d + 1) _
      (Expr.Good.instantiate1 (v := .fvar d ty') he.2 hty' 0))) (fun body' hbody' => ?_)
    have hR := Expr.Good.abstract1 hbody' d 0
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · exact SimE.bind (annotPwLam_sim hE hr (d + 1) hbody')
        (fun _ _ => SimE.pure' ⟨hty', hR⟩ (by simp))
    · exact SimE.bind (SimV.pureT _) (fun _ _ => SimE.pure' ⟨hty', hR⟩ (by simp))
  | letE ty v b l =>
    simp only [annotateBody, Expr.mapKeys]
    refine SimE.bind (hr.annotate d ty he.1) (fun ty' hty' => ?_)
    refine SimE.bind (hr.infer d ty' hty') (fun tt htt => ?_)
    refine SimE.bind (ensureSort_sim (env := env) (env' := env') hr d htt) (fun _ _ => ?_)
    refine SimE.bind (hr.annotate d v he.2.1) (fun v' hv' => ?_)
    refine SimE.bind (hr.infer d v' hv') (fun tv htv => ?_)
    refine SimE.bind (hr.defeq d tv ty' htv hty') (fun _ _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    exact SimE.congr (by simp) (hr.annotate d _ (Expr.Good.instantiate1 he.2.2 he.2.1 0))
  | proj sn i pe =>
    have hsn : sn.Good P := he.1
    simp only [annotateBody, Expr.mapKeys]
    refine SimE.bind (hr.annotate d pe he.2) (fun e' he' => ?_)
    refine SimE.bind (hr.inferIO d e' he') (fun t ht => ?_)
    refine SimE.bind (hr.whnf d t ht) (fun te hte => ?_)
    rw [← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys]
    have hg := Expr.Good.getAppFn hte
    generalize te.getAppFn = g at hg ⊢
    cases g with
    | const T us =>
      simp only [Expr.mapKeys]
      rw [hE.findProj? hg i]
      cases hent : env.findProj? T i with
      | none => exact SimE.throw'
      | some entry =>
        simp only [Option.map_some, List.length_map]
        refine SimE.ite (Key.map_eq_map_iff hE.inj hg hsn).symm (fun _ => ?_)
          (fun _ => SimE.throw_bind)
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
        exact SimE.pure' ⟨hg, he'⟩ rfl
    | _ => exact SimE.throw'

/-! ## The knot -/

/-- **The core records at every fuel**, over related environments, are
related. -/
theorem coreKnot_sim (mode : CheckMode) (hE : EnvRelG P f L env env') :
    ∀ F, CoreSim P f (coreKnot mode env id F) (coreKnot mode env' id F)
  | 0 => CoreSim.zero mode env env'
  | F + 1 =>
    have ih := coreKnot_sim mode hE F
    { whnfCore := fun d _ he => whnfCoreBody_sim mode hE ih d he
      whnf := fun d _ he => whnfBody_sim hE ih d he
      infer := fun d _ he => inferBody_sim mode hE ih d he
      defeq := fun d _ _ ha hb => defeqBody_sim mode hE ih d ha hb
      annotate := fun d _ he => annotateBody_sim hE ih d he
      inferIO := fun d _ he =>
        SimE.ite Iff.rfl (fun _ => inferBodyIO_sim mode hE ih.ioView d he)
          (fun _ => inferBody_sim mode hE ih d he) }

/-! ## The declaration checker's operations -/

/-- **Two operation records of the declaration checker, one the renaming of
the other**: at related environments, every entry's success is the renamed
entry's; `orElse` runs related attempts and fallbacks. -/
structure OpsSim (P : md.Id → Prop) (f : md.Id → md'.Id) (L : Env md → Env md' → Prop)
    (ops : (CheckerOps md) (CheckM md))
    (ops' : (CheckerOps md') (CheckM md')) : Prop where
  annotate : ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' → ∀ d (e : Expr md), e.Good P →
    SimX P f (ops.annotate env d e) (ops'.annotate env' d (e.mapKeys f))
  inferType : ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' → ∀ d (e : Expr md),
    e.Good P → SimX P f (ops.inferType env d e) (ops'.inferType env' d (e.mapKeys f))
  isDefEq : ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' → ∀ d (a b : Expr md),
    a.Good P → b.Good P →
      SimV (ops.isDefEq env d a b) (ops'.isDefEq env' d (a.mapKeys f) (b.mapKeys f))
  ensureSort : ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' → ∀ d (e : Expr md),
    e.Good P → SimV (ops.ensureSort env d e) (ops'.ensureSort env' d (e.mapKeys f))
  whnf : ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' → ∀ d (e : Expr md), e.Good P →
    SimX P f (ops.whnf env d e) (ops'.whnf env' d (e.mapKeys f))
  orElse : ∀ (x : CheckM md Bool) (x' : CheckM md' Bool)
    (k : Option (CheckError md) → CheckM md Unit) (k' : Option (CheckError md') → CheckM md' Unit),
    SimV x x' → SimV (k none) (k' none) → SimV (ops.orElse x k) (ops'.orElse x' k')

/-- **The pure operation record at any fuel** is related to itself across
the renaming. -/
theorem fueledOps_sim (mode : CheckMode) (F : Nat) :
    OpsSim P f L (fueledOps mode F) (fueledOps mode F) where
  annotate hE d _ he := (coreKnot_sim mode hE F).annotate d _ he
  inferType hE d _ he := (coreKnot_sim mode hE F).infer d _ he
  isDefEq hE d _ _ ha hb := (coreKnot_sim mode hE F).defeq d _ _ ha hb
  ensureSort {env} {env'} hE d _ he := ensureSort_sim (env := env) (env' := env') (coreKnot_sim mode hE F) d he
  whnf hE d _ he := (coreKnot_sim mode hE F).whnf d _ he
  orElse x x' k k' hx hk := by
    show SimV (match x with | .ok true => pure () | _ => k none)
      (match x' with | .ok true => pure () | _ => k' none)
    intro u hu
    refine ⟨trivial, ?_⟩
    cases x with
    | ok b =>
      have hx' := (hx b rfl).2
      cases b with
      | true => rw [hx']; rfl
      | false => rw [hx']; exact (hk u hu).2
    | error e =>
      cases x' with
      | ok b' =>
        cases b' with
        | true => rfl
        | false => exact (hk u hu).2
      | error e' => exact (hk u hu).2

end Ix.Kernel
