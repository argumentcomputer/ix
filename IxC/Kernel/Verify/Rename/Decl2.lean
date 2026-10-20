module

public import IxC.Kernel.Verify.Rename.Decl1
public import IxC.Kernel.Checker

@[expose] public section

/-!
# The renaming walk through the value checks and the basis installs

`checkDefnVal`, `checkThmVal` and `checkOpaqueVal` at renamed arguments over
related operation records and environments: every success is matched by the
renamed run's, the two extended environments related (`EnvRel`); the
structural operations' equation certificates, the compiler-trust identity
certificate, and the pinned basis installs likewise.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]

/-- The recurrence equations name role keys, fvars and the operation. -/
theorem natOpEquations_good (hpre : P.Pre) (d : Nat) (k : Key md)
    (hdeps : ∀ n ∈ natOpDeps k, n.Good P) :
    ∀ p ∈ natOpEquations d k, p.1.Good P ∧ p.2.Good P := by
  have h1 := hpre .nat (by decide)
  have h2 := hpre .natZero (by decide)
  have h3 := hpre .natSucc (by decide)
  have h4 := hpre .bool (by decide)
  have h5 := hpre .boolTrue (by decide)
  have h6 := hpre .boolFalse (by decide)
  unfold natOpEquations
  repeat' split
  all_goals (try subst_vars); simp [natOpDeps, Key.Good] at hdeps; simp_all [Expr.Good, Key.Good]

section Vals

variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem certifyNatEqs_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') :
    ∀ (eqs : List (Expr md × Expr md)), (∀ p ∈ eqs, p.1.Good P ∧ p.2.Good P) →
      SimV (certifyNatEqs ops env eqs)
        (certifyNatEqs ops' env' (eqs.map fun p => (p.1.mapKeys f, p.2.mapKeys f)))
  | [], _ => SimV.pureT true
  | p :: eqs, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, certifyNatEqs]
    refine SimE.bind (hops.isDefEq hE 2 p.1 p.2 h.1.1 h.1.2) (fun b _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
    exact certifyNatEqs_sim hops hE eqs h.2

theorem checkDefnVal_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {cv : ConstantVal md} (hcv : cv.Good P) {value : Expr md}
    (hv : value.Good P) (hint : ReducibilityHint) :
    SimR (EnvRelG P f L) (checkDefnVal ops env cv value hint)
      (checkDefnVal ops' env' (cv.mapKeys f) (value.mapKeys f) hint) := by
  unfold checkDefnVal
  simp only [ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
  refine SimR.bindE (hops.annotate hE 0 value hv) (fun v hvA => ?_)
  refine SimR.ite (by simp) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite (by rw [constsResolve_ren hE hvA]) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.bindE (hops.inferType hE 0 v hvA) (fun vt hvt => ?_)
  refine SimR.bindE (hops.isDefEq hE 0 vt cv.type hvt hcv.2) (fun b _ => ?_)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  exact SimR.pure' (hE.push (c := .defnInfo cv v hint) ⟨hcv, hvA⟩)

theorem checkThmVal_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {cv : ConstantVal md} (hcv : cv.Good P) {value : Expr md}
    (hv : value.Good P) :
    SimR (EnvRelG P f L) (checkThmVal ops env cv value)
      (checkThmVal ops' env' (cv.mapKeys f) (value.mapKeys f)) := by
  unfold checkThmVal
  simp only [ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys]
  refine SimR.bindE (hops.inferType hE 0 cv.type hcv.2) (fun st hst => ?_)
  refine SimR.bindE (hops.ensureSort hE 0 st hst) (fun u _ => ?_)
  refine SimR.bindE (SimE.liftFueled _ _) (fun b _ => ?_)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
  refine SimR.bindE (hops.annotate hE 0 value hv) (fun jv hjv => ?_)
  refine SimR.ite (by simp) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite (by rw [constsResolve_ren hE hjv]) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.bindE (hops.inferType hE 0 jv hjv) (fun vt hvt => ?_)
  refine SimR.bindE (hops.isDefEq hE 0 vt cv.type hvt hcv.2) (fun b _ => ?_)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  exact SimR.pure' (hE.push (c := .thmInfo cv value) ⟨hcv, hv⟩)

theorem checkOpaqueVal_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {cv : ConstantVal md} (hcv : cv.Good P) {value : Expr md}
    (hv : value.Good P) :
    SimR (EnvRelG P f L) (checkOpaqueVal ops env cv value)
      (checkOpaqueVal ops' env' (cv.mapKeys f) (value.mapKeys f)) := by
  unfold checkOpaqueVal
  simp only [ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
  refine SimR.bindE (hops.annotate hE 0 value hv) (fun v hvA => ?_)
  refine SimR.ite (by simp) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.ite (by rw [constsResolve_ren hE hvA]) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.bindE (hops.inferType hE 0 v hvA) (fun vt hvt => ?_)
  refine SimR.bindE (hops.isDefEq hE 0 vt cv.type hvt hcv.2) (fun b _ => ?_)
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  exact SimR.pure' (hE.push (c := .axiomInfo cv) hcv)

theorem installBasisDecl_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {ci : ConstantInfo md} (hci : ci.Good P) :
    SimR (EnvRelG P f L) (installBasisDecl env ci : CheckM md (Env md))
      (installBasisDecl env' (ci.mapKeys f) : CheckM md' (Env md')) := by
  unfold installBasisDecl
  rw [ConstantInfo.mapKeys_name, hE.find _ hci.name, Option.isNone_map]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  exact SimR.pure' (hE.push hci)

theorem foldlM_installBasisDecl_sim :
    ∀ (cs : List (ConstantInfo md)) {env : Env md} {env' : Env md'}, EnvRelG P f L env env' →
      (∀ c ∈ cs, c.Good P) →
      SimR (EnvRelG P f L) (cs.foldlM installBasisDecl env : CheckM md (Env md))
        ((cs.map (ConstantInfo.mapKeys f)).foldlM installBasisDecl env' : CheckM md' (Env md'))
  | [], _, _, hE, _ => SimR.pure' hE
  | c :: cs, _, _, hE, h => by
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.map_cons, List.foldlM_cons]
    exact SimR.bind (installBasisDecl_sim hE h.1)
      (fun _ _ hR => foldlM_installBasisDecl_sim cs hR h.2)

theorem checkBasisDecl_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    (kind : BasisKind) :
    SimR (EnvRelG P f L) (checkBasisDecl env kind : CheckM md (Env md))
      (checkBasisDecl env' kind : CheckM md' (Env md')) := by
  have hq : (env'.find? eqName = some eqA) ↔ (env.find? eqName = some eqA) := by
    have h := find_eq_pin_ren hE (k := eqName) (pin := eqA) (hE.pre .eq (by decide))
      (ConstantInfo.good_of_pinIn hE.pre eqA_pinIn)
    simp only [decide_eq_decide] at h
    exact h
  have hd : ∀ c ∈ kind.declsA (md := md), c.Good P := by
    have := declsA_pinIn (md := md) kind
    simp only [List.all_eq_true] at this
    exact fun c hc => ConstantInfo.good_of_pinIn hE.pre (this c hc)
  unfold checkBasisDecl
  rw [← declsA_mapKeys (f := f) kind]
  simp only []
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => foldlM_installBasisDecl_sim _ hE hd)
  exact SimR.ite hq.symm (fun _ => foldlM_installBasisDecl_sim _ hE hd) (fun _ => SimR.throw_bind)

end Vals

end Ix.Kernel
