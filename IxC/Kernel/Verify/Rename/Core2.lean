module

public import IxC.Kernel.Verify.Rename.Core1

@[expose] public section

/-!
# The renaming walk through the core, part 2: the stuck fallbacks

The structure-η and unit-like certificates (`structEtaProjCerts`,
`structEtaCertWith`, `structEtaCert`, `structUnitCert`), function η
(`etaCert`) and the stuck fallbacks (`stuckIrrel`), at renamed arguments
over related core records and environments.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

@[simp] theorem reservedBasisNames_contains_map (k : Key md) :
    (reservedBasisNames (md := md')).contains (k.map f) =
      (reservedBasisNames (md := md)).contains k := by
  simp [reservedBasisNames]

/-- A renamed optional key is the renamed key exactly when the option is the
key (on good keys). -/
theorem Option.map_keyMap_eq_some_iff (hf : InjOn f P) {o : Option (Key md)}
    (ho : ∀ k ∈ o, k.Good P) {c : Key md} (hc : c.Good P) :
    o.map (Key.map f) = some (c.map f) ↔ o = some c := by
  cases o with
  | none => simp
  | some k =>
    simp only [Option.map_some, Option.some.injEq]
    exact Key.map_eq_map_iff hf (ho k rfl) hc

theorem iotaCerts_sim' (hr : CoreSim P f r r') (d : Nat) (lic : Bool) {ty : Expr md}
    {args : List (Expr md)} (hty : ty.Good P) (hargs : Expr.GoodList P args) {ty' : Expr md'}
    {args' : List (Expr md')} (h₁ : ty' = ty.mapKeys f) (h₂ : args' = args.map (Expr.mapKeys f)) :
    SimV (iotaCerts r env d lic ty args) (iotaCerts r' env' d lic ty' args') := by
  subst h₁ h₂; exact iotaCerts_sim hr d lic args ty hty hargs

theorem defEqList_sim' (hr : CoreSim P f r r') (d : Nat) {as bs : List (Expr md)}
    (has : Expr.GoodList P as) (hbs : Expr.GoodList P bs) {as' bs' : List (Expr md')}
    (h₁ : as' = as.map (Expr.mapKeys f)) (h₂ : bs' = bs.map (Expr.mapKeys f)) :
    SimV (defEqList r env d as bs) (defEqList r' env' d as' bs') := by
  subst h₁ h₂; exact defEqList_sim hr d as bs has hbs

/-! ## Structure η -/

theorem structEtaProjCerts_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {T : Key md} (hT : T.Good P) (us' : List Level) {targs : List (Expr md)}
    (ht : Expr.GoodList P targs) {b : Expr md} (hb : b.Good P) (lpsT : List LevelParam) :
    ∀ is : List Nat,
      SimV (structEtaProjCerts r env d T us' targs b lpsT is)
        (structEtaProjCerts r' env' d (T.map f) us' (targs.map (Expr.mapKeys f)) (b.mapKeys f)
          lpsT is)
  | [] => SimV.pureT true
  | i :: rest => by
    simp only [structEtaProjCerts]
    have h := hE.find (projFnName T i) hT
    simp only [projFnName, auxKey, Key.map_aux] at h ⊢
    rw [h]
    cases hc : env.find? (.aux T (.projFn i)) with
    | none => exact SimV.pureT false
    | some c =>
      have hg := hE.good (projFnName T i) c hT hc
      cases c with
      | recInfo cvp mI rP rules =>
        simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams,
          ConstantVal.mapKeys_type, Expr.stripPis_mapKeys, Option.isSome_map, List.length_map]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
        refine SimE.bind (iotaCerts_sim' hr d false
          (Expr.Good.instantiateLevelParams hg.1.2 _ _) (by simp [Expr.goodList_append, ht, hb])
          (by simp) (by simp)) (fun ok _ => ?_)
        exact SimE.ite Iff.rfl (fun _ => structEtaProjCerts_sim hE hr d hT us' ht hb lpsT rest)
          (fun _ => SimV.pureT false)
      | _ => exact SimV.pureT false

theorem structEtaCertWith_sim (mode : CheckMode) (hE : EnvRel P f env env')
    (hr : CoreSim P f r r') (d : Nat) {a b wtb : Expr md} (ha : a.Good P) (hb : b.Good P)
    (hw : wtb.Good P) :
    SimV (structEtaCertWith mode r env d a b wtb)
      (structEtaCertWith mode r' env' d (a.mapKeys f) (b.mapKeys f) (wtb.mapKeys f)) := by
  unfold structEtaCertWith
  rw [← Expr.mapKeys_getAppFn]
  have hga := Expr.Good.getAppFn ha
  have haa := Expr.Good.getAppArgs ha
  have hwa := Expr.Good.getAppArgs hw
  generalize a.getAppFn = g at hga ⊢
  cases g with
  | const c us =>
    simp only [Expr.mapKeys]
    rw [hE.find c hga]
    cases hcc : env.find? c with
    | none => exact SimV.pureT false
    | some cc =>
      have hgc := hE.good c cc hga hcc
      cases cc with
      | ctorInfo cvc cnP cnF =>
        simp only [Option.map_some, ConstantInfo.mapKeys, Expr.getAppArgs_mapKeys,
          List.length_map, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
        rw [← Expr.mapKeys_getAppFn]
        have hgw := Expr.Good.getAppFn hw
        generalize wtb.getAppFn = gw at hgw ⊢
        cases gw with
        | const T us' =>
          simp only [Expr.mapKeys]
          rw [hE.find T hgw]
          cases hcT : env.find? T with
          | none => exact SimV.pureT false
          | some cT =>
            have hgT := hE.good T cT hgw hcT
            cases cT with
            | indInfo cvT caps =>
              simp only [Option.map_some, ConstantInfo.mapKeys, IndCaps.mapKeys,
                ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
                reservedBasisNames_contains_map, towerSlotsAll_ren hE hgw,
                recSlotsAll_ren hE hgw]
              refine SimE.ite ?_ (fun _ => ?_) (fun _ => SimV.pureT false)
              · rw [Option.map_keyMap_eq_some_iff hE.inj hgT.2 hga]
              refine SimE.bind (SimE.liftFueled _ _) (fun okL _ => ?_)
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
              refine SimE.bind (iotaCerts_sim' hr d false
                (Expr.Good.instantiateLevelParams hgT.1.2 _ _) hwa (by simp) rfl)
                (fun ok₁ _ => ?_)
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
              refine SimE.bind (?_ : SimV _ _) (fun ok₂ _ => ?_)
              · refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
                exact structEtaProjCerts_sim hE hr d hgw us' hwa hb _ _
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
              refine SimE.bind (defEqList_sim' hr d (haa.take _) hwa (by simp) rfl)
                (fun ok₃ _ => ?_)
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
              refine SimE.bind (?_ : SimV _ _) (fun ok₄ _ => ?_)
              · simp only [CheckMode.ttChecks]
                exact SimV.pureT true
              refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
              exact defEqList_sim' hr d (haa.drop _)
                (etaProjs_good hgw hwa hb _) (by simp)
                (by rw [etaProjs_ren hE hgw])
            | _ => exact SimV.pureT false
        | _ => exact SimV.pureT false
      | _ => exact SimV.pureT false
  | _ => exact SimV.pureT false

theorem structEtaCert_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (structEtaCert mode r env d a b)
      (structEtaCert mode r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold structEtaCert
  rw [etaCtorShape_ren hE ha]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
  refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
  refine SimE.bind (hr.whnf d tb htb) (fun wtb hwtb => ?_)
  exact structEtaCertWith_sim mode hE hr d ha hb hwtb

theorem structUnitCert_sim (hE : EnvRel P f env env') (hr : CoreSim P f r r') (d : Nat)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (structUnitCert r env d a b) (structUnitCert r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold structUnitCert
  refine SimE.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine SimE.bind (hr.whnf d ta hta) (fun wta hwta => ?_)
  rw [← Expr.mapKeys_getAppFn]
  have hg := Expr.Good.getAppFn hwta
  have hwa := Expr.Good.getAppArgs hwta
  generalize wta.getAppFn = g at hg ⊢
  cases g with
  | const T us' =>
    simp only [Expr.mapKeys]
    rw [hE.find T hg]
    cases hcT : env.find? T with
    | none => exact SimV.pureT false
    | some cT =>
      have hgT := hE.good T cT hg hcT
      cases cT with
      | indInfo cvT caps =>
        simp only [Option.map_some, ConstantInfo.mapKeys, IndCaps.mapKeys,
          ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
          reservedBasisNames_contains_map, Expr.getAppArgs_mapKeys, List.length_map]
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
        refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
        refine SimE.bind (hr.whnf d tb htb) (fun wtb hwtb => ?_)
        refine SimE.bind (hr.defeq d wta wtb hwta hwtb) (fun ok _ => ?_)
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
        exact iotaCerts_sim' hr d false (Expr.Good.instantiateLevelParams hgT.1.2 _ _) hwa
          (by simp) (by simp)
      | _ => exact SimV.pureT false
  | _ => exact SimV.pureT false

/-! ## Function η and the stuck fallbacks -/

theorem etaCert_sim (mode : CheckMode) (hr : CoreSim P f r r') (d : Nat)
    {ty₁ body₁ : Expr md} (m₁ : BinderMeta) {b : Expr md} (hty : ty₁.Good P)
    (hbody : body₁.Good P) (hb : b.Good P) :
    SimV (etaCert mode r env d ty₁ body₁ m₁ b)
      (etaCert mode r' env' d (ty₁.mapKeys f) (body₁.mapKeys f) m₁ (b.mapKeys f)) := by
  unfold etaCert
  refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
  refine SimE.bind (hr.whnf d tb htb) (fun w hw => ?_)
  cases w with
  | forallE ty₂ x₂ m₂ =>
    refine SimE.bind (hr.defeq d ty₂ ty₁ hw.1 hty) (fun ok _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
    refine SimE.bind (SimE.congr (by simp) (hr.defeq (d + 1) (body₁.instantiate1 (.fvar d ty₁))
      (.app b (.fvar d ty₁)) (Expr.Good.instantiate1 (v := .fvar d ty₁) hbody hty 0) ⟨hb, hty⟩))
      (fun ok₂ _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
      refine SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => SimV.pureT true)
    · exact SimV.pureT false
  | _ => exact SimV.pureT false

theorem stuckIrrel_sim (mode : CheckMode) (hE : EnvRel P f env env') (hr : CoreSim P f r r')
    (d : Nat) {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (stuckIrrel mode r env d a b)
      (stuckIrrel mode r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold stuckIrrel
  refine SimE.bind (structEtaCert_sim mode hE hr d ha hb) (fun ok₁ _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  refine SimE.bind (structEtaCert_sim mode hE hr d hb ha) (fun ok₂ _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  refine SimE.bind (structUnitCert_sim hE hr d ha hb) (fun ok₃ _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  exact proofIrrel_sim hE hr d ha hb

end Ix.Kernel
