module

public import IxC.Kernel.Verify.Rename.Native3

@[expose] public section

/-!
# The renaming walk through the fixpoint route: the recursor and the route (step 7.3, chunk (iii))

The generated rules (`checkNativeRules`), the recursor (`checkNativeRec`), one
pass over the former and the constructors (`checkNativePass`), the install after
it (`checkNativeTail`) and the route (`checkNative`), at a renamed block over
related environments: every success of the original is a success of the renamed
run, with related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

theorem IndCaps.mapKeys_beq (hf : InjOn f P) {a b : IndCaps md} (ha : a.Good P) (hb : b.Good P) :
    (a.mapKeys f == b.mapKeys f) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨IndCaps.mapKeys_inj hf ha hb, fun h => h ▸ rfl⟩

@[simp] theorem InductiveShape.mapKeys_rulePrefix (p : InductiveShape md) :
    (p.mapKeys f).rulePrefix = p.rulePrefix := by
  unfold InductiveShape.rulePrefix InductiveShape.mapKeys
  simp

@[simp] theorem InductiveShape.mapKeys_majorIdx (p : InductiveShape md) :
    (p.mapKeys f).majorIdx = p.majorIdx := by
  unfold InductiveShape.majorIdx
  rw [InductiveShape.mapKeys_rulePrefix]
  rfl

/-! ## The recursor -/

theorem checkNativeRules_sim {envR : Env md} {envR' : Env md'} (hE : EnvRelG P f L envR envR')
    (rlps : List LevelParam) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (elim : LevelParam) (large : Bool) (nP nIdx : Nat) {tty : Expr md} (ht : tty.Good P)
    {ctors : List (Key md × Nat × Expr md × List Nat)} (hcs : ctors4Good P ctors)
    {recC : Key md} (hr : recC.Good P) (rlvls : List Level) :
    ∀ (k j : Nat), SimE (Expr.GoodList P) (List.map (Expr.mapKeys f))
      (checkNativeRules (m := CheckM md) envR rlps T lps elim large nP nIdx tty ctors recC rlvls k j)
      (checkNativeRules (m := CheckM md') envR' rlps (T.map f) lps elim large nP nIdx
        (tty.mapKeys f) (ctors4Map f ctors) (recC.map f) rlvls k j)
  | 0, _ => SimE.pure' (by simp) rfl
  | k + 1, j => by
    simp only [checkNativeRules, structRecRhsR_map]
    refine SimE.bind (SimE.unwrapOr' (G := Expr.Good P)
      (fun r h => structRecRhsR_good hT ht hcs hr h)) (fun rhs hrhs => ?_)
    simp only [Expr.allLevelParamsDefined_mapKeys, constsResolve_ren hE hrhs,
      Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys]
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    refine SimE.bind (checkNativeRules_sim hE rlps hT lps elim large nP nIdx ht hcs hr rlvls k
      (j + 1)) (fun rest hrest => ?_)
    exact SimE.pure' (by simp [hrhs, hrest]) rfl

/-- **The recursor's stage at a renamed block.** -/
theorem checkNativeRec_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {p : NativeParts md} (hp : p.Good P) {cvTa : ConstantVal md}
    (hTa : cvTa.Good P) {ctorsA : List (ConstantVal md × Nat)} (hcs : ∀ c ∈ ctorsA, c.1.Good P) :
    SimE (fun r : ConstantVal md × List (Expr md) => r.1.Good P ∧ Expr.GoodList P r.2)
      (fun r => (r.1.mapKeys f, r.2.map (Expr.mapKeys f)))
      (checkNativeRec ops env p cvTa ctorsA)
      (checkNativeRec ops' env' (p.mapKeys f) (cvTa.mapKeys f)
        (ctorsA.map fun c => (c.1.mapKeys f, c.2))) := by
  unfold checkNativeRec
  simp only [NativeParts.mapKeys_toInductiveShape, nativeRecLpsOk_map,
    NativeParts.mapKeys_recPinned, NativeParts.mapKeys_kinds]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hcvR : (p.toInductiveShape.mapKeys f).cvR = p.cvR.mapKeys f := rfl
  have hcvT : (p.toInductiveShape.mapKeys f).cvT = p.cvT.mapKeys f := rfl
  have hpe : (p.toInductiveShape.mapKeys f).elim = p.elim := rfl
  have hpl : (p.toInductiveShape.mapKeys f).large = p.large := rfl
  have hpn : (p.toInductiveShape.mapKeys f).nP = p.nP := rfl
  have hpi : (p.toInductiveShape.mapKeys f).nIdx = p.nIdx := rfl
  simp only [hcvR, hcvT, hpe, hpl, hpn, hpi, InductiveShape.mapKeys_majorIdx,
    InductiveShape.mapKeys_rulePrefix]
  refine SimE.bind (checkConstantVal_sim hops hE hp.cvR) (fun cvRi hcvRi => ?_)
  simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    nativeCtors4_map, structRecTyR_map]
  have hctors := nativeCtors4_good hcs p.kinds
  refine SimE.bind (SimE.unwrapOr' (G := Expr.Good P)
    (fun r h => structRecTyR_good hp.cvT.1 hTa.2 hctors h)) (fun recTy hty => ?_)
  simp only [Expr.allLevelParamsDefined_mapKeys, constsResolve_ren hE hty,
    Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (hops.inferType hE 0 recTy hty) (fun sty hsty => ?_)
  refine SimE.bind (hops.ensureSort hE 0 sty hsty) (fun _ _ => ?_)
  refine SimE.bind (hops.isDefEq hE 0 cvRi.type recTy hcvRi.2 hty) (fun c _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hcvRa : (⟨p.cvR.name, p.cvR.levelParams, recTy⟩ : ConstantVal md).Good P := ⟨hp.cvR.1, hty⟩
  have hER := hE.push (c := .recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ p.majorIdx
    p.rulePrefix []) ⟨hcvRa, fun _ h => (nomatch h)⟩
  rw [ctors4Map_length]
  refine SimE.bind (checkNativeRules_sim hER p.cvR.levelParams hp.cvT.1 p.cvT.levelParams p.elim
    p.large p.nP p.nIdx hTa.2 hctors hp.cvR.1 _ _ 0) (fun rhss hrhss => ?_)
  exact SimE.pure' ⟨hcvRa, hrhss⟩ rfl

/-! ## One pass over the former and the constructors -/

/-- Two passes' records, one the renaming of the other. -/
structure NativePassRel (P : KeyScope md) (f : md.Id → md'.Id) (L : Env md → Env md' → Prop)
    (q : (NativePass md) (Env md))
    (q' : (NativePass md') (Env md')) : Prop where
  env : EnvRelG P f L q.env₁ q'.env₁
  cvTa : q.cvTa.Good P
  cvTa' : q'.cvTa = q.cvTa.mapKeys f
  p : q.p.Good P
  p' : q'.p = q.p.mapKeys f
  ctors : ∀ c ∈ q.ctorsA, c.1.Good P
  ctors' : q'.ctorsA = q.ctorsA.map fun c => (c.1.mapKeys f, c.2)
  sortss : q'.sortss = q.sortss

theorem checkNativePass_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {p₀ : NativeParts md} (hp₀ : p₀.Good P) (isRec : Bool) :
    SimR (fun (r : (NativePass md) (Env md) × Bool) (r' : (NativePass md') (Env md') × Bool) =>
        NativePassRel P f L r.1 r'.1 ∧ r'.2 = r.2)
      (checkNativePass ops env p₀ isRec) (checkNativePass ops' env' (p₀.mapKeys f) isRec) := by
  unfold checkNativePass
  rw [NativeParts.mapKeys_toInductiveShape]
  refine SimR.bind (checkSumInd_sim hops hE hp₀ (capsOf := fun p₁ => nativeCapsAt p₁ isRec)
    (capsOf' := fun p₁ => nativeCapsAt p₁ isRec)
    (fun q hq => ⟨nativeCapsAt_map q isRec, nativeCapsAt_good hq isRec⟩)) (fun r r' hr => ?_)
  obtain ⟨env₁, cvTa, p₁⟩ := r
  obtain ⟨env₁', cvTa', p₁'⟩ := r'
  obtain ⟨hE₁, hTa, rfl, hp₁, rfl⟩ := hr
  simp only []
  have hpC : (p₀.mapKeys f).complete (p₁.mapKeys f) = (p₀.complete p₁).mapKeys f := rfl
  rw [hpC]
  have hT : (p₀.complete p₁).cvT.name.Good P := hp₁.cvT.1
  have hcs : ∀ c ∈ (p₀.complete p₁).ctors, c.1.Good P := hp₁.ctors
  have hctorsMap : ((p₀.complete p₁).mapKeys f).ctors =
      (p₀.complete p₁).ctors.map fun c => (c.1.mapKeys f, c.2) := rfl
  have hcvTMap : ((p₀.complete p₁).mapKeys f).cvT = (p₀.complete p₁).cvT.mapKeys f := rfl
  simp only [hctorsMap, hcvTMap, ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams]
  refine SimR.bindE (checkSumCtors_sim hops hE₁ hE₁ hT _ _ _ _ _ _ hTa _ hcs) (fun r hr => ?_)
  obtain ⟨ctorsA, sortss⟩ := r
  simp only []
  refine SimR.bindE (classifyFixKinds_sim hE₁.inj hT _ _ _ hr) (fun kinds _ => ?_)
  simp only [id]
  have hpK : ((p₀.complete p₁).mapKeys f).withKinds kinds =
      ((p₀.complete p₁).withKinds kinds).mapKeys f := rfl
  rw [hpK, nativeCaps_map, nativeCapsAt_map]
  have hpg : ((p₀.complete p₁).withKinds kinds).Good P := hp₁
  rw [IndCaps.mapKeys_beq hE₁.inj (a := nativeCaps ((p₀.complete p₁).withKinds kinds))
    (nativeCapsAt_good hpg _) (nativeCapsAt_good hp₁ isRec)]
  exact SimR.pure' ⟨⟨hE₁, hTa, rfl, hpg, rfl, hr, rfl, rfl⟩, rfl⟩

/-! ## The install after the pass, and the route -/

theorem checkNativeTail_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {q : (NativePass md) (Env md)} {q' : (NativePass md') (Env md')}
    (hq : NativePassRel P f L q q') :
    SimR (EnvRelG P f L) (checkNativeTail ops env q) (checkNativeTail ops' env' q') := by
  obtain ⟨env₁, cvTa, p, ctorsA, sortss⟩ := q
  obtain ⟨env₁', cvTa', p', ctorsA', sortss'⟩ := q'
  obtain ⟨hE₁, hTa, hTa', hp, hp', hcs, hcs', hss⟩ := hq
  simp only at hE₁ hTa hTa' hp hp' hcs hcs' hss
  subst hTa' hp' hcs' hss
  unfold checkNativeTail
  simp only [NativeParts.mapKeys_toInductiveShape]
  have hlen : (p.toInductiveShape.mapKeys f).ctors.length = p.ctors.length := by
    simp [InductiveShape.mapKeys]
  have hcvR : (p.toInductiveShape.mapKeys f).cvR = p.cvR.mapKeys f := rfl
  have hcvT : (p.toInductiveShape.mapKeys f).cvT = p.cvT.mapKeys f := rfl
  have hrhss : (p.toInductiveShape.mapKeys f).rhss = p.rhss.map (Expr.mapKeys f) := rfl
  have hpl : (p.toInductiveShape.mapKeys f).large = p.large := rfl
  have hps : (p.toInductiveShape.mapKeys f).resSort = p.resSort := rfl
  have hpn : (p.toInductiveShape.mapKeys f).nP = p.nP := rfl
  have hpi : (p.toInductiveShape.mapKeys f).nIdx = p.nIdx := rfl
  simp only [hlen, hcvR, hcvT, hrhss, hpl, hps, hpn, hpi, NativeParts.mapKeys_kinds,
    InductiveShape.mapKeys_majorIdx, InductiveShape.mapKeys_rulePrefix]
  refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
  simp only [ConstantVal.mapKeys_type, openPisAtFvars_mapKeys]
  refine SimR.bindE (SimE.unwrapOr'
    (G := fun t : List (Expr md) × Expr md => Expr.GoodList P t.1 ∧ t.2.Good P)
    (fun t ht => Expr.openPisAtFvars_good hTa.2 ht)) (fun tq htq => ?_)
  obtain ⟨tfvs, _⟩ := tq
  simp only [Expr.mapDoms, ← List.map_drop]
  have hnil : ([] : List (Expr md')) = ([] : List (Expr md)).map (Expr.mapKeys f) := rfl
  rw [hnil]
  refine SimR.bindE (checkStructFieldSortsI_sim hops hE₁ true false p.resSort p.nP
    (htq.1.drop p.nP) (by simp) p.nIdx) (fun _ _ => ?_)
  simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams,
    nativeFieldsOk_map hE hp.cvT.1 _ _ _ hcs]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  simp only [nativeRulesOk_map hE.inj hp.cvR.1 _ _ _ _ hcs _ hp.rhss hp.cvR.2]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  have hE₂ := consSumCtors_rel (f := f) p.nP ctorsA hcs hE₁
  refine SimR.bindE (checkNativeRec_sim hops hE₂ hp hTa hcs) (fun r hr => ?_)
  obtain ⟨cvRa, rhss⟩ := r
  obtain ⟨hcvRa, hrhs⟩ := hr
  simp only []
  rw [show (cvRa.mapKeys f).name = cvRa.name.map f from rfl,
    show (cvRa.mapKeys f).type = cvRa.type.mapKeys f from rfl,
    sumRules_ren hE₂ hcvRa.1 _ _ _ _ ctorsA rhss hcs hrhs]
  have hE₃ := hE₂.push (c := .recInfo cvRa p.majorIdx p.rulePrefix
    (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix
      cvRa.type ctorsA rhss)) ⟨hcvRa, sumRules_good _ _ _ _ ctorsA rhss hcs hrhs⟩
  exact checkNativeTable_sim hE₃ hp hcs _

/-- **The fixpoint route at a renamed block.** -/
theorem checkNative_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {p₀ : NativeParts md} (hp₀ : p₀.Good P) :
    SimR (EnvRelG P f L) (checkNative ops env p₀) (checkNative ops' env' (p₀.mapKeys f)) := by
  unfold checkNative
  have hnames : ((p₀.mapKeys f).ctors.map (·.1.name)) = (p₀.ctors.map (·.1.name)).map (Key.map f) := by
    simp [NativeParts.mapKeys, InductiveShape.mapKeys, List.map_map, Function.comp_def]
  have hng : ∀ k ∈ p₀.ctors.map (·.1.name), k.Good P := by
    intro k hk
    simp only [List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    exact (hp₀.ctors c hc).1
  rw [hnames]
  refine SimR.ite (by rw [nodup_map_ren hE.inj hng]) (fun _ => ?_) (fun _ => SimR.throw_bind)
  rw [nativeRawRec_map hE.inj hp₀]
  refine SimR.bind (checkNativePass_sim hops hE hp₀ _) (fun r r' hr => ?_)
  obtain ⟨q, settled⟩ := r
  obtain ⟨q', settled'⟩ := r'
  obtain ⟨hq, rfl⟩ := hr
  simp only []
  refine SimR.ite Iff.rfl (fun _ => checkNativeTail_sim hops hE hq) (fun _ => ?_)
  rw [hq.p', NativeParts.mapKeys_kinds]
  refine SimR.bind (checkNativePass_sim hops hE hp₀ _) (fun r r' hr => ?_)
  obtain ⟨q₂, settled₂⟩ := r
  obtain ⟨q₂', settled₂'⟩ := r'
  obtain ⟨hq₂, rfl⟩ := hr
  simp only []
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  exact checkNativeTail_sim hops hE hq₂

end Ix.Kernel
