module

public import IxC.Kernel.Verify.Rename.Install1

@[expose] public section

/-!
# The renaming walk through the install stages: the constructors (step 7.3, chunk (iii))

Official's positivity walk as a normalisation (`normPosDom`, `normFieldDoms`,
`normCtorVal`), the constructor stage (`checkSumCtor`, `checkSumCtors`), the
constructors' conses, the stored rules (`sumRules`) and the projection table
(`checkStructProjTable`), at renamed arguments over related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-! ## Lists of terms -/

/-- `==` of renamed good lists. -/
theorem list_beq_mapKeys (hf : InjOn f P) {as bs : List (Expr md)} (ha : Expr.GoodList P as)
    (hb : Expr.GoodList P bs) :
    (as.map (Expr.mapKeys f) == bs.map (Expr.mapKeys f)) = (as == bs) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => Expr.mapKeys_list_inj hf ha hb h, fun h => h ▸ rfl⟩

/-! ## Official's positivity walk -/

/-- The positivity normalisation at a renamed domain. -/
theorem normPosDom_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) :
    ∀ (d fuel : Nat) {e : Expr md}, e.Good P →
      SimX P f (normPosDom ops env T d fuel e) (normPosDom ops' env' (T.map f) d fuel (e.mapKeys f))
  | _, 0, _, _ => SimE.throw'
  | d, fuel + 1, e, he => by
    simp only [normPosDom, Expr.mentionsConst_map hE.inj hT he]
    refine SimE.ite Iff.rfl (fun _ => SimE.pure' he rfl) (fun _ => ?_)
    refine SimE.bind (hops.whnf hE d e he) (fun w hw => ?_)
    rw [Expr.mentionsConst_map hE.inj hT hw]
    refine SimE.ite Iff.rfl (fun _ => SimE.pure' hw rfl) (fun _ => ?_)
    cases w with
    | forallE dom body bm =>
      simp only [Expr.Good] at hw
      simp only [Expr.mapKeys, Expr.mentionsConst_map hE.inj hT hw.1]
      refine SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => ?_)
      have hfv : (Expr.fvar d dom : Expr md).Good P := by simpa using hw.1
      have hrec := normPosDom_sim hops hE hT (d + 1) fuel (Expr.Good.instantiate1 hw.2 hfv 0)
      simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at hrec
      refine SimE.bind hrec (fun b hb => ?_)
      exact SimE.pure' ⟨hw.1, Expr.Good.abstract1 hb d 0⟩ (by simp [Expr.mapKeys_abstract1])
    | _ => exact SimE.pure' hw rfl

/-- The fields' normalisation at a renamed telescope. -/
theorem normFieldDoms_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) :
    ∀ (i n : Nat) {e : Expr md}, e.Good P →
      SimE (fun r : List (Expr md × BinderMeta) × Expr md => Expr.BindersGood P r.1 ∧ r.2.Good P)
        (Expr.mapTele f)
        (normFieldDoms ops env T i n e) (normFieldDoms ops' env' (T.map f) i n (e.mapKeys f))
  | _, 0, e, he => by
    refine SimE.pure' ?_ rfl
    exact ⟨fun _ h => (nomatch h), he⟩
  | i, n + 1, e, he => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.Good] at he
      simp only [Expr.mapKeys, normFieldDoms]
      refine SimE.bind (normPosDom_sim hops hE hT i 1024 he.1) (fun dom' hdom' => ?_)
      have hfv : (Expr.fvar i dom : Expr md).Good P := by simpa using he.1
      have hrec := normFieldDoms_sim hops hE hT (i + 1) n (Expr.Good.instantiate1 he.2 hfv 0)
      simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at hrec
      refine SimE.bind hrec (fun r hr => ?_)
      obtain ⟨bs, res⟩ := r
      refine SimE.pure' ⟨?_, hr.2⟩ (by simp [Expr.mapTele])
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hdom'
      · exact hr.1 b hb
    | _ => exact SimE.throw'

theorem zipWith_fvarTypeD_map (fvs : List (Expr md)) (cbs : List (Expr md × BinderMeta)) :
    List.zipWith (fun (x : Expr md') (b : Expr md' × BinderMeta) => (x.fvarTypeD, b.2))
        (fvs.map (Expr.mapKeys f)) (Expr.mapBinders f cbs) =
      Expr.mapBinders f
        (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) fvs cbs) := by
  induction fvs generalizing cbs with
  | nil => rfl
  | cons x xs ih =>
    cases cbs with
    | nil => rfl
    | cons b bs =>
      obtain ⟨t, m⟩ := b
      simp [List.zipWith_cons_cons, Expr.mapBinders_cons, ih, Expr.mapKeys_fvarTypeD]

theorem zipWith_fvarTypeD_good : ∀ {fvs : List (Expr md)}, Expr.GoodList P fvs →
    ∀ (cbs : List (Expr md × BinderMeta)), Expr.BindersGood P
      (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) fvs cbs)
  | [], _, cbs => by
    simp only [List.zipWith_nil_left]
    exact fun _ h => nomatch h
  | _ :: _, _, [] => by
    simp only [List.zipWith_nil_right]
    exact fun _ h => nomatch h
  | x :: xs, h, b :: bs => by
    simp only [Expr.goodList_cons] at h
    simp only [List.zipWith_cons_cons, Expr.BindersGood, List.mem_cons]
    rintro b' (rfl | hb')
    · exact h.1.fvarTypeD
    · exact zipWith_fvarTypeD_good h.2 bs b' hb'

theorem Expr.mapBinders_append (as bs : List (Expr md × BinderMeta)) :
    Expr.mapBinders f (as ++ bs) = Expr.mapBinders f as ++ Expr.mapBinders f bs := by
  simp [Expr.mapBinders]

/-- The constructor with its field domains normalised, at a renamed constructor. -/
theorem normCtorVal_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P) (nP nF : Nat)
    {cvC cvCa : ConstantVal md} (hC : cvC.Good P) (hCa : cvCa.Good P) :
    SimE (ConstantVal.Good P) (ConstantVal.mapKeys f) (normCtorVal ops env T nP nF cvC cvCa)
      (normCtorVal ops' env' (T.map f) nP nF (cvC.mapKeys f) (cvCa.mapKeys f)) := by
  unfold normCtorVal
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys, openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md × BinderMeta) × Expr md => Expr.BindersGood P q.1)
    (fun q hq => (Expr.stripPis_good hCa.2 hq).1)) (fun q _ => ?_)
  obtain ⟨cbs, _⟩ := q
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hCa.2 hq)) (fun q hq => ?_)
  obtain ⟨fvsP, crest⟩ := q
  simp only [Expr.mapDoms, Expr.mapTele]
  refine SimE.bind (normFieldDoms_sim hops hE hT nP nF hq.2) (fun r hr => ?_)
  obtain ⟨fbs, resid⟩ := r
  simp only [Expr.mapTele, zipWith_fvarTypeD_map, ← Expr.mapBinders_append, closeTelescope_mapKeys]
  have hty : (closeTelescope (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) =>
      (x.fvarTypeD, b.2)) fvsP cbs ++ fbs) 0 resid).Good P := by
    refine closeTelescope_good 0 ?_ hr.2
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact zipWith_fvarTypeD_good hq.1 cbs b hb
    · exact hr.1 b hb
  rw [Expr.mapKeys_beq hE.inj hty hCa.2]
  refine SimE.ite Iff.rfl (fun _ => SimE.pure' hCa rfl) (fun _ => ?_)
  rw [← ConstantVal.mapKeys_withType]
  exact checkConstantVal_sim hops hE ⟨hC.1, hty⟩

/-! ## The constructor stage -/

/-- **One constructor's stage at a renamed constructor**: over the related
pre-block environments and the related environments holding the former. -/
theorem checkSumCtor_sim (hops : OpsSim P f L ops ops') {env₀ env : Env md} {env₀' env' : Env md'}
    (hE₀ : EnvRelG P f L env₀ env₀') (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    {cvC : ConstantVal md} (hC : cvC.Good P) (nF : Nat) {cvTa : ConstantVal md}
    (hTa : cvTa.Good P) :
    SimE (fun r : ConstantVal md × List Level => r.1.Good P) (fun r => (r.1.mapKeys f, r.2))
      (checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa)
      (checkSumCtor ops' env₀' env' (T.map f) lps nP nIdx resSort isProp large (cvC.mapKeys f) nF
        (cvTa.mapKeys f)) := by
  unfold checkSumCtor
  refine SimE.bind (checkConstantVal_sim hops hE hC) (fun cvCa₀ h₀ => ?_)
  refine SimE.bind (normCtorVal_sim hops hE hT nP nF hC h₀) (fun cvCa hCa => ?_)
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys, openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md × BinderMeta) × Expr md => q.2.Good P)
    (fun q hq => (Expr.stripPis_good hCa.2 hq).2)) (fun q hq => ?_)
  obtain ⟨_, cbody⟩ := q
  simp only [Expr.mapTele, structCtorResidOk_map hE.inj hT lps nP nF nIdx hq]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hCa.2 hq)) (fun cq hcq => ?_)
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hTa.2 hq)) (fun tq htq => ?_)
  obtain ⟨cfvs, crest⟩ := cq
  obtain ⟨tfvs, trest⟩ := tq
  simp only [Expr.mapDoms, map_fvarTypeD_mapKeys]
  refine SimE.bind (checkStructDomsAt_sim hops hE 0 hcq.1 htq.1.map_fvarTypeD nP) (fun _ _ => ?_)
  rw [openPisAtFvars_mapKeys]
  refine SimE.bind (SimE.unwrapOr'
    (G := fun q : List (Expr md) × Expr md => Expr.GoodList P q.1 ∧ q.2.Good P)
    (fun q hq => Expr.openPisAtFvars_good hcq.2 hq)) (fun xq hxq => ?_)
  obtain ⟨xfvs, xres⟩ := xq
  simp only [Expr.mapDoms, ← Expr.mapKeys_getAppFn, Expr.getAppArgs_mapKeys, ← List.map_take,
    List.length_map]
  have hfn : (Expr.const (T.map f) (lps.map Level.param) : Expr md') =
      (Expr.const T (lps.map Level.param) : Expr md).mapKeys f := rfl
  rw [hfn, Expr.mapKeys_beq hE.inj hxq.2.getAppFn (show Expr.Good P (Expr.const T _) from hT),
    list_beq_mapKeys hE.inj (hxq.2.getAppArgs.take nP) hcq.1]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hall1 : (xfvs.map (Expr.mapKeys f)).all (fun x => x.fvarTypeD.constsResolve env₀') =
      xfvs.all (fun x => x.fvarTypeD.constsResolve env₀) := by
    rw [List.all_map]
    exact List.all_congr_mem' fun x hx => by
      simp only [Function.comp, ← Expr.mapKeys_fvarTypeD]
      exact constsResolve_ren hE₀ (hxq.1 x hx).fvarTypeD
  rw [hall1]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  have hall2 : ((xres.getAppArgs.map (Expr.mapKeys f)).drop nP).all (fun e => e.constsResolve env₀') =
      (xres.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) := by
    rw [← List.map_drop, List.all_map]
    exact List.all_congr_mem' fun x hx => by
      simp only [Function.comp]
      exact constsResolve_ren hE₀ (hxq.2.getAppArgs.drop nP x hx)
  rw [hall2]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
  rw [← List.map_drop]
  refine SimE.bind (checkStructFieldSortsI_sim hops hE isProp large resSort nP hxq.1
    (hxq.2.getAppArgs.drop nP) nF) (fun sorts _ => ?_)
  exact SimE.pure' hCa rfl

/-- All constructors' stages at renamed constructors. -/
theorem checkSumCtors_sim (hops : OpsSim P f L ops ops') {env₀ env : Env md} {env₀' env' : Env md'}
    (hE₀ : EnvRelG P f L env₀ env₀') (hE : EnvRelG P f L env env') {T : Key md} (hT : T.Good P)
    (lps : List LevelParam) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    {cvTa : ConstantVal md} (hTa : cvTa.Good P) :
    ∀ (cs : List (ConstantVal md × Nat)), (∀ c ∈ cs, c.1.Good P) →
      SimE (fun r : List (ConstantVal md × Nat) × List (List Level) => ∀ c ∈ r.1, c.1.Good P)
        (fun r => (r.1.map fun c => (c.1.mapKeys f, c.2), r.2))
        (checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs)
        (checkSumCtors ops' env₀' env' (T.map f) lps nP nIdx resSort isProp large (cvTa.mapKeys f)
          (cs.map fun c => (c.1.mapKeys f, c.2)))
  | [], _ => SimE.pure' (fun _ h => nomatch h) rfl
  | c :: cs, hcs => by
    simp only [List.map_cons, checkSumCtors]
    refine SimE.bind (checkSumCtor_sim hops hE₀ hE hT lps nP nIdx resSort isProp large
      (hcs c List.mem_cons_self) c.2 hTa) (fun r hr => ?_)
    obtain ⟨cvCa, sorts⟩ := r
    refine SimE.bind (checkSumCtors_sim hops hE₀ hE hT lps nP nIdx resSort isProp large hTa cs
      (fun c' h => hcs c' (List.mem_cons_of_mem _ h))) (fun r' hr' => ?_)
    obtain ⟨rest, srest⟩ := r'
    refine SimE.pure' ?_ rfl
    intro c' hc'
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact hr
    · exact hr' c' hc'

/-- The constructors' conses keep related environments related. -/
theorem consSumCtors_rel (nP : Nat) :
    ∀ (cs : List (ConstantVal md × Nat)), (∀ c ∈ cs, c.1.Good P) →
      ∀ {env : Env md} {env' : Env md'}, EnvRelG P f L env env' →
        EnvRelG P f L (consSumCtors nP cs env)
          (consSumCtors nP (cs.map fun c => (c.1.mapKeys f, c.2)) env')
  | [], _, _, _, hE => hE
  | c :: cs, hcs, env, env', hE => by
    simp only [List.map_cons, consSumCtors]
    exact consSumCtors_rel nP cs (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
      (hE.push (c := .ctorInfo c.1 nP c.2) (hcs c List.mem_cons_self))

/-! ## The stored rules -/

theorem sumRules_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') {recName : Key md}
    (hrn : recName.Good P) (nP mI rP : Nat) (recTy : Expr md) :
    ∀ (cs : List (ConstantVal md × Nat)) (rhss : List (Expr md)), (∀ c ∈ cs, c.1.Good P) →
      Expr.GoodList P rhss →
      sumRules env'.find? (recName.map f) nP mI rP (recTy.mapKeys f)
          (cs.map fun c => (c.1.mapKeys f, c.2)) (rhss.map (Expr.mapKeys f)) =
        (sumRules env.find? recName nP mI rP recTy cs rhss).map (RecRule.mapKeys f)
  | c :: cs, rhs :: rhss, hcs, hrhss => by
    simp only [Expr.goodList_cons] at hrhss
    simp only [List.map_cons, sumRules, List.map_cons, Expr.recRulePlain_mapKeys]
    have hrl : RecRule.Good P
        ({ ctor := c.1.name, nfields := c.2, ctorParams := nP,
           fire := (if Expr.recRulePlain recTy mI rP nP then .plain else .inert),
           rhs := rhs, paramsBlind := true } : RecRule md) := by
      refine ⟨(hcs c List.mem_cons_self).1, ?_, hrhss.1⟩
      split <;> trivial
    have h := recRuleBits_ren hE (recName := recName) hrl
    congr 1
    · rw [← h]
      simp only [RecRule.mapKeys, ConstantVal.mapKeys_name]
      split <;> rfl
    · exact sumRules_ren hE hrn nP mI rP recTy cs rhss
        (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) hrhss.2
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem sumRules_good {find? : Key md → Option (ConstantInfo md)} {recName : Key md}
    (nP mI rP : Nat) (recTy : Expr md) :
    ∀ (cs : List (ConstantVal md × Nat)) (rhss : List (Expr md)), (∀ c ∈ cs, c.1.Good P) →
      Expr.GoodList P rhss → ∀ r ∈ sumRules find? recName nP mI rP recTy cs rhss, r.Good P
  | c :: cs, rhs :: rhss, hcs, hrhss, r, hr => by
    simp only [Expr.goodList_cons] at hrhss
    simp only [sumRules, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨(hcs c List.mem_cons_self).1, ?_, hrhss.1⟩
      simp only [recRuleBits]
      split <;> trivial
    · exact sumRules_good nP mI rP recTy cs rhss
        (fun c' h' => hcs c' (List.mem_cons_of_mem _ h')) hrhss.2 r hr
  | [], _, _, _, r, hr => by simp [sumRules] at hr
  | _ :: _, [], _, _, r, hr => by simp [sumRules] at hr

end Ix.Kernel
