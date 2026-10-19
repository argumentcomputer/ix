module

public import IxC.Kernel.Verify.Rename.Shape
public import IxC.Kernel.Verify.Rename.Ind3
public import IxC.Kernel.Inductives.SumInstall

@[expose] public section

/-!
# The renaming walk through the install stages: the shared stages (step 7.3, chunk (iii))

The former's telescope (`whnfTelescope`, `closeTelescope`, `checkSumTele`,
`checkSumInd`), the binder-domain pins (`checkStructDomsAt`) and the field-sort
walk (`checkStructFieldSortsI`) of `IxC/Kernel/Inductives/SumInstall.lean` and
`StructInstall.lean`, at renamed arguments over related environments.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-- `unwrapOr` at a renamed option. -/
theorem SimE.unwrapOr' {α α' : Type} {G : α → Prop} {g : α → α'} {o : Option α}
    {e : CheckError md} {e' : CheckError md'} (hG : ∀ a, o = some a → G a) :
    SimE G g (unwrapOr (m := CheckM md) o e) (unwrapOr (m := CheckM md') (o.map g) e') := by
  cases h : o with
  | none => exact SimE.throw'
  | some a => exact SimE.pure' (hG a h) rfl

/-- The binder-domain pins at renamed telescopes. -/
theorem checkStructDomsAt_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') (off : Nat) {fvs doms : List (Expr md)}
    (hfvs : Expr.GoodList P fvs) (hdoms : Expr.GoodList P doms) :
    ∀ n, SimV (checkStructDomsAt ops env off fvs doms n)
      (checkStructDomsAt ops' env' off (fvs.map (Expr.mapKeys f)) (doms.map (Expr.mapKeys f)) n)
  | 0 => SimV.pureT ()
  | j + 1 => by
    simp only [checkStructDomsAt, List.getElem?_map]
    refine SimE.bind (SimE.unwrapOr' (G := Expr.Good P)
      (fun a h => hfvs a (List.mem_of_getElem? h))) (fun a ha => ?_)
    refine SimE.bind (SimE.unwrapOr' (G := Expr.Good P)
      (fun b h => hdoms b (List.mem_of_getElem? h))) (fun b hb => ?_)
    rw [← Expr.mapKeys_fvarTypeD]
    refine SimE.bind (hops.isDefEq hE (off + j) _ b ha.fvarTypeD hb) (fun c _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
    exact checkStructDomsAt_sim hops hE off hfvs hdoms j

/-! ## The former's telescope -/

/-- Official's telescope loop at a renamed type. -/
theorem whnfTelescope_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') :
    ∀ (i n : Nat) {e : Expr md}, e.Good P →
      SimE (fun r : List (Expr md × BinderMeta) × Level => Expr.BindersGood P r.1)
        (fun r => (Expr.mapBinders f r.1, r.2))
        (whnfTelescope ops env i n e) (whnfTelescope ops' env' i n (e.mapKeys f))
  | i, 0, e, he => by
    simp only [whnfTelescope]
    refine SimE.bind (hops.whnf hE i e he) (fun w _ => ?_)
    cases w with
    | sort s => exact SimE.pure' (fun _ h => nomatch h) rfl
    | _ => exact SimE.throw'
  | i, n + 1, e, he => by
    simp only [whnfTelescope]
    refine SimE.bind (hops.whnf hE i e he) (fun w hw => ?_)
    cases w with
    | forallE dom body bm =>
      simp only [Expr.Good] at hw
      have hfv : (Expr.fvar i dom : Expr md).Good P := by simpa using hw.1
      have hrec := whnfTelescope_sim hops hE (i + 1) n (Expr.Good.instantiate1 hw.2 hfv 0)
      simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at hrec
      simp only [Expr.mapKeys]
      refine SimE.bind hrec (fun r hr => ?_)
      obtain ⟨bs, s⟩ := r
      refine SimE.pure' ?_ (by simp)
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hw.1
      · exact hr b hb
    | _ => exact SimE.throw'

/-- Closing a renamed telescope. -/
theorem closeTelescope_mapKeys : ∀ (bs : List (Expr md × BinderMeta)) (i : Nat) (body : Expr md),
    closeTelescope (Expr.mapBinders f bs) i (body.mapKeys f) = (closeTelescope bs i body).mapKeys f
  | [], _, _ => rfl
  | (dom, bm) :: bs, i, body => by
    simp only [Expr.mapBinders_cons, closeTelescope, closeTelescope_mapKeys bs (i + 1) body,
      Expr.mapKeys_abstract1, Expr.mapKeys]

theorem closeTelescope_good : ∀ {bs : List (Expr md × BinderMeta)} (i : Nat) {body : Expr md},
    Expr.BindersGood P bs → body.Good P → (closeTelescope bs i body).Good P
  | [], _, _, _, hb => hb
  | (dom, bm) :: bs, i, body, hbs, hb => by
    simp only [closeTelescope, Expr.Good]
    refine ⟨hbs _ List.mem_cons_self, Expr.Good.abstract1 ?_ i 0⟩
    exact closeTelescope_good (i + 1) (fun b h => hbs b (List.mem_cons_of_mem _ h)) hb

/-- A header with its type replaced, renamed. -/
theorem ConstantVal.mapKeys_withType (cv : ConstantVal md) (t : Expr md) :
    ({ cv with type := t } : ConstantVal md).mapKeys f = { cv.mapKeys f with type := t.mapKeys f } :=
  rfl

/-- The former's telescope stage at a renamed former. -/
theorem checkSumTele_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {cv cvTa₀ : ConstantVal md} (hcv : cv.Good P)
    (hTa : cvTa₀.Good P) (n : Nat) :
    SimE (fun r : ConstantVal md × Level => r.1.Good P) (fun r => (r.1.mapKeys f, r.2))
      (checkSumTele ops env cv n cvTa₀)
      (checkSumTele ops' env' (cv.mapKeys f) n (cvTa₀.mapKeys f)) := by
  have hgen : SimE (fun r : ConstantVal md × Level => r.1.Good P) (fun r => (r.1.mapKeys f, r.2))
      (do
        let (bs, s) ← whnfTelescope ops env 0 n cvTa₀.type
        let cvTa ← checkConstantVal ops env { cv with type := closeTelescope bs 0 (.sort s) }
        pure (cvTa, s))
      (do
        let (bs, s) ← whnfTelescope ops' env' 0 n (cvTa₀.mapKeys f).type
        let cvTa ← checkConstantVal ops' env' { cv.mapKeys f with type := closeTelescope bs 0 (.sort s) }
        pure (cvTa, s)) := by
    simp only [ConstantVal.mapKeys_type]
    refine SimE.bind (whnfTelescope_sim hops hE 0 n hTa.2) (fun r hr => ?_)
    obtain ⟨bs, s⟩ := r
    simp only []
    have hty : closeTelescope (Expr.mapBinders f bs) 0 (.sort s) =
        (closeTelescope bs 0 (.sort s) : Expr md).mapKeys f :=
      closeTelescope_mapKeys bs 0 (.sort s)
    rw [hty, ← ConstantVal.mapKeys_withType]
    refine SimE.bind (checkConstantVal_sim hops hE
      (cv := { cv with type := closeTelescope bs 0 (.sort s) })
      ⟨hcv.1, closeTelescope_good 0 hr trivial⟩) (fun cvTa hcvTa => ?_)
    exact SimE.pure' hcvTa rfl
  unfold checkSumTele
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
  cases h : cvTa₀.type.stripPis n with
  | none => exact hgen
  | some p =>
    obtain ⟨bs, b⟩ := p
    cases b with
    | sort s => exact SimE.pure' hTa rfl
    | _ => exact hgen

/-- **The former's stage at a renamed shape**: the environments it returns
stay related, its constant and shape are the renamed ones. -/
theorem checkSumInd_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {p : InductiveShape md} (hp : p.Good P)
    {capsOf : InductiveShape md → IndCaps md} {capsOf' : InductiveShape md' → IndCaps md'}
    (hcaps : ∀ q : InductiveShape md, q.Good P →
      capsOf' (q.mapKeys f) = (capsOf q).mapKeys f ∧ (capsOf q).Good P) :
    SimR (fun (r : Env md × ConstantVal md × InductiveShape md)
        (r' : Env md' × ConstantVal md' × InductiveShape md') =>
        EnvRel P f r.1 r'.1 ∧ r.2.1.Good P ∧ r'.2.1 = r.2.1.mapKeys f ∧ r.2.2.Good P ∧
          r'.2.2 = r.2.2.mapKeys f)
      (checkSumInd ops env p capsOf) (checkSumInd ops' env' (p.mapKeys f) capsOf') := by
  unfold checkSumInd
  have hcvT : (p.mapKeys f).cvT = p.cvT.mapKeys f := rfl
  have hn : (p.mapKeys f).nP + (p.mapKeys f).nIdx = p.nP + p.nIdx := rfl
  rw [hcvT, hn]
  refine SimR.bindE (checkConstantVal_sim hops hE hp.cvT) (fun cvTa₀ h₀ => ?_)
  refine SimR.bindE (checkSumTele_sim hops hE hp.cvT h₀ _) (fun r hr => ?_)
  obtain ⟨cvTa, s⟩ := r
  simp only [ConstantVal.mapKeys_type, Expr.stripPis_mapKeys]
  refine SimR.bindE (SimE.unwrapOr' (G := fun q : List (Expr md × BinderMeta) × Expr md => q.2.Good P)
    (fun q hq => (Expr.stripPis_good hr.2 hq).2)) (fun q hq => ?_)
  obtain ⟨_, tbody⟩ := q
  simp only [Expr.mapTele]
  have htb : (tbody.mapKeys f == Expr.sort s) = (tbody == Expr.sort s) := by
    rw [show (Expr.sort s : Expr md') = (Expr.sort s : Expr md).mapKeys f from rfl,
      Expr.mapKeys_beq hE.inj hq (show (Expr.sort s : Expr md).Good P from trivial)]
  refine SimR.ite (by rw [htb]) (fun _ => ?_) (fun _ => SimR.throw_bind)
  have hps : (p.mapKeys f).withSort s = (p.withSort s).mapKeys f := rfl
  have hpg : (p.withSort s).Good P := ⟨hp.cvT, hp.ctors, hp.cvR, hp.rhss⟩
  obtain ⟨hc, hcg⟩ := hcaps _ hpg
  rw [hps, hc]
  refine SimR.pure' ⟨?_, hr, rfl, hpg, rfl⟩
  exact hE.push (c := .indInfo cvTa (capsOf (p.withSort s))) ⟨hr, hcg⟩

/-! ## The fields' sorts -/

/-- `contains` of a renamed list of good terms, at a renamed good term. -/
theorem contains_mapKeys_ren (hf : InjOn f P) : ∀ {l : List (Expr md)}, Expr.GoodList P l →
    ∀ {e : Expr md}, e.Good P → (l.map (Expr.mapKeys f)).contains (e.mapKeys f) = l.contains e
  | [], _, _, _ => rfl
  | a :: as, hl, e, he => by
    simp only [Expr.goodList_cons] at hl
    simp only [List.map_cons, List.contains_cons, Expr.mapKeys_beq hf he hl.1,
      contains_mapKeys_ren hf hl.2 he]

/-- The field-sort walk at renamed fields. -/
theorem checkStructFieldSortsI_sim (hops : OpsSim P f ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') (isProp large : Bool) (s : Level) (nP : Nat)
    {fvs idxArgs : List (Expr md)} (hfvs : Expr.GoodList P fvs) (hidx : Expr.GoodList P idxArgs) :
    ∀ n, SimV (checkStructFieldSortsI ops env isProp large s nP fvs idxArgs n)
      (checkStructFieldSortsI ops' env' isProp large s nP (fvs.map (Expr.mapKeys f))
        (idxArgs.map (Expr.mapKeys f)) n)
  | 0 => SimV.pureT []
  | j + 1 => by
    simp only [checkStructFieldSortsI, List.getElem?_map]
    refine SimE.bind (SimE.unwrapOr' (G := Expr.Good P)
      (fun a h => hfvs a (List.mem_of_getElem? h))) (fun fv hfv => ?_)
    rw [← Expr.mapKeys_fvarTypeD]
    refine SimE.bind (hops.inferType hE (nP + j) _ hfv.fvarTypeD) (fun ty hty => ?_)
    refine SimE.bind (hops.ensureSort hE (nP + j) ty hty) (fun u _ => ?_)
    have hcont := checkStructFieldSortsI_sim hops hE isProp large s nP hfvs hidx j
    have hc := contains_mapKeys_ren hE.inj hidx hfv
    split
    · refine SimE.bind (SimE.liftFueled _ _) (fun ok _ => ?_)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.bind hcont (fun rest _ => ?_)
      exact SimV.pureT _
    · split
      · refine SimE.ite (by simp only [id, hc]) (fun _ => ?_) (fun _ => SimE.throw_bind)
        refine SimE.bind hcont (fun rest _ => ?_)
        exact SimV.pureT _
      · refine SimE.bind hcont (fun rest _ => ?_)
        exact SimV.pureT _

end Ix.Kernel
