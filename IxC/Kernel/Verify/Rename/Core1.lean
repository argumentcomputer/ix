module

public import IxC.Kernel.Verify.Rename.PropRead

@[expose] public section

/-!
# The renaming walk through the core, part 1: certificates and literals

The bodies of `IxC/Kernel/Core.lean` before reduction proper, each at a
renamed argument, over related core records (`CoreSim`) and environments
(`EnvRel`): the literal acceleration `reduceNat`, the spine certificates
`iotaCerts`, `defEqList`, `iotaIndexOk`, and proof irrelevance
(`proofIrrel`, `propIrrel`).
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {env : Env md} {env' : Env md'}
variable {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}

/-- Simulation of a key-free result: equal successes. -/
abbrev SimV {α : Type} (x : CheckM md α) (x' : CheckM md' α) : Prop :=
  SimE (fun _ => True) id x x'

/-- Simulation of a term result. -/
abbrev SimX (P : md.Id → Prop) (f : md.Id → md'.Id) (x : CheckM md (Expr md))
    (x' : CheckM md' (Expr md')) : Prop :=
  SimE (Expr.Good P) (Expr.mapKeys f) x x'

/-- Simulation of an optional term result. -/
abbrev SimO (P : md.Id → Prop) (f : md.Id → md'.Id) (x : CheckM md (Option (Expr md)))
    (x' : CheckM md' (Option (Expr md'))) : Prop :=
  SimE (fun o => ∀ e ∈ o, Expr.Good P e) (Option.map (Expr.mapKeys f)) x x'

theorem SimV.pureT {α : Type} (a : α) : SimV (pure a : CheckM md α) (pure a : CheckM md' α) :=
  SimE.pure' trivial rfl

/-! ## Readers -/

theorem isUnitLikeTy_ren (hE : EnvRelG P f L env env') {e : Expr md} (he : e.Good P) :
    isUnitLikeTy env' (e.mapKeys f) = isUnitLikeTy env e := by
  cases e with
  | const c us =>
    simp only [Expr.mapKeys, isUnitLikeTy, Key.map_beq_role, hE.find_role]
    congr 1
    · congr 1
      cases env.find? punitName with
      | none => rfl
      | some ci => cases ci <;> rfl
    · cases env.find? punitRecName with
      | none => rfl
      | some ci =>
        cases ci with
        | recInfo cv mI rP rules =>
          rcases rules with _ | ⟨rl, _ | _⟩ <;> rfl
        | _ => rfl
  | _ => rfl

theorem natOpResult_good (c : Key md) (a b : Nat) : ∀ e ∈ natOpResult c a b, e.Good P := by
  intro e he
  rcases c with i | r | ⟨k, d⟩
  · simp [natOpResult] at he
  · cases r <;> simp [natOpResult] at he <;>
      first
        | (subst he; trivial)
        | (obtain ⟨-, rfl⟩ := he; trivial)
        | (subst he; split <;> trivial)
  · simp [natOpResult] at he

@[simp] theorem mem_natOpWfNames_map (k : Key md) :
    k.map f ∈ (natOpWfNames (md := md')) ↔ k ∈ (natOpWfNames (md := md)) := by
  simp [natOpWfNames]

@[simp] theorem mem_natOpNames_map (k : Key md) :
    k.map f ∈ (natOpNames (md := md')) ↔ k ∈ (natOpNames (md := md)) := by
  simp [natOpNames]

@[simp] theorem mem_natDivModNames_map (k : Key md) :
    k.map f ∈ (natDivModNames (md := md')) ↔ k ∈ (natDivModNames (md := md)) := by
  simp [natDivModNames]

/-! ## Literal acceleration -/

theorem reduceNat_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {e : Expr md} (he : e.Good P) :
    SimO P f (reduceNat r env d e) (reduceNat r' env' d (e.mapKeys f)) := by
  unfold reduceNat
  rcases e with _ | _ | _ | _ |
    ⟨_ | _ | _ | ⟨c, _ | _⟩ | ⟨_ | _ | _ | ⟨c, _ | _⟩ | _ | _ | _ | _ | _ | _, a⟩ |
      _ | _ | _ | _ | _, b⟩ | _ | _ | _ | _ | _ <;>
    simp only [Expr.mapKeys] <;>
    first
      | exact SimE.pure' (fun _ h => nomatch h) rfl
      | skip
  · -- `Nat.succ` on a literal
    have hb : b.Good P := he.2
    refine SimE.ite (by simp [natLitSupported_ren hE]) (fun _ => ?_) (fun _ => ?_)
    · refine SimE.bind (hr.whnf d b hb) (fun w _ => ?_)
      rw [rawNatLit?_mapKeys]
      cases rawNatLit? w with
      | none => exact SimE.pure' (fun _ h => nomatch h) rfl
      | some n => exact SimE.pure' (fun _ h => by cases h; trivial) rfl
    · exact SimE.pure' (fun _ h => nomatch h) rfl
  · -- a binary operation on literals
    have hc : c.Good P := he.1.1
    have ha : a.Good P := he.1.2
    have hb : b.Good P := he.2
    refine SimE.ite (by simp [natOpStored_ren hE hc]) (fun _ => ?_) (fun _ => ?_)
    · refine SimE.bind (hr.whnf d a ha) (fun w _ => ?_)
      rw [rawNatLit?_mapKeys]
      cases rawNatLit? w with
      | none => exact SimE.pure' (fun _ h => nomatch h) rfl
      | some n₁ =>
        refine SimE.bind (hr.whnf d b hb) (fun w₂ _ => ?_)
        rw [rawNatLit?_mapKeys]
        cases rawNatLit? w₂ with
        | none => exact SimE.pure' (fun _ h => nomatch h) rfl
        | some n₂ => exact SimE.pure' (natOpResult_good c n₁ n₂) (natOpResult_map c n₁ n₂)
    · refine SimE.ite (by simp [natLitSupported_ren hE]) (fun _ => ?_) (fun _ => ?_)
      · refine SimE.bind (hr.whnf d a ha) (fun w _ => ?_)
        rw [rawNatLit?_mapKeys]
        cases rawNatLit? w with
        | none => exact SimE.pure' (fun _ h => nomatch h) rfl
        | some n₁ =>
          refine SimE.bind (hr.whnf d b hb) (fun w₂ _ => ?_)
          rw [rawNatLit?_mapKeys]
          cases rawNatLit? w₂ with
          | none => exact SimE.pure' (fun _ h => nomatch h) rfl
          | some n₂ => exact SimE.throw'
      · exact SimE.pure' (fun _ h => nomatch h) rfl

/-! ## Spine certificates -/

theorem iotaCerts_sim (hr : CoreSim P f r r') (d : Nat) (lic : Bool) :
    ∀ (args : List (Expr md)) (ty : Expr md), ty.Good P → Expr.GoodList P args →
      SimV (iotaCerts r env d lic ty args)
        (iotaCerts r' env' d lic (ty.mapKeys f) (args.map (Expr.mapKeys f)))
  | [], ty, _, _ => by cases ty <;> exact SimV.pureT true
  | a :: as, ty, hty, has => by
    simp only [Expr.goodList_cons] at has
    cases ty with
    | forallE t b mb =>
      simp only [Expr.mapKeys, List.map_cons, iotaCerts]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · rw [← Expr.mapKeys_instantiate1]
        exact iotaCerts_sim hr d lic as _ (Expr.Good.instantiate1 hty.2 has.1 0) has.2
      · refine SimE.bind (hr.inferIO d a has.1) (fun ta hta => ?_)
        refine SimE.bind (hr.defeq d ta t hta hty.1) (fun ok _ => ?_)
        refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimV.pureT false)
        rw [← Expr.mapKeys_instantiate1]
        exact iotaCerts_sim hr d lic as _ (Expr.Good.instantiate1 hty.2 has.1 0) has.2
    | _ => exact SimV.pureT false

theorem defEqList_sim (hr : CoreSim P f r r') (d : Nat) :
    ∀ (as bs : List (Expr md)), Expr.GoodList P as → Expr.GoodList P bs →
      SimV (defEqList r env d as bs)
        (defEqList r' env' d (as.map (Expr.mapKeys f)) (bs.map (Expr.mapKeys f)))
  | [], [], _, _ => SimV.pureT true
  | [], _ :: _, _, _ => SimV.pureT false
  | _ :: _, [], _, _ => SimV.pureT false
  | a :: as, b :: bs, has, hbs => by
    simp only [Expr.goodList_cons] at has hbs
    simp only [List.map_cons, defEqList]
    refine SimE.bind (hr.defeq d a b has.1 hbs.1) (fun ok _ => ?_)
    exact SimE.ite Iff.rfl (fun _ => defEqList_sim hr d as bs has.2 hbs.2)
      (fun _ => SimV.pureT false)

theorem Expr.GoodList.drop {as : List (Expr md)} (h : Expr.GoodList P as) (n : Nat) :
    Expr.GoodList P (as.drop n) := fun x hx => h x (List.mem_of_mem_drop hx)

theorem Expr.GoodList.take {as : List (Expr md)} (h : Expr.GoodList P as) (n : Nat) :
    Expr.GoodList P (as.take n) := fun x hx => h x (List.mem_of_mem_take hx)

theorem iotaIndexOk_sim (hr : CoreSim P f r r') (d mI rP cnP : Nat) {tyCtor : Expr md}
    (hty : tyCtor.Good P) {margs idx : List (Expr md)} (hm : Expr.GoodList P margs)
    (hi : Expr.GoodList P idx) :
    SimV (iotaIndexOk r env d mI rP cnP tyCtor margs idx)
      (iotaIndexOk r' env' d mI rP cnP (tyCtor.mapKeys f) (margs.map (Expr.mapKeys f))
        (idx.map (Expr.mapKeys f))) := by
  unfold iotaIndexOk
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  rw [piResidual_mapKeys]
  cases hres : piResidual tyCtor margs with
  | none => exact SimV.pureT false
  | some res =>
    have hg := piResidual_good hty hm hres
    simp only [Option.map_some]
    rw [Expr.getAppArgs_mapKeys, ← List.map_drop]
    exact defEqList_sim hr d _ _ ((Expr.Good.getAppArgs hg).drop cnP) hi

/-! ## Proof irrelevance -/

theorem proofIrrel_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (proofIrrel r env d a b) (proofIrrel r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold proofIrrel
  refine SimE.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine SimE.bind (hr.whnf d ta hta) (fun wa hwa => ?_)
  rw [isUnitLikeTy_ren hE hwa]
  refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
  · refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
    refine SimE.bind (hr.whnf d tb htb) (fun wb hwb => ?_)
    rw [isUnitLikeTy_ren hE hwb]
    exact SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => SimV.pureT false)
  · refine SimE.bind (hr.inferIO d ta hta) (fun tta htta => ?_)
    refine SimE.bind (hr.whnf d tta htta) (fun w _ => ?_)
    cases w with
    | sort uT =>
      refine SimE.bind (SimE.liftFueled _ _) (fun okA _ => ?_)
      refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
      refine SimE.bind (hr.inferIO d tb htb) (fun ttb httb => ?_)
      refine SimE.bind (hr.whnf d ttb httb) (fun w₂ _ => ?_)
      cases w₂ with
      | sort vT =>
        refine SimE.bind (SimE.liftFueled _ _) (fun okB _ => ?_)
        exact SimV.pureT _
      | _ => exact SimV.pureT false
    | _ => exact SimV.pureT false

theorem propIrrel_sim (hE : EnvRelG P f L env env') (hr : CoreSim P f r r') (d : Nat)
    {a b : Expr md} (ha : a.Good P) (hb : b.Good P) :
    SimV (propIrrel r env d a b) (propIrrel r' env' d (a.mapKeys f) (b.mapKeys f)) := by
  unfold propIrrel
  rw [notProofFast_ren hE ha, notProofFast_ren hE hb, isProofFast_ren hE ha,
    isProofFast_ren hE hb]
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT false) (fun _ => ?_)
  refine SimE.ite Iff.rfl (fun _ => SimV.pureT true) (fun _ => ?_)
  refine SimE.bind (hr.inferIO d a ha) (fun ta hta => ?_)
  refine SimE.bind (hr.inferIO d ta hta) (fun tta htta => ?_)
  refine SimE.bind (hr.whnf d tta htta) (fun w _ => ?_)
  cases w with
  | sort uT =>
    refine SimE.bind (SimE.liftFueled _ _) (fun okA _ => ?_)
    refine SimE.bind (hr.inferIO d b hb) (fun tb htb => ?_)
    refine SimE.bind (hr.inferIO d tb htb) (fun ttb httb => ?_)
    refine SimE.bind (hr.whnf d ttb httb) (fun w₂ _ => ?_)
    cases w₂ with
    | sort vT =>
      refine SimE.bind (SimE.liftFueled _ _) (fun okB _ => ?_)
      exact SimV.pureT _
    | _ => exact SimV.pureT false
  | _ => exact SimV.pureT false

end Ix.Kernel
