module

public import IxC.Kernel.Verify.Rename.Native2

@[expose] public section

/-!
# The renaming walk through the fixpoint route: the install (step 7.3, chunk (iii))

The projection table (`checkStructProjTable`, `checkNativeTable`), the kinds'
classification (`classifyFixKinds`), the recursor with its rules
(`checkNativeRules`, `checkNativeRec`), one pass over the former and the
constructors (`checkNativePass`), the install after it (`checkNativeTail`) and
the route (`checkNative`), at renamed arguments over related environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-! ## The projection table -/

theorem structProjBodiesGo_map (T : Key md) :
    ∀ (k i : Nat) (e : Expr md),
      structProjBodiesGo (T.map f) k i (e.mapKeys f) =
        (structProjBodiesGo T k i e).map (List.map (Expr.mapKeys f))
  | 0, _, _ => rfl
  | k + 1, i, .forallE fdom body bm => by
    have h := structProjBodiesGo_map T k (i + 1) (body.instantiate1Lift (structProjArgP T i))
    simp only [Expr.mapKeys_instantiate1Lift] at h
    simp only [Expr.mapKeys, structProjBodiesGo]
    rw [show (structProjArgP (T.map f) i : Expr md') = (structProjArgP T i).mapKeys f from rfl, h]
    cases structProjBodiesGo T k (i + 1) (body.instantiate1Lift (structProjArgP T i)) <;> rfl
  | _ + 1, _, .bvar _ | _ + 1, _, .fvar _ _ | _ + 1, _, .sort _ | _ + 1, _, .const _ _
  | _ + 1, _, .app _ _ | _ + 1, _, .lam _ _ _ | _ + 1, _, .letE _ _ _ _ | _ + 1, _, .lit _
  | _ + 1, _, .proj _ _ _ => rfl

theorem structProjBodiesGo_good {T : Key md} (hT : T.Good P) :
    ∀ {k i : Nat} {e : Expr md} {bs : List (Expr md)}, e.Good P →
      structProjBodiesGo T k i e = some bs → Expr.GoodList P bs
  | 0, _, _, bs, _, h => by
    simp only [structProjBodiesGo, Option.some.injEq] at h
    subst h; simp
  | k + 1, i, .forallE fdom body bm, bs, he, h => by
    simp only [Expr.Good] at he
    simp only [structProjBodiesGo, Option.map_eq_some_iff] at h
    obtain ⟨bs₀, h₀, rfl⟩ := h
    have harg : (structProjArgP T i : Expr md).Good P := ⟨hT, trivial⟩
    have := structProjBodiesGo_good hT (Expr.Good.instantiate1Lift he.2 harg 0) h₀
    simp [he.1, this]
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar _ _, _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const _ _, _, _, h | _ + 1, _, .app _ _, _, _, h | _ + 1, _, .lam _ _ _, _, _, h
  | _ + 1, _, .letE _ _ _ _, _, _, h | _ + 1, _, .lit _, _, _, h
  | _ + 1, _, .proj _ _ _, _, _, h => nomatch h

theorem Expr.instPisAtLift_good : ∀ {as : List (Expr md)} {e r : Expr md}, Expr.GoodList P as →
    e.Good P → Expr.instPisAtLift as e = some r → r.Good P
  | [], e, r, _, he, h => by
    simp only [Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ he
  | a :: as, .forallE dom body m, r, has, he, h => by
    simp only [Expr.instPisAtLift] at h
    simp only [Expr.goodList_cons] at has
    simp only [Expr.Good] at he
    exact Expr.instPisAtLift_good has.2 (Expr.Good.instantiate1Lift he.2 has.1 0) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, h | _ :: _, .sort _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, h | _ :: _, .app _ _, _, _, _, h
  | _ :: _, .lam _ _ _, _, _, _, h | _ :: _, .letE _ _ _ _, _, _, _, h
  | _ :: _, .lit _, _, _, _, h | _ :: _, .proj _ _ _, _, _, _, h => nomatch h

theorem structProjBodies_map (T : Key md) (nP nF : Nat) (cty : Expr md) :
    structProjBodies (T.map f) nP nF (cty.mapKeys f) =
      (structProjBodies T nP nF cty).map (Array.map (Expr.mapKeys f)) := by
  unfold structProjBodies
  rw [← structProjPs_map (f := f) nP, Expr.instPisAtLift_mapKeys]
  cases Expr.instPisAtLift (structProjPs nP) cty with
  | none => rfl
  | some r =>
    simp only [Option.map_some, structProjBodiesGo_map]
    cases structProjBodiesGo T nF 0 r <;> simp

theorem structProjBodies_good {T : Key md} (hT : T.Good P) (nP nF : Nat) {cty : Expr md}
    (hc : cty.Good P) {bodies : Array (Expr md)} (h : structProjBodies T nP nF cty = some bodies) :
    ∀ b ∈ bodies, b.Good P := by
  unfold structProjBodies at h
  cases hi : Expr.instPisAtLift (structProjPs nP) cty with
  | none => rw [hi] at h; exact nomatch h
  | some r =>
    rw [hi] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨bs, hbs, rfl⟩ := h
    have hr : r.Good P := by
      have := Expr.instPisAtLift_good (P := P) (as := structProjPs nP)
        (fun x hx => by
          simp only [structProjPs, List.mem_map] at hx
          obtain ⟨_, _, rfl⟩ := hx; trivial) hc hi
      exact this
    intro b hb
    exact structProjBodiesGo_good hT hr hbs b (by simpa using hb)

theorem projFnName_map (T : Key md) (j : Nat) : (projFnName T j).map f = projFnName (T.map f) j :=
  rfl

theorem projTableName_map (T : Key md) : (projTableName T).map f = projTableName (T.map f) := rfl

/-- **The projection table's stage at a renamed structure.** -/
theorem checkStructProjTable_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {T C : Key md} (hT : T.Good P) (hC : C.Good P) (lps : List LevelParam) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) {cvCa : ConstantVal md}
    (hCa : cvCa.Good P) :
    SimR (EnvRelG P f L) (checkStructProjTable (m := CheckM md) T C lps nP nF resSort guards off cvCa env)
      (checkStructProjTable (m := CheckM md') (T.map f) (C.map f) lps nP nF resSort guards off
        (cvCa.mapKeys f) env') := by
  unfold checkStructProjTable
  simp only [ConstantVal.mapKeys_type, structProjBodies_map]
  refine SimR.bindE (SimE.unwrapOr' (G := fun bs : Array (Expr md) => ∀ b ∈ bs, b.Good P)
    (fun bs h => structProjBodies_good hT nP nF hCa.2 h)) (fun bodies hb => ?_)
  have hall : (bodies.map (Expr.mapKeys f)).all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined lps && b.constsResolve env' && b.looseBVarsBounded (nP + 1)) =
      bodies.all (fun b => !b.hasFvar && b.allLevelParamsDefined lps && b.constsResolve env &&
        b.looseBVarsBounded (nP + 1)) := by
    rw [← Array.all_toList, ← Array.all_toList, Array.toList_map, List.all_map]
    apply List.all_congr_mem'
    intro b hbm
    have hbg : b.Good P := hb b (Array.mem_def.mpr hbm)
    simp only [Function.comp, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys,
      constsResolve_ren hE hbg, Expr.looseBVarsBounded_mapKeys]
  rw [hall, Array.size_map]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  have hfn : (List.range nF).all (fun j => (env'.find? (projFnName (T.map f) j)).isNone) =
      (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) := by
    apply List.all_congr_mem'
    intro j _
    rw [← projFnName_map, ← Option.not_isSome, ← Option.not_isSome,
      hE.find_isSome (show (projFnName T j).Good P from hT)]
  rw [hfn]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  have htn : (env'.find? (projTableName (T.map f))).isNone = (env.find? (projTableName T)).isNone := by
    rw [← projTableName_map, ← Option.not_isSome, ← Option.not_isSome,
      hE.find_isSome (show (projTableName T).Good P from hT)]
  rw [htn]
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.pure' ?_
  exact hE.push (c := .projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, off⟩) ⟨hT, hC, hb⟩

/-- **The fixpoint route's table stage** at a renamed block. -/
theorem checkNativeTable_sim {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {p : NativeParts md} (hp : p.Good P) {ctorsA : List (ConstantVal md × Nat)}
    (hcs : ∀ c ∈ ctorsA, c.1.Good P) (sortss : List (List Level)) :
    SimR (EnvRelG P f L) (checkNativeTable (m := CheckM md) p ctorsA sortss env)
      (checkNativeTable (m := CheckM md') (p.mapKeys f)
        (ctorsA.map fun c => (c.1.mapKeys f, c.2)) sortss env') := by
  unfold checkNativeTable
  match ctorsA, sortss, hcs with
  | [cA], [sorts], hcs =>
    have hcA : cA.1.Good P := hcs cA List.mem_cons_self
    simp only [List.map_cons, List.map_nil]
    show SimR (EnvRelG P f L)
      (if p.nIdx == 0 then checkStructProjTable p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2
          p.resSort (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 env else pure env)
      (if p.nIdx == 0 then checkStructProjTable (p.cvT.name.map f) (cA.1.name.map f)
          p.cvT.levelParams p.nP cA.2 p.resSort
          (structProjGuards (cA.1.type.mapKeys f) p.nP cA.2 sorts) 1 (cA.1.mapKeys f) env'
        else pure env')
    rw [structProjGuards_map]
    refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.pure' hE)
    exact checkStructProjTable_sim hE hp.cvT.1 hcA.1 _ _ _ _ _ _ hcA
  | [], _, _ => exact SimR.pure' hE
  | _ :: _ :: _, _, _ => exact SimR.pure' hE
  | [_], [], _ => exact SimR.pure' hE
  | [_], _ :: _ :: _, _ => exact SimR.pure' hE

/-! ## The kinds' classification -/

theorem mapM_recCtorKinds_map (hf : InjOn f P) {T : Key md} (hT : T.Good P)
    (lps : List LevelParam) (nP nIdx : Nat) :
    ∀ (cs : List (ConstantVal md × Nat)), (∀ c ∈ cs, c.1.Good P) →
      (cs.map fun c => (c.1.mapKeys f, c.2)).mapM (recCtorKinds (T.map f) lps nP nIdx) =
        cs.mapM (recCtorKinds T lps nP nIdx)
  | [], _ => rfl
  | c :: cs, hcs => by
    simp only [List.map_cons, List.mapM_cons,
      recCtorKinds_map hf hT lps nP nIdx (hcs c List.mem_cons_self),
      mapM_recCtorKinds_map hf hT lps nP nIdx cs (fun c' h => hcs c' (List.mem_cons_of_mem _ h))]

theorem classifyFixKinds_sim (hf : InjOn f P) {T : Key md} (hT : T.Good P) (lps : List LevelParam)
    (nP nIdx : Nat) {ctorsA : List (ConstantVal md × Nat)} (hcs : ∀ c ∈ ctorsA, c.1.Good P) :
    SimV (classifyFixKinds (m := CheckM md) T lps nP nIdx ctorsA)
      (classifyFixKinds (m := CheckM md') (T.map f) lps nP nIdx
        (ctorsA.map fun c => (c.1.mapKeys f, c.2))) := by
  unfold classifyFixKinds
  rw [mapM_recCtorKinds_map hf hT lps nP nIdx ctorsA hcs]
  cases hk : List.mapM (recCtorKinds T lps nP nIdx) ctorsA with
  | none => exact SimE.throw_bind
  | some kinds =>
    refine SimE.bind (G := fun _ => True) (m := id)
      (SimE.pure' (a := kinds) (a' := kinds) trivial rfl) (fun kinds _ => ?_)
    simp only [id]
    refine SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => ?_)
    refine SimE.ite Iff.rfl (fun _ => SimE.throw') (fun _ => ?_)
    exact SimV.pureT _

end Ix.Kernel
