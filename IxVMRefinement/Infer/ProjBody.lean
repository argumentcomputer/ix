import IxVMRefinement.Core.Specs.Infer
import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Verify.EnvWF
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Inductives.StructBody
import IxC.Kernel.Verify.InferLemmas

/-! # Pure kernel telescope and projection-body lemmas for `Infer.proj`

* **Constructor telescope arity** (`lt_of_ctorTeleOk_instPis_fieldTypeAt`): when a constructor type
  has `ctorTeleOk` at `nP + nF` (its residual past `nP + nF` binders is headed by a constant, never
  a `∀`), instantiating `nP` parameter binders and peeling `f + 1` field binders forces `f < nF`.
* **Projection body opening** (`fieldTypeAt_eq_typeAt`): the domain reached by `instPis` followed by
  `fieldTypeAt` on `cvC.type.instantiateLevelParams` equals `(tbl.entry f).typeAt us Args PE`, by
  generalising `Ix.Kernel.structProjBody_open` from fresh variables to arbitrary closed terms.
* **Head reduction of a declared telescope's sort** (`peelRed_stripPis_sort`): `PeelRed` of at most
  `n` binders to a sort on a syntactic `n`-binder telescope ending in `.sort σ` yields `σ`
  (`Red.rigid`). -/

namespace IxVM.Refinement.Core.ProjBody

open Ix.Kernel (Expr)

set_option linter.unusedVariables false

/-! ## Constructor telescope arity (`f < nF`) -/

theorem getAppFn_instantiate1 (a : KExpr) (k : Nat) {e : KExpr} {c : KKey} {us : List KLevel}
    (h : e.getAppFn = .const c us) : (e.instantiate1 a k).getAppFn = .const c us := by
  induction e with
  | const _ _ => exact h
  | app f _ ihf _ => exact ihf h
  | _ => exact nomatch h

theorem ctorTeleOk_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel)
    {e : KExpr} {k : Nat} (h : e.ctorTeleOk k = true) :
    (e.instantiateLevelParams ks us).ctorTeleOk k = true := by
  obtain ⟨bs, body, c, vs, hs, hb⟩ := Expr.ctorTeleOk_head h
  obtain ⟨⟨bs', body'⟩, hs'⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome ks us k (by rw [hs]; rfl))
  obtain ⟨rfl, -⟩ := Expr.stripPis_instantiateLevelParams_eq ks us k hs hs'
  refine Expr.ctorTeleOk_of hs' (c := c) (us := vs.map (Ix.Kernel.Level.subst ks us)) ?_
  rw [Expr.getAppFn_instantiateLevelParams, hb]
  rfl

theorem ctorTeleOk_instantiate1 {dom body a : KExpr} {m : Ix.Kernel.BinderMeta} {k : Nat}
    (h : (Expr.forallE dom body m).ctorTeleOk (k + 1) = true) :
    (body.instantiate1 a).ctorTeleOk k = true := by
  obtain ⟨bs, res, c, vs, hs, hb⟩ := Expr.ctorTeleOk_head h
  simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
  obtain ⟨⟨bs0, res0⟩, hs0, heq⟩ := hs
  obtain ⟨-, rfl⟩ : (dom, m) :: bs0 = bs ∧ res0 = res := by simpa using heq
  obtain ⟨bs', hs', -⟩ := Ix.Kernel.stripPis_instantiate1_full (v := a) k 0 hs0
  exact Expr.ctorTeleOk_of hs' (getAppFn_instantiate1 a (0 + k) hb)

theorem ctorTeleOk_instPis :
    ∀ (Args : List KExpr) {nF : Nat} {T T' : KExpr},
      T.ctorTeleOk (Args.length + nF) = true →
      Specs.Infer.instPis Args.length T Args = some T' →
      T'.ctorTeleOk nF = true
  | [], _, T, T', hok, hpi => by
    simp only [List.length_nil, Nat.zero_add, Specs.Infer.instPis, Option.some.injEq] at hok hpi
    rwa [← hpi]
  | a :: as, nF, .forallE dom body m, T', hok, hpi => by
    simp only [List.length_cons, Specs.Infer.instPis] at hok hpi
    rw [show as.length + 1 + nF = (as.length + nF) + 1 by omega] at hok
    exact ctorTeleOk_instPis as (ctorTeleOk_instantiate1 hok) hpi
  | _ :: _, _, .bvar _, _, _, hpi | _ :: _, _, .fvar _ _, _, _, hpi
  | _ :: _, _, .sort _, _, _, hpi | _ :: _, _, .const _ _, _, _, hpi
  | _ :: _, _, .app _ _, _, _, hpi | _ :: _, _, .lam _ _ _, _, _, hpi
  | _ :: _, _, .letE _ _ _ _, _, _, hpi | _ :: _, _, .lit _, _, _, hpi
  | _ :: _, _, .proj _ _ _, _, _, hpi => nomatch hpi

private theorem not_ctorTeleOk_zero_forallE (dom body : KExpr) (m : Ix.Kernel.BinderMeta) :
    (Expr.forallE dom body m).ctorTeleOk 0 = false := by
  unfold Expr.ctorTeleOk Expr.stripPis Expr.getAppFn
  rfl

theorem lt_of_ctorTeleOk_fieldTypeAt {S : KKey} {PE : KExpr} :
    ∀ (nF f c0 : Nat) {T FT : KExpr},
      T.ctorTeleOk nF = true →
      Specs.Infer.fieldTypeAt S PE f c0 T = some FT →
      f < nF
  | 0, 0, _, .forallE dom body m, _, hok, _ => by
    rw [not_ctorTeleOk_zero_forallE] at hok; exact nomatch hok
  | 0, _ + 1, _, .forallE dom body m, _, hok, _ => by
    rw [not_ctorTeleOk_zero_forallE] at hok; exact nomatch hok
  | 0, 0, _, .bvar _, _, _, hf | 0, 0, _, .fvar _ _, _, _, hf
  | 0, 0, _, .sort _, _, _, hf | 0, 0, _, .const _ _, _, _, hf
  | 0, 0, _, .app _ _, _, _, hf | 0, 0, _, .lam _ _ _, _, _, hf
  | 0, 0, _, .letE _ _ _ _, _, _, hf | 0, 0, _, .lit _, _, _, hf
  | 0, 0, _, .proj _ _ _, _, _, hf => nomatch hf
  | 0, _ + 1, _, .bvar _, _, _, hf | 0, _ + 1, _, .fvar _ _, _, _, hf
  | 0, _ + 1, _, .sort _, _, _, hf | 0, _ + 1, _, .const _ _, _, _, hf
  | 0, _ + 1, _, .app _ _, _, _, hf | 0, _ + 1, _, .lam _ _ _, _, _, hf
  | 0, _ + 1, _, .letE _ _ _ _, _, _, hf | 0, _ + 1, _, .lit _, _, _, hf
  | 0, _ + 1, _, .proj _ _ _, _, _, hf => nomatch hf
  | nF + 1, 0, _, _, _, _, _ => Nat.zero_lt_succ nF
  | nF + 1, f + 1, c0, .forallE dom body m, FT, hok, hf => by
    simp only [Specs.Infer.fieldTypeAt] at hf
    exact Nat.succ_lt_succ
      (lt_of_ctorTeleOk_fieldTypeAt nF f (c0 + 1) (ctorTeleOk_instantiate1 hok) hf)
  | _ + 1, _ + 1, _, .bvar _, _, _, hf | _ + 1, _ + 1, _, .fvar _ _, _, _, hf
  | _ + 1, _ + 1, _, .sort _, _, _, hf | _ + 1, _ + 1, _, .const _ _, _, _, hf
  | _ + 1, _ + 1, _, .app _ _, _, _, hf | _ + 1, _ + 1, _, .lam _ _ _, _, _, hf
  | _ + 1, _ + 1, _, .letE _ _ _ _, _, _, hf | _ + 1, _ + 1, _, .lit _, _, _, hf
  | _ + 1, _ + 1, _, .proj _ _ _, _, _, hf => nomatch hf

theorem lt_of_ctorTeleOk_instPis_fieldTypeAt {S : KKey} {PE T T_after FT : KExpr}
    {Args : List KExpr} {nP nF f : Nat}
    (hok : T.ctorTeleOk (nP + nF) = true) (hlen : Args.length = nP)
    (hpi : Specs.Infer.instPis nP T Args = some T_after)
    (hf : Specs.Infer.fieldTypeAt S PE f 0 T_after = some FT) : f < nF := by
  subst hlen
  exact lt_of_ctorTeleOk_fieldTypeAt nF f 0 (ctorTeleOk_instPis Args hok hpi) hf

/-! ## Level instantiation through `structProjBodies` -/

theorem liftLooseBVars_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel)
    (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars n c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).liftLooseBVars n c
  | .bvar i, c => by
    show Expr.instantiateLevelParams ks us
        (if i ≥ c then (.bvar (i + n) : KExpr) else .bvar i) =
      (if i ≥ c then (.bvar (i + n) : KExpr) else .bvar i)
    split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ks us n f c,
      liftLooseBVars_instantiateLevelParams ks us n a c]
  | .lam ty b m, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ks us n ty c,
      liftLooseBVars_instantiateLevelParams ks us n b (c + 1)]
  | .forallE ty b m, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ks us n ty c,
      liftLooseBVars_instantiateLevelParams ks us n b (c + 1)]
  | .letE ty v b l, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ks us n ty c,
      liftLooseBVars_instantiateLevelParams ks us n v c,
      liftLooseBVars_instantiateLevelParams ks us n b (c + 1)]
  | .proj s i e, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams ks us n e c]

theorem instantiate1Lift_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel)
    (v : KExpr) :
    ∀ (e : KExpr) (d : Nat),
      (e.instantiate1Lift v d).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).instantiate1Lift (v.instantiateLevelParams ks us) d
  | .bvar i, d => by
    show Expr.instantiateLevelParams ks us
        (if i = d then v.liftLooseBVars d 0 else if i > d then .bvar (i - 1) else .bvar i) =
      (if i = d then (v.instantiateLevelParams ks us).liftLooseBVars d 0
       else if i > d then .bvar (i - 1) else .bvar i)
    by_cases h1 : i = d
    · rw [ite_eq_left h1, ite_eq_left h1]
      exact liftLooseBVars_instantiateLevelParams ks us d v 0
    · rw [ite_eq_right h1, ite_eq_right h1]
      split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ks us v f d,
      instantiate1Lift_instantiateLevelParams ks us v a d]
  | .lam ty b m, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ks us v ty d,
      instantiate1Lift_instantiateLevelParams ks us v b (d + 1)]
  | .forallE ty b m, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ks us v ty d,
      instantiate1Lift_instantiateLevelParams ks us v b (d + 1)]
  | .letE ty val b l, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ks us v ty d,
      instantiate1Lift_instantiateLevelParams ks us v val d,
      instantiate1Lift_instantiateLevelParams ks us v b (d + 1)]
  | .proj s i e, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams ks us v e d]

theorem instPisAtLift_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (ps : List KExpr) (e : KExpr),
      (∀ p ∈ ps, p.instantiateLevelParams ks us = p) →
      Expr.instPisAtLift ps (e.instantiateLevelParams ks us) =
        (Expr.instPisAtLift ps e).map (·.instantiateLevelParams ks us)
  | [], e, _ => rfl
  | p :: ps, .forallE dom body m, hp => by
    simp only [Expr.instantiateLevelParams, Expr.instPisAtLift]
    have hp0 : p.instantiateLevelParams ks us = p := hp p (List.mem_cons_self ..)
    have hstep := instantiate1Lift_instantiateLevelParams ks us p body 0
    rw [hp0] at hstep
    rw [← hstep]
    exact instPisAtLift_instantiateLevelParams ks us ps _
      (fun q hq => hp q (List.mem_cons_of_mem _ hq))
  | _ :: _, .bvar _, _ | _ :: _, .fvar _ _, _ | _ :: _, .sort _, _ | _ :: _, .const _ _, _
  | _ :: _, .app _ _, _ | _ :: _, .lam _ _ _, _ | _ :: _, .letE _ _ _ _, _ | _ :: _, .lit _, _
  | _ :: _, .proj _ _ _, _ => rfl

theorem structProjBodiesGo_instantiateLevelParams (ks : List Ix.Kernel.LevelParam)
    (us : List KLevel) (T : KKey) :
    ∀ (k i : Nat) (r : KExpr),
      Ix.Kernel.structProjBodiesGo T k i (r.instantiateLevelParams ks us) =
        (Ix.Kernel.structProjBodiesGo T k i r).map (List.map (·.instantiateLevelParams ks us))
  | 0, _, _ => rfl
  | k + 1, i, .forallE fdom body m => by
    simp only [Expr.instantiateLevelParams, Ix.Kernel.structProjBodiesGo]
    have harg : (Ix.Kernel.structProjArgP T i).instantiateLevelParams ks us =
        Ix.Kernel.structProjArgP T i := rfl
    have hstep := instantiate1Lift_instantiateLevelParams ks us (Ix.Kernel.structProjArgP T i) body 0
    rw [harg] at hstep
    rw [← hstep, structProjBodiesGo_instantiateLevelParams ks us T k (i + 1)]
    cases Ix.Kernel.structProjBodiesGo T k (i + 1)
      (body.instantiate1Lift (Ix.Kernel.structProjArgP T i)) <;> rfl
  | _ + 1, _, .bvar _ | _ + 1, _, .fvar _ _ | _ + 1, _, .sort _ | _ + 1, _, .const _ _
  | _ + 1, _, .app _ _ | _ + 1, _, .lam _ _ _ | _ + 1, _, .letE _ _ _ _ | _ + 1, _, .lit _
  | _ + 1, _, .proj _ _ _ => rfl

theorem structProjBodies_instantiateLevelParams (ks : List Ix.Kernel.LevelParam) (us : List KLevel)
    {T : KKey} {nP nF : Nat} {cty : KExpr} {bodies : Array KExpr}
    (h : Ix.Kernel.structProjBodies T nP nF cty = some bodies) :
    Ix.Kernel.structProjBodies T nP nF (cty.instantiateLevelParams ks us) =
      some (bodies.map (·.instantiateLevelParams ks us)) := by
  unfold Ix.Kernel.structProjBodies at h ⊢
  have hps : ∀ p ∈ (Ix.Kernel.structProjPs (md := .anon) nP),
      p.instantiateLevelParams ks us = p := by
    intro p hp
    unfold Ix.Kernel.structProjPs at hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
    rfl
  rw [instPisAtLift_instantiateLevelParams ks us _ cty hps]
  cases hr : Expr.instPisAtLift (Ix.Kernel.structProjPs nP) cty with
  | none => rw [hr] at h; exact nomatch h
  | some r =>
    rw [hr] at h
    simp only [Option.map_some, Option.map_eq_some_iff] at h ⊢
    obtain ⟨bs, hgo, rfl⟩ := h
    rw [structProjBodiesGo_instantiateLevelParams ks us T nF 0 r, hgo]
    simp

/-! ## Generalised `structProjBody_open` at closed argument spines -/

theorem structProjArgs_instSeq_gen (T : KKey) {Args : List KExpr} {PE : KExpr} {nP : Nat}
    (hlenA : Args.length = nP)
    (hclosed : ∀ a ∈ Args ++ [PE], a.looseBVarsBounded 0 = true) (i : Nat) :
    (Ix.Kernel.structProjPs nP ++ (List.range i).map (Ix.Kernel.structProjArgP T)).map
        (Expr.instSeq (Args ++ [PE]) nP)
      = Args ++ (List.range i).map (fun j => Expr.proj T j PE) := by
  have hlen : (Args ++ [PE]).length = nP + 1 := by simp [hlenA]
  have hbvar : ∀ j, j ≤ nP → (Args ++ [PE])[nP - j]? =
      some (Expr.instSeq (Args ++ [PE]) nP (.bvar j)) := by
    intro j hj
    exact Expr.instSeq_bvar (Args ++ [PE]) nP j hclosed hj (by rw [hlen]; omega)
  rw [List.map_append]
  congr 1
  · unfold Ix.Kernel.structProjPs
    rw [List.map_map]
    apply List.ext_getElem
    · simp [hlenA]
    · intro k hk1 hk2
      simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
      have hk : k < nP := by simpa using hk1
      have h1 := hbvar (nP - k) (by omega)
      rw [show nP - (nP - k) = k by omega,
        List.getElem?_append_left (by rw [hlenA]; exact hk),
        List.getElem?_eq_getElem hk2] at h1
      exact (Option.some.inj h1).symm
  · rw [List.map_map]
    apply List.map_congr_left
    intro j _
    show Expr.instSeq (Args ++ [PE]) nP (.proj T j (.bvar 0)) = _
    rw [Ix.Kernel.instSeq_proj]
    have h0 := hbvar 0 (Nat.zero_le _)
    rw [Nat.sub_zero, List.getElem?_append_right (by omega),
      hlenA, Nat.sub_self] at h0
    have hPE : Expr.instSeq (Args ++ [PE]) nP (.bvar 0) = PE := (Option.some.inj h0).symm
    rw [hPE]

theorem structProjBody_open_gen {T : KKey} {nP nF : Nat} {cty : KExpr} {bodies : Array KExpr}
    (h : Ix.Kernel.structProjBodies T nP nF cty = some bodies)
    (hstrip : (cty.stripPis (nP + nF)).isSome = true)
    (hcl : cty.looseBVarsBounded 0 = true)
    {Args : List KExpr} {PE : KExpr} (hlenA : Args.length = nP)
    (hclosed : ∀ a ∈ Args ++ [PE], a.looseBVarsBounded 0 = true)
    {i : Nat} (hi : i < nF) :
    ∃ (cds : List KExpr) (bodyC : KExpr) (mb : Ix.Kernel.BinderMeta),
      Expr.instPisAt (Args ++ (List.range i).map (fun j => Expr.proj T j PE)) cty
        = some (cds, .forallE
            (Expr.instSpine (Args ++ [PE]) nP (bodies.getD i default)) bodyC mb) := by
  obtain ⟨-, hspec⟩ := Ix.Kernel.structProjBodies_spec h
  obtain ⟨b', mb, hres⟩ := hspec i hi
  rw [Ix.Kernel.structProjResidP_eq] at hres
  have hlenB : (Ix.Kernel.structProjPs (md := .anon) nP ++
      (List.range i).map (Ix.Kernel.structProjArgP T)).length = nP + i := by
    simp [Ix.Kernel.structProjPs]
  have hlenF : (Args ++ (List.range i).map (fun j => Expr.proj T j PE)).length = nP + i := by
    simp [hlenA]
  obtain ⟨⟨bs, body0⟩, hs⟩ := Option.isSome_iff_exists.mp
    (Ix.Kernel.stripPis_isSome_of_le (k := nP + i + 1) (by omega) hstrip)
  have hbsLen : bs.length = nP + i + 1 := Expr.stripPis_length _ hs
  obtain ⟨b, hb⟩ : ∃ b, bs[nP + i]? = some b :=
    ⟨bs[nP + i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨bodyR, hhead⟩ := Expr.instPisAtLift_head _ (mrem := 0) hres
    (by rw [hlenB]; exact hs) (by rw [hlenB]; exact hb)
  obtain ⟨hbody, -, -⟩ := Expr.forallE.inj hhead
  obtain ⟨⟨cds, rest⟩, hpa⟩ := Option.isSome_iff_exists.mp
    (Ix.Kernel.instPisAt_isSome_of_stripPis (Args ++ (List.range i).map (fun j => Expr.proj T j PE))
      (by rw [hlenF]; exact Ix.Kernel.stripPis_isSome_of_le (by omega) hstrip))
  obtain ⟨bodyC, hheadF⟩ := Ix.Kernel.instPisAt_head _ (mrem := 0) hpa
    (by rw [hlenF]; exact hs) (by rw [hlenF]; exact hb)
  refine ⟨cds, bodyC, b.2, ?_⟩
  rw [hpa, hheadF, hbody, Expr.instSpine_eq_instSeq]
  have hdomB : b.1.looseBVarsBounded (nP + i) = true := by
    have := Ix.Kernel.stripPis_binder_bounded (nP + i + 1) hs hcl (nP + i) b hb
    simpa using this
  have hcol := Expr.instSeq_instSeqLift (Args ++ [PE]) nP hclosed
    (by simp [hlenA]) _ (Ix.Kernel.structProjArgs_bounded T nP i) b.1
  rw [hlenB, structProjArgs_instSeq_gen T hlenA hclosed i,
    Ix.Kernel.instSeq_eq_self_of_bounded _ _ hdomB (by simp [hlenA]; omega)] at hcol
  rw [hlenB, hlenF, hcol]

/-! ## Connecting `Specs.Infer.instPis` and `Specs.Infer.fieldTypeAt` to `Expr.instPisAt` -/

theorem instPisAt_append (xs ys : List KExpr) :
    ∀ {e mid res : KExpr} {ds1 ds2 : List KExpr},
      Expr.instPisAt xs e = some (ds1, mid) →
      Expr.instPisAt ys mid = some (ds2, res) →
      Expr.instPisAt (xs ++ ys) e = some (ds1 ++ ds2, res) := by
  induction xs with
  | nil =>
    intro e mid res ds1 ds2 h1 h2
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | cons x xs ih =>
    intro e mid res ds1 ds2 h1 h2
    cases e with
    | forallE dom body m =>
      simp only [List.cons_append, Expr.instPisAt, Option.map_eq_some_iff] at h1 ⊢
      obtain ⟨⟨ds1', mid'⟩, h1', heq⟩ := h1
      obtain ⟨rfl, rfl⟩ : dom :: ds1' = ds1 ∧ mid' = mid := by simpa using heq
      exact ⟨(ds1' ++ ds2, res), ih h1' h2, rfl⟩
    | _ => exact nomatch h1

theorem instPisAt_of_instPis :
    ∀ (Args : List KExpr) {T T' : KExpr},
      Specs.Infer.instPis Args.length T Args = some T' →
      ∃ ds, Expr.instPisAt Args T = some (ds, T')
  | [], T, T', h => by
    simp only [List.length_nil, Specs.Infer.instPis, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl⟩
  | a :: as, .forallE dom body m, T', h => by
    simp only [List.length_cons, Specs.Infer.instPis] at h
    obtain ⟨ds, hds⟩ := instPisAt_of_instPis as h
    exact ⟨dom :: ds, by simp [Expr.instPisAt, hds]⟩
  | _ :: _, .bvar _, _, h | _ :: _, .fvar _ _, _, h | _ :: _, .sort _, _, h
  | _ :: _, .const _ _, _, h | _ :: _, .app _ _, _, h | _ :: _, .lam _ _ _, _, h
  | _ :: _, .letE _ _ _ _, _, h | _ :: _, .lit _, _, h | _ :: _, .proj _ _ _, _, h => nomatch h

theorem instPisAt_of_fieldTypeAt (S : KKey) (PE : KExpr) :
    ∀ (f c0 : Nat) {T FT : KExpr},
      Specs.Infer.fieldTypeAt S PE f c0 T = some FT →
      ∃ ds bodyC mb,
        Expr.instPisAt ((List.range f).map (fun j => Expr.proj S (c0 + j) PE)) T =
          some (ds, .forallE FT bodyC mb)
  | 0, c0, .forallE dom body m, FT, h => by
    simp only [Specs.Infer.fieldTypeAt, Option.some.injEq] at h
    subst h
    exact ⟨[], body, m, rfl⟩
  | f + 1, c0, .forallE dom body m, FT, h => by
    simp only [Specs.Infer.fieldTypeAt] at h
    obtain ⟨ds, bodyC, mb, hrec⟩ := instPisAt_of_fieldTypeAt S PE f (c0 + 1) h
    refine ⟨dom :: ds, bodyC, mb, ?_⟩
    rw [List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
    have hmap : List.map ((fun j => Expr.proj S (c0 + j) PE) ∘ Nat.succ) (List.range f) =
        List.map (fun j => Expr.proj S (c0 + 1 + j) PE) (List.range f) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, show c0 + (j + 1) = c0 + 1 + j by omega]
    rw [hmap]
    simp [Expr.instPisAt, hrec]
  | 0, _, .bvar _, _, h | 0, _, .fvar _ _, _, h | 0, _, .sort _, _, h
  | 0, _, .const _ _, _, h | 0, _, .app _ _, _, h | 0, _, .lam _ _ _, _, h
  | 0, _, .letE _ _ _ _, _, h | 0, _, .lit _, _, h | 0, _, .proj _ _ _, _, h => nomatch h
  | _ + 1, _, .bvar _, _, h | _ + 1, _, .fvar _ _, _, h | _ + 1, _, .sort _, _, h
  | _ + 1, _, .const _ _, _, h | _ + 1, _, .app _ _, _, h | _ + 1, _, .lam _ _ _, _, h
  | _ + 1, _, .letE _ _ _ _, _, h | _ + 1, _, .lit _, _, h | _ + 1, _, .proj _ _ _, _, h =>
    nomatch h

private theorem array_getD_map_of_lt {α β : Type} (xs : Array α) (g : α → β) (d1 : α) (d2 : β)
    {i : Nat} (hi : i < xs.size) :
    (xs.map g).getD i d2 = g (xs.getD i d1) := by
  simp [Array.getD, hi]

/-- **`fieldTypeAt` after `instPis` computes `(tbl.entry f).typeAt`.** -/
theorem fieldTypeAt_eq_typeAt {tbl : Ix.Kernel.ProjTable .anon} {nP nF f : Nat}
    {cvC : Ix.Kernel.ConstantVal .anon} {us : List KLevel} {Args : List KExpr}
    {PE T_after FT : KExpr}
    (hbodies : Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies)
    (hnPt : tbl.numParams = nP)
    (hstrip : (cvC.type.stripPis (nP + nF)).isSome = true)
    (hcl : cvC.type.looseBVarsBounded 0 = true)
    (hf : f < nF) (hlenA : Args.length = nP)
    (hclA : ∀ a ∈ Args, a.looseBVarsBounded 0 = true)
    (hclPE : PE.looseBVarsBounded 0 = true)
    (hpis : Specs.Infer.instPis nP (cvC.type.instantiateLevelParams tbl.levelParams us) Args =
      some T_after)
    (hfield : Specs.Infer.fieldTypeAt tbl.structName PE f 0 T_after = some FT) :
    FT = (tbl.entry f).typeAt us Args PE := by
  have hclosed : ∀ a ∈ Args ++ [PE], a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hclA a ha
    · rw [List.mem_singleton] at ha; subst ha; exact hclPE
  have hbSz : tbl.bodies.size = nF := (Ix.Kernel.structProjBodies_spec hbodies).1
  have hbodies' := structProjBodies_instantiateLevelParams tbl.levelParams us hbodies
  have hstrip' : ((cvC.type.instantiateLevelParams tbl.levelParams us).stripPis (nP + nF)).isSome =
      true := Expr.stripPis_instantiateLevelParams_isSome tbl.levelParams us (nP + nF) hstrip
  have hcl' : (cvC.type.instantiateLevelParams tbl.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hcl
  obtain ⟨cds, bodyC, mb, hopen⟩ :=
    structProjBody_open_gen hbodies' hstrip' hcl' hlenA hclosed hf
  obtain ⟨ds1, hpa1⟩ := instPisAt_of_instPis Args (by rw [hlenA]; exact hpis)
  obtain ⟨ds2, bodyC2, mb2, hpa2⟩ := instPisAt_of_fieldTypeAt tbl.structName PE f 0 hfield
  simp only [Nat.zero_add] at hpa2
  have hpa := instPisAt_append Args ((List.range f).map (fun j => Expr.proj tbl.structName j PE))
    hpa1 hpa2
  rw [hpa] at hopen
  injection hopen with hp
  obtain ⟨-, hfor⟩ := Prod.mk.inj hp
  obtain ⟨hdom, -, -⟩ := Expr.forallE.inj hfor
  rw [hdom, array_getD_map_of_lt tbl.bodies _ default default (by omega)]
  have hentry := Ix.Kernel.ProjEntry.typeAt_eq_instSpine (tbl.entry f) us
    (by show Args.length = tbl.numParams; rw [hnPt]; exact hlenA) PE
  simpa [Ix.Kernel.ProjTable.entry, hnPt] using hentry.symm

/-! ## `PeelRed` on a syntactic `∀`-telescope ending in a sort -/

theorem peelRed_stripPis_sort {env : Ix.Kernel.Env .anon} {Γ' : Nat → KExpr} (n : Nat) :
    ∀ {T : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {σ u : KLevel} {d k : Nat},
      T.stripPis n = some (bs, .sort σ) →
      Specs.Infer.PeelRed env Γ' d T k (.sort u) →
      k ≤ n →
      u = σ := by
  induction n with
  | zero =>
    intro T bs σ u d k hs hpeel hk
    obtain rfl : k = 0 := by omega
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    cases hpeel with
    | done hred => exact Ix.Kernel.Rules.Red.sort_eq hred
  | succ n ih =>
    intro T bs σ u d k hs hpeel hk
    cases T with
    | forallE dom body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs0, res0⟩, hs0, heq⟩ := hs
      obtain ⟨-, rfl⟩ : (dom, m) :: bs0 = bs ∧ res0 = .sort σ := by simpa using heq
      cases hpeel with
      | done hred =>
        have hrig := Ix.Kernel.Rules.Red.rigid hred rfl
        exact nomatch hrig
      | @step _ k' _ body' _ m' hred hrest =>
        have hrig := Ix.Kernel.Rules.Red.rigid hred rfl
        obtain ⟨-, rfl, -⟩ := Expr.forallE.inj hrig
        obtain ⟨bs', hs', -⟩ := Ix.Kernel.stripPis_instantiate1_full (v := .fvar d (Γ' d)) n 0 hs0
        exact ih hs' hrest (by omega)
    | _ => exact nomatch hs

end IxVM.Refinement.Core.ProjBody
