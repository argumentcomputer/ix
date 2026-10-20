module

public import IxC.Kernel.Verify.Rename.Modeled5

@[expose] public section

/-!
# The renaming walk through the modeled route: the capability theorems (step 7.3, chunk (iii))

The eta and unit-likeness theorems' checks (`checkEtaThm`, `checkUnitThm`), the
capability record (`indBlockCaps`), the residual and structure-likeness gates
(`ctorResidualOk`, `ctorTargetsFam`) at a renamed block over related
environments: they answer alike.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : md.Id → Prop}

/-- A lookup at a key given in its renamed spelling. -/
theorem EnvRel.find_of {env : Env md} {env' : Env md'} (h : EnvRel P f env env') {k : Key md}
    (hk : k.Good P) {k' : Key md'} (hk' : k' = k.map f) :
    env'.find? k' = (env.find? k).map (ConstantInfo.mapKeys f) :=
  hk' ▸ h.find k hk

theorem ConstantInfo.mapKeys_beq (hf : InjOn f P) {a b : ConstantInfo md} (ha : a.Good P)
    (hb : b.Good P) : (a.mapKeys f == b.mapKeys f) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ConstantInfo.mapKeys_eq_iff hf ha hb

/-- A constant applied to bound variables, at a renamed constant. -/
theorem bvarsApp_map (K : Key md) (us : List Level) (n : Nat) (g : Nat → Nat) :
    (Expr.mkAppN (.const (K.map f) us) ((List.range n).map fun k => Expr.bvar (g k)) : Expr md') =
      (Expr.mkAppN (.const K us) ((List.range n).map fun k => Expr.bvar (g k)) : Expr md).mapKeys f := by
  simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def, Expr.mapKeys]

theorem bvarsApp_good {K : Key md} (hK : K.Good P) (us : List Level) (n : Nat) (g : Nat → Nat) :
    (Expr.mkAppN (.const K us) ((List.range n).map fun k => Expr.bvar (g k)) : Expr md).Good P :=
  Expr.Good.mkAppN (show Expr.Good P (Expr.const K us) from hK) (bvarList_good n g)

/-- The eta theorem's right side, at a renamed structure. -/
theorem etaRhs_map (T C : Key md) (us : List Level) (nP nF : Nat) :
    (Expr.mkAppN (.const (auxKey (C.map f) .model) us)
      (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
        (List.range nF).map fun j => Expr.mkAppN (.const (projModelName (T.map f) j) us)
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++ [Expr.bvar 0])) : Expr md') =
    (Expr.mkAppN (.const (auxKey C .model) us)
      (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
        (List.range nF).map fun j => Expr.mkAppN (.const (projModelName T j) us)
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++ [Expr.bvar 0])) : Expr md).mapKeys f := by
  simp [Expr.mapKeys_mkAppN, List.map_map, Function.comp_def, Expr.mapKeys]
  rfl

theorem etaRhs_good {T C : Key md} (hT : T.Good P) (hC : C.Good P) (us : List Level) (nP nF : Nat) :
    (Expr.mkAppN (.const (auxKey C .model) us)
      (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
        (List.range nF).map fun j => Expr.mkAppN (.const (projModelName T j) us)
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++ [Expr.bvar 0])) : Expr md).Good P := by
  refine Expr.Good.mkAppN (show Expr.Good P (Expr.const (auxKey C .model) us) from hC) ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact bvarList_good nP _ x hx
  · simp only [List.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    refine Expr.Good.mkAppN (show Expr.Good P (Expr.const (projModelName T j) us) from hT) ?_
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact bvarList_good nP _ y hy
    · simp only [List.mem_singleton] at hy
      subst hy
      trivial

/-- **The eta theorem's check at a renamed structure** answers alike. -/
theorem checkEtaThm_map (mode : CheckMode) {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {T C : Key md} (hT : T.Good P) (hC : C.Good P)
    (lps : List LevelParam) (nP nF : Nat) :
    checkEtaThm mode env' (T.map f) (C.map f) lps nP nF = checkEtaThm mode env T C lps nP nF := by
  have hf := hE.inj
  unfold checkEtaThm
  rw [hE.find_of (k := auxKey (auxKey T .model) .eta) (k' := auxKey (auxKey (T.map f) .model) .eta)
      hT rfl,
    hE.find_of (k := auxKey T .model) (k' := auxKey (T.map f) .model) hT rfl,
    hE.find_of (k := auxKey C .model) (k' := auxKey (C.map f) .model) hC rfl,
    hE.find_of (k := (eqName : Key md)) (k' := (eqName : Key md')) trivial rfl]
  cases h1 : env.find? (auxKey (auxKey T .model) .eta) with
  | none => rfl
  | some c1 => ?_
  have hc1 := hE.good (auxKey (auxKey T .model) .eta) c1 hT h1
  cases c1 with
  | thmInfo tcv tval => ?_
  | _ => rfl
  cases h2 : env.find? (auxKey T .model) with
  | none => rfl
  | some c2 => ?_
  have hc2 := hE.good (auxKey T .model) c2 hT h2
  cases c2 with
  | defnInfo cvmT vT hT' => ?_
  | _ => rfl
  cases h3 : env.find? (auxKey C .model) with
  | none => rfl
  | some c3 => ?_
  cases c3 with
  | defnInfo cvmC vC hC' => ?_
  | _ => rfl
  cases h4 : env.find? eqName with
  | none => rfl
  | some eqStored => ?_
  have hc4 := hE.good (eqName : Key md) eqStored trivial h4
  simp only [Option.map_some]
  generalize hes : ConstantInfo.mapKeys f eqStored = eS'
  simp only [ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.stripPis_mapKeys]
  subst hes
  rw [← eqA_mapKeys (f := f), ConstantInfo.mapKeys_beq hf hc4 (ConstantInfo.good_of_noIds eqA_noIds)]
  refine andC (andC rfl ?_) ?_
  · refine congrArg (List.all (List.range nF)) (funext fun j => ?_)
    rw [hE.find_of (k := projModelName T j) (k' := projModelName (T.map f) j) hT rfl]
    cases env.find? (projModelName T j) with
    | none => rfl
    | some c => cases c <;> rfl
  cases h5 : Expr.stripPis (nP + 1) tcv.type with
  | none => rfl
  | some q5 => ?_
  obtain ⟨sbinders, sbody⟩ := q5
  obtain ⟨hsb, hsbody⟩ := Expr.stripPis_good hc1.1.2 h5
  cases h6 : Expr.stripPis nP cvmT.type with
  | none => rfl
  | some q6 => ?_
  obtain ⟨tbindersM, tbodyM⟩ := q6
  obtain ⟨htb, htbody⟩ := Expr.stripPis_good hc2.1.2 h6
  simp only [Option.map_some, Expr.mapTele]
  rw [domsMatchAux_ren (g := fun _ e => e) (fun _ _ _ => rfl) (fun _ _ he => he) hf hsb htb,
    mapBinders_getElem?]
  refine andC (andC rfl ?_) ?_
  · cases hx : sbinders[nP]? with
    | none => rfl
    | some xb =>
      obtain ⟨xdom, _⟩ := xb
      have hxd : xdom.Good P := hsb (xdom, _) (List.mem_of_getElem? hx)
      simp only [Option.map_some]
      rw [show (auxKey (T.map f) .model : Key md') = (auxKey T .model).map f from rfl,
        bvarsApp_map, Expr.mapKeys_beq hf hxd (bvarsApp_good (K := auxKey T .model) hT _ _ _)]
  cases sbody with
  | app s₁ rhsC => ?_
  | _ => rfl
  cases s₁ with
  | app s₂ lhsC => ?_
  | _ => rfl
  cases s₂ with
  | app s₃ tySlot => ?_
  | _ => rfl
  cases s₃ with
  | const c us => ?_
  | _ => rfl
  cases us with
  | cons ℓA rest => ?_
  | nil => rfl
  cases rest with
  | nil => ?_
  | cons _ _ => rfl
  simp only [Expr.Good] at hsbody
  obtain ⟨⟨⟨hcg, htys⟩, hlhsC⟩, hrhsC⟩ := hsbody
  simp only [Expr.mapKeys, eqName, roleKey, Key.map_beq_role, Expr.mapKeys_beq_bvar']
  rw [etaRhs_map, Expr.mapKeys_beq hf hrhsC (etaRhs_good hT hC _ nP nF),
    show (auxKey (T.map f) .model : Key md') = (auxKey T .model).map f from rfl,
    bvarsApp_map, Expr.mapKeys_beq hf htys (bvarsApp_good (K := auxKey T .model) hT _ _ _),
    show (Expr.sort ℓA : Expr md') = (Expr.sort ℓA : Expr md).mapKeys f from rfl,
    Expr.mapKeys_beq hf htbody (show Expr.Good P (Expr.sort ℓA : Expr md) from trivial)]


/-- **The unit-likeness theorem's check at a renamed family** answers alike. -/
theorem checkUnitThm_map (mode : CheckMode) {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {T : Key md} (hT : T.Good P) (lps : List LevelParam) (nP : Nat) :
    checkUnitThm mode env' (T.map f) lps nP = checkUnitThm mode env T lps nP := by
  have hf := hE.inj
  unfold checkUnitThm
  rw [hE.find_of (k := auxKey (auxKey T .model) .unitlike)
      (k' := auxKey (auxKey (T.map f) .model) .unitlike) hT rfl,
    hE.find_of (k := auxKey T .model) (k' := auxKey (T.map f) .model) hT rfl,
    hE.find_of (k := (eqName : Key md)) (k' := (eqName : Key md')) trivial rfl]
  cases h1 : env.find? (auxKey (auxKey T .model) .unitlike) with
  | none => rfl
  | some c1 => ?_
  have hc1 := hE.good (auxKey (auxKey T .model) .unitlike) c1 hT h1
  cases c1 with
  | thmInfo tcv tval => ?_
  | _ => rfl
  cases h2 : env.find? (auxKey T .model) with
  | none => rfl
  | some c2 => ?_
  have hc2 := hE.good (auxKey T .model) c2 hT h2
  cases c2 with
  | defnInfo cvmT vT hT' => ?_
  | _ => rfl
  cases h4 : env.find? eqName with
  | none => rfl
  | some eqStored => ?_
  have hc4 := hE.good (eqName : Key md) eqStored trivial h4
  simp only [Option.map_some]
  generalize hes : ConstantInfo.mapKeys f eqStored = eS'
  simp only [ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.stripPis_mapKeys]
  subst hes
  rw [← eqA_mapKeys (f := f), ConstantInfo.mapKeys_beq hf hc4 (ConstantInfo.good_of_noIds eqA_noIds)]
  refine andC rfl ?_
  cases h5 : Expr.stripPis (nP + 2) tcv.type with
  | none => rfl
  | some q5 => ?_
  obtain ⟨sbinders, sbody⟩ := q5
  obtain ⟨hsb, hsbody⟩ := Expr.stripPis_good hc1.1.2 h5
  cases h6 : Expr.stripPis nP cvmT.type with
  | none => rfl
  | some q6 => ?_
  obtain ⟨tbindersM, tbodyM⟩ := q6
  obtain ⟨htb, htbody⟩ := Expr.stripPis_good hc2.1.2 h6
  simp only [Option.map_some, Expr.mapTele]
  rw [domsMatchAux_ren (g := fun _ e => e) (fun _ _ _ => rfl) (fun _ _ he => he) hf hsb htb,
    mapBinders_getElem?, mapBinders_getElem?]
  refine andC (andC (andC rfl ?_) ?_) ?_
  · cases hx : sbinders[nP]? with
    | none => rfl
    | some xb =>
      obtain ⟨xdom, _⟩ := xb
      have hxd : xdom.Good P := hsb (xdom, _) (List.mem_of_getElem? hx)
      simp only [Option.map_some]
      rw [show (auxKey (T.map f) .model : Key md') = (auxKey T .model).map f from rfl,
        bvarsApp_map, Expr.mapKeys_beq hf hxd (bvarsApp_good (K := auxKey T .model) hT _ _ _)]
  · cases hy : sbinders[nP + 1]? with
    | none => rfl
    | some yb =>
      obtain ⟨ydom, _⟩ := yb
      have hyd : ydom.Good P := hsb (ydom, _) (List.mem_of_getElem? hy)
      simp only [Option.map_some]
      rw [show (auxKey (T.map f) .model : Key md') = (auxKey T .model).map f from rfl,
        bvarsApp_map, Expr.mapKeys_beq hf hyd (bvarsApp_good (K := auxKey T .model) hT _ _ _)]
  cases sbody with
  | app s₁ rhsC => ?_
  | _ => rfl
  cases s₁ with
  | app s₂ lhsC => ?_
  | _ => rfl
  cases s₂ with
  | app s₃ tySlot => ?_
  | _ => rfl
  cases s₃ with
  | const c us => ?_
  | _ => rfl
  cases us with
  | cons ℓA rest => ?_
  | nil => rfl
  cases rest with
  | nil => ?_
  | cons _ _ => rfl
  simp only [Expr.Good] at hsbody
  obtain ⟨⟨⟨hcg, htys⟩, hlhsC⟩, hrhsC⟩ := hsbody
  simp only [Expr.mapKeys, eqName, roleKey, Key.map_beq_role, Expr.mapKeys_beq_bvar']
  rw [show (auxKey (T.map f) .model : Key md') = (auxKey T .model).map f from rfl,
    bvarsApp_map, Expr.mapKeys_beq hf htys (bvarsApp_good (K := auxKey T .model) hT _ _ _),
    show (Expr.sort ℓA : Expr md') = (Expr.sort ℓA : Expr md).mapKeys f from rfl,
    Expr.mapKeys_beq hf htbody (show Expr.Good P (Expr.sort ℓA : Expr md) from trivial)]

theorem piResultIsProp_mapKeys (e : Expr md) : piResultIsProp (e.mapKeys f) = piResultIsProp e := by
  unfold piResultIsProp
  rw [← Expr.mapKeys_piResult]
  cases e.piResult <;> rfl

theorem piResultZ_mapKeys (e : Expr md) : piResultZ (e.mapKeys f) = piResultZ e := by
  unfold piResultZ
  rw [← Expr.mapKeys_piResult]
  cases e.piResult <;> rfl

/-- **The capability record at a renamed block** is the renamed record. -/
theorem indBlockCaps_map (mode : CheckMode) {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {cvT cvC : ConstantVal md} (hT : cvT.Good P) (hC : cvC.Good P)
    (nP nF : Nat) :
    indBlockCaps mode env' (cvT.mapKeys f) (cvC.mapKeys f) nP nF =
      (indBlockCaps mode env cvT cvC nP nF).mapKeys f := by
  simp only [indBlockCaps, IndCaps.mapKeys, ConstantVal.mapKeys_levelParams,
    ConstantVal.mapKeys_name, ConstantVal.mapKeys_type, checkEtaThm_map mode hE hT.1 hC.1,
    checkUnitThm_map mode hE hT.1, piResultIsProp_mapKeys, piResultZ_mapKeys, Option.map_some]
  rfl

theorem indBlockCaps_good (mode : CheckMode) (env : Env md) {cvT cvC : ConstantVal md}
    (hC : cvC.Good P) (nP nF : Nat) : (indBlockCaps mode env cvT cvC nP nF).Good P := by
  intro k hk
  simp only [indBlockCaps, Option.mem_def, Option.some.injEq] at hk
  subst hk
  exact hC.1

/-- **The eta constructor's residual gate at a renamed block** answers alike. -/
theorem ctorResidualOk_map (mode : CheckMode) {env : Env md} {env' : Env md'}
    (hE : EnvRel P f env env') {T C : Key md} (hT : T.Good P) (hC : C.Good P)
    (lps : List LevelParam) (nP nF : Nat) (eta : Bool) :
    ctorResidualOk mode env' (T.map f) (C.map f) lps nP nF eta =
      ctorResidualOk mode env T C lps nP nF eta := by
  have hf := hE.inj
  unfold ctorResidualOk
  rw [hE.find C hC]
  cases h : env.find? C with
  | none => rfl
  | some c => ?_
  have hc := hE.good C c hC h
  cases c with
  | ctorInfo cv cnP cnF => ?_
  | _ => rfl
  simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_type,
    Expr.stripPis_mapKeys]
  cases h2 : Expr.stripPis (nP + nF) cv.type with
  | none => rfl
  | some q => ?_
  obtain ⟨bs, cbody⟩ := q
  obtain ⟨_, hcb⟩ := Expr.stripPis_good hc.2 h2
  simp only [Option.map_some, Expr.mapTele]
  rw [structFam_map, Expr.mapKeys_beq hf hcb (structFam_good hT lps nP nF)]

/-- **The structure-likeness gate at a renamed block** answers alike. -/
theorem ctorTargetsFam_map (hf : InjOn f P) {ty : Expr md} (hty : ty.Good P) {T : Key md}
    (hT : T.Good P) (lps : List LevelParam) (nP nF : Nat) :
    ctorTargetsFam (ty.mapKeys f) (T.map f) lps nP nF = ctorTargetsFam ty T lps nP nF := by
  unfold ctorTargetsFam
  rw [Expr.stripPis_mapKeys]
  cases h : Expr.stripPis (nP + nF) ty with
  | none => rfl
  | some q =>
    obtain ⟨bs, cbody⟩ := q
    obtain ⟨_, hcb⟩ := Expr.stripPis_good hty h
    simp only [Option.map_some, Expr.mapTele]
    rw [structFam_map, Expr.mapKeys_beq hf hcb (structFam_good hT lps nP nF)]

/-- The projection name family's freeness at a renamed family. -/
theorem projFamFree_map {env : Env md} {env' : Env md'} (hE : EnvRel P f env env') {T : Key md}
    (hT : T.Good P) (nF : Nat) :
    ((List.range nF).all fun j => (env'.find? (projFnName (T.map f) j)).isNone) =
      ((List.range nF).all fun j => (env.find? (projFnName T j)).isNone) := by
  refine congrArg (List.all (List.range nF)) (funext fun j => ?_)
  rw [hE.find_of (k := projFnName T j) (k' := projFnName (T.map f) j) hT rfl]
  cases env.find? (projFnName T j) <;> rfl
end Ix.Kernel
