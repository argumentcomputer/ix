module

public import IxCK.Kernel.Verify.Rename.Modeled7

@[expose] public section

/-!
# The renaming walk: one declaration (step 7.3, chunk (iii))

`checkDecl` at a renamed declaration, over related environments and renamed
evidence: every arm (definitions with the structural and well-founded `Nat`
operations' gates, theorems, opaques, axioms with the quotient soundness
record, the basis, inductive blocks through the shape guard, the pinned
blocks, the parameter count and both routes, quotient records) is simulated.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-! ## The routes' recognisers -/

theorem nativeShape?_good {nPd : Nat} {block : List (ConstantInfo md)}
    (hb : ∀ c ∈ block, c.Good P) {p : InductiveShape md} (h : nativeShape? nPd block = some p) :
    p.Good P := by
  unfold nativeShape? at h
  rcases block with _ | ⟨c, rest⟩
  · cases h
  cases c with
  | indInfo cvT caps => ?_
  | _ => cases h
  dsimp only at h
  have hT : cvT.Good P := (hb _ List.mem_cons_self).1
  have hrest : ∀ c ∈ rest, c.Good P := fun c hc => hb c (List.mem_cons_of_mem _ hc)
  cases hs : sumSplit rest with
  | none => rw [hs] at h; cases h
  | some q => ?_
  rw [hs] at h
  obtain ⟨cs, cvR, mI, rP, rules⟩ := q
  obtain ⟨hcs, hR, hrules⟩ := sumSplit_good hrest hs
  have hctors : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)), c.1.Good P := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact hcs d hd
  have hrhss : Expr.GoodList P (rules.map (·.rhs)) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact (hrules r hr).2.2
  dsimp only at h
  cases hc : nativeCounts? nPd cvT cs mI rP with
  | none => rw [hc] at h; cases h
  | some c => ?_
  rw [hc] at h
  obtain ⟨nP, nIdx⟩ := c
  dsimp only at h
  split at h
  · split at h <;> (cases h; exact ⟨hT, hctors, hR, hrhss⟩)
  · cases h

theorem nativeParts?_good {nPd : Nat} {block : List (ConstantInfo md)}
    (hb : ∀ c ∈ block, c.Good P) {p : NativeParts md} (h : nativeParts? nPd block = some p) :
    p.Good P := by
  unfold nativeParts? at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact nativeShape?_good hb hs

theorem Expr.piSortTeleLen?_mapKeys (e : Expr md) :
    (e.mapKeys f).piSortTeleLen? = e.piSortTeleLen? := by
  induction e <;> simp_all [Expr.piSortTeleLen?, Expr.mapKeys]

theorem indParamsOk_map (nP : Nat) (block : List (ConstantInfo md)) :
    indParamsOk nP (block.map (ConstantInfo.mapKeys f)) = indParamsOk nP block := by
  unfold indParamsOk
  rw [List.all_map]
  congr 1
  funext c
  cases c <;> simp [ConstantInfo.mapKeys, Expr.piSortTeleLen?_mapKeys]

/-! ## The quotient soundness record -/

theorem quotSoundPin_ren (hf : InjOn f P) (hpre : P.Pre) {cv : ConstantVal md} (hcv : cv.Good P) :
    ConstantInfo.canonEq (.axiomInfo (cv.mapKeys f))
        ((quotBasis (md := md')).getD 4 (.axiomInfo default)) =
      ConstantInfo.canonEq (.axiomInfo cv) ((quotBasis (md := md)).getD 4 (.axiomInfo default)) := by
  have hd := decls_mapKeys (md := md) (f := f) .quotK
  change ConstantInfo.canonEq _ ((BasisKind.quotK.decls (md := md')).getD 4 _) =
    ConstantInfo.canonEq _ ((BasisKind.quotK.decls (md := md)).getD 4 _)
  rw [← hd]
  have hpin : ((BasisKind.quotK.decls (md := md)).getD 4 (.axiomInfo default)).Good P := by
    simp only [List.getD_eq_getElem?_getD]
    cases hk : (BasisKind.quotK.decls (md := md))[4]? with
    | none => exact ⟨hpre .nat (by decide), trivial⟩
    | some c => exact decls_good hpre .quotK c (List.mem_of_getElem? hk)
  have hg : ((BasisKind.quotK.decls (md := md)).map (ConstantInfo.mapKeys f)).getD 4
      (.axiomInfo default) =
      ((BasisKind.quotK.decls (md := md)).getD 4 (.axiomInfo default)).mapKeys f := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (BasisKind.quotK.decls (md := md))[4]? <;> rfl
  rw [hg, show (ConstantInfo.axiomInfo (cv.mapKeys f)) = (ConstantInfo.axiomInfo cv).mapKeys f
    from rfl, ConstantInfo.canonEq_ren hf (a := .axiomInfo cv) hcv hpin]

theorem natOpEnv_ren {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') (hall : P.All)
    (k : Key md) :
    (natOpGuard env' (k.map f) && (natOpDeps (k.map f)).all (natOpStoredOk env')) =
      (natOpGuard env k && (natOpDeps k).all (natOpStoredOk env)) := by
  rw [natOpGuard_ren_of hE k (natOpDeps_good_all hall k), natOpDeps_map, List.all_map]
  refine andC rfl ?_
  apply List.all_congr_mem
  intro n hn
  exact natOpStoredOk_ren hE (natOpDeps_good_all hall k n hn)

theorem natOpEqsSubst_ren (hf : InjOn f P) (hall : P.All) {k : Key md} (hk : k.Good P) (value' : Expr md) :
    ((natOpEquations 0 (k.map f)).map fun eq =>
        (Expr.substConst0 (k.map f) (value'.mapKeys f) eq.1,
         Expr.substConst0 (k.map f) (value'.mapKeys f) eq.2)) =
      (((natOpEquations 0 k).map fun eq =>
          (Expr.substConst0 k value' eq.1, Expr.substConst0 k value' eq.2)).map
        fun p => (p.1.mapKeys f, p.2.mapKeys f)) := by
  rw [natOpEquations_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro p hp
  have hg := natOpEquations_good hall.pre 0 k (natOpDeps_good_all hall k) p hp
  simp only [Function.comp_def, substConst0_ren hf hk value' hg.1, substConst0_ren hf hk value' hg.2]

theorem natOpEqsSubst_good (hall : P.All) {k : Key md} {value' : Expr md} (hv : value'.Good P) :
    ∀ p ∈ ((natOpEquations 0 k).map fun eq =>
        (Expr.substConst0 k value' eq.1, Expr.substConst0 k value' eq.2)),
      p.1.Good P ∧ p.2.Good P := by
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hg := natOpEquations_good hall.pre 0 k (natOpDeps_good_all hall k) q hq
  exact ⟨substConst0_good hv hg.1, substConst0_good hv hg.2⟩

/-! ## One declaration -/

/-- **A declaration that installs no operation**: not a definition named by a
structural or well-founded `Nat` operation. Such a declaration's check
consults neither the evidence nor the operations' roles. -/
def Declaration.NoOp : Declaration md → Prop
  | .defnDecl cv _ _ => natOpNames.contains cv.name = false ∧ natDivModNames.contains cv.name = false
  | _ => True

/-- The standard axioms' check fails at any other name. -/
theorem stdAxiomOk_other {env : Env md} {cvA : ConstantVal md}
    (h : ¬(cvA.name = propextName ∨ cvA.name = choiceName)) : stdAxiomOk env cvA = false := by
  unfold stdAxiomOk
  rw [if_neg (fun e => h (Or.inl e)), if_neg (fun e => h (Or.inr e))]

private def Key.isRole : Key md → Bool
  | .role _ => true
  | _ => false

private def Expr.roleOnly : Expr md → Bool
  | .bvar _ | .sort _ | .lit _ => true
  | .const k _ => k.isRole
  | .fvar _ ty => ty.roleOnly
  | .app g a => g.roleOnly && a.roleOnly
  | .lam t b _ | .forallE t b _ => t.roleOnly && b.roleOnly
  | .letE t v b _ => t.roleOnly && v.roleOnly && b.roleOnly
  | .proj s _ x => s.isRole && x.roleOnly

private theorem Key.map_eq_of_isRole (f : md.Id → md'.Id) {k p : Key md} (hp : p.isRole = true) :
    k.map f = p.map f ↔ k = p := by
  cases p with
  | role r =>
    cases k <;> simp [Key.map]
  | id _ | aux _ _ => exact nomatch hp

private theorem Expr.mapKeys_eq_of_roleOnly (f : md.Id → md'.Id) :
    ∀ {e p : Expr md}, p.roleOnly = true → (e.mapKeys f = p.mapKeys f ↔ e = p) := by
  intro e p hp
  induction e generalizing p with
  | bvar i => cases p <;> simp [Expr.mapKeys]
  | sort u => cases p <;> simp [Expr.mapKeys]
  | fvar i ty ih =>
    cases p with
    | fvar j ty' =>
      simp only [Expr.roleOnly] at hp
      simp only [Expr.mapKeys, Expr.fvar.injEq, ih hp]
    | _ => simp [Expr.mapKeys]
  | const k us =>
    cases p with
    | const k' us' =>
      simp only [Expr.roleOnly] at hp
      simp only [Expr.mapKeys, Expr.const.injEq, Key.map_eq_of_isRole f hp]
    | _ => simp [Expr.mapKeys]
  | app g a ihg iha =>
    cases p with
    | app g' a' =>
      simp only [Expr.roleOnly, Bool.and_eq_true] at hp
      simp only [Expr.mapKeys, Expr.app.injEq, ihg hp.1, iha hp.2]
    | _ => simp [Expr.mapKeys]
  | lam t b m iht ihb =>
    cases p with
    | lam t' b' m' =>
      simp only [Expr.roleOnly, Bool.and_eq_true] at hp
      simp only [Expr.mapKeys, Expr.lam.injEq, iht hp.1, ihb hp.2]
    | _ => simp [Expr.mapKeys]
  | forallE t b m iht ihb =>
    cases p with
    | forallE t' b' m' =>
      simp only [Expr.roleOnly, Bool.and_eq_true] at hp
      simp only [Expr.mapKeys, Expr.forallE.injEq, iht hp.1, ihb hp.2]
    | _ => simp [Expr.mapKeys]
  | letE t v b m iht ihv ihb =>
    cases p with
    | letE t' v' b' m' =>
      simp only [Expr.roleOnly, Bool.and_eq_true] at hp
      simp only [Expr.mapKeys, Expr.letE.injEq, iht hp.1.1, ihv hp.1.2, ihb hp.2]
    | _ => simp [Expr.mapKeys]
  | lit l => cases p <;> simp [Expr.mapKeys]
  | proj s i x ihx =>
    cases p with
    | proj s' i' x' =>
      simp only [Expr.roleOnly, Bool.and_eq_true] at hp
      simp only [Expr.mapKeys, Expr.proj.injEq, Key.map_eq_of_isRole f hp.1, ihx hp.2]
    | _ => simp [Expr.mapKeys]

private theorem Expr.erasePw_roleOnly : ∀ {e : Expr md}, e.roleOnly = true → e.erasePw.roleOnly = true := by
  intro e he
  induction e with
  | bvar _ | sort _ | lit _ => exact he
  | const _ _ => exact he
  | fvar _ _ ih => exact ih he
  | app _ _ ih1 ih2 =>
    simp only [Expr.roleOnly, Bool.and_eq_true] at he
    simp [Expr.erasePw, Expr.roleOnly, ih1 he.1, ih2 he.2]
  | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
    simp only [Expr.roleOnly, Bool.and_eq_true] at he
    simp [Expr.erasePw, Expr.roleOnly, ih1 he.1, ih2 he.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.roleOnly, Bool.and_eq_true] at he
    simp [Expr.erasePw, Expr.roleOnly, ih1 he.1.1, ih2 he.1.2, ih3 he.2]
  | proj _ _ _ ih =>
    simp only [Expr.roleOnly, Bool.and_eq_true] at he
    simp [Expr.erasePw, Expr.roleOnly, he.1, ih he.2]

private theorem ConstantVal.matchesPin_of_roleOnly (f : md.Id → md'.Id) {cv pin : ConstantVal md}
    (hn : pin.name.isRole = true) (ht : pin.type.roleOnly = true) :
    ConstantVal.matchesPin (cv.mapKeys f) (pin.mapKeys f) = ConstantVal.matchesPin cv pin := by
  rw [Bool.eq_iff_iff]
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
    Expr.erasePw_mapKeys, Key.map_eq_of_isRole f hn,
    Expr.mapKeys_eq_of_roleOnly f (Expr.erasePw_roleOnly ht)]

private theorem installAnchorPin?_map (f : md.Id → md'.Id) (k : Key md) :
    installAnchorPin? (k.map f) = (installAnchorPin? k).map (ConstantVal.mapKeys f) := by
  cases k with
  | id _ | aux _ _ => rfl
  | role r => cases r <;> rfl

private theorem installAnchorPin?_roleOnly (r : Role) {pin : ConstantVal md}
    (h : installAnchorPin? (.role r) = some pin) :
    pin.name.isRole = true ∧ pin.type.roleOnly = true := by
  cases r <;> simp only [installAnchorPin?] at h <;> cases h <;> (cases md <;> decide)

theorem anchorMismatch?_isNone_mapKeys (f : md.Id → md'.Id) (cv : ConstantVal md) :
    (anchorMismatch? (cv.mapKeys f)).isNone = (anchorMismatch? cv).isNone := by
  unfold anchorMismatch?
  simp only [ConstantVal.mapKeys_name, installAnchorPin?_map]
  cases h : installAnchorPin? cv.name with
  | none => rfl
  | some pin =>
    have hro : pin.name.isRole = true ∧ pin.type.roleOnly = true := by
      cases hk : cv.name with
      | id _ | aux _ _ => rw [hk] at h; cases h
      | role r => rw [hk] at h; exact installAnchorPin?_roleOnly r h
    simp only [Option.map_some, ConstantVal.matchesPin_of_roleOnly f hro.1 hro.2]
    cases cv.matchesPin pin <;> rfl

/-- **One declaration at its renaming.** An operation's declaration reads the
operations' roles and the evidence unprompted, so it is simulated at a scope
allowing every role (`P.All`, the renaming's); any other at any scope. -/
theorem checkDecl_sim (mode : CheckMode) (hops : OpsSim P f L ops ops') {ev : Evidences md}
    (hev : ev.Good P) {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env')
    {d : Declaration md} (hd : d.Good P) (hop : d.NoOp ∨ P.All) :
    SimR (EnvRelG P f L) (checkDecl mode ops ev env d)
      (checkDecl mode ops' (ev.mapKeys f) env' (d.mapKeys f)) := by
  have hf := hE.inj
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨hcv, hv⟩ := hd
    simp only [checkDecl, Declaration.mapKeys, ConstantVal.mapKeys_name, Key.map_isCompilerTrust]
    refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
    refine SimR.bindE (checkConstantVal_sim_name hops hE hcv) (fun cvA ⟨hcvA, hname⟩ => ?_)
    refine SimR.bind (checkDefnVal_sim hops hE hcvA hv hint) (fun env2 env2' hE2 => ?_)
    simp only [ConstantVal.mapKeys_name, natOpNames_contains_map, natDivModNames_contains_map]
    rcases hop with ⟨h1, h2⟩ | hall
    · rw [hname, h1, h2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimR.pure' hE2
    have htail := SimR.ite (R := EnvRelG P f L) (c := natDivModNames.contains cvA.name = true)
      Iff.rfl
      (fun _ => SimR.bindE (k := fun _ => pure env2) (k' := fun _ => pure env2')
        (checkDivModEvidence_sim hops hE hE2 hall hev hcvA.1)
        (fun _ _ => SimR.pure' hE2))
      (fun _ => SimR.pure' hE2)
    refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => htail)
    refine SimR.ite (by rw [evidenceDefeqOk_ren]) (fun _ => ?_) (fun _ => SimR.throw_bind)
    refine SimR.ite (by rw [natOpEnv_ren hE2 hall]) (fun _ => ?_) (fun _ => SimR.throw_bind)
    rw [hE2.find _ hcvA.1]
    cases hfd : env2.find? cvA.name with
    | none => exact SimR.throw_bind
    | some c => ?_
    cases c with
    | defnInfo val value' hint' => ?_
    | _ => exact SimR.throw_bind
    have hv' : value'.Good P := (hE2.good _ _ hcvA.1 hfd).2
    simp only [Option.map_some, ConstantInfo.mapKeys]
    rw [natOpEqsSubst_ren hf hall hcvA.1 value']
    refine SimR.bindE (certifyNatEqs_sim hops hE _ (natOpEqsSubst_good hall hv')) (fun ok _ => ?_)
    exact SimR.ite Iff.rfl (fun _ => htail) (fun _ => SimR.throw_bind)
  | thmDecl cv value =>
    obtain ⟨hcv, hv⟩ := hd
    simp only [checkDecl, Declaration.mapKeys, ConstantVal.mapKeys_name, Key.map_isCompilerTrust]
    refine SimR.ite Iff.rfl (fun _ => SimR.throw_bind) (fun _ => ?_)
    exact SimR.bindE (checkConstantVal_sim hops hE hcv) (fun cvA hcvA => checkThmVal_sim hops hE hcvA hv)
  | opaqueDecl cv value =>
    obtain ⟨hcv, hv⟩ := hd
    simp only [checkDecl, Declaration.mapKeys, ConstantVal.mapKeys_name,
      Key.map_isCompilerTrustOpaque, Key.map_isCompilerTrustAxiom]
    refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · refine SimR.ite (by rw [anchorMismatch?_isNone_mapKeys]) (fun _ => ?_) (fun _ => SimR.throw')
      simp only [hE.find cv.name hcv.1, Option.isSome_map,
        Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys,
        ConstantVal.mapKeys_levelParams, Expr.allLevelParamsDefined_mapKeys]
      refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      exact SimR.bindE (checkConstantVal_sim hops hE hcv) (fun _ _ => SimR.pure' hE)
    · refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      exact SimR.bindE (checkConstantVal_sim hops hE hcv)
        (fun cvA hcvA => checkOpaqueVal_sim hops hE hcvA hv)
  | axiomDecl cv =>
    simp only [checkDecl, Declaration.mapKeys, ConstantVal.mapKeys_name,
      Key.map_isCompilerTrustAxiom, Key.map_isCompilerTrustOpaque]
    have hcv : cv.Good P := hd
    refine SimR.ite (by simp) (fun _ => ?_) (fun _ => ?_)
    · exact SimR.ite (by rw [quotSoundPin_ren hf hE.pre hcv]) (fun _ => SimR.pure' hE) (fun _ => SimR.throw')
    refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
    · refine SimR.ite (by rw [anchorMismatch?_isNone_mapKeys]) (fun _ => ?_) (fun _ => SimR.throw')
      simp only [hE.find cv.name hcv.1, Option.isSome_map,
        ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type,
        Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys, Expr.allLevelParamsDefined_mapKeys]
      refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
      refine SimR.ite (by simp) (fun _ => ?_) (fun _ => ?_)
      · exact SimR.bindE (checkConstantVal_sim hops hE hcv) (fun _ _ => SimR.pure' hE)
      · refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
        refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
        refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
        exact SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => SimR.pure' hE)
    refine SimR.ite Iff.rfl (fun _ => SimR.throw') (fun _ => ?_)
    refine SimR.bindE (checkConstantVal_sim hops hE hcv) (fun cvA hcvA => ?_)
    by_cases hok : stdAxiomOk env cvA = true
    · refine SimR.ite (by rw [stdAxiomOk_ren hE hcvA hok])
        (fun _ => SimR.pure' (hE.push (c := .axiomInfo cvA) hcvA)) (fun _ => ?_)
      exact absurd hok ‹_›
    by_cases hn : cvA.name = propextName ∨ cvA.name = choiceName
    · rw [if_neg hok, if_pos hn]
      exact SimR.throw'
    have hn' : ¬((cvA.mapKeys f).name = propextName ∨ (cvA.mapKeys f).name = choiceName) := by
      simpa using hn
    rw [stdAxiomOk_other hn', stdAxiomOk_other hn]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimR.ite (by simp) (fun _ => SimR.throw') (fun _ => ?_)
    exact SimR.ite (by simp) (fun _ => SimR.pure' hE) (fun _ => SimR.throw')
  | basisDecl kind =>
    simp only [checkDecl, Declaration.mapKeys]
    exact checkBasisDecl_sim hE kind
  | indDecl block nP =>
    simp only [checkDecl, Declaration.mapKeys]
    refine SimR.bindE (checkIndShape_sim hE hd) (fun _ _ => ?_)
    rw [basisPinHit_ren hf hE.pre hd]
    cases basisPinHit block with
    | some kind => exact checkBasisDecl_sim hE kind
    | none =>
      simp only [indParamsOk_map]
      refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw')
      rw [nativeParts?_map hf nP hd]
      cases hp : nativeParts? nP block with
      | some p => exact checkNative_sim hops hE (nativeParts?_good hd hp)
      | none => exact checkModeled_sim mode hops hE hd
  | quotDecl k cv =>
    simp only [checkDecl, Declaration.mapKeys]
    rw [quotPinHit_ren hf hE.pre k hd]
    refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw')
    cases k <;> first | exact checkBasisDecl_sim hE .quotK | exact SimR.pure' hE

end Ix.Kernel
