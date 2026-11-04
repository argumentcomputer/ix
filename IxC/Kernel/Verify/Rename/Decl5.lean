module

public import IxC.Kernel.Verify.Rename.Modeled7

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
    simp only [checkDecl, Declaration.mapKeys]
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
    simp only [checkDecl, Declaration.mapKeys]
    exact SimR.bindE (checkConstantVal_sim hops hE hcv) (fun cvA hcvA => checkThmVal_sim hops hE hcvA hv)
  | opaqueDecl cv value =>
    obtain ⟨hcv, hv⟩ := hd
    simp only [checkDecl, Declaration.mapKeys]
    exact SimR.bindE (checkConstantVal_sim hops hE hcv)
      (fun cvA hcvA => checkOpaqueVal_sim hops hE hcvA hv)
  | axiomDecl cv =>
    simp only [checkDecl, Declaration.mapKeys]
    have hcv : cv.Good P := hd
    refine SimR.ite (by simp) (fun _ => ?_) (fun _ => ?_)
    · exact SimR.ite (by rw [quotSoundPin_ren hf hE.pre hcv]) (fun _ => SimR.pure' hE) (fun _ => SimR.throw')
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
