import IxVMRefinement.Decl.NativeRecRules

/-!
# Native Inductive Declarations (Top-Level Dispatcher & Structure Postconditions)

Top-level entry point for unpinned canonical native inductive declarations (`.indDecl block nPd`),
combining:
* **Native blocks with recursor** (`Ix.Kernel.nativeParts? nPd block = some p₀`), refined to
  `DeclNativeRunJ` + `InstallStep` + `DeclInv` in `IxVMRefinement.Decl.NativeRecRules`.
* **Recursor-less native blocks** (`nativePartsNoRec? nPd block = some p₀`), refined to
  `DeclNativeNoRecRunJ` + `InstallStep` + `DeclInv` in `IxVMRefinement.Decl.NativeFront`.
* **Post-install native structure & capability lemmas** (`nativeCapsAt`, `nativeCaps`,
  `checkNativeTable`, `ctorTeleOk`, `ctorZeroOk`, `FieldSortsJ`) used by `L7` when discharging
  `LoadFacts` (`projTables`, `projTablesAt`, `projTablesGuard`, `unitLike`, `eta`, `etaIota`).
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)
open Ix.Kernel.Semantics (Judgements ConstantValCheckJ StructDomsJ FieldSortsJ
  SumIndRunJ SumCtorRunJ SumCtorsRunJ FormerReadJ DeclRunJ IndRoutesJ
  DeclNativeRunJ DeclNativeNoRecRunJ nativePartsNoRec? ctorZeroOk)
open Ix.Kernel.Model (rulesJ)

/-! ## Section 1: Disjointness of `nativeParts?` and `nativePartsNoRec?` -/

/-- `Ix.Kernel.nativeParts?` (one-type native block with recursor) and `nativePartsNoRec?`
(one-type native block without recursor) are mutually exclusive on every block. -/
theorem nativeParts?_and_nativePartsNoRec?_disjoint {nPd : Nat} {block : List KConstantInfo}
    {p₁ p₂ : Ix.Kernel.NativeParts .anon}
    (hp₁ : Ix.Kernel.nativeParts? nPd block = some p₁)
    (hp₂ : nativePartsNoRec? nPd block = some p₂) : False := by
  obtain ⟨caps₁, cs₁, mI₁, rP₁, rules₁, hblk₁, _⟩ := nativeParts?_withRec_inv hp₁
  obtain ⟨caps₂, hblk₂, _⟩ := nativePartsNoRec?_inv hp₂
  rw [List.cons_append] at hblk₁
  have heq := hblk₁.symm.trans hblk₂
  injection heq with _ htail
  have hmem : (ConstantInfo.recInfo p₁.cvR mI₁ rP₁ rules₁ : KConstantInfo) ∈
      (p₂.ctors.map fun c => (ConstantInfo.ctorInfo c.1 p₂.nP c.2 : KConstantInfo)) := by
    rw [← htail]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hmem
  exact nomatch hc

/-! ## Section 2: Unified `NativeCheckedExtra` & Top-Level Native Block Dispatcher -/

/-- Extra `L7 → L5` record/role and specification-bridge hypotheses for an unpinned canonical
native `.indDecl block nPd` declaration (either with a recursor record or recursor-less). -/
inductive NativeCheckedExtra (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (block : List KConstantInfo) (nPd : Nat) : Prop where
  | withRec (p₀ : Ix.Kernel.NativeParts .anon)
      (hpin : Ix.Kernel.basisPinHit block = none)
      (hparts : Ix.Kernel.nativeParts? nPd block = some p₀)
      (extra : NativeWithRecExtra calls env block p₀) :
      NativeCheckedExtra calls env block nPd
  | noRec (p₀ : Ix.Kernel.NativeParts .anon)
      (hpin : Ix.Kernel.basisPinHit block = none)
      (hparts : nativePartsNoRec? nPd block = some p₀)
      (extra : NativeNoRecExtra calls env p₀) :
      NativeCheckedExtra calls env block nPd

/-- Unified `DeclRunJ` + `InstallStep` refinement for unpinned canonical native `.indDecl` blocks
(covering both `nativeParts?` with recursor and `nativePartsNoRec?` without recursor). -/
theorem nativeInd_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nPd : Nat}
    (hS : DeclStoreInv env)
    (extra : NativeCheckedExtra calls env block nPd) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nPd) env₂ ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nPd) env₂ := by
  rcases extra with ⟨p₀, hpin, hparts, hex⟩ | ⟨p₀, hpin, hparts, hex⟩
  · obtain ⟨env₂, hinst, hrun⟩ := nativeWithRec_step hLevels hCore hpin hparts hS hex
    exact ⟨env₂, hinst, declRunJ_of_native hpin hparts hrun⟩
  · obtain ⟨env₂, hinst, hrun⟩ := nativeNoRec_step hLevels hCore hpin hparts hS hex
    exact ⟨env₂, hinst, declRunJ_of_nativeNoRec hpin hparts hrun⟩

/-- Unified `DeclInv`-preserving `L5` step for unpinned canonical native `.indDecl` blocks. -/
theorem nativeInd_declInv_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nPd : Nat}
    (hchk : S0.Checked calls env (.indDecl block nPd))
    (extra : NativeCheckedExtra calls env block nPd) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nPd) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  rcases extra with ⟨p₀, hpin, hparts, hex⟩ | ⟨p₀, hpin, hparts, hex⟩
  · exact nativeWithRec_declInv_step hLevels hCore hchk hpin hparts hex
  · exact nativeNoRec_declInv_step hLevels hCore hchk hpin hparts hex

/-! ## Section 3: Native Structure Capabilities & `ProjTable` Postconditions for `LoadFacts` -/

/-- At a one-constructor index-free native inductive with zero fields, `nativeCapsAt` sets
`unitlike = true` and `unitParams = p₁.nP` (for `LoadFacts.unitLike`). -/
theorem nativeCapsAt_unitlike {p₁ : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {c : KConstantVal × Nat}
    (hctors : p₁.ctors = [c]) (hnIdx : p₁.nIdx = 0) (hnF : c.2 = 0) :
    (Ix.Kernel.nativeCapsAt p₁ isRec).unitlike = true ∧
    (Ix.Kernel.nativeCapsAt p₁ isRec).unitParams = p₁.nP := by
  simp [Ix.Kernel.nativeCapsAt, hctors, hnIdx, hnF]

/-- `nativeCaps` specialization of `nativeCapsAt_unitlike`. -/
theorem nativeCaps_unitlike {p : Ix.Kernel.NativeParts .anon} {c : KConstantVal × Nat}
    (hctors : p.ctors = [c]) (hnIdx : p.nIdx = 0) (hnF : c.2 = 0) :
    (Ix.Kernel.nativeCaps p).unitlike = true ∧
    (Ix.Kernel.nativeCaps p).unitParams = p.nP :=
  nativeCapsAt_unitlike hctors hnIdx hnF

/-- If some level substitution of `s` satisfies `Level.isNeverZero = true`, then `s` is not
equivalent to `.zero` (`(Level.isEquiv s .zero == some true) = false`, used by `LoadFacts.eta` and
`LoadFacts.etaIota`). -/
theorem isEquiv_zero_false_of_subst_isNeverZero {ps : List LevelParam} {us : List KLevel}
    {s : KLevel} (hnz : (Level.subst ps us s).isNeverZero = true) :
    (Level.isEquiv s .zero == some true) = false := by
  cases heq : (Level.isEquiv s .zero == some true) with
  | false => rfl
  | true =>
    have h0 := eval_zero_of_isEquiv_zero heq (Level.substFn (fun _ => 0) ps us)
    rw [← Level.eval_subst (fun _ => 0) ps us s] at h0
    exact absurd h0 (Ix.Kernel.Level.isNeverZero_sound (fun _ => 0) _ hnz)

/-- At a one-constructor index-free non-propositional non-recursive native inductive,
`nativeCapsAt` sets `eta = true`, `etaCtor = some c.1.name`, `etaFields = c.2`, and
`etaParams = p₁.nP` (for `LoadFacts.eta` and `LoadFacts.etaIota`). -/
theorem nativeCapsAt_eta_true {p₁ : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {c : KConstantVal × Nat}
    (hctors : p₁.ctors = [c]) (hnIdx : p₁.nIdx = 0)
    (hprop : p₁.isProp = false) (hrec : isRec = false) :
    (Ix.Kernel.nativeCapsAt p₁ isRec).eta = true ∧
    (Ix.Kernel.nativeCapsAt p₁ isRec).etaCtor = some c.1.name ∧
    (Ix.Kernel.nativeCapsAt p₁ isRec).etaFields = c.2 ∧
    (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams = p₁.nP := by
  simp [Ix.Kernel.nativeCapsAt, hctors, hnIdx, hprop, hrec]

/-- `nativeCaps` specialization of `nativeCapsAt_eta_true`. -/
theorem nativeCaps_eta_true {p : Ix.Kernel.NativeParts .anon} {c : KConstantVal × Nat}
    (hctors : p.ctors = [c]) (hnIdx : p.nIdx = 0)
    (hprop : p.isProp = false) (hrec : Ix.Kernel.nativeIsRec p.kinds = false) :
    (Ix.Kernel.nativeCaps p).eta = true ∧
    (Ix.Kernel.nativeCaps p).etaCtor = some c.1.name ∧
    (Ix.Kernel.nativeCaps p).etaFields = c.2 ∧
    (Ix.Kernel.nativeCaps p).etaParams = p.nP :=
  nativeCapsAt_eta_true hctors hnIdx hprop hrec

/-- Any constructor type whose `stripPis k` residual is `Expr.mkAppN (.const T us) args` satisfies
`Expr.ctorTeleOk ty k = true` (for `LoadFacts.projTablesGuard`). -/
theorem ctorTeleOk_of_stripPis_mkAppN_const {ty : KExpr} {k : Nat}
    {bs : List (KExpr × Ix.Kernel.BinderMeta)} {T : KKey} {us : List KLevel} {args : List KExpr}
    (hst : ty.stripPis k = some (bs, Expr.mkAppN (.const T us) args)) :
    Expr.ctorTeleOk ty k = true := by
  unfold Expr.ctorTeleOk
  rw [hst]
  dsimp only
  rw [getAppFn_mkAppN]
  rfl

/-- Along any prefix peeled by `Expr.stripPis k`, `ctorZeroOk T z ty = true` forces every peeled
binder's `PropWhen` metadata to equal `z` (for `LoadFacts.projTables` and `LoadFacts.projTablesAt`). -/
theorem stripPis_pw_of_ctorZeroOk {T : KKey} {z : Ix.Kernel.PropWhen} :
    ∀ {k : Nat} {ty : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      ty.stripPis k = some (bs, body) →
      ctorZeroOk T z ty = true →
      ∀ bm ∈ bs, bm.2.pw = z
  | 0, _, bs, _, hst, _, bm, hbm => by
    injection hst with hpair
    rw [← (Prod.mk.inj hpair).1] at hbm
    exact nomatch hbm
  | k + 1, .forallE dom b m, bs, body, hst, hcz, bm, hbm => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
    obtain ⟨⟨bs', body'⟩, hst', hpair⟩ := hst
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    simp only [ctorZeroOk, Bool.and_eq_true, beq_iff_eq] at hcz
    rcases List.mem_cons.mp hbm with rfl | hbm'
    · exact hcz.1.1
    · exact stripPis_pw_of_ctorZeroOk hst' hcz.2 bm hbm'
  | _ + 1, .bvar _, _, _, hst, _, _, _
  | _ + 1, .fvar _ _, _, _, hst, _, _, _
  | _ + 1, .sort _, _, _, hst, _, _, _
  | _ + 1, .const _ _, _, _, hst, _, _, _
  | _ + 1, .app _ _, _, _, hst, _, _, _
  | _ + 1, .lam _ _ _, _, _, hst, _, _, _
  | _ + 1, .letE _ _ _ _, _, _, hst, _, _, _
  | _ + 1, .lit _, _, _, hst, _, _, _
  | _ + 1, .proj _ _ _, _, _, hst, _, _, _ => nomatch hst

/-- Unpack `SumCtorRunJ` into constructor name/level-parameter agreement, sort-list length,
`Expr.ctorTeleOk`, stripped telescope, and `FieldSortsJ`. -/
theorem sumCtorRunJ_struct_facts {J : Judgements .anon} {env₀ env : Ix.Kernel.Env .anon}
    {T : KKey} {lps : List LevelParam} {nP nIdx : Nat} {resSort : KLevel} {isProp large : Bool}
    {cvC : KConstantVal} {nF : Nat} {cvTa cvCa : KConstantVal} {sorts : List KLevel}
    (hCtor : SumCtorRunJ J env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    cvCa.name = cvC.name ∧
    cvCa.levelParams = cvC.levelParams ∧
    sorts.length = nF ∧
    Expr.ctorTeleOk cvCa.type (nP + nF) = true ∧
    (∃ cbs es,
      cvCa.type.stripPis (nP + nF) =
        some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)) ∧
      es.length = nIdx) ∧
    ∃ xFvs idxArgs,
      FieldSortsJ J env isProp large resSort nP xFvs idxArgs nF sorts := by
  obtain ⟨⟨cvCa₀, ⟨_, _, hcv₀⟩, hca_or⟩, ⟨cbs, es, hst, hes_len⟩,
    ⟨_, _, _, _, xFvs, idxArgs, _, _, _, _, _, _, _, hFS⟩⟩ := hCtor
  have hnl : cvCa.name = cvC.name ∧ cvCa.levelParams = cvC.levelParams := by
    rcases hca_or with rfl | ⟨ty', _, _, hcv₁⟩
    · rw [hcv₀]; exact ⟨rfl, rfl⟩
    · rw [hcv₁]; exact ⟨rfl, rfl⟩
  exact ⟨hnl.1, hnl.2, hFS.1, ctorTeleOk_of_stripPis_mkAppN_const hst,
    ⟨cbs, es, hst, hes_len⟩, ⟨xFvs, idxArgs, hFS⟩⟩

/-- Unpack `checkNativeTable` on a one-constructor index-free native block (`p.nIdx = 0`), yielding
the installed `ProjTable` at the head of `env₂`, its lookup under `projTableName`, its `findProj?`
entries for every field `f < cA.2`, `structProjBodies`, and `structProjGuards` (for
`LoadFacts.projTables`, `LoadFacts.projTablesAt`, and `LoadFacts.projTablesGuard`). -/
theorem checkNativeTable_struct_inv {p : Ix.Kernel.NativeParts .anon}
    {cA : KConstantVal × Nat} {sorts : List KLevel} {env_pre env₂ : Ix.Kernel.Env .anon}
    (hnIdx : p.nIdx = 0)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p [cA] [sorts] env_pre =
      .ok env₂) :
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      env₂ = ⟨.projInfo tbl :: env_pre.consts⟩ ∧
      env_pre.find? (Ix.Kernel.projTableName p.cvT.name) = none ∧
      env₂.find? (Ix.Kernel.projTableName p.cvT.name) = some (.projInfo tbl) ∧
      tbl.structName = p.cvT.name ∧
      tbl.ctor = cA.1.name ∧
      tbl.numParams = p.nP ∧
      tbl.numFields = cA.2 ∧
      tbl.levelParams = p.cvT.levelParams ∧
      tbl.structSort = p.resSort ∧
      tbl.off = 1 ∧
      Ix.Kernel.structProjBodies tbl.structName p.nP cA.2 cA.1.type = some tbl.bodies ∧
      tbl.guards = Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts ∧
      (∀ f < cA.2, env₂.findProj? tbl.structName f = some (tbl.entry f)) := by
  unfold Ix.Kernel.checkNativeTable at hTbl
  simp only [hnIdx, beq_self_eq_true, ↓reduceIte] at hTbl
  obtain ⟨bodies, hbodies, _, _, hfresh_tbl, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
  let tbl : Ix.Kernel.ProjTable .anon :=
    ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort,
      bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩
  have hfind_tbl :
      (⟨.projInfo tbl :: env_pre.consts⟩ : Ix.Kernel.Env .anon).find?
        (Ix.Kernel.projTableName p.cvT.name) = some (.projInfo tbl) := by
    rw [Ix.Kernel.Env.find?_cons,
      ite_eq_left (show (ConstantInfo.projInfo tbl).name = Ix.Kernel.projTableName p.cvT.name
        from rfl)]
  refine ⟨tbl, rfl, hfresh_tbl, hfind_tbl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hbodies, rfl, fun f hf => ?_⟩
  unfold Ix.Kernel.Env.findProj?
  have hsn : tbl.structName = p.cvT.name := rfl
  rw [hsn, hfind_tbl]
  simp [tbl, hf]

end IxVM.Refinement.Decl
