import IxVMRefinement.FamilyAlias.ProjTableLaw
import IxVMRefinement.FamilyAlias.Selected

/-! # Installing modeled structure projection tables across a family block

Combines `ProjTablePrep`, `ProjCoherenceTop`, and `ProjTableLaw` into the block-level projection
table installer consumed by `FamilyAlias/StepFamily.lean`, `StepKeeps.lean`, `BlockLoads.lean`,
`BlockRowCheck.lean`, and `ClosureFamilyStep.lean`:

* **Computable, `V`- and `E`-independent projection constants** (`posProjTable?`,
  `blockProjEntries`, `projConstsOfTables`, `blockProjConsts`): extracts the `ProjTable .anon`
  (`off := 2`) for each eligible member `pos < ms.size` of a modeled block and emits its `nF`
  chain-graph axioms plus its `.projInfo` table.
* **Pure structural installation** (`fold_tables_pure`): establishes `EnvExt env env₃`,
  `StoreInv env₃`, `StoreArR env₃`, `NoProjEnv` bookkeeping, lookup preservation `find₂₃`,
  freshness, and `TowerHead` for every installed table entry.
* **Model installation** (`fold_tables_model`): folds `chainAxiom_step` (from
  `field_chain_coherence`) and `declStep_preserves_of_tower_cons` (from `modeled_towerEntryLaw`)
  across all eligible members, extending `ModelExt` and preserving `EtaFamiliesClosed`.
* **Whole-block result** (`BlockProjTableData`, `BlockProjInstallResult`,
  `install_block_proj_tables`): packages every invariant needed by the downstream family step and
  load contract (`Nodup`, freshness, `EnvExt`, `EnvModelN`, `FoldStoreInv`, `StoreArR`,
  `ThmLevels`, `AuxRootSynced`, `EtaStable`, and `BlockProjTableData`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts
  nonrecsOf recsOf storedMember auxKey_ne_of_isBaseKey find?_append_none)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule ProjEntry ProjTable LevelParam
  BinderMeta Key Env EnvExt SetTheory)
open Ix.Kernel.Semantics
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open Ix.Kernel.Model

/-! ## Section 1: Computable `V`-independent projection tables and constants -/

/-- Build the modeled projection table (`off := 2`) for position `pos` of block `B` directly from
`env₂` when `elig pos = true`. -/
def posProjTable? (t : Ix.Kernel.RoleTable) (env₂ : Env .anon) (B : _root_.Address)
    (elig : Nat → Bool) (pos : Nat) : Option (ProjTable .anon) :=
  if elig pos then
    let T := Core.keyOf t (Core.iprjAddr B pos)
    let C := Core.keyOf t (Core.cprjAddr B pos 0)
    match env₂.find? T, env₂.find? C with
    | some (.indInfo cvT _), some (.ctorInfo cvC nP nF) =>
      match cvT.type.stripPis nP, Ix.Kernel.structProjBodies T nP nF cvC.type with
      | some (_, .sort structSort), some bodies =>
        some
          { structName := T
            ctor := C
            numParams := nP
            numFields := nF
            levelParams := cvT.levelParams
            structSort := structSort
            bodies := bodies
            guards := Ix.Kernel.structProjGuards cvC.type nP nF (List.replicate nF .zero)
            off := 2 }
      | _, _ => none
    | _, _ => none
  else none

/-- Ordered list of eligible member projection tables (paired with their positions) for block `B`. -/
def blockProjEntries (t : Ix.Kernel.RoleTable) (env₂ : Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) (elig : Nat → Bool) : List (Nat × ProjTable .anon) :=
  (List.range ms.size).filterMap fun pos =>
    (posProjTable? t env₂ B elig pos).map fun tbl => (pos, tbl)

/-- All projection-table and chain-axiom constants prepended onto `env₂` for a list of tables
(installed right-to-left: tail tables are consed onto `env₂` first, head table sits on top). -/
def projConstsOfTables : List (Nat × ProjTable .anon) → List (ConstantInfo .anon)
  | [] => []
  | (_, tbl) :: rest => memberProjConsts tbl ++ projConstsOfTables rest

/-- All projection-table and chain-axiom constants for block `B`. -/
def blockProjConsts (t : Ix.Kernel.RoleTable) (env₂ : Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) (elig : Nat → Bool) : List (ConstantInfo .anon) :=
  projConstsOfTables (blockProjEntries t env₂ B ms elig)

/-- Installed projection-table data for every eligible member of a modeled block, consumed by
`BlockLoads.lean` to discharge `projTables`, `projTablesAt`, `projCtorTele`, and `projFire`. -/
structure BlockProjTableData (t : Ix.Kernel.RoleTable) (env₃ : Env .anon)
    (projConsts : List (ConstantInfo .anon)) (B : _root_.Address) (ms : Array Ixon.MutConst)
    (elig : Nat → Bool) where
  atEligible : ∀ pos < ms.size, elig pos = true →
    ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor)
      (cvC : ConstantVal .anon) (tbl : ProjTable .anon),
      ms[pos]? = some (.indc ind) ∧
      ind.ctors[0]? = some ct ∧
      ind.indices.toNat = 0 ∧
      ind.ctors.size = 1 ∧
      ct.params.toNat = ind.params.toNat ∧
      0 < ct.fields.toNat ∧
      env₃.find? (Core.keyOf t (Core.cprjAddr B pos 0)) =
        some (.ctorInfo cvC ind.params.toNat ct.fields.toNat) ∧
      env₃.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B pos))) =
        some (.projInfo tbl) ∧
      tbl.structName = Core.keyOf t (Core.iprjAddr B pos) ∧
      tbl.ctor = Core.keyOf t (Core.cprjAddr B pos 0) ∧
      tbl.numParams = ind.params.toNat ∧
      tbl.numFields = ct.fields.toNat ∧
      tbl.levelParams = cvC.levelParams ∧
      tbl.structSort.isNeverZero = true ∧
      (∀ f, f < ct.fields.toNat →
        env₃.findProj? tbl.structName f = some (tbl.entry f) ∧
        Ix.Kernel.TowerHead env₃ (tbl.entry f)) ∧
      Ix.Kernel.structProjBodies tbl.structName ind.params.toNat ct.fields.toNat cvC.type =
        some tbl.bodies ∧
      (∃ sorts : List KLevel, sorts.length = ct.fields.toNat ∧
        tbl.guards = Ix.Kernel.structProjGuards cvC.type ind.params.toNat ct.fields.toNat sorts) ∧
      (∃ bs body, cvC.type.stripPis (ind.params.toNat + ct.fields.toNat) = some (bs, body) ∧
        ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort) ∧
      Ix.Kernel.Expr.ctorTeleOk cvC.type (ind.params.toNat + ct.fields.toNat) = true
  projTablesNeverZero : ∀ tbl, ConstantInfo.projInfo tbl ∈ projConsts →
    tbl.structSort.isNeverZero = true
  projTablesPos : ∀ tbl, ConstantInfo.projInfo tbl ∈ projConsts →
    ∃ pos < ms.size, elig pos = true ∧
      tbl.structName = Core.keyOf t (Core.iprjAddr B pos)

/-- Complete result of installing all eligible modeled structure projection tables for a family
block onto `env₂` (reaching `env₃ = ⟨pcs ++ env₂.consts⟩`). -/
structure BlockProjInstallResult (t : Ix.Kernel.RoleTable) (env env₂ : Env .anon)
    (Reg : NativeFam .anon → Prop) (B : _root_.Address) (ms : Array Ixon.MutConst)
    (elig : Nat → Bool) (pcs : List (ConstantInfo .anon)) : Prop where
  nodup : (pcs.map (·.name)).Nodup
  freshPrefix : ∀ c ∈ pcs, env.find? c.name = none
  freshEnv₂ : ∀ c ∈ pcs, env₂.find? c.name = none
  kindAndName : ∀ c ∈ pcs,
    ∃ pos < ms.size, elig pos = true ∧
      ((∃ tbl, c = .projInfo tbl ∧
          c.name = Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B pos)) ∧
          tbl.structName = Core.keyOf t (Core.iprjAddr B pos) ∧
          tbl.structSort.isNeverZero = true) ∨
        (∃ j, c = chainAxiom (Core.keyOf t (Core.iprjAddr B pos)) j ∧
          c.name = Ix.Kernel.projChainKey (Core.keyOf t (Core.iprjAddr B pos)) j))
  envExt : EnvExt env ⟨pcs ++ env₂.consts⟩
  find₂ : ∀ {k : KKey} {ci : ConstantInfo .anon},
    env₂.find? k = some ci → (⟨pcs ++ env₂.consts⟩ : Env .anon).find? k = some ci
  model : ∀ (V : Type u) [SetTheory V],
    EnvModelN V .verified env Reg → EnvModelN V .verified ⟨pcs ++ env₂.consts⟩ Reg
  foldStore : Decl.FoldStoreInv ⟨pcs ++ env₂.consts⟩
  storeArR : Ix.Kernel.Model.StoreArR ⟨pcs ++ env₂.consts⟩
  thmLevels : Ix.Kernel.ThmLevels ⟨pcs ++ env₂.consts⟩
  auxRoot : Decl.AuxRootSynced ⟨pcs ++ env₂.consts⟩
  tableData : BlockProjTableData t ⟨pcs ++ env₂.consts⟩ pcs B ms elig

private theorem aliasGroup_defn_of_mem {env : Env .anon} {h : KKey → KKey}
    {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as) :
    ∀ a ∈ as, (∃ cv v hint, a = ConstantInfo.defnInfo cv v hint) ∧
      ∀ T, a.name ≠ Ix.Kernel.projTableName T := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons _ _ _ _ _ _ _ _ _ _ _ _ hnpt _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨⟨_, _, _, rfl⟩, hnpt⟩
    · exact ih a ha'

private theorem aliasGroup_name_aux {env : Env .anon} {h : KKey → KKey}
    {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as) :
    ∀ a ∈ as, ∃ n d, a.name = Ix.Kernel.auxKey n d := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons _ _ _ n d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨n, d, rfl⟩
    · exact ih a ha'

private theorem find?_append_cases_local {env : Env .anon} {k : KKey} :
    ∀ (new : List (ConstantInfo .anon)) {x : ConstantInfo .anon},
      (⟨new ++ env.consts⟩ : Env .anon).find? k = some x →
        x ∈ new ∨ env.find? k = some x
  | [], _, h => Or.inr h
  | c :: rest, x, h => by
    have h' : (⟨c :: (rest ++ env.consts)⟩ : Env .anon).find? k = some x := h
    rw [Ix.Kernel.Env.find?_cons] at h'
    split at h'
    · obtain rfl := Option.some.inj h'
      exact Or.inl List.mem_cons_self
    · rcases find?_append_cases_local rest h' with hm | ho
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr ho

/-! ## Section 2: Reading shape, distinctness, and `posProjTable?` specification -/

private theorem reads_ind_shape {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms) {pos : Nat} {ind : Ixon.Inductive}
    (hpos : pos < UInt64.size) (hms : ms[pos]? = some (.indc ind))
    {ci : ConstantInfo .anon} (hR : Reads t E₀ (Core.iprjAddr B pos) ci) :
    ∃ ty₀ caps, ci = .indInfo ⟨Core.keyOf t (Core.iprjAddr B pos), List.range ind.lvls.toNat, ty₀⟩ caps := by
  have hrec := hB.members pos (.indc ind) hms
  have hpos_u : pos.toUInt64.toNat = pos := by
    change (UInt64.ofNat pos).toNat = pos
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hpos
  obtain ⟨c, hrec', hRR⟩ := hR
  have hc_eq : c = memberProjection B pos (.indc ind) := Option.some.inj (hrec'.symm.trans hrec)
  subst hc_eq
  dsimp only [memberProjection, ReadsRecord] at hRR
  obtain ⟨cb', ms', ind', ⟨hcb', hms', hget', -, -, -⟩, ty₀, caps, -, hci⟩ := hRR
  have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans hB.record)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
  subst e2
  rw [hpos_u] at hget'
  have e3 : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hget'.symm.trans hms))
  subst e3
  exact ⟨ty₀, caps, hci⟩

private theorem reads_ctor_shape {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms) {pos : Nat} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hpos : pos < UInt64.size) (hms : ms[pos]? = some (.indc ind))
    (hct : ind.ctors[0]? = some ct) (hct_sz : 0 < ind.ctors.size)
    {ci : ConstantInfo .anon} (hR : Reads t E₀ (Core.cprjAddr B pos 0) ci) :
    ∃ ty₀, ci = .ctorInfo ⟨Core.keyOf t (Core.cprjAddr B pos 0), List.range ct.lvls.toNat, ty₀⟩
      ct.params.toNat ct.fields.toNat := by
  have hrec := hB.ctors pos ind 0 hms hct_sz
  have hpos_u : pos.toUInt64.toNat = pos := by
    change (UInt64.ofNat pos).toNat = pos
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hpos
  obtain ⟨c, hrec', hRR⟩ := hR
  have hc_eq : c = constructorProjection B pos 0 := Option.some.inj (hrec'.symm.trans hrec)
  subst hc_eq
  dsimp only [constructorProjection, ReadsRecord] at hRR
  obtain ⟨cb', ms', ind', ct', hcb', hms', hget', hct', -, -, -, -, ty₀, -, hci⟩ := hRR
  have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans hB.record)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
  subst e2
  rw [hpos_u] at hget'
  have e3 : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hget'.symm.trans hms))
  subst e3
  have e4 : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst e4
  exact ⟨ty₀, hci⟩

/-- Distinct positions `< ms.size` (`< UInt64.size`) in a `FamBlockRecord` have distinct
`Core.keyOf t (Core.iprjAddr B pos)` keys. -/
theorem iprjKey_inj_of_block {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (htwf : t.wf = true) (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {p₁ p₂ : Nat} (hp₁ : p₁ < ms.size) (hp₂ : p₂ < ms.size)
    (heq : Core.keyOf t (Core.iprjAddr B p₁) = Core.keyOf t (Core.iprjAddr B p₂)) :
    p₁ = p₂ := by
  have haddr : Core.iprjAddr B p₁ = Core.iprjAddr B p₂ := Core.keyOf_inj htwf heq
  obtain ⟨ind₁, hm₁⟩ := hB.indcs (ms[p₁]'hp₁) (Array.mem_toList_iff.mpr (Array.getElem_mem hp₁))
  obtain ⟨ind₂, hm₂⟩ := hB.indcs (ms[p₂]'hp₂) (Array.mem_toList_iff.mpr (Array.getElem_mem hp₂))
  have hr₁ : recordOf E₀ (Core.iprjAddr B p₁) = some (memberProjection B p₁ (.indc ind₁)) :=
    hB.members p₁ (.indc ind₁) (by rw [Array.getElem?_eq_getElem hp₁, hm₁])
  have hr₂ : recordOf E₀ (Core.iprjAddr B p₂) = some (memberProjection B p₂ (.indc ind₂)) :=
    hB.members p₂ (.indc ind₂) (by rw [Array.getElem?_eq_getElem hp₂, hm₂])
  rw [haddr] at hr₁
  have hmp : memberProjection B p₁ (.indc ind₁) = memberProjection B p₂ (.indc ind₂) :=
    Option.some.inj (hr₁.symm.trans hr₂)
  have hinfo : (memberProjection B p₁ (.indc ind₁)).info =
      (memberProjection B p₂ (.indc ind₂)).info := congrArg Ixon.Constant.info hmp
  simp only [memberProjection] at hinfo
  have hip : p₁.toUInt64 = p₂.toUInt64 :=
    (Ixon.InductiveProj.mk.inj (Ixon.ConstantInfo.iPrj.inj hinfo)).1
  have hu1 : p₁.toUInt64.toNat = p₁ := by
    change (UInt64.ofNat p₁).toNat = p₁
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans hp₁ hms_u64)
  have hu2 : p₂.toUInt64.toNat = p₂ := by
    change (UInt64.ofNat p₂).toNat = p₂
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans hp₂ hms_u64)
  rw [← hu1, ← hu2, hip]

/-- Complete specification of one eligible member's extracted `ProjTable` at `env₂`. -/
structure EligibleTableSpec (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (env env₂ : Env .anon)
    (B : _root_.Address) (ms : Array Ixon.MutConst) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (g : KKey → KKey) (pos : Nat) (tbl : ProjTable .anon) where
  ind : Ixon.Inductive
  ct : Ixon.Constructor
  kT : Nat
  kC : Nat
  ciT : ConstantInfo .anon
  ciC : ConstantInfo .anon
  tyA_T : KExpr
  tyA_C : KExpr
  cvT : ConstantVal .anon
  cvC : ConstantVal .anon
  hT_nr : (nonrecsOf blk)[kT]? = some ciT
  hT_name : ciT.name = Core.keyOf t (Core.iprjAddr B pos)
  hT_ty : tys[kT]? = some tyA_T
  hC_nr : (nonrecsOf blk)[kC]? = some ciC
  hC_name : ciC.name = Core.keyOf t (Core.cprjAddr B pos 0)
  hC_ty : tys[kC]? = some tyA_C
  mpf : MemberProjFacts t E env B ms g pos tyA_T tyA_C
  hmpf_ind : mpf.ind = ind
  hmpf_ct : mpf.ct = ct
  hfindT₂ : env₂.find? tbl.structName = some (.indInfo cvT {})
  hfindC₂ : env₂.find? tbl.ctor = some (.ctorInfo cvC tbl.numParams tbl.numFields)
  htbl_sn : tbl.structName = Core.keyOf t (Core.iprjAddr B pos)
  htbl_ctor : tbl.ctor = Core.keyOf t (Core.cprjAddr B pos 0)
  htbl_nP : tbl.numParams = ind.params.toNat
  htbl_nF : tbl.numFields = ct.fields.toNat
  htbl_lps : tbl.levelParams = List.range ind.lvls.toNat
  htbl_sort : tbl.structSort = mpf.structSort
  htbl_off : tbl.off = 2
  htbl_guards : tbl.guards = Ix.Kernel.structProjGuards cvC.type tbl.numParams tbl.numFields
    (List.replicate tbl.numFields .zero)
  hcvT_eq : cvT = ⟨tbl.structName, tbl.levelParams, tyA_T⟩
  hcvC_eq : cvC = ⟨tbl.ctor, tbl.levelParams, tyA_C⟩
  hbodies : Ix.Kernel.structProjBodies tbl.structName tbl.numParams tbl.numFields cvC.type =
    some tbl.bodies
  hbodies_sz : tbl.bodies.size = tbl.numFields
  hbodies_wf : ∀ (j : Nat) (b : KExpr), tbl.bodies[j]? = some b →
    b.hasFvar = false ∧ b.allLevelParamsDefined tbl.levelParams = true ∧
      b.constsResolve env₂ = true ∧ b.looseBVarsBounded (tbl.numParams + 1) = true
  hT_pw : ∀ bm ∈ mpf.bsT, bm.2.pw = .never
  hC_pw : ∀ bm ∈ mpf.bsC, bm.2.pw = .never
  hC_tele : Ix.Kernel.Expr.ctorTeleOk cvC.type (tbl.numParams + tbl.numFields) = true
  hT_ren_eq : tyA_T.renameConsts g = tyA_T
  hmfT : Decl.FamilyAlias.MemberFacts env g ciT tyA_T
  hmfC : Decl.FamilyAlias.MemberFacts env g ciC tyA_C
  hciT_lps : ciT.toConstantVal.levelParams = List.range ind.lvls.toNat
  hciC_lps : ciC.toConstantVal.levelParams = List.range ind.lvls.toNat

/-- Every member of `blk` is fresh in `env` across `AliasGroup` + `DeclIndRenRunJ`. -/
private theorem blk_fresh_in_env {env env₂ : Env .anon} {h : KKey → KKey}
    {as blk : List (ConstantInfo .anon)} (hg : AliasGroup env h as)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂) :
    ∀ ci ∈ blk, env.find? ci.name = none := by
  obtain ⟨hsplit, envM, hmemR, hrecsR⟩ := hd.shape
  have hextA : EnvExt env ⟨as ++ env.consts⟩ := Decl.FamilyAlias.AliasGroup.envExt hg
  have hextM : EnvExt ⟨as ++ env.consts⟩ envM := Ix.Kernel.Semantics.indMembersRunJ_envExt hmemR
  intro ci hci
  rw [hsplit] at hci
  rcases List.mem_append.mp hci with hm | hr
  · have hfr := Ix.Kernel.Semantics.indMembersRun_fresh _ hmemR ci hm
    cases hf : env.find? ci.name with
    | none => rfl
    | some x =>
      have h1 := hextA.find hf
      rw [hfr] at h1; exact nomatch h1
  · rcases hrecsR with ⟨hnil, -⟩ | ⟨-, -, _, _, hprov, -⟩
    · rw [hnil] at hr; exact nomatch hr
    · have hfr := Ix.Kernel.Semantics.provisionRecsRunS_fresh _ hprov ci hr
      cases hf : env.find? ci.name with
      | none => rfl
      | some x =>
        have h1 := (hextA.trans hextM).find hf
        rw [hfr] at h1; exact nomatch h1

/-- At every eligible position `pos < ms.size`, `posProjTable?` succeeds and satisfies
`EligibleTableSpec`. -/
theorem posProjTable?_spec {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env env₂ : Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {blk as : List (ConstantInfo .anon)}
    {h : KKey → KKey} {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (htwf : t.wf = true) (hB : FamBlockRecord E₀ B cb ms)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hg : AliasGroup env h as)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    (hI : SelectedInstalled blk tys rhsss env₂)
    (hS₀ : Decl.FoldStoreInv env)
    (bpf : BlockProjFacts t E₀ E env B cb ms blk tys adv.ren)
    {pos : Nat} (hpos : pos < ms.size) (helig : bpf.elig pos = true) :
    ∃ tbl, posProjTable? t env₂ B bpf.elig pos = some tbl ∧
      Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren pos tbl) := by
  obtain ⟨ind, ct, kT, kC, ciT, ciC, tyA_T, tyA_C, hms, hct, hT_nr, hT_name, hT_ty,
    hC_nr, hC_name, hC_ty, ⟨mpf⟩⟩ := bpf.atPos pos hpos helig
  have hind_eq : mpf.ind = ind := Ixon.MutConst.indc.inj (Option.some.inj (mpf.hms.symm.trans hms))
  have hct_eq : mpf.ct = ct := by
    have h1 := mpf.hct
    rw [hind_eq] at h1
    exact Option.some.inj (h1.symm.trans hct)
  have hpos_u64 : pos < UInt64.size := Nat.lt_trans hpos bpf.hms_size
  have hciT_mem : ciT ∈ blk := (List.mem_filter.mp (List.mem_of_getElem? hT_nr)).1
  have hciC_mem : ciC ∈ blk := (List.mem_filter.mp (List.mem_of_getElem? hC_nr)).1
  obtain ⟨xT, -, hxT_key, hRT⟩ := hreads.2.1 ciT hciT_mem
  have hxT_eq : xT = Core.iprjAddr B pos := Core.keyOf_inj htwf (hxT_key.symm.trans hT_name)
  rw [hxT_eq] at hRT
  obtain ⟨ty₀T, capsT, hciT_eq⟩ := reads_ind_shape hB hpos_u64 hms hRT
  obtain ⟨xC, -, hxC_key, hRC⟩ := hreads.2.1 ciC hciC_mem
  have hxC_eq : xC = Core.cprjAddr B pos 0 := Core.keyOf_inj htwf (hxC_key.symm.trans hC_name)
  rw [hxC_eq] at hRC
  have hct_sz : 0 < ind.ctors.size := by rw [← hind_eq, mpf.hnc1]; omega
  obtain ⟨ty₀C, hciC_eq⟩ := reads_ctor_shape hB hpos_u64 hms hct hct_sz hRC
  have hfindT₂ : env₂.find? (Core.keyOf t (Core.iprjAddr B pos)) =
      some (.indInfo ⟨Core.keyOf t (Core.iprjAddr B pos), List.range ind.lvls.toNat, tyA_T⟩ {}) := by
    have h1 := hI.nonrecs kT ciT tyA_T hT_nr hT_ty
    rw [hT_name, hciT_eq] at h1
    exact h1
  have hcnl : ct.lvls.toNat = ind.lvls.toNat := by rw [← hind_eq, ← hct_eq]; exact mpf.hcnl
  have hcnp : ct.params.toNat = ind.params.toNat := by rw [← hind_eq, ← hct_eq]; exact mpf.hcnp
  have hfindC₂ : env₂.find? (Core.keyOf t (Core.cprjAddr B pos 0)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B pos 0), List.range ind.lvls.toNat, tyA_C⟩
        ind.params.toNat ct.fields.toNat) := by
    have h1 := hI.nonrecs kC ciC tyA_C hC_nr hC_ty
    rw [hC_name, hciC_eq, hcnl, hcnp] at h1
    exact h1
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)
  have hS₂ := Decl.FamilyAlias.foldStoreInv_famStep hg hreads.2.2.2 hna hd hS₀
  have hwfC₂ := hS₂.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfindC₂)
  have hposC_eq : Core.posOf (List.range mpf.ct.lvls.toNat) tyA_C = tyA_C := by
    rw [hct_eq, hcnl]
    exact posOf_range_eq_prep ind.lvls.toNat tyA_C
  have hstripC : tyA_C.stripPis (ind.params.toNat + ct.fields.toNat) = some (mpf.bsC, mpf.cret) := by
    have h1 := mpf.hC_ret
    rw [hposC_eq, hind_eq, hct_eq] at h1
    exact h1
  have hstripT : tyA_T.stripPis ind.params.toNat = some (mpf.bsT, .sort mpf.structSort) := by
    have h1 := mpf.hT_sort; rw [hind_eq] at h1; exact h1
  obtain ⟨bodies, hbodies, hbodies_sz, hbodies_wf⟩ :=
    structProjBodies_exists_wf (T := Core.keyOf t (Core.iprjAddr B pos))
      (nP := ind.params.toNat) (nF := ct.fields.toNat) (cty := tyA_C)
      (by rw [hfindT₂]; rfl) (by rw [hstripC]; rfl)
      hwfC₂.1 hwfC₂.2.1 hwfC₂.2.2.1 hwfC₂.2.2.2.1
  have hblk_split := hF.split
  have hnr_lt_T : kT < (nonrecsOf blk).length := (List.getElem?_eq_some_iff.mp hT_nr).1
  have hnr_lt_C : kC < (nonrecsOf blk).length := (List.getElem?_eq_some_iff.mp hC_nr).1
  have hblk_kT : blk[kT]? = some ciT := by
    rw [hblk_split, List.getElem?_append_left hnr_lt_T]; exact hT_nr
  have hblk_kC : blk[kC]? = some ciC := by
    rw [hblk_split, List.getElem?_append_left hnr_lt_C]; exact hC_nr
  have hmfT := Decl.FamilyAlias.MembersFacts.get hF.members hblk_kT hT_ty
  have hmfC := Decl.FamilyAlias.MembersFacts.get hF.members hblk_kC hC_ty
  have hT_ren_eq : tyA_T.renameConsts adv.ren = tyA_T := by
    obtain ⟨_, _, _, _, _, _, _, _, _, fp₀, _⟩ := mpf.hfields 0 mpf.hnf_pos
    refine tyA_T_renameConsts_eq hS₀.store.wf (fun k hk => ?_) mpf.hT_sort fp₀
    refine Decl.FamilyAlias.aliasMap_of_not_key adv.models k ?_
    rw [hF.table]
    intro hmem
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hmem
    rw [blk_fresh_in_env hg hd ci hci] at hk
    exact Bool.false_ne_true hk
  have hT_eq' : ciT.toConstantVal.levelParams = List.range ind.lvls.toNat := by
    rw [hciT_eq]; rfl
  have hC_eq' : ciC.toConstantVal.levelParams = List.range ind.lvls.toNat := by
    rw [hciC_eq, hcnl]; rfl
  have hT_pw : ∀ bm ∈ mpf.bsT, bm.2.pw = .never :=
    type_binders_pw_never hmfT hT_ren_eq hstripT
  have hC_pw : ∀ bm ∈ mpf.bsC, bm.2.pw = .never := by
    have hC_ret_eq' : mpf.cret = Expr.mkAppN
        (.const ciT.name ((List.range ind.lvls.toNat).map .param))
        ((List.range ind.params.toNat).map fun m =>
          .bvar (ind.params.toNat + ct.fields.toNat - 1 - m)) := by
      rw [hT_name, ← hind_eq, ← hct_eq]; exact mpf.hC_ret_eq
    have h1 := ctor_binders_pw_never hS₀.store.wf hmfT hmfC hT_eq' hT_ren_eq hstripT
      mpf.hT_sort_nz (by simp) (hC_ret_eq' ▸ hstripC)
    have hzer : Ix.Kernel.Level.zeronessOf mpf.structSort = .never :=
      zeronessOf_eq_never_of_pos (eval_pos_of_isNeverZero mpf.hT_sort_nz)
    intro bm hbm
    exact (h1 bm hbm).trans hzer
  have hC_tele : Ix.Kernel.Expr.ctorTeleOk tyA_C (ind.params.toNat + ct.fields.toNat) = true := by
    have hstripC' := hstripC
    rw [mpf.hC_ret_eq] at hstripC'
    exact ctorTeleOk_of_stripPis_ret hstripC'
  let tbl : ProjTable .anon :=
    { structName := Core.keyOf t (Core.iprjAddr B pos)
      ctor := Core.keyOf t (Core.cprjAddr B pos 0)
      numParams := ind.params.toNat
      numFields := ct.fields.toNat
      levelParams := List.range ind.lvls.toNat
      structSort := mpf.structSort
      bodies := bodies
      guards := Ix.Kernel.structProjGuards tyA_C ind.params.toNat ct.fields.toNat
        (List.replicate ct.fields.toNat .zero)
      off := 2 }
  refine ⟨tbl, ?_, ⟨?_⟩⟩
  · unfold posProjTable?
    simp only [helig, ↓reduceIte, hfindT₂, hfindC₂, hstripT, hbodies]
    rfl
  · exact
      { ind := ind
        ct := ct
        kT := kT
        kC := kC
        ciT := ciT
        ciC := ciC
        tyA_T := tyA_T
        tyA_C := tyA_C
        cvT := ⟨Core.keyOf t (Core.iprjAddr B pos), List.range ind.lvls.toNat, tyA_T⟩
        cvC := ⟨Core.keyOf t (Core.cprjAddr B pos 0), List.range ind.lvls.toNat, tyA_C⟩
        hT_nr := hT_nr
        hT_name := hT_name
        hT_ty := hT_ty
        hC_nr := hC_nr
        hC_name := hC_name
        hC_ty := hC_ty
        mpf := mpf
        hmpf_ind := hind_eq
        hmpf_ct := hct_eq
        hfindT₂ := hfindT₂
        hfindC₂ := hfindC₂
        htbl_sn := rfl
        htbl_ctor := rfl
        htbl_nP := rfl
        htbl_nF := rfl
        htbl_lps := rfl
        htbl_sort := rfl
        htbl_off := rfl
        htbl_guards := rfl
        hcvT_eq := rfl
        hcvC_eq := rfl
        hbodies := hbodies
        hbodies_sz := hbodies_sz
        hbodies_wf := hbodies_wf
        hT_pw := hT_pw
        hC_pw := hC_pw
        hC_tele := hC_tele
        hT_ren_eq := hT_ren_eq
        hmfT := hmfT
        hmfC := hmfC
        hciT_lps := hT_eq'
        hciC_lps := hC_eq' }

/-! ## Section 3: Pure structural facts for `projConstsOfTables` -/

private theorem projConstsOfTables_mem_iff :
    ∀ {xs : List (Nat × ProjTable .anon)} {c : ConstantInfo .anon},
      c ∈ projConstsOfTables xs ↔ ∃ p ∈ xs, c ∈ memberProjConsts p.2
  | [], _ => by simp [projConstsOfTables]
  | (pos, tbl) :: rest, c => by
    simp only [projConstsOfTables, List.mem_append, projConstsOfTables_mem_iff, List.mem_cons]
    constructor
    · rintro (hc | ⟨p, hp, hc⟩)
      · exact ⟨(pos, tbl), Or.inl rfl, hc⟩
      · exact ⟨p, Or.inr hp, hc⟩
    · rintro ⟨p, rfl | hp, hc⟩
      · exact Or.inl hc
      · exact Or.inr ⟨p, hp, hc⟩

private theorem projConstsOfTables_nodup :
    ∀ {xs : List (Nat × ProjTable .anon)},
      (xs.map (·.2.structName)).Nodup →
      ((projConstsOfTables xs).map (·.name)).Nodup
  | [], _ => List.nodup_nil
  | (pos, tbl) :: rest, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [projConstsOfTables, List.map_append]
    refine List.nodup_append.mpr ⟨memberProjConsts_nodup tbl, projConstsOfTables_nodup hnd.2, ?_⟩
    intro k1 hk1 k2 hk2 heq
    obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hk1
    obtain ⟨c2, hc2, rfl⟩ := List.mem_map.mp hk2
    obtain ⟨p, hp, hc2'⟩ := projConstsOfTables_mem_iff.mp hc2
    have hne : tbl.structName ≠ p.2.structName := fun heq =>
      hnd.1 (List.mem_map.mpr ⟨p, hp, heq.symm⟩)
    exact memberProjConsts_disjoint hne c1 hc1 c2 hc2' heq

/-- `EnvExt env ⟨c :: envCur.consts⟩` when `c.name` is fresh in `envCur` and never equals
`projTableName T` for any `T` stored in `env`. -/
theorem envExt_cons_of_fresh_and_not_old_table {env envCur : Env .anon}
    (hext : EnvExt env envCur) {c : ConstantInfo .anon}
    (hfresh : envCur.find? c.name = none)
    (hnotOldTbl : ∀ T, (env.find? T).isSome = true → c.name ≠ Ix.Kernel.projTableName T) :
    EnvExt env ⟨c :: envCur.consts⟩ where
  find {k ci} hf := by
    have h1 := hext.find hf
    rw [Ix.Kernel.Env.find?_cons]
    split
    · rename_i heq
      rw [heq, h1] at hfresh
      exact nomatch hfresh
    · exact h1
  tables {T cvT caps} hf := by
    have h1 := hext.tables hf
    rw [Ix.Kernel.Env.find?_cons]
    split
    · rename_i heq
      exact absurd heq (hnotOldTbl T (by rw [hf]; rfl))
    · exact h1

/-- `ConstWF` for `.projInfo tbl` from `structProjBodies_exists_wf` + `constsResolve` monotonicity. -/
theorem constWF_projInfo {env : Env .anon} {tbl : ProjTable .anon}
    (hsz : tbl.bodies.size = tbl.numFields)
    (hwf : ∀ (j : Nat) (b : KExpr), tbl.bodies[j]? = some b →
      b.hasFvar = false ∧ b.allLevelParamsDefined tbl.levelParams = true ∧
        b.constsResolve env = true ∧ b.looseBVarsBounded (tbl.numParams + 1) = true) :
    Ix.Kernel.ConstWF ⟨.projInfo tbl :: env.consts⟩ (.projInfo tbl) := by
  refine ⟨rfl, rfl, rfl, rfl,
    (fun _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h), ?_, (fun _ _ h => nomatch h)⟩
  intro tbl' heq
  obtain rfl := ConstantInfo.projInfo.inj heq
  refine ⟨hsz, fun j b hjb => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hwf j b hjb
  exact ⟨h1, h2, Ix.Kernel.Expr.constsResolve_of_find (fun n hn => by
    rw [Ix.Kernel.Env.find?_cons]
    split
    · rfl
    · exact hn) h3, h4⟩

/-- Freshness of `projTableName T` and `projChainKey T j` in `env₂` for any fresh base key `T`. -/
private theorem projKeys_fresh_in_env₂ {env env₂ : Env .anon} {h : KKey → KKey}
    {as blk : List (ConstantInfo .anon)}
    (haux₀ : Decl.AuxRootSynced env)
    (hnames : ∀ a ∈ as, ∃ ci ∈ blk,
      a.name = Ix.Kernel.auxKey ci.name .model ∨ ∃ j, a.name = Decl.FamilyAlias.iotaKey ci.name j)
    (hblkBase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    {T : KKey} (hTbase : Decl.isBaseKey T = true) (hTfresh : env.find? T = none) :
    env₂.find? (Ix.Kernel.projTableName T) = none ∧
    ∀ j, env₂.find? (Ix.Kernel.projChainKey T j) = none := by
  obtain ⟨new', henv₂, hnewN, -⟩ := famStep_consts hd
  have hnot_new : ∀ k, (∀ ci ∈ blk, k ≠ ci.name) → ∀ c ∈ new', c.name ≠ k := fun k hne c hc heq => by
    obtain ⟨ci, hci, hcn⟩ := hnewN c hc
    exact hne ci hci (heq.symm.trans hcn)
  have htbl₀ : env.find? (Ix.Kernel.projTableName T) = none :=
    haux₀.fresh_of_base_none (by rw [projTableName_base hTbase]; exact hTfresh)
  have hch₀ : ∀ j, env.find? (Ix.Kernel.projChainKey T j) = none := fun j =>
    haux₀.fresh_of_base_none (by rw [projChainKey_base hTbase j]; exact hTfresh)
  have henv_eq : env₂ = ⟨(new' ++ as) ++ env.consts⟩ := by
    rw [henv₂]
  rw [henv_eq]
  refine ⟨find?_append_none (new' ++ as) (fun c hc heq => ?_) htbl₀,
    fun j => find?_append_none (new' ++ as) (fun c hc heq => ?_) (hch₀ j)⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact hnot_new _ (fun ci hci hEq => auxKey_ne_of_isBaseKey (hblkBase ci hci) hEq) c hc heq
    · obtain ⟨ci, -, hEq | ⟨j', hEq⟩⟩ := hnames c hc
      · exact projTableName_ne_model T ci.name (heq.symm.trans hEq)
      · exact projTableName_ne_iota T ci.name j' (heq.symm.trans hEq)
  · rcases List.mem_append.mp hc with hc | hc
    · exact hnot_new _ (fun ci hci hEq => auxKey_ne_of_isBaseKey (hblkBase ci hci) hEq) c hc heq
    · obtain ⟨ci, -, hEq | ⟨j', hEq⟩⟩ := hnames c hc
      · exact projChainKey_ne_model T ci.name j (heq.symm.trans hEq)
      · exact projChainKey_ne_iota T ci.name j j' (heq.symm.trans hEq)

/-! ## Section 4: Folding chain axioms + table cons for one eligible member -/

/-- Fold `chainAxiom_step` over a nodup list `js` of field indices `< nF` fresh in `envCur`. -/
private theorem fold_chainAxioms_model {V : Type u} [SetTheory V]
    {T : KKey} {nF : Nat}
    (A_chain : Nat → (LevelParam → Nat) → AnnotTerm)
    (hAclosed : ∀ j < nF, ∀ ψ k, (A_chain j ψ).liftN 1 k = A_chain j ψ)
    (hAparams : ∀ j < nF, ∀ ψ₁ ψ₂, ψ₁ 0 = ψ₂ 0 → A_chain j ψ₁ = A_chain j ψ₂)
    (hAok : ∀ j < nF, ∀ ψ ρ, WellDenotedV V ρ (A_chain j ψ))
    (hAmem : ∀ j < nF, ∀ ψ ρ, interp V ρ (A_chain j ψ) ∈ˢ (univ (ψ 0 + 1) : V)) :
    ∀ (js : List Nat) {envCur : Env .anon},
      js.Nodup → (∀ j ∈ js, j < nF) →
      (∀ j ∈ js, envCur.find? (Ix.Kernel.projChainKey T j) = none) →
      ∀ (mpCur : EnvModelM V .verified envCur),
        Ix.Kernel.EtaFamiliesClosed envCur →
        Ix.Kernel.EtaFamiliesClosed ⟨js.map (chainAxiom T) ++ envCur.consts⟩ ∧
        ∃ mpCh : EnvModelM V .verified ⟨js.map (chainAxiom T) ++ envCur.consts⟩,
          ModelExt mpCur mpCh ∧
          (∀ j ∈ js, ∀ ψ, mpCh.base2.acval (Ix.Kernel.projChainKey T j) ψ = A_chain j ψ) ∧
          (∀ k, (envCur.find? k).isSome = true → ∀ ψ, mpCh.base2.acval k ψ = mpCur.base2.acval k ψ)
  | [], envCur, _, _, _, mpCur, hE =>
    ⟨hE, mpCur, ModelExt.refl, (fun _ hm => nomatch hm), fun _ _ _ => rfl⟩
  | j :: js, envCur, hnd, hlt, hfr, mpCur, hE => by
    rw [List.nodup_cons] at hnd
    have hj_lt : j < nF := hlt j List.mem_cons_self
    obtain ⟨hE1, mp1, hext1, hac_js, hac_old⟩ :=
      fold_chainAxioms_model A_chain hAclosed hAparams hAok hAmem js hnd.2
        (fun j' hj' => hlt j' (List.mem_cons_of_mem _ hj'))
        (fun j' hj' => hfr j' (List.mem_cons_of_mem _ hj')) mpCur hE
    have hfr_j1 : (⟨js.map (chainAxiom T) ++ envCur.consts⟩ : Env .anon).find?
        (Ix.Kernel.projChainKey T j) = none := by
      refine find?_append_none (js.map (chainAxiom T)) (fun c hc heq => ?_) (hfr j List.mem_cons_self)
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hc
      have hjj' : j' = j := (projChainKey_inj heq).2
      subst hjj'
      exact hnd.1 hj'
    obtain ⟨hE2, mp2, hac2, hext2⟩ :=
      chainAxiom_step mp1 hE1 hfr_j1 (A_chain j) (hAclosed j hj_lt) (hAparams j hj_lt)
        (hAok j hj_lt) (hAmem j hj_lt)
    refine ⟨hE2, mp2, hext1.trans hext2, ?_, ?_⟩
    · intro j' hj' ψ
      rcases List.mem_cons.mp hj' with rfl | hj'
      · rw [hac2, acvalWith_self]
      · have hne : Ix.Kernel.projChainKey T j' ≠ Ix.Kernel.projChainKey T j := fun h =>
          hnd.1 ((projChainKey_inj h).2 ▸ hj')
        rw [hac2, acvalWith_ne hne, hac_js j' hj' ψ]
    · intro k hk ψ
      exact modelExt_acval_eq_of_isSome (hext1.trans hext2) hk ψ

/-- Pure bookkeeping (`EnvExt`, `StoreInv`, `StoreArR`, `NoProjEnv`, `find?`, `findProj?`) across
folding chain axioms for `T`. -/
private theorem fold_chainAxioms_pure {T : KKey} :
    ∀ (js : List Nat) {env envCur : Env .anon},
      js.Nodup →
      (∀ j ∈ js, envCur.find? (Ix.Kernel.projChainKey T j) = none) →
      EnvExt env envCur →
      Ix.Kernel.Open.StoreInv envCur →
      Ix.Kernel.Model.StoreArR envCur →
      EnvExt env ⟨js.map (chainAxiom T) ++ envCur.consts⟩ ∧
      Ix.Kernel.Open.StoreInv ⟨js.map (chainAxiom T) ++ envCur.consts⟩ ∧
      Ix.Kernel.Model.StoreArR ⟨js.map (chainAxiom T) ++ envCur.consts⟩ ∧
      (∀ T' i, NoProjEnv envCur T' i → NoProjEnv ⟨js.map (chainAxiom T) ++ envCur.consts⟩ T' i) ∧
      (∀ k ci, envCur.find? k = some ci →
        (⟨js.map (chainAxiom T) ++ envCur.consts⟩ : Env .anon).find? k = some ci) ∧
      (∀ s i, (⟨js.map (chainAxiom T) ++ envCur.consts⟩ : Env .anon).findProj? s i =
        envCur.findProj? s i) ∧
      (∀ j ∈ js, (⟨js.map (chainAxiom T) ++ envCur.consts⟩ : Env .anon).find?
        (Ix.Kernel.projChainKey T j) = some (chainAxiom T j))
  | [], _, _, _, _, hext, hS, hAr =>
    ⟨hext, hS, hAr, fun _ _ h => h, fun _ _ h => h, fun _ _ => rfl, fun _ hm => nomatch hm⟩
  | j :: js, env, envCur, hnd, hfr, hext, hS, hAr => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hext1, hS1, hAr1, hnp1, hfind1, hfp1, hfound1⟩ :=
      fold_chainAxioms_pure js hnd.2 (fun j' hj' => hfr j' (List.mem_cons_of_mem _ hj'))
        hext hS hAr
    have hfr_j1 : (⟨js.map (chainAxiom T) ++ envCur.consts⟩ : Env .anon).find?
        (Ix.Kernel.projChainKey T j) = none := by
      refine find?_append_none (js.map (chainAxiom T)) (fun c hc heq => ?_) (hfr j List.mem_cons_self)
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hc
      exact hnd.1 ((projChainKey_inj heq).2 ▸ hj')
    refine ⟨envExt_cons_of_fresh_and_not_old_table hext1 hfr_j1
        (fun T' _ => projChainKey_ne_projTableName T T' j),
      storeInv_cons_chainAxiom hS1 hfr_j1,
      storeArR_cons_chainAxiom hAr1 hfr_j1,
      fun T' i hnp => (hnp1 T' i hnp).cons (NoProjHead.ofType
        (by simp [chainAxiom, ConstantInfo.toConstantVal])
        (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h)),
      fun k ci hk => by
        have h1 := hfind1 k ci hk
        rw [List.map_cons, List.cons_append, Ix.Kernel.Env.find?_cons]
        split
        · rename_i heq; simp only [chainAxiom_name] at heq; rw [heq, h1] at hfr_j1; exact nomatch hfr_j1
        · exact h1,
      fun s i => by
        show (⟨chainAxiom T j :: (js.map (chainAxiom T) ++ envCur.consts)⟩ : Env .anon).findProj? s i = _
        unfold Ix.Kernel.Env.findProj?
        rw [Ix.Kernel.Env.find?_cons, chainAxiom_name,
          ite_eq_right (fun h => absurd h (projChainKey_ne_projTableName T s j))]
        exact hfp1 s i,
      fun j' hj' => by
        rw [List.map_cons, List.cons_append, Ix.Kernel.Env.find?_cons, chainAxiom_name]
        rcases List.mem_cons.mp hj' with rfl | hj'
        · simp
        · have hne : Ix.Kernel.projChainKey T j ≠ Ix.Kernel.projChainKey T j' := fun h =>
            hnd.1 ((projChainKey_inj h).2 ▸ hj')
          rw [ite_eq_right (fun h => absurd h hne)]
          exact hfound1 j' hj'⟩

/-! ## Section 5: Pure & model folds across all eligible members of a block -/

/-- Pure (`V`-independent) bookkeeping across installing all projection tables in `entries` onto
`env₂`. -/
private theorem fold_tables_pure {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env env₂ : Env .anon} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {blk as : List (ConstantInfo .anon)}
    {h : KKey → KKey} {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (htwf : t.wf = true)
    (hB : FamBlockRecord E₀ B cb ms)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hg : AliasGroup env h as)
    (hnames : ∀ a ∈ as, ∃ ci ∈ blk,
      a.name = Ix.Kernel.auxKey ci.name .model ∨ ∃ j, a.name = Decl.FamilyAlias.iotaKey ci.name j)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    (hI : SelectedInstalled blk tys rhsss env₂)
    (hS₀ : Decl.FoldStoreInv env)
    (hS₂ : Decl.FoldStoreInv env₂)
    (hAr₂ : Ix.Kernel.Model.StoreArR env₂)
    (haux₀ : Decl.AuxRootSynced env)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (Core.keyOf t x) = none)
    (hkey : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (Core.keyOf t x))
    (bpf : BlockProjFacts t E₀ E env B cb ms blk tys adv.ren)
    (hext02 : EnvExt env env₂)
    (hblkBase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true) :
    ∀ (entries : List (Nat × ProjTable .anon)),
      (entries.map (·.2.structName)).Nodup →
      (∀ p ∈ entries, p.1 < ms.size ∧ bpf.elig p.1 = true ∧
        Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren p.1 p.2)) →
      let pcs := projConstsOfTables entries
      let env₃ : Env .anon := ⟨pcs ++ env₂.consts⟩
      EnvExt env env₃ ∧
      Ix.Kernel.Open.StoreInv env₃ ∧
      Ix.Kernel.Model.StoreArR env₃ ∧
      (∀ k ci, env₂.find? k = some ci → env₃.find? k = some ci) ∧
      (∀ T', Decl.isBaseKey T' = true → env.find? T' = none →
        (∀ p ∈ entries, p.2.structName ≠ T') →
        ∀ i, NoProjEnv env₃ T' i) ∧
      (∀ p ∈ entries,
        env₃.find? (Ix.Kernel.projTableName p.2.structName) = some (.projInfo p.2) ∧
        (∀ f < p.2.numFields,
          env₃.findProj? p.2.structName f = some (p.2.entry f) ∧
          Ix.Kernel.TowerHead env₃ (p.2.entry f))) ∧
      (∀ s i, (∀ p ∈ entries, p.2.structName ≠ s) → env₃.findProj? s i = env₂.findProj? s i) ∧
      (∀ c ∈ pcs, env₂.find? c.name = none)
  | [], _, _ =>
    ⟨hext02, hS₂.store, hAr₂, (fun _ _ h => h),
      fun T' hBase hT' _ i =>
        noProjEnv_famStep hS₀.store.wf hBase hT'
          (haux₀.fresh_of_base_none (by rw [projTableName_base hBase]; exact hT'))
          hblkBase hg hd i,
      (fun _ hm => nomatch hm), (fun _ _ _ => rfl), (fun _ hm => nomatch hm)⟩
  | (pos, tbl) :: rest, hnd, hall => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hrest_all : ∀ p ∈ rest, p.1 < ms.size ∧ bpf.elig p.1 = true ∧
        Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren p.1 p.2) :=
      fun p hp => hall p (List.mem_cons_of_mem _ hp)
    obtain ⟨hextR, hSR, hArR, hfindR, hnpR, htblsR, hfpR, hfr₂R⟩ :=
      fold_tables_pure htwf hB hreads hF hg hnames hd hI hS₀ hS₂ hAr₂ haux₀ hfresh hkey bpf
        hext02 hblkBase rest hnd.2 hrest_all
    obtain ⟨hpos, helig, ⟨sp⟩⟩ := hall (pos, tbl) List.mem_cons_self
    dsimp only at hpos helig sp
    let T := tbl.structName
    let C := tbl.ctor
    let envR : Env .anon := ⟨projConstsOfTables rest ++ env₂.consts⟩
    have hT_fam : FamAddr B cb rb crb (Core.iprjAddr B pos) :=
      Or.inl (Or.inr ⟨ms, pos, .indc sp.ind, hB.muts, sp.hmpf_ind ▸ sp.mpf.hms, Or.inl rfl⟩)
    have hC_fam : FamAddr B cb rb crb (Core.cprjAddr B pos 0) :=
      Or.inl (Or.inr ⟨ms, pos, .indc sp.ind, hB.muts, sp.hmpf_ind ▸ sp.mpf.hms,
        Or.inr ⟨sp.ind, 0, rfl, by rw [← sp.hmpf_ind, sp.mpf.hnc1]; omega, rfl⟩⟩)
    have hT_base : Decl.isBaseKey T = true := by
      rw [show T = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
      exact Decl.isBaseKey_keyOf t _
    have hT_fresh₀ : env.find? T = none := by
      rw [show T = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
      exact hfresh _ hT_fam
    have hT_not_rest : ∀ p ∈ rest, p.2.structName ≠ T := fun p hp heq =>
      hnd.1 (List.mem_map.mpr ⟨p, hp, heq⟩)
    obtain ⟨hTbl_fr₂, hCh_fr₂⟩ := projKeys_fresh_in_env₂ haux₀ hnames hblkBase hd hT_base hT_fresh₀
    have hnot_rest_mem : ∀ c ∈ projConstsOfTables rest,
        c.name ≠ Ix.Kernel.projTableName T ∧ ∀ j, c.name ≠ Ix.Kernel.projChainKey T j := by
      intro c hc
      obtain ⟨p, hp, hcm⟩ := projConstsOfTables_mem_iff.mp hc
      have hne : p.2.structName ≠ T := hT_not_rest p hp
      rcases memberProjConsts_names_aux p.2 c hcm with ⟨-, hEq⟩ | ⟨j', -, -, hEq⟩
      · exact ⟨fun h => hne (projTableName_inj (hEq.symm.trans h)),
          fun j h => (projChainKey_ne_projTableName T p.2.structName j) (h.symm.trans hEq)⟩
      · exact ⟨fun h => projChainKey_ne_projTableName p.2.structName T j' (hEq.symm.trans h),
          fun j h => hne (projChainKey_inj (hEq.symm.trans h)).1⟩
    have hCh_frR : ∀ j ∈ List.range tbl.numFields, envR.find? (Ix.Kernel.projChainKey T j) = none :=
      fun j _ => find?_append_none (projConstsOfTables rest)
        (fun c hc heq => (hnot_rest_mem c hc).2 j heq) (hCh_fr₂ j)
    -- Step 1: Fold chain axioms for `T`
    obtain ⟨hextCh, hSCh, hArCh, hnpCh, hfindCh, hfpCh, hfoundCh⟩ :=
      fold_chainAxioms_pure (T := T) (List.range tbl.numFields) List.nodup_range hCh_frR
        hextR hSR hArR
    let envCh : Env .anon := ⟨(List.range tbl.numFields).map (chainAxiom T) ++ envR.consts⟩
    -- Step 2: Cons `.projInfo tbl` onto `envCh`
    have hTbl_frR : envR.find? (Ix.Kernel.projTableName T) = none :=
      find?_append_none (projConstsOfTables rest)
        (fun c hc heq => (hnot_rest_mem c hc).1 heq) hTbl_fr₂
    have hTbl_frCh : envCh.find? (Ix.Kernel.projTableName T) = none :=
      find?_append_none ((List.range tbl.numFields).map (chainAxiom T)) (fun c hc heq => by
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hc
        exact projChainKey_ne_projTableName T T j' heq) hTbl_frR
    let env₃ : Env .anon := ⟨.projInfo tbl :: envCh.consts⟩
    have henv₃_eq : (⟨projConstsOfTables ((pos, tbl) :: rest) ++ env₂.consts⟩ : Env .anon) = env₃ := by
      simp only [projConstsOfTables, memberProjConsts, List.cons_append, List.append_assoc, env₃,
        envCh, envR, T]
    dsimp only
    rw [henv₃_eq]
    have hfind₂Ch : ∀ k ci, env₂.find? k = some ci → envCh.find? k = some ci :=
      fun k ci hk => hfindCh k ci (hfindR k ci hk)
    have hfindCh₃ : ∀ k ci, envCh.find? k = some ci → env₃.find? k = some ci := fun k ci hk => by
      rw [Ix.Kernel.Env.find?_cons]
      split
      · rename_i heq; rw [projInfo_name] at heq; rw [heq, hk] at hTbl_frCh; exact nomatch hTbl_frCh
      · exact hk
    have hfind₂₃ : ∀ k ci, env₂.find? k = some ci → env₃.find? k = some ci :=
      fun k ci hk => hfindCh₃ k ci (hfind₂Ch k ci hk)
    have hext₃ : EnvExt env env₃ :=
      envExt_cons_of_fresh_and_not_old_table hextCh hTbl_frCh fun T' hT' heq => by
        have hEq : T = T' := projTableName_inj heq
        rw [← hEq, hT_fresh₀] at hT'
        exact Bool.false_ne_true hT'
    -- `EnvWF env₃`
    have hwf₃ : Ix.Kernel.EnvWF env₃ := by
      refine Ix.Kernel.EnvWF.cons hSCh.wf (constWF_projInfo sp.hbodies_sz fun j b hjb => ?_)
      obtain ⟨h1, h2, h3, h4⟩ := sp.hbodies_wf j b hjb
      refine ⟨h1, h2, Expr.constsResolve_of_find (fun n hn => ?_) h3, h4⟩
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      rw [hfind₂Ch n ci hci]; rfl
    -- `TowerHead env₃ (tbl.entry j)` for every `j < tbl.numFields`
    have hhead : ∀ j < tbl.numFields, Ix.Kernel.TowerHead env₃ (tbl.entry j) := by
      intro j hj
      have hposC_eq : Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C = sp.tyA_C := by
        rw [sp.hmpf_ct, show sp.ct.lvls.toNat = sp.ind.lvls.toNat by
          rw [← sp.hmpf_ind, ← sp.hmpf_ct]; exact sp.mpf.hcnl]
        exact posOf_range_eq_prep sp.ind.lvls.toNat sp.tyA_C
      have hstripC : sp.cvC.type.stripPis (tbl.numParams + tbl.numFields) =
          some (sp.mpf.bsC, sp.mpf.cret) := by
        have h1 := sp.mpf.hC_ret
        rw [hposC_eq, sp.hmpf_ind, sp.hmpf_ct] at h1
        rw [sp.hcvC_eq, sp.htbl_nP, sp.htbl_nF]
        exact h1
      have hstripT : sp.cvT.type.stripPis tbl.numParams = some (sp.mpf.bsT, .sort tbl.structSort) := by
        have h1 := sp.mpf.hT_sort
        rw [sp.hmpf_ind] at h1
        rw [sp.hcvT_eq, sp.htbl_nP, sp.htbl_sort]
        exact h1
      have hret_eq : sp.mpf.cret = Expr.mkAppN (.const T (tbl.levelParams.map .param))
          ((List.range tbl.numParams).map fun k => .bvar (tbl.numFields + tbl.numParams - 1 - k)) := by
        have h1 := sp.mpf.hC_ret_eq
        rw [sp.hmpf_ind, sp.hmpf_ct, ← sp.htbl_sn, ← sp.htbl_nP, ← sp.htbl_nF, ← sp.htbl_lps] at h1
        rw [h1]
        congr 1
        refine List.map_congr_left fun m _ => ?_
        congr 1; omega
      refine ⟨by
          simp only [ProjTable.entry_structName]
          rw [show tbl.structName = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
          exact (hkey _ hT_fam).1,
        by
          simp only [ProjTable.entry_ctor]
          rw [show tbl.ctor = Core.keyOf t (Core.cprjAddr B pos 0) from sp.htbl_ctor]
          exact (hkey _ hC_fam).1,
        hj,
        ⟨sp.cvT, {}, hfind₂₃ _ _ sp.hfindT₂, by rw [sp.hcvT_eq]; rfl, ⟨sp.mpf.bsT, hstripT⟩⟩,
        ⟨sp.cvC, hfind₂₃ _ _ sp.hfindC₂, by rw [sp.hcvC_eq]; rfl, ⟨sp.mpf.bsC, hret_eq ▸ hstripC⟩⟩,
        Or.inr ⟨⟨Ix.Kernel.projChainKey T j, [0], .sort (.succ (.param 0))⟩,
          hfindCh₃ _ _ (hfoundCh j (List.mem_range.mpr hj))⟩⟩
    -- `StoreInv env₃`
    have hS₃ : Ix.Kernel.Open.StoreInv env₃ := by
      refine ⟨hwf₃, Ix.Kernel.RecCtorsStored.cons hSCh.rec_ctors hTbl_frCh (fun _ _ _ _ h => nomatch h),
        fun n tbl' hf j hj => ?_⟩
      rw [Ix.Kernel.Env.find?_cons] at hf
      split at hf
      · obtain rfl := ConstantInfo.projInfo.inj (Option.some.inj hf)
        exact hhead j hj
      · exact (hSCh.proj_ok n tbl' hf j hj).mono (fun n' ci _ h' => hfindCh₃ n' ci h')
    -- `StoreArR env₃`
    have hAr₃ : Ix.Kernel.Model.StoreArR env₃ := by
      refine Ix.Kernel.Model.storeArR_cons (ci := .projInfo tbl) hArCh hTbl_frCh
        (Ix.Kernel.Model.ConstArR.of_proj fun j b hjb => ?_) (fun ⟨_, _, _, h⟩ _ => nomatch h)
      have hC_ar : Expr.arOk env₃ sp.cvC.type = true :=
        (Ix.Kernel.Model.ArRes.mono (fun {k ci} hk => hfindCh₃ k ci hk)
          (hArCh.const (hfind₂Ch _ _ sp.hfindC₂)).type).ar
      have hb_mem : b ∈ tbl.bodies := Array.mem_of_getElem? hjb
      have hb_ar : Expr.arOk env₃ b = true := arOk_structProjBodies hC_ar sp.hbodies b hb_mem
      obtain ⟨-, -, h3, -⟩ := sp.hbodies_wf j b hjb
      have hb_res : b.constsResolve env₃ = true := Expr.constsResolve_of_find (fun n hn => by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
        rw [hfind₂₃ n ci hci]; rfl) h3
      exact ⟨hb_ar, hb_res⟩
    -- `NoProjEnv env₃ T' i` for any fresh base key `T'` not in `(pos, tbl) :: rest`
    have hnp₃ : ∀ T', Decl.isBaseKey T' = true → env.find? T' = none →
        (∀ p ∈ (pos, tbl) :: rest, p.2.structName ≠ T') → ∀ i, NoProjEnv env₃ T' i := by
      intro T' hBase' hT' hnot' i
      have hne_T : T' ≠ T := fun h => hnot' (pos, tbl) List.mem_cons_self h.symm
      have hnp_Ch : NoProjEnv envCh T' i :=
        hnpCh T' i (hnpR T' hBase' hT' (fun p hp => hnot' p (List.mem_cons_of_mem _ hp)) i)
      refine hnp_Ch.cons ⟨by simp [ConstantInfo.toConstantVal], (fun _ _ _ h => nomatch h),
        (fun _ _ _ _ h => nomatch h), ?_⟩
      intro tbl' heq j hj
      obtain rfl := ConstantInfo.projInfo.inj heq
      have hnp_cvC : Expr.NoProjAt T' i sp.cvC.type :=
        (noProjEnv_famStep hS₀.store.wf hBase' hT'
          (haux₀.fresh_of_base_none (by rw [projTableName_base hBase']; exact hT'))
          hblkBase hg hd i).type _ (Ix.Kernel.Semantics.Env.find?_mem sp.hfindC₂)
      have hj_sz : j < tbl.bodies.size := by rw [sp.hbodies_sz]; exact hj
      simp only [Array.getD, hj_sz, ↓reduceDIte]
      exact noProjAt_structProjBodies_ne hne_T.symm hnp_cvC sp.hbodies _ (Array.getElem_mem hj_sz)
    -- Installed table entries & `TowerHead`
    have htbls₃ : ∀ p ∈ (pos, tbl) :: rest,
        env₃.find? (Ix.Kernel.projTableName p.2.structName) = some (.projInfo p.2) ∧
        (∀ f < p.2.numFields,
          env₃.findProj? p.2.structName f = some (p.2.entry f) ∧
          Ix.Kernel.TowerHead env₃ (p.2.entry f)) := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have hft : env₃.find? (Ix.Kernel.projTableName T) = some (.projInfo tbl) :=
          Ix.Kernel.Env.find?_cons_self _ _
        exact ⟨hft, fun f hf => ⟨Ix.Kernel.Env.findProj?_of_table hft hf, hhead f hf⟩⟩
      · obtain ⟨hftR, hthR⟩ := htblsR p hp
        have hft₃ : env₃.find? (Ix.Kernel.projTableName p.2.structName) = some (.projInfo p.2) :=
          hfindCh₃ _ _ (hfindCh _ _ hftR)
        exact ⟨hft₃, fun f hf => ⟨Ix.Kernel.Env.findProj?_of_table hft₃ hf,
          (hthR f hf).2.mono (fun n' ci _ h' => hfindCh₃ n' ci (hfindCh n' ci h'))⟩⟩
    -- `findProj?` unchanged outside `(pos, tbl) :: rest`
    have hfp₃ : ∀ s i, (∀ p ∈ (pos, tbl) :: rest, p.2.structName ≠ s) →
        env₃.findProj? s i = env₂.findProj? s i := by
      intro s i hnot
      have hne_s : T ≠ s := hnot (pos, tbl) List.mem_cons_self
      have h1 : env₃.findProj? s i = envCh.findProj? s i := by
        unfold Ix.Kernel.Env.findProj?
        rw [Ix.Kernel.Env.find?_cons, projInfo_name,
          ite_eq_right (fun h => absurd (projTableName_inj h) hne_s)]
      rw [h1, hfpCh s i, hfpR s i (fun p hp => hnot p (List.mem_cons_of_mem _ hp))]
    -- Freshness in `env₂`
    have hfr₂₃ : ∀ c ∈ projConstsOfTables ((pos, tbl) :: rest), env₂.find? c.name = none := by
      intro c hc
      simp only [projConstsOfTables, List.mem_append] at hc
      rcases hc with hc | hc
      · rcases memberProjConsts_names_aux tbl c hc with ⟨-, hEq⟩ | ⟨j, -, -, hEq⟩
        · rw [hEq]; exact hTbl_fr₂
        · rw [hEq]; exact hCh_fr₂ j
      · exact hfr₂R c hc
    exact ⟨hext₃, hS₃, hAr₃, hfind₂₃, hnp₃, htbls₃, hfp₃, hfr₂₃⟩

set_option maxHeartbeats 1600000 in
/-- Model-side fold across all projection tables in `entries` installed onto `env₂` (given
`mp₀`, `mp₂`, and `hblk_map`), extending `ModelExt` and preserving `EtaFamiliesClosed`. -/
private theorem fold_tables_model {V : Type u} [SetTheory V]
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env env₂ : Env .anon} {Reg : NativeFam .anon → Prop}
    {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {blk as new' : List (ConstantInfo .anon)}
    {h : KKey → KKey} {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (htwf : t.wf = true) (ht : t.check = .ok ())
    (hB : FamBlockRecord E₀ B cb ms)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hg : AliasGroup env h as)
    (hnames : ∀ a ∈ as, ∃ ci ∈ blk,
      a.name = Ix.Kernel.auxKey ci.name .model ∨ ∃ j, a.name = Decl.FamilyAlias.iotaKey ci.name j)
    (htgt : ∀ ci ∈ blk, h (Ix.Kernel.auxKey ci.name .model) = adv.ren ci.name)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    (henv₂ : env₂ = ⟨(new' ++ as) ++ env.consts⟩)
    (hnew'_nothm : ∀ c ∈ new', ∀ cv v, c ≠ .thmInfo cv v)
    (hI : SelectedInstalled blk tys rhsss env₂)
    (hS₀ : Decl.FoldStoreInv env)
    (hS₂ : Decl.FoldStoreInv env₂)
    (hAr₂ : Ix.Kernel.Model.StoreArR env₂)
    (haux₀ : Decl.AuxRootSynced env)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (Core.keyOf t x) = none)
    (hkey : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (Core.keyOf t x))
    (heqPin : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith FormerOpenTraceAt t E env Reg)
    (bpf : BlockProjFacts t E₀ E env B cb ms blk tys adv.ren)
    (hext02E : EnvExt env env₂)
    (hblkBase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true)
    (mp₀ : EnvModelM V .verified env)
    (hThm₀ : ThmValOk mp₀)
    (hN₀ : ∀ fam, Reg fam → NativeFamOk mp₀ fam)
    (mp₂ : EnvModelM V .verified env₂)
    (hE₂ : Ix.Kernel.EtaFamiliesClosed env₂)
    (hext02M : ModelExt mp₀ mp₂)
    (hblk_map : ∀ k ∈ blk.map (·.name), ∀ ci₂, env₂.find? k = some ci₂ →
      ∃ (cvm : ConstantVal .anon) (mval : KExpr) (hint : Ix.Kernel.ReducibilityHint),
        env.find? (adv.ren k) = some (.defnInfo cvm mval hint) ∧
        ci₂.toConstantVal.levelParams.Nodup ∧
        cvm.levelParams.Nodup ∧
        cvm.levelParams.length = ci₂.toConstantVal.levelParams.length ∧
        ∀ ψ, mp₂.base2.acval k ψ =
          mp₀.base2.acval (adv.ren k) (Level.substFn ψ cvm.levelParams
            (ci₂.toConstantVal.levelParams.map .param))) :
    ∀ (entries : List (Nat × ProjTable .anon)),
      (entries.map (·.2.structName)).Nodup →
      (∀ p ∈ entries, p.1 < ms.size ∧ bpf.elig p.1 = true ∧
        Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren p.1 p.2)) →
      let env₃ : Env .anon := ⟨projConstsOfTables entries ++ env₂.consts⟩
      Ix.Kernel.EtaFamiliesClosed env₃ ∧
      ∃ mp₃ : EnvModelM V .verified env₃, ModelExt mp₂ mp₃
  | [], _, _ => ⟨hE₂, mp₂, ModelExt.refl⟩
  | (pos, tbl) :: rest, hnd, hall => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hrest_all : ∀ p ∈ rest, p.1 < ms.size ∧ bpf.elig p.1 = true ∧
        Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren p.1 p.2) :=
      fun p hp => hall p (List.mem_cons_of_mem _ hp)
    obtain ⟨hER, mpR, hext2R⟩ :=
      fold_tables_model htwf ht hB hreads hF hg hnames htgt hd henv₂ hnew'_nothm hI hS₀ hS₂ hAr₂
        haux₀ hfresh hkey heqPin hbasis hreg bpf hext02E hblkBase mp₀ hThm₀ hN₀ mp₂ hE₂ hext02M
        hblk_map rest hnd.2 hrest_all
    obtain ⟨hextR, hSR, hArR, hfindR, hnpR, htblsR, hfpR, hfr₂R⟩ :=
      fold_tables_pure htwf hB hreads hF hg hnames hd hI hS₀ hS₂ hAr₂ haux₀ hfresh hkey bpf
        hext02E hblkBase rest hnd.2 hrest_all
    obtain ⟨hpos, helig, ⟨sp⟩⟩ := hall (pos, tbl) List.mem_cons_self
    dsimp only at hpos helig sp
    let T := tbl.structName
    let C := tbl.ctor
    let nP := tbl.numParams
    let nF := tbl.numFields
    let bnl := sp.ind.lvls.toNat
    let envR : Env .anon := ⟨projConstsOfTables rest ++ env₂.consts⟩
    have hT_fam : FamAddr B cb rb crb (Core.iprjAddr B pos) :=
      Or.inl (Or.inr ⟨ms, pos, .indc sp.ind, hB.muts, sp.hmpf_ind ▸ sp.mpf.hms, Or.inl rfl⟩)
    have hC_fam : FamAddr B cb rb crb (Core.cprjAddr B pos 0) :=
      Or.inl (Or.inr ⟨ms, pos, .indc sp.ind, hB.muts, sp.hmpf_ind ▸ sp.mpf.hms,
        Or.inr ⟨sp.ind, 0, rfl, by rw [← sp.hmpf_ind, sp.mpf.hnc1]; omega, rfl⟩⟩)
    have hT_base : Decl.isBaseKey T = true := by
      rw [show T = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
      exact Decl.isBaseKey_keyOf t _
    have hT_fresh₀ : env.find? T = none := by
      rw [show T = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
      exact hfresh _ hT_fam
    have hT_not_rest : ∀ p ∈ rest, p.2.structName ≠ T := fun p hp heq =>
      hnd.1 (List.mem_map.mpr ⟨p, hp, heq⟩)
    obtain ⟨hTbl_fr₂, hCh_fr₂⟩ := projKeys_fresh_in_env₂ haux₀ hnames hblkBase hd hT_base hT_fresh₀
    have hnot_rest_mem : ∀ c ∈ projConstsOfTables rest,
        c.name ≠ Ix.Kernel.projTableName T ∧ ∀ j, c.name ≠ Ix.Kernel.projChainKey T j := by
      intro c hc
      obtain ⟨p, hp, hcm⟩ := projConstsOfTables_mem_iff.mp hc
      have hne : p.2.structName ≠ T := hT_not_rest p hp
      rcases memberProjConsts_names_aux p.2 c hcm with ⟨-, hEq⟩ | ⟨j', -, -, hEq⟩
      · exact ⟨fun h => hne (projTableName_inj (hEq.symm.trans h)),
          fun j h => (projChainKey_ne_projTableName T p.2.structName j) (h.symm.trans hEq)⟩
      · exact ⟨fun h => projChainKey_ne_projTableName p.2.structName T j' (hEq.symm.trans h),
          fun j h => hne (projChainKey_inj (hEq.symm.trans h)).1⟩
    have hCh_frR : ∀ j ∈ List.range nF, envR.find? (Ix.Kernel.projChainKey T j) = none :=
      fun j _ => find?_append_none (projConstsOfTables rest)
        (fun c hc heq => (hnot_rest_mem c hc).2 j heq) (hCh_fr₂ j)
    -- Step 1: Extract `hTM_find` and `hCM_find` for `T` and `C`
    have hT_in_bn : T ∈ blk.map (·.name) :=
      List.mem_map.mpr ⟨sp.ciT, (List.mem_filter.mp (List.mem_of_getElem? sp.hT_nr)).1,
        sp.hT_name.trans sp.htbl_sn.symm⟩
    have hC_in_bn : C ∈ blk.map (·.name) :=
      List.mem_map.mpr ⟨sp.ciC, (List.mem_filter.mp (List.mem_of_getElem? sp.hC_nr)).1,
        sp.hC_name.trans sp.htbl_ctor.symm⟩
    obtain ⟨cvTM, mvalTM, hintTM, hfindTM, -, hTM_nd, hTM_len, hacT₂⟩ :=
      hblk_map T hT_in_bn _ sp.hfindT₂
    obtain ⟨cvCM, mvalCM, hintCM, hfindCM, -, hCM_nd, hCM_len, hacC₂⟩ :=
      hblk_map C hC_in_bn _ sp.hfindC₂
    obtain ⟨cvTM', mvalTM', hintTM', hfindTM', hTM_perm', hTM_lv⟩ := sp.hmfT.model
    have hTM_name_eq : adv.ren sp.ciT.name = adv.ren T := by
      rw [sp.hT_name, ← sp.htbl_sn]
    rw [hTM_name_eq, hfindTM] at hfindTM'
    obtain ⟨hcvTM_eq, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfindTM')
    subst hcvTM_eq
    have hTM_perm : cvTM.levelParams.Perm (List.range bnl) := by
      rw [sp.hciT_lps, List.length_range] at hTM_perm'
      exact hTM_perm'
    have hTM_lvls : cvTM.levelParams.length = bnl := by
      simpa [ConstantInfo.toConstantVal, sp.hcvT_eq, sp.htbl_lps] using hTM_len
    have hTM_ty : ExprSemEq (Core.posOf cvTM.levelParams cvTM.type)
        (Core.posOf (List.range bnl) sp.tyA_T) := by
      rw [sp.hciT_lps, sp.hT_ren_eq] at hTM_lv
      exact exprSemEq_symm (exprSemEq_of_exprLvEq hTM_lv)
    obtain ⟨cvCM', mvalCM', hintCM', hfindCM', hCM_perm', -⟩ := sp.hmfC.model
    have hCM_name_eq : adv.ren sp.ciC.name = adv.ren C := by
      rw [sp.hC_name, ← sp.htbl_ctor]
    rw [hCM_name_eq, hfindCM] at hfindCM'
    obtain ⟨hcvCM_eq, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hfindCM')
    subst hcvCM_eq
    have hCM_perm : cvCM.levelParams.Perm (List.range bnl) := by
      rw [sp.hciC_lps, List.length_range] at hCM_perm'
      exact hCM_perm'
    have hCM_lvls : cvCM.levelParams.length = bnl := by
      simpa [ConstantInfo.toConstantVal, sp.hcvC_eq, sp.htbl_lps] using hCM_len
    -- Step 2: Obtain `A_chain j` for every `j < nF` from `field_chain_coherence`!
    have hnP_eq : nP = sp.mpf.ind.params.toNat := by
      rw [show nP = tbl.numParams from rfl, sp.htbl_nP, sp.hmpf_ind]
    have hnF_eq : nF = sp.mpf.ct.fields.toNat := by
      rw [show nF = tbl.numFields from rfl, sp.htbl_nF, sp.hmpf_ct]
    have hbnl_eq : bnl = sp.mpf.ind.lvls.toNat := by
      rw [show bnl = sp.ind.lvls.toNat from rfl, sp.hmpf_ind]
    have hposT_eq : Core.posOf (List.range bnl) sp.tyA_T = sp.tyA_T :=
      posOf_range_eq_prep bnl sp.tyA_T
    have hT_sort_pos : (Core.posOf (List.range bnl) sp.tyA_T).stripPis nP =
        some (sp.mpf.bsT, .sort sp.mpf.structSort) := by
      rw [hposT_eq, hnP_eq]
      exact sp.mpf.hT_sort
    have hfield_ex : ∀ j (hj : j < nF),
        ∃ A_chain : (LevelParam → Nat) → AnnotTerm,
          (∀ ψ k, (A_chain ψ).liftN 1 k = A_chain ψ) ∧
          (∀ ψ₁ ψ₂, ψ₁ 0 = ψ₂ 0 → A_chain ψ₁ = A_chain ψ₂) ∧
          (∀ ψ ρ, WellDenotedV V ρ (A_chain ψ)) ∧
          (∀ ψ ρ, interp V ρ (A_chain ψ) ∈ˢ (univ (ψ 0 + 1) : V)) ∧
          ∀ (fdom frest rawDom : KExpr) (fbm : BinderMeta)
            (bsRaw : List (KExpr × BinderMeta)) (remRaw : KExpr)
            (fp : FieldProjFacts t E env (adv.ren T) (adv.ren C)
              (Core.posOf (List.range sp.mpf.ind.lvls.toNat) sp.tyA_T)
              (Decl.renameAll adv.ren (Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C))
              nP sp.mpf.ind.lvls.toNat nF j fdom rawDom),
            fp.projKey = sp.mpf.projKeyAt j →
            ∀ (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V),
              vs_v.length = nP →
              (∀ cvTM₀ mvalTM₀ hintTM₀,
                env.find? (adv.ren T) = some (.defnInfo cvTM₀ mvalTM₀ hintTM₀) →
                AppChainOk (interp V ρ₀ (mp₀.base2.acval (adv.ren T) (origVal cvTM₀.levelParams ψ_P))) vs_v ∧
                x_v ∈ˢ vs_v.foldl SetTheory.app
                  (interp V ρ₀ (mp₀.base2.acval (adv.ren T) (origVal cvTM₀.levelParams ψ_P)))) →
              Ix.Kernel.chainApp (fun n => interp V ρ₀ (A_chain (fun _ => n))) x_v =
                (vs_v ++ [x_v]).foldl SetTheory.app
                  (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∧
              ∀ rdomA,
                denoteMeta mp₀.base2.acval env ψ_P (nP + 1)
                  (openDummiesP (nP + 1) 0 0 fp.rdom) = some rdomA →
                (vs_v ++ [x_v]).foldl SetTheory.app
                  (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
                  interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA := by
      intro j hj
      have hj' : j < sp.mpf.ct.fields.toNat := by rw [← hnF_eq]; exact hj
      obtain ⟨fdom₀, frest₀, rawDom₀, fbm₀, bsRaw₀, remRaw₀, htele₀, hstripRaw₀, hrawAt₀,
        fp₀, hfp₀_key⟩ := sp.mpf.hfields j hj'
      have hrawDom_at : (fp₀.cbsI.map Prod.fst)[sp.mpf.ind.params.toNat + j]? = some rawDom₀ := by
        have h1 : fp₀.cbsI = bsRaw₀ :=
          (Prod.mk.inj (Option.some.inj (fp₀.hC_strip.symm.trans hstripRaw₀))).1
        rw [h1]; exact hrawAt₀
      have hT_sort_mpf : (Core.posOf (List.range sp.mpf.ind.lvls.toNat) sp.tyA_T).stripPis
          sp.mpf.ind.params.toNat = some (sp.mpf.bsT, .sort sp.mpf.structSort) := by
        rw [← hbnl_eq, ← hnP_eq]; exact hT_sort_pos
      have hTM_find_mpf : ∃ cvTM₀ mvalTM₀ hintTM₀,
          env.find? (adv.ren (Core.keyOf t (Core.iprjAddr B pos))) =
            some (.defnInfo cvTM₀ mvalTM₀ hintTM₀) ∧
          cvTM₀.levelParams.length = sp.mpf.ind.lvls.toNat ∧
          cvTM₀.levelParams.Perm (List.range sp.mpf.ind.lvls.toNat) ∧
          ExprSemEq (Core.posOf cvTM₀.levelParams cvTM₀.type)
            (Core.posOf (List.range sp.mpf.ind.lvls.toNat) sp.tyA_T) := by
        rw [← sp.htbl_sn, ← hbnl_eq]
        exact ⟨cvTM, mvalTM, hintTM, hfindTM, hTM_lvls, hTM_perm, hTM_ty⟩
      obtain ⟨A_ch, hAcl, hAprm, hAok, hAmem, hAcoh⟩ :=
        field_chain_coherence ht hbasis hreg hS₀.defnTyped mp₀ hN₀ hT_sort_mpf sp.mpf.hT_sort_nz
          sp.hT_pw hTM_find_mpf fp₀ hj' ⟨sp.mpf.projKeyAt, frest₀, fbm₀, htele₀⟩ hrawDom_at
      refine ⟨A_ch, hAcl, hAprm, hAok, hAmem, ?_⟩
      intro fdom frest rawDom fbm bsRaw remRaw fp hfp_key ψ_P ρ₀ vs_v x_v hvs_len hTM_all
      have hvs_len' : vs_v.length = sp.mpf.ind.params.toNat := by
        rw [← hnP_eq]; exact hvs_len
      have hTM_all' : ∀ cvTM₀ mvalTM₀ hintTM₀,
          env.find? (adv.ren (Core.keyOf t (Core.iprjAddr B pos))) =
            some (.defnInfo cvTM₀ mvalTM₀ hintTM₀) →
          AppChainOk (interp V ρ₀ (mp₀.base2.acval (adv.ren (Core.keyOf t (Core.iprjAddr B pos)))
            (origVal cvTM₀.levelParams ψ_P))) vs_v ∧
          x_v ∈ˢ vs_v.foldl SetTheory.app
            (interp V ρ₀ (mp₀.base2.acval (adv.ren (Core.keyOf t (Core.iprjAddr B pos)))
              (origVal cvTM₀.levelParams ψ_P))) := by
        rw [← sp.htbl_sn]; exact hTM_all
      obtain ⟨hch_eq, hmem_r0⟩ := hAcoh ψ_P ρ₀ vs_v x_v hvs_len' hTM_all'
      have hkey_eq : fp.projKey = fp₀.projKey := hfp_key.trans hfp₀_key.symm
      have hcvP_eq : fp.cvProj = fp₀.cvProj := by
        have hf1 := fp.hfindProj
        rw [hkey_eq, fp₀.hfindProj] at hf1
        exact (ConstantInfo.defnInfo.inj (Option.some.inj hf1)).1.symm
      have hrdom_eq : fp.rdom = fp₀.rdom := by
        have hs1 := fp.hProj_strip
        have hs2 := fp₀.hProj_strip
        conv at hs2 => lhs; rw [← hcvP_eq, ← hnP_eq]
        have h2 := Option.some.inj (hs1.symm.trans hs2)
        exact (Expr.forallE.inj (Prod.mk.inj h2).2).2.1
      rw [hkey_eq, hcvP_eq]
      refine ⟨hch_eq, fun rdomA hr => ?_⟩
      rw [hrdom_eq, hnP_eq] at hr
      exact hmem_r0 rdomA hr
    -- Choose `A_chain : Nat → (LevelParam → Nat) → AnnotTerm`
    let A_chain : Nat → (LevelParam → Nat) → AnnotTerm := fun j =>
      if hj : j < nF then (hfield_ex j hj).choose else fun _ => .sort 0
    have hA_spec : ∀ j (hj : j < nF),
        (∀ ψ k, (A_chain j ψ).liftN 1 k = A_chain j ψ) ∧
        (∀ ψ₁ ψ₂, ψ₁ 0 = ψ₂ 0 → A_chain j ψ₁ = A_chain j ψ₂) ∧
        (∀ ψ ρ, WellDenotedV V ρ (A_chain j ψ)) ∧
        (∀ ψ ρ, interp V ρ (A_chain j ψ) ∈ˢ (univ (ψ 0 + 1) : V)) ∧
        ∀ (fdom frest rawDom : KExpr) (fbm : BinderMeta)
          (bsRaw : List (KExpr × BinderMeta)) (remRaw : KExpr)
          (fp : FieldProjFacts t E env (adv.ren T) (adv.ren C)
            (Core.posOf (List.range sp.mpf.ind.lvls.toNat) sp.tyA_T)
            (Decl.renameAll adv.ren (Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C))
            nP sp.mpf.ind.lvls.toNat nF j fdom rawDom),
          fp.projKey = sp.mpf.projKeyAt j →
          ∀ (ψ_P : LevelParam → Nat) (ρ₀ : Nat → V) (vs_v : List V) (x_v : V),
            vs_v.length = nP →
            (∀ cvTM₀ mvalTM₀ hintTM₀,
              env.find? (adv.ren T) = some (.defnInfo cvTM₀ mvalTM₀ hintTM₀) →
              AppChainOk (interp V ρ₀ (mp₀.base2.acval (adv.ren T) (origVal cvTM₀.levelParams ψ_P))) vs_v ∧
              x_v ∈ˢ vs_v.foldl SetTheory.app
                (interp V ρ₀ (mp₀.base2.acval (adv.ren T) (origVal cvTM₀.levelParams ψ_P)))) →
            Ix.Kernel.chainApp (fun n => interp V ρ₀ (A_chain j (fun _ => n))) x_v =
              (vs_v ++ [x_v]).foldl SetTheory.app
                (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∧
            ∀ rdomA,
              denoteMeta mp₀.base2.acval env ψ_P (nP + 1)
                (openDummiesP (nP + 1) 0 0 fp.rdom) = some rdomA →
              (vs_v ++ [x_v]).foldl SetTheory.app
                (interp V ρ₀ (mp₀.base2.acval fp.projKey (origVal fp.cvProj.levelParams ψ_P))) ∈ˢ
                interp V (consList (vs_v ++ [x_v]) ρ₀) rdomA := fun j hj => by
      simp only [A_chain, hj, ↓reduceDIte]
      exact (hfield_ex j hj).choose_spec
    -- Step 3: Fold `chainAxiom_step` over `List.range nF`
    obtain ⟨hECh, mpCh, hextRCh, hacCh_chains, hacCh_old⟩ :=
      fold_chainAxioms_model A_chain (fun j hj => (hA_spec j hj).1)
        (fun j hj => (hA_spec j hj).2.1) (fun j hj => (hA_spec j hj).2.2.1)
        (fun j hj => (hA_spec j hj).2.2.2.1) (List.range nF) List.nodup_range
        (fun _ hj => List.mem_range.mp hj) hCh_frR mpR hER
    obtain ⟨hextChE, hSCh, hArCh, hnpCh, hfindCh, hfpCh, hfoundCh⟩ :=
      fold_chainAxioms_pure (T := T) (List.range nF) List.nodup_range hCh_frR hextR hSR hArR
    let envCh : Env .anon := ⟨(List.range nF).map (chainAxiom T) ++ envR.consts⟩
    let env₃ : Env .anon := ⟨.projInfo tbl :: envCh.consts⟩
    have henv₃_eq : (⟨projConstsOfTables ((pos, tbl) :: rest) ++ env₂.consts⟩ : Env .anon) = env₃ := by
      simp only [projConstsOfTables, memberProjConsts, List.cons_append, List.append_assoc, env₃,
        envCh, envR, T, nF]
    dsimp only
    rw [henv₃_eq]
    have hTbl_frR : envR.find? (Ix.Kernel.projTableName T) = none :=
      find?_append_none (projConstsOfTables rest)
        (fun c hc heq => (hnot_rest_mem c hc).1 heq) hTbl_fr₂
    have hTbl_frCh : envCh.find? (Ix.Kernel.projTableName T) = none :=
      find?_append_none ((List.range nF).map (chainAxiom T)) (fun c hc heq => by
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hc
        exact projChainKey_ne_projTableName T T j' heq) hTbl_frR
    have hfind₂Ch : ∀ k ci, env₂.find? k = some ci → envCh.find? k = some ci :=
      fun k ci hk => hfindCh k ci (hfindR k ci hk)
    have hfindCh₃ : ∀ k ci, envCh.find? k = some ci → env₃.find? k = some ci := fun k ci hk => by
      rw [Ix.Kernel.Env.find?_cons]
      split
      · rename_i heq; rw [projInfo_name] at heq; rw [heq, hk] at hTbl_frCh; exact nomatch hTbl_frCh
      · exact hk
    have hfind₂₃ : ∀ k ci, env₂.find? k = some ci → env₃.find? k = some ci :=
      fun k ci hk => hfindCh₃ k ci (hfind₂Ch k ci hk)
    -- Pure facts for `declStep_preserves_of_tower_cons`
    have hwf₃ : Ix.Kernel.EnvWF env₃ := by
      refine Ix.Kernel.EnvWF.cons hSCh.wf (constWF_projInfo sp.hbodies_sz fun j b hjb => ?_)
      obtain ⟨h1, h2, h3, h4⟩ := sp.hbodies_wf j b hjb
      refine ⟨h1, h2, Expr.constsResolve_of_find (fun n hn => ?_) h3, h4⟩
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      rw [hfind₂Ch n ci hci]; rfl
    have hnp_Ch_T : ∀ j, NoProjEnv envCh T j := fun j =>
      hnpCh T j (hnpR T hT_base hT_fresh₀ hT_not_rest j)
    have hhead : ∀ j < nF, Ix.Kernel.TowerHead env₃ (tbl.entry j) := by
      intro j hj
      have hposC_eq : Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C = sp.tyA_C := by
        rw [sp.hmpf_ct, show sp.ct.lvls.toNat = sp.ind.lvls.toNat by
          rw [← sp.hmpf_ind, ← sp.hmpf_ct]; exact sp.mpf.hcnl]
        exact posOf_range_eq_prep sp.ind.lvls.toNat sp.tyA_C
      have hstripC : sp.cvC.type.stripPis (nP + nF) = some (sp.mpf.bsC, sp.mpf.cret) := by
        have h1 := sp.mpf.hC_ret
        rw [hposC_eq, sp.hmpf_ind, sp.hmpf_ct] at h1
        rw [sp.hcvC_eq, show nP = tbl.numParams from rfl, show nF = tbl.numFields from rfl,
          sp.htbl_nP, sp.htbl_nF]
        exact h1
      have hstripT : sp.cvT.type.stripPis nP = some (sp.mpf.bsT, .sort tbl.structSort) := by
        have h1 := sp.mpf.hT_sort
        rw [sp.hmpf_ind] at h1
        rw [sp.hcvT_eq, show nP = tbl.numParams from rfl, sp.htbl_nP, sp.htbl_sort]
        exact h1
      have hret_eq : sp.mpf.cret = Expr.mkAppN (.const T (tbl.levelParams.map .param))
          ((List.range nP).map fun k => .bvar (nF + nP - 1 - k)) := by
        have h1 := sp.mpf.hC_ret_eq
        rw [sp.hmpf_ind, sp.hmpf_ct, ← sp.htbl_sn, ← sp.htbl_nP, ← sp.htbl_nF, ← sp.htbl_lps] at h1
        rw [h1]
        congr 1
        refine List.map_congr_left fun m _ => ?_
        congr 1; omega
      refine ⟨by
          simp only [ProjTable.entry_structName]
          rw [show tbl.structName = Core.keyOf t (Core.iprjAddr B pos) from sp.htbl_sn]
          exact (hkey _ hT_fam).1,
        by
          simp only [ProjTable.entry_ctor]
          rw [show tbl.ctor = Core.keyOf t (Core.cprjAddr B pos 0) from sp.htbl_ctor]
          exact (hkey _ hC_fam).1,
        hj,
        ⟨sp.cvT, {}, hfind₂₃ _ _ sp.hfindT₂, by rw [sp.hcvT_eq]; rfl, ⟨sp.mpf.bsT, hstripT⟩⟩,
        ⟨sp.cvC, hfind₂₃ _ _ sp.hfindC₂, by rw [sp.hcvC_eq]; rfl, ⟨sp.mpf.bsC, hret_eq ▸ hstripC⟩⟩,
        Or.inr ⟨⟨Ix.Kernel.projChainKey T j, [0], .sort (.succ (.param 0))⟩,
          hfindCh₃ _ _ (hfoundCh j (List.mem_range.mpr hj))⟩⟩
    -- Precompute `denoteMeta mp₂.base2.acval env₂ ψ 0 sp.cvC.type = denoteMeta mp₀.base2.acval env ψ 0 (sp.tyA_C.renameConsts adv.ren)`
    have hwfC₂ := hS₂.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem sp.hfindC₂)
    have hwfT₂ := hS₂.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem sp.hfindT₂)
    have hout_ren : ∀ k, k ∉ blk.map (·.name) → adv.ren k = k := fun k hk =>
      Decl.FamilyAlias.aliasMap_of_not_key adv.models k (by rw [hF.table]; exact hk)
    have hpre_ren : ∀ k, (env.find? k).isSome = true → adv.ren k = k := fun k hk =>
      hout_ren k fun hin => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hin
        rw [blk_fresh_in_env hg hd ci hci] at hk
        exact Bool.false_ne_true hk
    have hC_noProj_blk : ∀ k ∈ blk.map (·.name), ∀ j, Expr.NoProjAt k j sp.tyA_C := by
      intro k hk j
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
      have hkb := hblkBase ci hci
      have hkf := blk_fresh_in_env hg hd ci hci
      have hnp := noProjEnv_famStep hS₀.store.wf hkb hkf
        (haux₀.fresh_of_base_none (by rw [projTableName_base hkb]; exact hkf))
        hblkBase hg hd j
      have h1 := hnp.type _ (Ix.Kernel.Semantics.Env.find?_mem sp.hfindC₂)
      simpa [ConstantInfo.toConstantVal, sp.hcvC_eq] using h1
    have hC_ren_eq : Decl.renameAll adv.ren (Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C) =
        sp.tyA_C.renameConsts adv.ren := by
      have hposC_eq : Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C = sp.tyA_C := by
        rw [sp.hmpf_ct, show sp.ct.lvls.toNat = sp.ind.lvls.toNat by
          rw [← sp.hmpf_ind, ← sp.hmpf_ct]; exact sp.mpf.hcnl]
        exact posOf_range_eq_prep sp.ind.lvls.toNat sp.tyA_C
      rw [hposC_eq]
      exact renameAll_eq_renameConsts_of_noProj hout_ren
        (by simpa [ConstantInfo.toConstantVal, sp.hcvC_eq] using hwfC₂.1) hC_noProj_blk
    have hC_ren_res : (sp.tyA_C.renameConsts adv.ren).constsResolve env = true := by
      obtain ⟨stype, u, ⟨ps, -, hinf⟩, -⟩ := sp.hmfC.modelTyped
      have hfv_ren : (sp.tyA_C.renameConsts adv.ren).hasFvar = false := by
        have hfv : sp.tyA_C.hasFvar = false := by
          simpa [ConstantInfo.toConstantVal, sp.hcvC_eq] using hwfC₂.1
        have hgo : ∀ e : KExpr, e.hasFvar = false → (e.renameConsts adv.ren).hasFvar = false := by
          intro e; induction e with
          | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
          | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
          | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
            intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
            simp [Expr.renameConsts, Expr.hasFvar, ih1 h.1, ih2 h.2]
          | letE _ _ _ _ ih1 ih2 ih3 =>
            intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
            simp [Expr.renameConsts, Expr.hasFvar, ih1 h.1.1, ih2 h.1.2, ih3 h.2]
          | proj _ _ _ ih1 => intro h; exact ih1 h
        exact hgo sp.tyA_C hfv
      have hfv_pos : ∀ e : KExpr, e.hasFvar = false →
          (e.instantiateLevelParams ps (Core.posLevels ps)).hasFvar = false := by
        intro e; induction e with
        | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
        | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
        | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
          intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
          simp [Expr.instantiateLevelParams, Expr.hasFvar, ih1 h.1, ih2 h.2]
        | letE _ _ _ _ ih1 ih2 ih3 =>
          intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
          simp [Expr.instantiateLevelParams, Expr.hasFvar, ih1 h.1.1, ih2 h.1.2, ih3 h.2]
        | proj _ _ _ ih1 => intro h; exact ih1 h
      have hcr_pos := Decl.infer_constsResolve hinf hS₀.store (hfv_pos _ hfv_ren)
      have hcr_inv : ∀ e : KExpr,
          (e.instantiateLevelParams ps (Core.posLevels ps)).constsResolve env = e.constsResolve env := by
        intro e; induction e with
        | bvar _ | sort _ | const _ _ | lit _ => rfl
        | fvar _ _ ih => exact ih
        | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
          simp [Expr.instantiateLevelParams, Expr.constsResolve, ih1, ih2]
        | letE _ _ _ _ ih1 ih2 ih3 =>
          simp [Expr.instantiateLevelParams, Expr.constsResolve, ih1, ih2, ih3]
        | proj _ _ _ ih => simp [Expr.instantiateLevelParams, Expr.constsResolve, ih]
      exact (hcr_inv _).symm.trans hcr_pos
    have hC_men : ∀ k, sp.tyA_C.mentionsConst k = true →
        (env.find? k).isSome = true ∨ k ∈ blk.map (·.name) := by
      intro k hk
      by_cases hmem : k ∈ blk.map (·.name)
      · exact Or.inr hmem
      · refine Or.inl ?_
        have h1 : (sp.tyA_C.renameConsts adv.ren).mentionsConst k = true := by
          have hgo : ∀ e : KExpr, e.mentionsConst k = true →
              (e.renameConsts adv.ren).mentionsConst (adv.ren k) = true := by
            intro e; induction e with
            | bvar _ | sort _ | lit _ => intro h; simp [Expr.mentionsConst] at h
            | fvar _ ty ih => intro h; exact ih h
            | const n _ =>
              intro h; simp only [Expr.mentionsConst, beq_iff_eq] at h
              subst h; simp [Expr.renameConsts, Expr.mentionsConst]
            | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
              intro h; simp only [Expr.mentionsConst, Bool.or_eq_true] at h
              simp only [Expr.renameConsts, Expr.mentionsConst, Bool.or_eq_true]
              exact h.imp ih1 ih2
            | letE _ _ _ _ ih1 ih2 ih3 =>
              intro h; simp only [Expr.mentionsConst, Bool.or_eq_true] at h
              simp only [Expr.renameConsts, Expr.mentionsConst, Bool.or_eq_true]
              rcases h with (h | h) | h
              · exact Or.inl (Or.inl (ih1 h))
              · exact Or.inl (Or.inr (ih2 h))
              · exact Or.inr (ih3 h)
            | proj s _ _ ih =>
              intro h; simp only [Expr.mentionsConst, Bool.or_eq_true] at h
              simp only [Expr.renameConsts, Expr.mentionsConst, Bool.or_eq_true]
              rcases h with hs | he
              · have heq : s = k := beq_iff_eq.mp hs
                subst heq
                rw [hout_ren s hmem]
                exact Or.inl (beq_self_eq_true s)
              · exact Or.inr (ih he)
          have h2 := hgo sp.tyA_C hk
          rwa [hout_ren k hmem] at h2
        have hgo2 : ∀ e : KExpr, e.constsResolve env = true → e.mentionsConst k = true →
            (env.find? k).isSome = true := by
          intro e; induction e with
          | bvar _ | sort _ | lit _ => intro _ h; simp [Expr.mentionsConst] at h
          | fvar _ ty ih => intro hr hm; exact ih hr hm
          | const n _ =>
            intro hr hm; simp only [Expr.mentionsConst, beq_iff_eq] at hm
            subst hm; exact hr
          | app _ _ ih1 ih2 | lam _ _ _ ih1 ih2 | forallE _ _ _ ih1 ih2 =>
            intro hr hm; simp only [Expr.constsResolve, Bool.and_eq_true] at hr
            simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
            rcases hm with hm | hm
            · exact ih1 hr.1 hm
            · exact ih2 hr.2 hm
          | letE _ _ _ _ ih1 ih2 ih3 =>
            intro hr hm; simp only [Expr.constsResolve, Bool.and_eq_true] at hr
            simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
            rcases hm with (hm | hm) | hm
            · exact ih1 hr.1.1 hm
            · exact ih2 hr.1.2 hm
            · exact ih3 hr.2 hm
          | proj s _ _ ih =>
            intro hr hm; simp only [Expr.constsResolve, Bool.and_eq_true] at hr
            simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
            rcases hm with hs | he
            · have heq : s = k := beq_iff_eq.mp hs
              subst heq; exact hr.1
            · exact ih hr.2 he
        exact hgo2 _ hC_ren_res h1
    have hC_denote₂ : ∀ ψ,
        denoteMeta mp₂.base2.acval env₂ ψ 0 sp.cvC.type =
          denoteMeta mp₀.base2.acval env ψ 0 (sp.tyA_C.renameConsts adv.ren) := by
      intro ψ
      rw [sp.hcvC_eq]
      refine denoteMeta_famStep_eq_renameConsts mp₀ mp₂ hext02M hext02E hpre_ren
        (fun k hk => by
          obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
          obtain ⟨newW, henvW, -, hallW⟩ := famStep_consts hd
          obtain ⟨c', hc', hcn⟩ := hallW ci hci
          rw [henvW]
          show (((newW ++ as) ++ env.consts).find? (·.name == ci.name)).isSome = true
          exact List.find?_isSome.mpr ⟨c', List.mem_append_left _ (List.mem_append_left _ hc'),
            by rw [hcn]; exact beq_self_eq_true _⟩)
        (fun k hk ci₂ hf₂ => by
          obtain ⟨cvm, mval, hint, hfm, hnd₂, hndm, hlenm, hacm⟩ := hblk_map k hk ci₂ hf₂
          exact ⟨.defnInfo cvm mval hint, hfm, hnd₂, hndm, hlenm, hacm⟩)
        (fun s j hs => by
          unfold Ix.Kernel.Env.findProj?
          have h1 : env₂.find? (Ix.Kernel.projTableName s) = env.find? (Ix.Kernel.projTableName s) := by
            rw [henv₂]
            cases hfs : env.find? (Ix.Kernel.projTableName s) with
            | some ci =>
              have := hext02E.find hfs
              rw [henv₂] at this
              exact this
            | none =>
              refine find?_append_none (new' ++ as) (fun c hc heq => ?_) hfs
              rcases List.mem_append.mp hc with hc | hc
              · obtain ⟨newW', henv₂', hnewN', -⟩ := famStep_consts hd
                have hne_eq : new' = newW' := by
                  have h1 := congrArg Env.consts (henv₂.symm.trans henv₂')
                  simpa [List.append_assoc] using h1
                subst hne_eq
                obtain ⟨ci, hci, hcn⟩ := hnewN' c hc
                exact auxKey_ne_of_isBaseKey (hblkBase ci hci) (heq.symm.trans hcn)
              · obtain ⟨ci, -, hEq | ⟨j', hEq⟩⟩ := hnames c hc
                · exact projTableName_ne_model s ci.name (heq.symm.trans hEq)
                · exact projTableName_ne_iota s ci.name j' (heq.symm.trans hEq)
          rw [h1])
        (fun s j entry _ hfp hgt => by
          obtain ⟨tbl', hftbl', hlt', rfl⟩ := Ix.Kernel.Env.findProj?_some hfp
          have hsn' : tbl'.structName = s :=
            projTableName_inj (Ix.Kernel.Semantics.Env.find?_name hftbl')
          have h1 := (mp₀.base2.proj_ok _ tbl' hftbl' j hlt').chain_isSome hgt
          simpa [ProjTable.entry, hsn'] using h1)
        ψ 0 sp.tyA_C hC_ren_res hC_men hC_noProj_blk
    have hC_denoteCh : ∀ ψ,
        denoteMeta mpCh.base2.acval envCh ψ 0 sp.cvC.type =
          denoteMeta mp₀.base2.acval env ψ 0 (sp.tyA_C.renameConsts adv.ren) := by
      intro ψ
      rw [← hC_denote₂ ψ]
      refine denoteMeta_ext_of_findProj_eq (hext2R.trans hextRCh) (fun {k ci} hk => hfind₂Ch k ci hk)
        ψ 0 sp.cvC.type hwfC₂.2.2.1 fun s j hne => ?_
      have hneR : envR.findProj? s j ≠ env₂.findProj? s j := by
        rwa [hfpCh s j] at hne
      have hs_in : ∃ p ∈ rest, p.2.structName = s := by
        by_contra hnot
        push Not at hnot
        exact hneR (hfpR s j hnot)
      obtain ⟨p, hp, rfl⟩ := hs_in
      obtain ⟨-, -, ⟨sp'⟩⟩ := hrest_all p hp
      have hs_in_bn : p.2.structName ∈ blk.map (·.name) :=
        List.mem_map.mpr ⟨sp'.ciT, (List.mem_filter.mp (List.mem_of_getElem? sp'.hT_nr)).1,
          sp'.hT_name.trans sp'.htbl_sn.symm⟩
      simpa [sp.hcvC_eq] using hC_noProj_blk p.2.structName hs_in_bn j
    -- Step 4: Install `.projInfo tbl` via `declStep_preserves_of_tower_cons` + `modeled_towerEntryLaw`!
    have hC_memCh : ConstantInfo.ctorInfo sp.cvC nP nF ∈ envCh.consts :=
      Ix.Kernel.Semantics.Env.find?_mem (hfind₂Ch _ _ sp.hfindC₂)
    have hC_mem₃ : ConstantInfo.ctorInfo sp.cvC nP nF ∈ env₃.consts :=
      Ix.Kernel.Semantics.Env.find?_mem (hfind₂₃ _ _ sp.hfindC₂)
    have hcross_C : ConsCrossAt (.projInfo tbl) sp.cvC.type := fun tbl' heq j => by
      obtain rfl := ConstantInfo.projInfo.inj heq
      exact (hnp_Ch_T j).type _ hC_memCh
    have hcb_C : ConstsBound envCh sp.cvC.type :=
      constsBound_of_constsResolve _ (mpCh.base2.wf _ hC_memCh).2.2.1
    have hneT_tbl : T ≠ Ix.Kernel.projTableName T :=
      fun h => auxKey_ne_of_isBaseKey hT_base h.symm
    have hneC_tbl : C ≠ Ix.Kernel.projTableName T := by
      have hCb : Decl.isBaseKey C = true := by
        rw [show C = Core.keyOf t (Core.cprjAddr B pos 0) from sp.htbl_ctor]
        exact Decl.isBaseKey_keyOf t _
      exact fun h => auxKey_ne_of_isBaseKey hCb h.symm
    obtain ⟨mp₃, hac₃⟩ := Ix.Kernel.Model.declStep_preserves_of_tower_cons mpCh (tbl := tbl)
      hTbl_frCh (projTableName_not_reserved T) hwf₃ hnp_Ch_T hhead (fun m₃ hac φ j hj => by
        have hC_den₃ : ∀ ψ, denoteMeta m₃.acval env₃ ψ 0 sp.cvC.type =
            denoteMeta mp₀.base2.acval env ψ 0 (sp.tyA_C.renameConsts adv.ren) := by
          intro ψ
          obtain ⟨TCa, hTCa⟩ := mpCh.type_reads _ hC_memCh ψ
          dsimp only [ConstantInfo.toConstantVal] at hTCa
          rw [hac, denoteMeta_cons_mono hTbl_frCh hcross_C ψ 0 hcb_C hTCa, ← hTCa]
          exact hC_denoteCh ψ
        have hC_reads₃ : ∀ ψ, ∃ TCa,
            denoteMeta m₃.acval env₃ ψ 0 sp.cvC.type = some TCa ∧
            (∀ ρ, WellDenotedV V ρ TCa) ∧
            (∀ ρ, interp V ρ (m₃.acval tbl.ctor ψ) ∈ˢ interp V ρ TCa) := by
          intro ψ
          obtain ⟨TCa, hTCa⟩ := mpCh.type_reads _ hC_memCh ψ
          refine ⟨TCa, ?_, mpCh.type_wellDenotedV _ hC_memCh ψ TCa hTCa, fun ρ => ?_⟩
          · rw [hac]
            exact denoteMeta_cons_mono hTbl_frCh hcross_C ψ 0 hcb_C hTCa
          · have hm := mpCh.mem_type _ hC_memCh ψ TCa hTCa ρ
            rw [Ix.Kernel.Semantics.Env.find?_name (hfind₂Ch _ _ sp.hfindC₂)] at hm
            rw [hac]
            show interp V ρ (acvalWith mpCh.base2.acval (Ix.Kernel.projTableName T) _ C ψ) ∈ˢ _
            rw [acvalWith_ne hneC_tbl]
            exact hm
        have hacT₃ : ∀ ψ, m₃.acval T ψ = mp₀.base2.acval (adv.ren T) (origVal cvTM.levelParams ψ) := by
          intro ψ
          rw [hac]
          show acvalWith mpCh.base2.acval (Ix.Kernel.projTableName T) _ T ψ = _
          rw [acvalWith_ne hneT_tbl,
            modelExt_acval_eq_of_isSome (hext2R.trans hextRCh) (by rw [sp.hfindT₂]; rfl),
            hacT₂ ψ]
          simp only [ConstantInfo.toConstantVal, sp.hcvT_eq, sp.htbl_lps]
          unfold origVal Core.posLevels
          rw [hTM_lvls]
        have hacC₃ : ∀ ψ, m₃.acval C ψ = mp₀.base2.acval (adv.ren C) (origVal cvCM.levelParams ψ) := by
          intro ψ
          rw [hac]
          show acvalWith mpCh.base2.acval (Ix.Kernel.projTableName T) _ C ψ = _
          rw [acvalWith_ne hneC_tbl,
            modelExt_acval_eq_of_isSome (hext2R.trans hextRCh) (by rw [sp.hfindC₂]; rfl),
            hacC₂ ψ]
          simp only [ConstantInfo.toConstantVal, sp.hcvC_eq, sp.htbl_lps]
          unfold origVal Core.posLevels
          rw [hCM_lvls]
        have hacChain₃ : ∀ k (hk : k < nF) (ψ : LevelParam → Nat),
            m₃.acval (Ix.Kernel.projChainKey T k) ψ = A_chain k ψ := by
          intro k hk ψ
          rw [hac]
          show acvalWith mpCh.base2.acval (Ix.Kernel.projTableName T) _
            (Ix.Kernel.projChainKey T k) ψ = _
          rw [acvalWith_ne (projChainKey_ne_projTableName T T k),
            hacCh_chains k (List.mem_range.mpr hk) ψ]
        exact modeled_towerEntryLaw (bn := []) mp₀ m₃ heqPin sp.mpf tbl sp.cvT sp.cvC {}
          sp.htbl_sn sp.htbl_ctor (by rw [sp.htbl_nP, sp.hmpf_ind])
          (by rw [sp.htbl_nF, sp.hmpf_ct]) (by rw [sp.htbl_lps, sp.hmpf_ind])
          sp.htbl_sort sp.htbl_off sp.hbodies (hfind₂₃ _ _ sp.hfindT₂) rfl
          (by rw [sp.hcvT_eq, sp.htbl_lps, sp.hmpf_ind]) (by rw [sp.hcvT_eq])
          (hfind₂₃ _ _ sp.hfindC₂) (by rw [sp.hcvC_eq, sp.htbl_lps, sp.hmpf_ind])
          (by rw [sp.hcvC_eq]) (Ix.Kernel.Env.find?_cons_self _ _)
          (fun k hk => by rw [hfindCh₃ _ _ (hfoundCh k (List.mem_range.mpr hk))]; rfl)
          hC_mem₃
          (by rw [sp.hmpf_ind]; simpa [ConstantInfo.toConstantVal, sp.hcvC_eq, sp.htbl_lps] using hwfC₂.2.1)
          (by rw [sp.hmpf_ind]; simpa [ConstantInfo.toConstantVal, sp.hcvT_eq, sp.htbl_lps] using hwfT₂.2.1)
          sp.hT_pw hC_ren_eq hC_den₃ hC_reads₃
          ⟨cvTM, mvalTM, hintTM, hfindTM, by rw [sp.hmpf_ind]; exact hTM_lvls,
            by rw [sp.hmpf_ind]; exact hTM_perm, by rw [sp.hmpf_ind]; exact hTM_ty, hacT₃⟩
          ⟨cvCM, mvalCM, hintCM, hfindCM, by rw [sp.hmpf_ind]; exact hCM_lvls,
            by rw [sp.hmpf_ind]; exact hCM_perm, hacC₃⟩
          (fun k hk ψ ρ => by rw [hacChain₃ k hk ψ]; exact (hA_spec k hk).2.2.1 ψ ρ)
          (fun k hk fdom frest rawDom fbm bsRaw remRaw fp hfp_key ψ_P ρ₀ vs_v x_v hvs_len hTM_all => by
            have h1 := (hA_spec k hk).2.2.2.2 fdom frest rawDom fbm bsRaw remRaw fp hfp_key
              ψ_P ρ₀ vs_v x_v hvs_len hTM_all
            simpa [T, nP, hacChain₃ k hk] using h1)
          φ j hj)
    -- Step 5: `ModelExt mpCh mp₃` (every `.thmInfo` in `envCh` was already in `env`, hence `NoProjAt T _`)
    have hcross_thm : ∀ cv v, ConstantInfo.thmInfo cv v ∈ envCh.consts →
        ConsCrossAt (.projInfo tbl) v := by
      intro cv v hmem tbl' heq j
      obtain rfl := ConstantInfo.projInfo.inj heq
      have hmem₀ : ConstantInfo.thmInfo cv v ∈ env.consts := by
        simp only [envCh, envR, henv₂, List.mem_append] at hmem
        rcases hmem with h1 | (h2 | ((h3 | h4) | h5))
        · obtain ⟨k, -, hk⟩ := List.mem_map.mp h1
          simp [chainAxiom] at hk
        · obtain ⟨p, -, hp⟩ := projConstsOfTables_mem_iff.mp h2
          rcases List.mem_cons.mp hp with hp | hp
          · exact nomatch hp
          · obtain ⟨k, -, hk⟩ := List.mem_map.mp hp
            simp [chainAxiom] at hk
        · exact absurd rfl (hnew'_nothm _ h3 cv v)
        · obtain ⟨cv', v', hint', heq'⟩ := (aliasGroup_defn_of_mem hg _ h4).1
          cases heq'
        · exact h5
      exact Ix.Kernel.Expr.noProjAt_of_constsResolve hT_fresh₀ v (hThm₀.resolve cv v hmem₀)
    have hextCh₃ : ModelExt mpCh mp₃ :=
      ModelExt.step ModelExt.refl hTbl_frCh hcross_thm (fun _ _ h => nomatch h) hac₃
    exact ⟨Ix.Kernel.EtaFamiliesClosed.cons_nonind hECh hTbl_frCh (fun _ _ h => nomatch h),
      mp₃, (hext2R.trans hextRCh).trans hextCh₃⟩

/-! ## Section 6: Whole-block entry point `install_block_proj_tables` -/

/-- No constant added by `DeclIndRenRunJ` is a `.thmInfo`, `.defnInfo`, or `.indInfo` with
`caps.eta = true`. -/
private theorem famStep_new_kinds {env env₂ : Env .anon} {h : KKey → KKey}
    {as blk new' : List (ConstantInfo .anon)}
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    (henv₂ : env₂ = ⟨(new' ++ as) ++ env.consts⟩) :
    ∀ c ∈ new',
      (∀ cv v, c ≠ .thmInfo cv v) ∧
      (∀ cv v hint, c ≠ .defnInfo cv v hint) ∧
      (∀ cv caps, c = .indInfo cv caps → caps.eta = false) := by
  obtain ⟨_, envM, hmemR, hrecsR⟩ := hd.shape
  have hmem_k : ∀ {J' : Ix.Kernel.Semantics.Judgements .anon} {ns : List KKey}
      {xs : List (ConstantInfo .anon)} {e₁ e₂ : Env .anon}
      {newM : List (ConstantInfo .anon)},
      Ix.Kernel.Semantics.IndMembersRunJ J' ns {} e₁ xs e₂ →
      e₂ = ⟨newM ++ e₁.consts⟩ →
      ∀ c ∈ newM, (∀ cv v, c ≠ .thmInfo cv v) ∧ (∀ cv v hint, c ≠ .defnInfo cv v hint) ∧
        (∀ cv caps, c = .indInfo cv caps → caps.eta = false) := by
    intro J' ns xs
    induction xs with
    | nil =>
      intro e₁ e₂ newM hm heq
      cases hm
      have hnil : newM = [] := by
        have := congrArg (·.consts.length) heq; simpa using this
      subst hnil; intro _ h; exact nomatch h
    | cons ci xs ih =>
      intro e₁ e₂ newM hm heq
      obtain ⟨cvA, -, hrest⟩ := hm
      cases ci with
      | indInfo _ _ =>
        obtain ⟨newM', heq', -⟩ := Decl.FamilyAlias.indMembersRunJ_consts_eq' xs hrest
        have hcat : newM = newM' ++ [.indInfo cvA {}] := List.append_cancel_right (by
          have h1 := congrArg Env.consts (heq.symm.trans heq')
          simpa [List.append_assoc] using h1)
        subst hcat
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact ih hrest heq' c hc
        · rw [List.mem_singleton.mp hc]
          exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ he => by
            injection he with _ hcaps; subst hcaps; rfl)⟩
      | ctorInfo _ nP nF =>
        obtain ⟨newM', heq', -⟩ := Decl.FamilyAlias.indMembersRunJ_consts_eq' xs hrest
        have hcat : newM = newM' ++ [.ctorInfo cvA nP nF] := List.append_cancel_right (by
          have h1 := congrArg Env.consts (heq.symm.trans heq')
          simpa [List.append_assoc] using h1)
        subst hcat
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact ih hrest heq' c hc
        · rw [List.mem_singleton.mp hc]
          exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
      | _ => exact hrest.elim
  have hrec_k : ∀ {J' : Ix.Kernel.Semantics.Judgements .anon} {ns : List KKey}
      {eM eS e₁ e₂ : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
      {newR : List (ConstantInfo .anon)},
      Ix.Kernel.Semantics.IndRecsFoldRunJ J' ns eM eS e₁ checked e₂ →
      e₂ = ⟨newR ++ e₁.consts⟩ →
      ∀ c ∈ newR, (∀ cv v, c ≠ .thmInfo cv v) ∧ (∀ cv v hint, c ≠ .defnInfo cv v hint) ∧
        (∀ cv caps, c = .indInfo cv caps → caps.eta = false) := by
    intro J' ns eM eS e₁ e₂ checked
    induction checked generalizing e₁ with
    | nil =>
      intro newR hf heq
      cases hf
      have hnil : newR = [] := by
        have := congrArg (·.consts.length) heq; simpa using this
      subst hnil; intro _ h; exact nomatch h
    | cons r rs ih =>
      intro newR hf heq
      obtain ⟨rls, -, hrest⟩ := hf
      have hrest' : Ix.Kernel.Semantics.IndRecsFoldRunJ J' ns eM eS
          ⟨[] ++ (ConstantInfo.recInfo r.1 r.2.1 r.2.2.1 rls :: e₁.consts)⟩ rs e₂ := hrest
      obtain ⟨newR', heq', -⟩ := Decl.FamilyAlias.indRecsFoldRunJ_consts_eq' rs hrest'
      simp only [List.append_nil] at heq'
      have hcat : newR = newR' ++ [.recInfo r.1 r.2.1 r.2.2.1 rls] := List.append_cancel_right (by
        have h1 := congrArg Env.consts (heq.symm.trans heq')
        simpa [List.append_assoc] using h1)
      subst hcat
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih hrest heq' c hc
      · rw [List.mem_singleton.mp hc]
        exact ⟨(fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  obtain ⟨newM, heqM, -⟩ := Decl.FamilyAlias.indMembersRunJ_consts_eq' _ hmemR
  rcases hrecsR with ⟨-, rfl⟩ | ⟨_, _, envSelf, checked, _, hfold⟩
  · have heq' : new' = newM := by
      have h1 := congrArg Env.consts (henv₂.symm.trans heqM)
      simpa [List.append_assoc] using h1
    subst heq'
    exact hmem_k hmemR heqM
  · have hfold' : Ix.Kernel.Semantics.IndRecsFoldRunJ
        (shapeJ (fun n => if (blk.map (·.name)).contains n then Ix.Kernel.auxKey n .model else n)
          (famJ h))
        (blk.map (·.name)) envM envSelf ⟨[] ++ envM.consts⟩ checked env₂ := hfold
    obtain ⟨newR, heqR, -⟩ := Decl.FamilyAlias.indRecsFoldRunJ_consts_eq' checked hfold'
    simp only [List.append_nil] at heqR
    have heq' : new' = newR ++ newM := List.append_cancel_right (by
      have h1 := congrArg Env.consts (henv₂.symm.trans (heqR.trans (by rw [heqM])))
      simpa [List.append_assoc] using h1)
    subst heq'
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hrec_k hfold heqR c hc
    · exact hmem_k hmemR heqM c hc

/-- Each member's model definition stored in the pre-block environment has the same level
parameters as the block member itself (from `MemberValRunJ`). -/
private theorem member_model_lps_eq {J : Ix.Kernel.Semantics.Judgements .anon}
    {env₁ env₂ : Env .anon} {blk : List (ConstantInfo .anon)}
    (hd : DeclIndRenRunJ J env₁ blk env₂)
    {ci : ConstantInfo .anon} (hci : ci ∈ blk)
    {cvM : ConstantVal .anon} {mval : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    (hfind : env₁.find? (Ix.Kernel.auxKey ci.name .model) = some (.defnInfo cvM mval hint)) :
    cvM.levelParams = ci.toConstantVal.levelParams := by
  obtain ⟨hsplit, envM, hmemR, hrecsR⟩ := hd.shape
  rw [hsplit] at hci
  rcases List.mem_append.mp hci with hnr | hr
  · have hgo : ∀ {J' : Ix.Kernel.Semantics.Judgements .anon} {bn : List KKey}
        {caps : Ix.Kernel.IndCaps .anon} {e₁ e₂ : Env .anon} {xs : List (ConstantInfo .anon)},
        Ix.Kernel.Semantics.IndMembersRunJ J' bn caps e₁ xs e₂ →
        ci ∈ xs →
        e₁.find? (Ix.Kernel.auxKey ci.name .model) = some (.defnInfo cvM mval hint) →
        cvM.levelParams = ci.toConstantVal.levelParams := by
      intro J' bn caps e₁ e₂ xs
      induction xs generalizing e₁ with
      | nil => intro _ hm _; exact nomatch hm
      | cons c₀ rest ih =>
        intro hm hmem hf
        obtain ⟨cvA, hmv, hrest⟩ := hm
        obtain ⟨type', hcv, hcvA, -, cvm', mval', hint', hf', hlps', -⟩ := hmv
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · have hnameA : cvA.name = ci.name := by simp only [hcvA, ConstantInfo.name]
          have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by simp only [hcvA]
          rw [hnameA, hf] at hf'
          obtain ⟨hcv_eq, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hf')
          rw [hcv_eq, hlps', hlpsA]
        · have hfr0 : e₁.find? cvA.name = none := by
            rw [show cvA.name = c₀.name by simp only [hcvA, ConstantInfo.name]]
            exact Option.isNone_iff_eq_none.mp hcv.1
          cases hc₀ : c₀ with
          | indInfo _ _ =>
            rw [hc₀] at hrest
            exact ih hrest hmem'
              (Ix.Kernel.Env.find?_cons_of_fresh (c := .indInfo cvA caps) hfr0 hf)
          | ctorInfo _ nP nF =>
            rw [hc₀] at hrest
            exact ih hrest hmem'
              (Ix.Kernel.Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF) hfr0 hf)
          | _ => rw [hc₀] at hrest; exact hrest.elim
    exact hgo hmemR hnr hfind
  · rcases hrecsR with ⟨hnil, -⟩ | ⟨_, _, envSelf, checked, hprov, -⟩
    · rw [hnil] at hr; exact nomatch hr
    · have hfindM : envM.find? (Ix.Kernel.auxKey ci.name .model) = some (.defnInfo cvM mval hint) :=
        Ix.Kernel.Semantics.indMembersRun_mono _ hmemR _ _ hfind
      have hgo : ∀ {J' : Ix.Kernel.Semantics.Judgements .anon} {bn : List KKey}
          {e₁ eS : Env .anon} {xs : List (ConstantInfo .anon)}
          {chk : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
          Ix.Kernel.Semantics.ProvisionRecsRunJ J' bn e₁ xs eS chk →
          ci ∈ xs →
          e₁.find? (Ix.Kernel.auxKey ci.name .model) = some (.defnInfo cvM mval hint) →
          cvM.levelParams = ci.toConstantVal.levelParams := by
        intro J' bn e₁ eS xs
        induction xs generalizing e₁ with
        | nil => intro _ _ hm _; exact nomatch hm
        | cons c₀ rest ih =>
          intro chk hp hmem hf
          obtain ⟨cvA, mI, rP, rls, rest', -, hmv, hrest, -⟩ := hp
          obtain ⟨type', hcv, hcvA, -, cvm', mval', hint', hf', hlps', -⟩ := hmv
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · have hnameA : cvA.name = ci.name := by simp only [hcvA, ConstantInfo.name]
            have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by simp only [hcvA]
            rw [hnameA, hf] at hf'
            obtain ⟨hcv_eq, -, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hf')
            rw [hcv_eq, hlps', hlpsA]
          · have hfr0 : e₁.find? cvA.name = none := by
              rw [show cvA.name = c₀.name by simp only [hcvA, ConstantInfo.name]]
              exact Option.isNone_iff_eq_none.mp hcv.1
            exact ih hrest hmem'
              (Ix.Kernel.Env.find?_cons_of_fresh (c := .recInfo cvA mI rP []) hfr0 hf)
      exact hgo hprov hr hfindM

set_option maxHeartbeats 1600000 in
/-- **Whole-block modeled projection-table installation.** Installs all eligible 1-constructor,
0-index, never-zero-sort members' chain axioms and `.projInfo` tables (`off := 2`) on top of
`env₂`, preserving every fold invariant and producing `BlockProjTableData`. -/
theorem install_block_proj_tables
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env env₂ : Env .anon} {Reg : NativeFam .anon → Prop}
    {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {blk as : List (ConstantInfo .anon)}
    {h : KKey → KKey} {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (htwf : t.wf = true) (ht : t.check = .ok ())
    (hB : FamBlockRecord E₀ B cb ms)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hg : AliasGroup env h as)
    (hnames : ∀ a ∈ as, ∃ ci ∈ blk,
      a.name = Ix.Kernel.auxKey ci.name .model ∨
        ∃ j, a.name = Decl.FamilyAlias.iotaKey ci.name j)
    (htgt : ∀ ci ∈ blk, h (Ix.Kernel.auxKey ci.name .model) = adv.ren ci.name)
    (hroots : ∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂)
    (hI : SelectedInstalled blk tys rhsss env₂)
    (hS₀ : Decl.FoldStoreInv env)
    (hAr₀ : Ix.Kernel.Model.StoreArR env)
    (hTL₀ : Ix.Kernel.ThmLevels env)
    (haux₀ : Decl.AuxRootSynced env)
    (heqPin : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hbasis : ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hreg : FamRegistryWith.{u} FormerOpenTraceAt t E env Reg)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (Core.keyOf t x) = none)
    (hkey : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (Core.keyOf t x))
    (bpf : BlockProjFacts t E₀ E env B cb ms blk tys adv.ren) :
    BlockProjInstallResult.{u} t env env₂ Reg B ms bpf.elig
      (blockProjConsts t env₂ B ms bpf.elig) := by
  have hblkBase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_keyOf t x
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    Decl.isBaseKey_iff_nonAuxKey.mp (hblkBase ci hci)
  have hext02E : EnvExt env env₂ :=
    (Decl.FamilyAlias.AliasGroup.envExt hg).trans (Ix.Kernel.Semantics.declIndRenRunJ_envExt hd)
  have hS₂ : Decl.FoldStoreInv env₂ :=
    Decl.FamilyAlias.foldStoreInv_famStep hg hreads.2.2.2 hna hd hS₀
  have hAr₂ : Ix.Kernel.Model.StoreArR env₂ :=
    Decl.FamilyAlias.familyKeepsStoreAr env env₂ h as blk hg hd hAr₀
  have hTL₂ : Ix.Kernel.ThmLevels env₂ :=
    Decl.FamilyAlias.thmLevels_famStep hg hd hTL₀
  have haux₂ : Decl.AuxRootSynced env₂ :=
    Decl.FamilyAlias.auxRootSynced_famStep haux₀ hna hroots hd
  obtain ⟨new', henv₂_raw, hnewN, -⟩ := famStep_consts hd
  have henv₂ : env₂ = ⟨(new' ++ as) ++ env.consts⟩ := henv₂_raw
  have hnew'_k := famStep_new_kinds hd henv₂
  let entries := blockProjEntries t env₂ B ms bpf.elig
  let pcs := blockProjConsts t env₂ B ms bpf.elig
  let env₃ : Env .anon := ⟨pcs ++ env₂.consts⟩
  -- Properties of `entries`
  have hentries_all : ∀ p ∈ entries, p.1 < ms.size ∧ bpf.elig p.1 = true ∧
      Nonempty (EligibleTableSpec t E₀ E env env₂ B ms blk tys adv.ren p.1 p.2) := by
    intro ⟨pos, tbl⟩ hmem
    simp only [entries, blockProjEntries, List.mem_filterMap, List.mem_range,
      Option.map_eq_some_iff] at hmem
    obtain ⟨pos', hpos', tbl', hpt, heq⟩ := hmem
    obtain ⟨hpeq, hteq'⟩ := Prod.mk.inj heq
    subst hpeq; subst hteq'
    have helig : bpf.elig pos' = true := by
      unfold posProjTable? at hpt
      cases hb : bpf.elig pos' with
      | true => rfl
      | false => rw [hb] at hpt; simp at hpt
    obtain ⟨tbl₀, hpt₀, hsp₀⟩ :=
      posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf hpos' helig
    have hteq : tbl₀ = tbl' := Option.some.inj (hpt₀.symm.trans hpt)
    subst hteq
    exact ⟨hpos', helig, hsp₀⟩
  have hentries_nd : (entries.map (·.2.structName)).Nodup := by
    -- `List.range ms.size` is nodup and `iprjKey_inj_of_block` makes `pos ↦ tbl.structName` injective!
    have hgo : ∀ (ps : List Nat), ps.Nodup → (∀ pos ∈ ps, pos < ms.size) →
        ((ps.filterMap fun pos => (posProjTable? t env₂ B bpf.elig pos).map fun tbl => (pos, tbl)).map
          (·.2.structName)).Nodup := by
      intro ps
      induction ps with
      | nil => intro _ _; exact List.nodup_nil
      | cons pos ps ih =>
        intro hnd hlt
        rw [List.nodup_cons] at hnd
        have hih := ih hnd.2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp))
        simp only [List.filterMap_cons]
        cases hpt : posProjTable? t env₂ B bpf.elig pos with
        | none => exact hih
        | some tbl =>
          simp only [Option.map_some, List.map_cons, List.nodup_cons]
          refine ⟨fun hin => ?_, hih⟩
          obtain ⟨q, hq, hqsn⟩ := List.mem_map.mp hin
          simp only [List.mem_filterMap, Option.map_eq_some_iff] at hq
          obtain ⟨pos', hpos'_mem, tbl', hpt', heq⟩ := hq
          subst heq
          have helig1 : bpf.elig pos = true := by
            unfold posProjTable? at hpt
            cases hb : bpf.elig pos with | true => rfl | false => rw [hb] at hpt; simp at hpt
          have helig2 : bpf.elig pos' = true := by
            unfold posProjTable? at hpt'
            cases hb : bpf.elig pos' with | true => rfl | false => rw [hb] at hpt'; simp at hpt'
          obtain ⟨tbl₁, hpt₁, ⟨sp₁⟩⟩ :=
            posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf (hlt pos List.mem_cons_self) helig1
          obtain ⟨tbl₂, hpt₂, ⟨sp₂⟩⟩ :=
            posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf
              (hlt pos' (List.mem_cons_of_mem _ hpos'_mem)) helig2
          have e1 : tbl₁ = tbl := Option.some.inj (hpt₁.symm.trans hpt)
          have e2 : tbl₂ = tbl' := Option.some.inj (hpt₂.symm.trans hpt')
          subst e1 e2
          have hsn_eq : Core.keyOf t (Core.iprjAddr B pos') = Core.keyOf t (Core.iprjAddr B pos) := by
            rw [← sp₂.htbl_sn, ← sp₁.htbl_sn]; exact hqsn
          have hpp : pos' = pos := iprjKey_inj_of_block htwf hB bpf.hms_size
            (hlt pos' (List.mem_cons_of_mem _ hpos'_mem)) (hlt pos List.mem_cons_self) hsn_eq
          subst hpp
          exact hnd.1 hpos'_mem
    exact hgo (List.range ms.size) List.nodup_range (fun _ h => List.mem_range.mp h)
  -- Run `fold_tables_pure`
  obtain ⟨hext03, hS₃, hAr₃, hfind₂₃, hnp₃, htbls₃, hfp₃, hfr₂₃⟩ :=
    fold_tables_pure htwf hB hreads hF hg hnames hd hI hS₀ hS₂ hAr₂ haux₀ hfresh hkey bpf
      hext02E hblkBase entries hentries_nd hentries_all
  -- Shape of every `c ∈ pcs`
  have hkindAndName : ∀ c ∈ pcs,
      ∃ pos < ms.size, bpf.elig pos = true ∧
        ((∃ tbl, c = .projInfo tbl ∧
            c.name = Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B pos)) ∧
            tbl.structName = Core.keyOf t (Core.iprjAddr B pos) ∧
            tbl.structSort.isNeverZero = true) ∨
          (∃ j, c = chainAxiom (Core.keyOf t (Core.iprjAddr B pos)) j ∧
            c.name = Ix.Kernel.projChainKey (Core.keyOf t (Core.iprjAddr B pos)) j)) := by
    intro c hc
    obtain ⟨⟨pos, tbl⟩, hp, hcm⟩ := projConstsOfTables_mem_iff.mp hc
    obtain ⟨hpos, helig, ⟨sp⟩⟩ := hentries_all (pos, tbl) hp
    refine ⟨pos, hpos, helig, ?_⟩
    rcases List.mem_cons.mp hcm with rfl | hcm
    · exact Or.inl ⟨tbl, rfl, by rw [projInfo_name, sp.htbl_sn], sp.htbl_sn,
        by rw [sp.htbl_sort]; exact sp.mpf.hT_sort_nz⟩
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hcm
      exact Or.inr ⟨j, by rw [sp.htbl_sn], by rw [chainAxiom_name, sp.htbl_sn]⟩
  have hshape : ∀ c ∈ pcs,
      ∃ pos < ms.size, bpf.elig pos = true ∧
        ((∃ tbl, c = .projInfo tbl ∧
            tbl.structName = Core.keyOf t (Core.iprjAddr B pos) ∧
            tbl.structSort.isNeverZero = true) ∨
          ∃ j, c = chainAxiom (Core.keyOf t (Core.iprjAddr B pos)) j) := fun c hc => by
    obtain ⟨pos, hpos, helig, ⟨tbl, rfl, -, hsn, hnz⟩ | ⟨j, rfl, -⟩⟩ := hkindAndName c hc
    · exact ⟨pos, hpos, helig, Or.inl ⟨tbl, rfl, hsn, hnz⟩⟩
    · exact ⟨pos, hpos, helig, Or.inr ⟨j, rfl⟩⟩
  have hfr₀₃ : ∀ c ∈ pcs, env.find? c.name = none := fun c hc => by
    cases hf : env.find? c.name with
    | none => rfl
    | some ci =>
      have h1 := hext02E.find hf
      rw [hfr₂₃ c hc] at h1
      exact nomatch h1
  -- All constants in `pcs ++ new' ++ as` satisfy `NotThm`, `NotBaseDefn`, `NoEtaInd`!
  have hall_new_env₃ : env₃ = ⟨(pcs ++ new' ++ as) ++ env.consts⟩ := by
    simp only [env₃, henv₂, List.append_assoc]
  have hnew_sat : ∀ (Q : ConstantInfo .anon → Prop),
      (∀ c ∈ pcs ++ new' ++ as, Q c) → Ix.Kernel.Model.NewSat env env₃ Q := by
    intro Q hQ n ci hf
    rw [hall_new_env₃] at hf
    rcases find?_append_cases_local (pcs ++ new' ++ as) hf with hm | ho
    · exact Or.inr (hQ ci hm)
    · exact Or.inl ho
  have hNoThm : Ix.Kernel.Model.NewSat env env₃ Ix.Kernel.Model.NotThm :=
    hnew_sat _ fun c hc cv v heq => by
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨_, -, -, ⟨_, rfl, -⟩ | ⟨_, rfl⟩⟩ := hshape c hc <;> exact nomatch heq
        · exact (hnew'_k c hc).1 cv v heq
      · obtain ⟨⟨_, _, _, h⟩, -⟩ := aliasGroup_defn_of_mem hg c hc
        rw [heq] at h; exact nomatch h
  have hNoBaseDefn : Ix.Kernel.Model.NewSat env env₃ Decl.NotBaseDefn :=
    hnew_sat _ fun c hc hna cv v hint heq => by
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨_, -, -, ⟨_, rfl, -⟩ | ⟨_, rfl⟩⟩ := hshape c hc <;> exact nomatch heq
        · exact (hnew'_k c hc).2.1 cv v hint heq
      · obtain ⟨n, d, haux⟩ := aliasGroup_name_aux hg c hc
        rw [haux] at hna
        exact absurd rfl (hna n d)
  have hNoEta : Ix.Kernel.Model.NewSat env env₃ Decl.NoEtaInd :=
    hnew_sat _ fun c hc cv caps heq => by
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨_, -, -, ⟨_, rfl, -⟩ | ⟨_, rfl⟩⟩ := hshape c hc <;> exact nomatch heq
        · exact (hnew'_k c hc).2.2 cv caps heq
      · obtain ⟨⟨_, _, _, h⟩, -⟩ := aliasGroup_defn_of_mem hg c hc
        rw [heq] at h; exact nomatch h
  have hNoRec_pcs : ∀ n cv mI rP rules, env₃.find? n = some (.recInfo cv mI rP rules) →
      env₂.find? n = none → False := by
    intro n cv mI rP rules hf hn
    rcases find?_append_cases_local pcs hf with hm | ho
    · obtain ⟨_, -, -, ⟨_, h, -⟩ | ⟨_, h⟩⟩ := hshape _ hm <;> cases h
    · rw [hn] at ho; exact nomatch ho
  -- `TableBodies env₃` and `StrongEnvProps env₃`
  have htb₃ : Ix.Kernel.Model.TableBodies env₃ := by
    refine Ix.Kernel.Model.tableBodies_step (fun {k x} hk => hfind₂₃ k x hk) hS₂.strongProps.1 ?_
    intro n tbl hf hn
    rcases find?_append_cases_local pcs hf with hm | ho
    · obtain ⟨p, hp, hcm⟩ := projConstsOfTables_mem_iff.mp hm
      rcases List.mem_cons.mp hcm with heq | hcm
      · obtain rfl := ConstantInfo.projInfo.inj heq
        obtain ⟨-, -, ⟨sp⟩⟩ := hentries_all p hp
        exact ⟨sp.cvC, hfind₂₃ _ _ sp.hfindC₂, sp.hbodies,
          ⟨List.replicate p.2.numFields .zero, List.length_replicate, sp.htbl_guards⟩⟩
      · obtain ⟨j, -, hj⟩ := List.mem_map.mp hcm
        simp [chainAxiom] at hj
    · rw [hn] at ho; exact nomatch ho
  have hstrong₃ : Decl.StrongEnvProps env₃ := by
    refine Decl.strongEnvProps_step (fun {k x} hk => hfind₂₃ k x hk) hS₂.strongProps htb₃ ?_
    intro n tbl hf hn
    rcases find?_append_cases_local pcs hf with hm | ho
    · obtain ⟨p, hp, hcm⟩ := projConstsOfTables_mem_iff.mp hm
      rcases List.mem_cons.mp hcm with heq | hcm
      · obtain rfl := ConstantInfo.projInfo.inj heq
        obtain ⟨-, -, ⟨sp⟩⟩ := hentries_all p hp
        exact Or.inl (by rw [sp.htbl_ctor]; exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t _))
      · obtain ⟨j, -, hj⟩ := List.mem_map.mp hcm
        simp [chainAxiom] at hj
    · rw [hn] at ho; exact nomatch ho
  have heta₃ := Decl.etaShape_step_noEta hext03 hS₀.etaCtorStored hS₀.etaShape hNoEta
  have hFoldStore₃ : Decl.FoldStoreInv env₃ :=
    { store := hS₃
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext03 hS₀.thmTyped hNoThm
      defnTyped := Decl.defnTyped_step_noBaseDefn hext03 hS₀.defnTyped hNoBaseDefn
      recK := Ix.Kernel.Model.recK_step hS₂.store hS₂.recK (fun {k x} hk => hfind₂₃ k x hk)
        (fun n cv mI rP rls hf hn => (hNoRec_pcs n cv mI rP rls hf hn).elim)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext03 hS₀.etaTowers
        (hnew_sat Ix.Kernel.Model.TowerFree fun c hc cv caps heq => by
          rcases List.mem_append.mp hc with hc | hc
          · rcases List.mem_append.mp hc with hc | hc
            · obtain ⟨_, -, -, ⟨_, rfl, -⟩ | ⟨_, rfl⟩⟩ := hshape c hc <;> exact nomatch heq
            · exact fun htrue => by rw [(hnew'_k c hc).2.2 cv caps heq] at htrue; exact nomatch htrue
          · obtain ⟨⟨_, _, _, h⟩, -⟩ := aliasGroup_defn_of_mem hg c hc
            rw [heq] at h; exact nomatch h)
      strongProps := hstrong₃
      recShape := Ix.Kernel.Model.recShape_step hS₂.store hS₂.recShape (fun {k x} hk => hfind₂₃ k x hk)
        (fun n cv mI rP rls hf hn => (hNoRec_pcs n cv mI rP rls hf hn).elim)
      etaCtorStored := heta₃.1
      etaShape := heta₃.2 }
  -- `ThmLevels env₃`
  have hTL₃ : Ix.Kernel.ThmLevels env₃ := by
    intro n cv v hf
    rcases find?_append_cases_local pcs hf with hm | ho
    · obtain ⟨_, -, -, ⟨_, h, -⟩ | ⟨_, h⟩⟩ := hshape _ hm <;> cases h
    · exact hTL₂ n cv v ho
  -- `AuxRootSynced env₃`
  have haux₃ : Decl.AuxRootSynced env₃ := by
    intro k hk
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rcases find?_append_cases_local pcs hci with hm | ho
    · have hkn : ci.name = k := Ix.Kernel.Semantics.Env.find?_name hci
      obtain ⟨pos, hpos, helig, ⟨tbl, rfl, hsn, -⟩ | ⟨j, rfl⟩⟩ := hshape ci hm
      · have hbase : k.base = Core.keyOf t (Core.iprjAddr B pos) := by
          rw [← hkn]
          exact projTableName_base (by rw [hsn]; exact Decl.isBaseKey_keyOf t _) |>.trans hsn
        rw [hbase]
        obtain ⟨tbl₀, hpt₀, ⟨sp₀⟩⟩ :=
          posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf hpos helig
        dsimp only [env₃, pcs, blockProjConsts]
        rw [← sp₀.htbl_sn, hfind₂₃ _ _ sp₀.hfindT₂]; rfl
      · have hbase : k.base = Core.keyOf t (Core.iprjAddr B pos) := by
          rw [← hkn]
          exact projChainKey_base (Decl.isBaseKey_keyOf t _) j
        rw [hbase]
        obtain ⟨tbl₀, hpt₀, ⟨sp₀⟩⟩ :=
          posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf hpos helig
        dsimp only [env₃, pcs, blockProjConsts]
        rw [← sp₀.htbl_sn, hfind₂₃ _ _ sp₀.hfindT₂]; rfl
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (haux₂ k (by rw [ho]; rfl))
      dsimp only [env₃, pcs, blockProjConsts]
      rw [hfind₂₃ _ _ hc']; rfl
  -- `BlockProjTableData`
  have hTableData : BlockProjTableData t env₃ pcs B ms bpf.elig :=
    { atEligible := fun pos hpos helig => by
        obtain ⟨tbl, hpt, ⟨sp⟩⟩ := posProjTable?_spec htwf hB hreads hF hg hd hI hS₀ bpf hpos helig
        have hp_mem : (pos, tbl) ∈ entries := by
          simp only [entries, blockProjEntries, List.mem_filterMap, List.mem_range,
            Option.map_eq_some_iff]
          exact ⟨pos, hpos, tbl, hpt, rfl⟩
        obtain ⟨hft₃, hth₃⟩ := htbls₃ (pos, tbl) hp_mem
        have hposC_eq : Core.posOf (List.range sp.mpf.ct.lvls.toNat) sp.tyA_C = sp.tyA_C := by
          rw [sp.hmpf_ct, show sp.ct.lvls.toNat = sp.ind.lvls.toNat by
            rw [← sp.hmpf_ind, ← sp.hmpf_ct]; exact sp.mpf.hcnl]
          exact posOf_range_eq_prep sp.ind.lvls.toNat sp.tyA_C
        have hstripC : sp.cvC.type.stripPis (sp.ind.params.toNat + sp.ct.fields.toNat) =
            some (sp.mpf.bsC, sp.mpf.cret) := by
          have h1 := sp.mpf.hC_ret
          rw [hposC_eq, sp.hmpf_ind, sp.hmpf_ct] at h1
          rw [sp.hcvC_eq]
          exact h1
        have hnz : tbl.structSort.isNeverZero = true := by
          rw [sp.htbl_sort]; exact sp.mpf.hT_sort_nz
        have hzer : Ix.Kernel.Level.zeronessOf tbl.structSort = .never :=
          zeronessOf_eq_never_of_pos (eval_pos_of_isNeverZero hnz)
        exact ⟨sp.ind, sp.ct, sp.cvC, tbl,
          sp.hmpf_ind ▸ sp.mpf.hms,
          sp.hmpf_ind ▸ sp.hmpf_ct ▸ sp.mpf.hct,
          sp.hmpf_ind ▸ sp.mpf.hni0,
          sp.hmpf_ind ▸ sp.mpf.hnc1,
          sp.hmpf_ind ▸ sp.hmpf_ct ▸ sp.mpf.hcnp,
          sp.hmpf_ct ▸ sp.mpf.hnf_pos,
          by rw [← sp.htbl_ctor, ← sp.htbl_nP, ← sp.htbl_nF]; exact hfind₂₃ _ _ sp.hfindC₂,
          by rw [← sp.htbl_sn]; exact hft₃,
          sp.htbl_sn, sp.htbl_ctor, sp.htbl_nP, sp.htbl_nF,
          by rw [sp.hcvC_eq],
          hnz,
          by rw [← sp.htbl_nF]; exact hth₃,
          by rw [← sp.htbl_nP, ← sp.htbl_nF]; exact sp.hbodies,
          ⟨List.replicate sp.ct.fields.toNat .zero, List.length_replicate,
            by rw [← sp.htbl_nP, ← sp.htbl_nF]; exact sp.htbl_guards⟩,
          ⟨sp.mpf.bsC, sp.mpf.cret, hstripC, fun bm hbm => by rw [hzer]; exact sp.hC_pw bm hbm⟩,
          by rw [← sp.htbl_nP, ← sp.htbl_nF]; exact sp.hC_tele⟩
      projTablesNeverZero := fun tbl hmem => by
        obtain ⟨_, -, -, ⟨tbl', heq, -, hnz⟩ | ⟨_, h⟩⟩ := hshape (.projInfo tbl) hmem
        · obtain rfl := ConstantInfo.projInfo.inj heq; exact hnz
        · simp [chainAxiom] at h
      projTablesPos := fun tbl hmem => by
        obtain ⟨pos, hpos, helig, ⟨tbl', heq, hsn, -⟩ | ⟨_, h⟩⟩ := hshape (.projInfo tbl) hmem
        · obtain rfl := ConstantInfo.projInfo.inj heq; exact ⟨pos, hpos, helig, hsn⟩
        · simp [chainAxiom] at h }
  -- `EnvModelN` transport for any `V`
  have hModel : ∀ (V : Type u) [SetTheory V],
      EnvModelN V .verified env Reg → EnvModelN V .verified env₃ Reg := by
    intro V _ hM₀
    obtain ⟨⟨mp₀, hThm₀, hN₀⟩, hE₀⟩ := hM₀
    obtain ⟨mp₁, hext01, hE₁, hA₁, hac_as⟩ := envModelM_aliasGroup mp₀ hE₀ hg
    obtain ⟨hE₂, mp₂, hIA₂, hext12⟩ :=
      declIndRenJ_acval_anon (Decl.FamilyAlias.judgeFrames_famJ h)
        (fun m => Decl.FamilyAlias.judgeSound_famJ_of m h) mp₁ hE₁ hd
    have hext02M : ModelExt mp₀ mp₂ := hext01.trans hext12
    -- Build `hblk_map` from `hIA₂` + `hac_as` + `htgt` + `hF.members`
    have hblk_map : ∀ k ∈ blk.map (·.name), ∀ ci₂, env₂.find? k = some ci₂ →
        ∃ (cvm : ConstantVal .anon) (mval : KExpr) (hint : Ix.Kernel.ReducibilityHint),
          env.find? (adv.ren k) = some (.defnInfo cvm mval hint) ∧
          ci₂.toConstantVal.levelParams.Nodup ∧
          cvm.levelParams.Nodup ∧
          cvm.levelParams.length = ci₂.toConstantVal.levelParams.length ∧
          ∀ ψ, mp₂.base2.acval k ψ =
            mp₀.base2.acval (adv.ren k) (Level.substFn ψ cvm.levelParams
              (ci₂.toConstantVal.levelParams.map .param)) := by
      intro k hk ci₂ hf₂
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
      obtain ⟨idx, hidx⟩ := List.getElem?_of_mem hci
      have hlen_tys := Decl.FamilyAlias.MembersFacts.length_eq blk tys hF.members
      have hidx_lt : idx < tys.length := by
        rw [← hlen_tys]; exact (List.getElem?_eq_some_iff.mp hidx).1
      have hmf := Decl.FamilyAlias.MembersFacts.get hF.members hidx
        (List.getElem?_eq_getElem hidx_lt)
      obtain ⟨cvm, mval, hint, hfm, hperm_m, -⟩ := hmf.model
      -- `auxKey ci.name .model` is stored in `⟨as ++ env.consts⟩` as an alias targeting `adv.ren ci.name`!
      have hmod_base : (Ix.Kernel.auxKey ci.name .model).base = ci.name := by
        show (Ix.Kernel.Key.aux ci.name .model).base = ci.name
        simp only [Ix.Kernel.Key.base]
        exact Decl.base_of_isBaseKey (hblkBase ci hci)
      have hmod_fr₀ : env.find? (Ix.Kernel.auxKey ci.name .model) = none :=
        haux₀.fresh_of_base_none (by rw [hmod_base]; exact blk_fresh_in_env hg hd ci hci)
      have hne_mod : h (Ix.Kernel.auxKey ci.name .model) ≠ Ix.Kernel.auxKey ci.name .model := by
        rw [htgt ci hci]
        intro heq
        rw [heq, hmod_fr₀] at hfm; exact nomatch hfm
      obtain ⟨lpsA, tyA', hintA, _, hciA, -, -, -⟩ := hA₁ (Ix.Kernel.auxKey ci.name .model) hne_mod
      rw [htgt ci hci] at hciA
      have hmod_some :
          ((⟨as ++ env.consts⟩ : Env .anon).find? (Ix.Kernel.auxKey ci.name .model)).isSome = true := by
        rw [hciA]; rfl
      have hlen_split : blk.length = (nonrecsOf blk).length + (recsOf blk).length := by
        conv => lhs; rw [hF.split]
        exact List.length_append
      have hrecs_len : (recsOf blk).length = rhsss.length := by
        have hgo : ∀ {rs : List (ConstantInfo .anon)} {ts : List KExpr}
            {rss : List (List KExpr)} {thss : List (List KKey)},
            Decl.FamilyAlias.RecsFacts env adv.ren blk tys rs ts rss thss →
            rs.length = rss.length := by
          intro rs ts rss thss
          induction rs generalizing ts rss thss with
          | nil =>
            cases ts <;> cases rss <;> cases thss <;> intro hr <;> first | rfl | exact hr.elim
          | cons r rs ih =>
            cases r with
            | recInfo cv mI rP rules =>
              cases ts <;> cases rss <;> cases thss <;> intro hr <;>
                first | exact hr.elim | (simp only [List.length_cons]; exact congrArg Nat.succ (ih hr.2))
            | _ => intro hr; exact hr.elim
        exact hgo hF.recs
      have hci₂_lps : ci₂.toConstantVal.levelParams = ci.toConstantVal.levelParams := by
        have hci' : ci ∈ nonrecsOf blk ++ recsOf blk := by rw [← hF.split]; exact hci
        rcases List.mem_append.mp hci' with hnr | hr
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem hnr
          have hj_lt : j < tys.length := by
            have := (List.getElem?_eq_some_iff.mp hj).1; omega
          have hst := hI.nonrecs j ci _ hj (List.getElem?_eq_getElem hj_lt)
          rw [hf₂] at hst
          obtain rfl := Option.some.inj hst.symm
          cases hci_c : ci with
          | indInfo cv _ | ctorInfo cv _ _ => rfl
          | _ =>
            have hk := List.all_eq_true.mp hF.kinds ci hnr
            rw [hci_c] at hk
            simp [Decl.FamilyAlias.isTypeOrCtor] at hk
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
          cases hci_c : ci with
          | recInfo cv mI rP rules =>
            rw [hci_c] at hj
            have hj_lt : (nonrecsOf blk).length + j < tys.length := by
              have := (List.getElem?_eq_some_iff.mp hj).1; omega
            have hj_r : j < rhsss.length := by
              have := (List.getElem?_eq_some_iff.mp hj).1; omega
            obtain ⟨rls', hst, -, -⟩ := hI.recs j cv mI rP rules _ _ hj
              (List.getElem?_eq_getElem hj_lt) (List.getElem?_eq_getElem hj_r)
            rw [hci_c] at hf₂
            dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hf₂
            rw [hf₂] at hst
            obtain rfl := Option.some.inj hst.symm
            rfl
          | _ =>
            have := (List.mem_filter.mp hr).2
            rw [hci_c] at this; exact nomatch this
      have hlpsA_eq : lpsA = ci₂.toConstantVal.levelParams := by
        have h1 := member_model_lps_eq hd hci hciA
        exact h1.trans hci₂_lps.symm
      have hnd_ci₂ : ci₂.toConstantVal.levelParams.Nodup := by
        rw [hci₂_lps]
        exact hmf.perm.nodup_iff.mpr List.nodup_range
      have hnd_cvm : cvm.levelParams.Nodup :=
        hperm_m.nodup_iff.mpr List.nodup_range
      have hlen_cvm : cvm.levelParams.length = ci₂.toConstantVal.levelParams.length := by
        rw [hci₂_lps, hperm_m.length_eq, List.length_range]
      refine ⟨cvm, mval, hint, hfm, hnd_ci₂, hnd_cvm, hlen_cvm, fun ψ => ?_⟩
      have hbn_c : (blk.map (·.name)).contains ci.name = true := by
        simpa using List.mem_map_of_mem hci
      have h1 : mp₂.base2.acval ci.name ψ = mp₂.base2.acval (Ix.Kernel.auxKey ci.name .model) ψ :=
        (hIA₂ ci.name hbn_c ci₂ hf₂ ψ).symm
      have h2 : mp₂.base2.acval (Ix.Kernel.auxKey ci.name .model) ψ =
          mp₁.base2.acval (Ix.Kernel.auxKey ci.name .model) ψ :=
        modelExt_acval_eq_of_isSome hext12 hmod_some ψ
      have h3 : mp₁.base2.acval (Ix.Kernel.auxKey ci.name .model) ψ =
          mp₀.base2.acval (adv.ren ci.name)
            (Level.substFn ψ cvm.levelParams (lpsA.map .param)) :=
        hac_as (Ix.Kernel.auxKey ci.name .model) lpsA tyA' (adv.ren ci.name) hintA
          (.defnInfo cvm mval hint) hciA hmod_fr₀ hfm ψ
      rw [h1, h2, h3, hlpsA_eq]
    obtain ⟨hE₃, mp₃, hext23⟩ :=
      fold_tables_model htwf ht hB hreads hF hg hnames htgt hd henv₂
        (fun c hc => (hnew'_k c hc).1) hI hS₀ hS₂ hAr₂ haux₀ hfresh hkey heqPin hbasis hreg bpf
        hext02E hblkBase mp₀ hThm₀ hN₀ mp₂ hE₂ hext02M hblk_map entries hentries_nd hentries_all
    have hext03M : ModelExt mp₀ mp₃ := hext02M.trans hext23
    exact ⟨⟨mp₃, ThmValOk.of_ext hext03M hThm₀, fun fam hf => (hN₀ fam hf).ext hext03M⟩, hE₃⟩
  exact
    { nodup := projConstsOfTables_nodup hentries_nd
      freshPrefix := hfr₀₃
      freshEnv₂ := hfr₂₃
      kindAndName := hkindAndName
      envExt := hext03
      find₂ := fun {k ci} hk => hfind₂₃ k ci hk
      model := hModel
      foldStore := hFoldStore₃
      storeArR := hAr₃
      thmLevels := hTL₃
      auxRoot := haux₃
      tableData := hTableData }

end IxVM.Refinement.Typing.FamilyAlias
