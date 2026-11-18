import IxVMRefinement.Assembly.FoldClause
import IxVMRefinement.Assembly.NativeAtGlue
import IxVMRefinement.Assembly.TypingDefnLimKeyed
import IxVMRefinement.Assembly.TypingRecLateNativeAux

/-! # The steps that keep the fold's clause

Each kind of accepted declaration step keeps `FoldClause` (`Assembly/FoldClause.lean`). The IxC
half is kept by IxC's own lemmas from the step's judgement: `EnvModelN.declRunJ` and
`EnvModelN.late` for the model, `storeFacts_declRunJA`, `storeFacts_lateTa` and the route's
`StoreArR` lemma for the store facts. The rest is kept from what the step reads off its run.

* A value step (a definition, a theorem, an axiom at the key of a 32-byte address, along its
  declaration judgement): `keepsValuesJ_famRegistry`, `keepsValuesKeyed_foldExtra`,
  `foldExtra_cons_thm`; the skeleton's step for a definition record at either role context,
  `unitStep_defn_foldExtra`.
* A native block's install: `foldExtra_install` (the general form), `foldExtra_nativeNoRec` (a
  former declared at its telescope, from `NativeNoRecFacts`), `FoldClauseWith.nativeAt` (a
  former declared at a definition, from `NativeAtFacts`). `NativeAtFacts.famStage` reads the
  telescope constant's facts, the stored former's level parameters and the telescope off the
  former's stage, with no relation between the stored former and the telescope constant.
* A late recursor for a registered family: `FoldClauseWith.lateRec` (the clause at the
  environment with the recursor, with no detour through the prefix invariant),
  `late_companions_read` (the companions, from the family read off the parent's record),
  `unitStep_recLate_foldExtra` (the skeleton's step, at any limit).
* Two facts the late recursor's specifications read of the telescope constant, from the clause:
  `storeArR_lateRec_read` and `late_tele_genScoped`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key RecRule)
open Ix.Kernel.Semantics (NativeFam NativeFamStored DeclRunJ IndRoutesJ DeclNativeRecLateRunJ
  SumIndRunJ Judgements)
open Ix.Kernel.Model (rulesJ EnvModelN EnvModelT ArRes StoreArR)

/-! ## Value steps -/

/-- **A declaration step that stores one constant that is no inductive type keeps the
registry** (IxC's `EnvModelN.declRunJ`). -/
theorem FamRegistry.cons_declRunJ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {ci : ConstantInfo .anon}
    {d : Ix.Kernel.Declaration .anon} (h : FamRegistry.{u} L t E env)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨ci :: env.consts⟩)
    (hfresh : env.find? ci.name = none)
    (hnt : ∀ T : Key .anon, ci.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, ci ≠ .indInfo cv caps) :
    FamRegistry.{u} L t E ⟨ci :: env.consts⟩ := by
  obtain ⟨Reg, hR⟩ := h
  refine ⟨Reg, hR.step hL (fun V _ hm => Ix.Kernel.Model.EnvModelN.declRunJ V hm hd)
    (Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)) ?_⟩
  intro P cm ip cv caps hf hold
  rw [find_ind_cons_old hind hf] at hold
  cases hold

/-- **The registry is kept by a value constant along its declaration step.** -/
theorem keepsValuesJ_famRegistry {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    KeepsValuesJ (FamRegistry.{u} L t E) :=
  fun _ _ _ h hfresh hval hnt hd => h.cons_declRunJ hL hd hfresh hnt hval.not_ind

/-- **A value step at the key of a 32-byte address keeps the part of the clause beside the
prefix invariant.** -/
theorem keepsValuesKeyed_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable}
    (htwf : t.wf = true) (E : Ixon.Env) : KeepsValuesKeyed t (FoldExtra.{u} L t E) :=
  ((((keepsValuesJ_famRegistry hL t E).keyed t).and (keepsValuesKeyed_hashKeyed htwf)).and
    (keepsValuesKeyed_auxRoot t)).and (keepsValuesKeyed_lvClauses t)

/-- **A theorem stored at the key of a 32-byte address, along its declaration step, keeps the
part of the clause beside the prefix invariant.** -/
theorem foldExtra_cons_thm {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    {v : Ix.Kernel.Expr .anon} {d : Ix.Kernel.Declaration .anon}
    (h : FoldExtra.{u} L t E env) (hfresh : env.find? cv.name = none)
    (hnt : ∀ T : Key .anon, cv.name ≠ Ix.Kernel.projTableName T)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨.thmInfo cv v :: env.consts⟩)
    (hkey : ∃ x : _root_.Address, cv.name = keyOf t x ∧ x.hash.size = 32) :
    FoldExtra.{u} L t E ⟨.thmInfo cv v :: env.consts⟩ :=
  keepsValuesKeyed_foldExtra hL htwf E env (.thmInfo cv v) d h hfresh
    (Or.inr (Or.inl ⟨cv, v, rfl⟩)) hnt hd hkey

/-- **`UnitStep` for a standalone definition record, keeping the clause**, at the limit of
either role context. -/
theorem unitStep_defn_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hkind : d.kind = .defn)
    (hchk : Claim.CheckedLimAt calls bAddr t A lim)
    (hkey : Decl.KeyFree (keyOf t A))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  exact unitStep_defn_lim_keyed ht hS hst hc hinfo hlogic hkind hchk hkey hinert hcover
    (keepsValuesKeyed_foldExtra hL htwf E)

section Steps

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {E : Ixon.Env} {lim : Option Nat} {env env₂ : Ix.Kernel.Env .anon}
  {Reg : NativeFam .anon → Prop}

/-! ## A step that registers no family -/

/-- **A step that registers no family keeps the part of the clause beside the prefix
invariant**: the general form, for a step on any route. The step extends the model at every
registry; it extends the environment; a family it stores new, under no basis name, is one the
circuit does not treat as native at the store; and the keys, the roots and the level clauses
hold at the new environment. This is what the step of a mutual or nested family hands over. -/
theorem foldExtra_step (hL : LinkLaws L) (h : FoldExtra.{u} L t E env)
    (hmodel : ∀ (Reg : NativeFam .anon → Prop) (V : Type u) [Ix.Kernel.SetTheory V],
      EnvModelN V .verified env Reg → EnvModelN V .verified env₂ Reg)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true)
    (hkeys₂ : HashKeyed t env₂) (haux₂ : Decl.AuxRootSynced env₂) (hlv₂ : LvClauses env₂) :
    FoldExtra.{u} L t E env₂ := by
  obtain ⟨⟨⟨⟨Reg, hR⟩, -⟩, -⟩, -⟩ := h
  exact ⟨⟨⟨⟨Reg, hR.step hL (hmodel Reg) hext hnew⟩, hkeys₂⟩, haux₂⟩, hlv₂⟩

/-! ## A native block's install -/

/-- **A native block's install keeps the part of the clause beside the prefix invariant**,
registering its family: the general form, from the step's registering model extension, the
family read off the store at the new environment, the one new inductive type, and the keys,
roots and level clauses at the new environment. -/
theorem foldExtra_install (hL : LinkLaws L) {fam : NativeFam .anon}
    (h : FoldExtra.{u} L t E env)
    (hmodel : ∀ (Reg : NativeFam .anon → Prop) (V : Type u) [Ix.Kernel.SetTheory V],
      EnvModelN V .verified env Reg → EnvModelN V .verified env₂ (fun f => Reg f ∨ f = fam))
    (hext : Ix.Kernel.EnvExt env env₂) (hread : FamRead L t E env₂ fam)
    (hnewInd : ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, ∀ cv caps, ci = .indInfo cv caps → cv = fam.cvS)
    (hkeys₂ : HashKeyed t env₂) (haux₂ : Decl.AuxRootSynced env₂) (hlv₂ : LvClauses env₂) :
    FoldExtra.{u} L t E env₂ := by
  obtain ⟨⟨⟨⟨Reg, hR⟩, -⟩, -⟩, -⟩ := h
  exact ⟨⟨⟨⟨_, hR.install hL (hmodel Reg) hext hread hnewInd⟩, hkeys₂⟩, haux₂⟩, hlv₂⟩

/-- **The install of a block whose former is declared at its telescope keeps the part of the
clause beside the prefix invariant.** The family's reading with the telescope equality
(`lateFamAt_of_install`) is read without it; the roots and the level clauses are the
install's. -/
theorem foldExtra_nativeNoRec (hL : LinkLaws L) {blk : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : FoldExtra.{u} L t E env) (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hwf : Ix.Kernel.EnvWF env₂) (hat : LateFamAt t E env₂ fam)
    (hrh : FamIxonRetHead t E fam) (hnp : BlockFamCtorNoProj fam)
    (hkeys₂ : HashKeyed t env₂) : FoldExtra.{u} L t E env₂ := by
  have hlv₂ : LvClauses env₂ := NativeNoRecFacts.lvClauses hpin hfacts h.2
  have haux₂ : Decl.AuxRootSynced env₂ := NativeNoRecFacts.auxRootSynced hpin hna hfacts h.1.2
  exact foldExtra_install hL h (fun Reg V _ hm => hfacts.register V hm) hfacts.envExt
    (FamRead.of_late hL hat hwf hlv₂.2 hrh hnp) hfacts.newInd hkeys₂ haux₂ hlv₂

/-- **The only inductive type the install at a given index count stores new is the family's
stored former.** -/
theorem NativeAtFacts.newInd {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, ∀ cv caps, ci = .indInfo cv caps → cv = fam.cvS := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := h
  subst hfam
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have hmem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps], ∀ cv caps', ci = .indInfo cv caps' → cv = cvS := by
    intro ci hci cv caps' he
    rcases List.mem_append.mp hci with hct | hind
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hct)
      cases he
    · rw [List.mem_singleton.mp hind] at he
      injection he with h1 _
      exact h1.symm
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, -⟩
  · refine ⟨_, ?_, hmem⟩
    rw [heq]
    exact congrArg Ix.Kernel.Env.mk hc
  · refine ⟨.projInfo tbl :: ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps]), ?_, ?_⟩
    · rw [heq, hc]
      rfl
    · intro ci hci cv caps' he
      rcases List.mem_cons.mp hci with rfl | hold
      · cases he
      · exact hmem ci hold cv caps' he

/-- **What IxC's former stage gives of the family an install at a given index count names**,
at the environment after the install: the telescope constant's facts, the stored former's level
parameters, and the telescope into the family's sort. The stored former and the telescope
constant are not related here; at a former declared at a definition they differ. -/
theorem NativeAtFacts.famStage {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    TeleChecked env₂ fam ∧ fam.cvS.levelParams = fam.p.cvT.levelParams ∧
      ∃ bs, fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (bs, .sort fam.p.resSort) := by
  have hext := h.envExt
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, -⟩ := h
  subst hfam
  have hlps := Ix.Kernel.Model.storedFormer_lps hInd hp
  obtain ⟨har, hfv, hlb, hlp⟩ := sumIndRunJ_tele hInd
  obtain ⟨cvTa₀, s, bs, cvS', -, -, hstrip, -, hp₁, -⟩ := hInd
  subst hp₁
  have hpT : p.cvT = p₀.cvT := by rw [hp]; rfl
  have hpnP : p.nP = p₀.nP := by rw [hp]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hp]; rfl
  have hpres : p.resSort = s := by rw [hp]; rfl
  refine ⟨⟨har.mono hext.find, hfv, hlb, ?_⟩, hlps, bs, ?_⟩
  · show cvTa.type.allLevelParamsDefined p.cvT.levelParams = true
    rw [hpT]
    exact hlp
  · show cvTa.type.stripPis (p.nP + p.nIdx) = some (bs, .sort p.resSort)
    rw [hpnP, hpnIdx, hpres]
    exact hstrip

/-- **The install of a block whose former is declared at a definition keeps the clause**,
registering its family. From the clause before and IxC's record of the install
(`NativeAtFacts`): the model step registers the family (`EnvModelN.nativeAt`); the level
clauses are IxC's along the routes (`thmLevels_declRunJA`, `storeArR_nativeAtRunJ`); the prefix
invariant is `PrefixInv.nativeAt`. What the step reads off its run: the load contract and η
stability at the new environment, that the new keys resolve and are keys of 32-byte addresses
or of none, and the family read off the store there. -/
theorem FoldClauseWith.nativeAt (hL : LinkLaws L) {blk : List (ConstantInfo .anon)}
    {nP nIdx : Nat} {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : FoldClauseWith.{u} L t E lim env Reg)
    (hfacts : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ Core.unresolvedKey)
    (hloads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env₂, t, lim⟩))
    (heta : Decl.EtaStable env₂) (hkeys₂ : HashKeyed t env₂)
    (hread : FamRead L t E env₂ fam) :
    FoldClauseWith.{u} L t E lim env₂ (fun f => Reg f ∨ f = fam) := by
  have hinv₂ : Decl.PrefixInv.{u} E t lim env₂ :=
    PrefixInv.nativeAt h.prefixInv hfacts hpin hna hres hloads heta
  have hd := hfacts.declRunJ hpin
  exact FoldClauseWith.of_prefix hinv₂
    (h.registry.install hL (fun V _ hm => hfacts.register V hm) hfacts.envExt hread
      hfacts.newInd)
    hkeys₂ (Decl.auxRootSynced_step_declRunJA h.auxRoot hna hd)
    ⟨Ix.Kernel.Model.thmLevels_declRunJA h.thmLevels hd,
      Ix.Kernel.Model.storeArR_nativeAtRunJ h.storeArR hfacts.runJ⟩

/-! ## A late recursor for a registered family -/

/-- **The late recursor's step keeps `StoreArR`** at a family read off the store: the telescope
constant's type is arity-correct at the step's environment whether or not it is the stored
former (`Ix.Kernel.Model.storeArR_nativeRecLateTa`). -/
theorem storeArR_lateRec_read {fam : NativeFam .anon} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (RecRule .anon)} (hfam : FamRead L t E env fam) (hA : StoreArR env)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂) : StoreArR env₂ :=
  Ix.Kernel.Model.storeArR_nativeRecLateTa hA hfam.tele.arRes hfam.lps hrun

/-- **The telescope constant's type is scoped at the environment**, at the family's own level
parameters: what the recursor generators read of it, from the former's stage. -/
theorem late_tele_genScoped {fam : NativeFam .anon} (hfam : FamRead L t E env fam) :
    Decl.GenScoped env fam.p.cvT.levelParams 0 fam.cvTa.type :=
  ⟨hfam.tele.bounded, hfam.tele.levels, hfam.tele.arRes.res, hfam.tele.closed,
    defnAritiesOk_of_arOk hfam.tele.arRes.ar⟩

/-- **The companions after the late step**, from the family read off the parent's record and
the step's relation. The recursor's major premise is the family, whose key is the parent's; its
rules are at the family's constructors in order, whose keys are the constructor projections of
the parent's member; a rule fires and its constructor builds the family by the stored
constructor's residual. -/
theorem late_companions_read {P : _root_.Address} {ip : Ixon.InductiveProj}
    {cm : Ixon.Constant} {fam : NativeFam .anon} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (RecRule .anon)} {cn : ConstantInfo .anon}
    (ht : t.check = .ok ()) (hcomp : Decl.CoreCompanions ⟨E, env, t, lim⟩)
    (hm : FamReadAt L t E env P ip fam) (hcm : Ix.Cert.recordAt E P = some cm)
    (hcmi : cm.info = .iPrj ip)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩) :
    Decl.CoreCompanions ⟨E, ⟨cn :: env.consts⟩, t, lim⟩ := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨hat, hTP, cb, ms, ind, -, -, -, -, -, -, hnames⟩ := hm
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hst, -, -, hRec, henv⟩ := hrun
  obtain ⟨hfT, hctor, hlenA, hk⟩ := hst.atRec hpR
  obtain ⟨hnR, -, hfR, hshR⟩ := hRec.recursor
  have hfreshR : env.find? cvRa.name = none := by rw [hnR]; exact hfR
  injection henv with h1
  injection h1 with hcn _
  subst hcn
  obtain ⟨bs, B, m, hmaj⟩ := hRec.majorOf ⟨fam.cvS, _, hfT⟩ hk hlenA
  have hdom : Core.piDomAt pR.majorIdx cvRa.type = some (Ix.Kernel.structFamI pR.cvT.name
      pR.cvT.levelParams pR.nP pR.nIdx (pR.ctors.length + 1) 0) :=
    (Decl.piDomAt_eq_some_iff _ _ _).mpr ⟨bs, B, m, hmaj⟩
  have hT : pR.cvT.name = Core.keyOf t P := by
    rw [hpR]
    exact hTP.trans (LoadedReads.keyOf_eq t P).symm
  have hhead : ∀ (T : Key .anon) (us : List Core.KLevel),
      (Core.piDomAt pR.majorIdx cvRa.type).map (·.getAppFn) = some (.const T us) →
      T = pR.cvT.name := by
    intro T us h
    rw [hdom] at h
    have h2 : (Ix.Kernel.structFamI pR.cvT.name pR.cvT.levelParams pR.nP pR.nIdx
        (pR.ctors.length + 1) 0).getAppFn = .const T us := Option.some.inj h
    rw [Ix.Kernel.Semantics.structFamI_getAppFn] at h2
    injection h2 with hT' _
    exact hT'.symm
  have hparent : ∀ (p : _root_.Address) (us : List Core.KLevel),
      (Core.piDomAt pR.majorIdx cvRa.type).map (·.getAppFn) =
        some (.const (Core.keyOf t p) us) → p = P := by
    intro p us h
    exact Core.keyOf_inj htwf ((hhead _ us h).trans hT)
  have hrule : ∀ r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix
      cvRa.type fam.ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal .anon × Nat),
        fam.ctorsA[j]? = some cA ∧ r.ctor = cA.1.name ∧ r.ctorParams = pR.nP := by
    intro r hr
    obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
    exact ⟨j, cA, hj, rfl, rfl⟩
  have hctorAt : ∀ (r : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat),
      r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
        fam.ctorsA rhss →
      (⟨.recInfo cvRa pR.majorIdx pR.rulePrefix (Ix.Kernel.sumRules env.find? cvRa.name pR.nP
        pR.majorIdx pR.rulePrefix cvRa.type fam.ctorsA rhss) :: env.consts⟩ :
          Ix.Kernel.Env .anon).find? r.ctor = some (.ctorInfo cvj nP nF) →
      ∃ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA ∧
        cvj = cA.1 ∧ nP = pR.nP ∧ r.ctorParams = pR.nP := by
    intro r cvj nP nF hr hc
    obtain ⟨j, cA, hj, hctorEq, hcp⟩ := hrule r hr
    obtain ⟨hfC, -, -⟩ := hctor j cA hj
    have hc' : (⟨.recInfo cvRa pR.majorIdx pR.rulePrefix (Ix.Kernel.sumRules env.find? cvRa.name
        pR.nP pR.majorIdx pR.rulePrefix cvRa.type fam.ctorsA rhss) :: env.consts⟩ :
          Ix.Kernel.Env .anon).find? cA.1.name = some (.ctorInfo cA.1 pR.nP cA.2) :=
      Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfC
    rw [← hctorEq, hc] at hc'
    obtain ⟨rfl, rfl, -⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hc')
    exact ⟨j, cA, hj, rfl, rfl, hcp⟩
  have hmr : pR.majorIdx - pR.rulePrefix = pR.nIdx :=
    Nat.add_sub_cancel_left pR.rulePrefix pR.nIdx
  refine CoreCompanions.cons_rec (c := ⟨E, env, t, lim⟩) hcomp hfreshR
    (fun T => by rw [hnR]; exact Ix.Kernel.Semantics.ne_projTableName_of_shape hshR T)
    (fun p us _ h => ⟨cm, by rw [hparent p us h]; exact hcm⟩) ⟨?_, ?_⟩ ?_ ?_
  · exact List.Nodup.sublist sumRules_ctors_sublist hat.nodup
  · intro p cm' ip' us h hcm' hcmi' j rl hrl
    have hp := hparent p us h
    subst hp
    rw [hcm] at hcm'
    have hcc : cm = cm' := Option.some.inj hcm'
    subst hcc
    rw [hcmi] at hcmi'
    have hii : ip = ip' := Ixon.ConstantInfo.iPrj.inj hcmi'
    subst hii
    obtain ⟨cA, hcA, hrc⟩ := sumRules_ctor_getElem? hrl
    rw [hrc]
    exact hnames j cA hcA
  · intro rl cvj nP nF hrl hfire hc
    obtain ⟨j, cA, hj, rfl, rfl, -⟩ := hctorAt rl cvj nP nF hrl hc
    obtain ⟨-, hlps, -⟩ := hctor j cA hj
    refine ⟨_, pR.cvT.name, hdom, ?_, ?_, ?_⟩
    · rw [Ix.Kernel.Semantics.structFamI_getAppFn, hlps]
    · have hps : Ix.Kernel.structPsAt (md := .anon) (0 + (pR.ctors.length + 1) + pR.nIdx) pR.nP =
          (List.range pR.nP).map (fun k => Ix.Kernel.Expr.bvar (pR.majorIdx - 1 - k)) := by
        unfold Ix.Kernel.structPsAt
        refine List.map_congr_left fun k _ => ?_
        congr 1
        show _ = pR.nP + 1 + pR.ctors.length + pR.nIdx - 1 - k
        omega
      rw [Ix.Kernel.Semantics.structFamI_getAppArgs,
        List.take_left' Ix.Kernel.Semantics.length_structPsAt, hps]
    · rw [hmr]
      exact Ix.Kernel.Semantics.structFamI_args_drop
  · intro rl cvj nP nF T us hrl hc hdom'
    obtain ⟨j, cA, hj, rfl, rfl, -⟩ := hctorAt rl cvj nP nF hrl hc
    obtain ⟨-, -, cbs, es, hres, -⟩ := hctor j cA hj
    rw [hhead T us hdom']
    exact ⟨_, Ix.Kernel.Model.family_of_residual hres⟩

/-- **The clause at the environment with the recursor.** From the clause before, a registered
family, the step's relation with the recursor `cn` in front, `cn` at the key of a 32-byte
address, the companions at the new environment and the recursor's reload. The model step is
IxC's `EnvModelN.late`; the eight store facts are `storeFacts_lateTa`, at the telescope
constant's facts the clause holds for the family; no field of the clause is taken through the
prefix invariant. -/
theorem FoldClauseWith.lateRec (hL : LinkLaws L) {fam : NativeFam .anon}
    {cvR : ConstantVal .anon} {mI rP : Nat} {rules : List (RecRule .anon)}
    {cn : ConstantInfo .anon} {a₀ : _root_.Address}
    (h : FoldClauseWith.{u} L t E lim env Reg) (hfam : Reg fam)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩)
    (hname : cn.name = Core.keyOf t a₀) (hsz : a₀.hash.size = 32)
    (hcomp : Decl.CoreCompanions ⟨E, ⟨cn :: env.consts⟩, t, lim⟩)
    (hreload : Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn) :
    FoldClauseWith.{u} L t E lim ⟨cn :: env.consts⟩ Reg := by
  obtain ⟨hfresh, hnt, -, cv, a, b, rs, hcn⟩ := late_head hrun
  have hind : ∀ cv' caps, cn ≠ .indInfo cv' caps := by
    intro cv' caps h'
    rw [hcn] at h'
    cases h'
  have hctor : ∀ cv' nP nF, cn ≠ .ctorInfo cv' nP nF := by
    intro cv' nP nF h'
    rw [hcn] at h'
    cases h'
  have hproj : ∀ tbl, cn ≠ .projInfo tbl := by
    intro tbl h'
    rw [hcn] at h'
    cases h'
  have hext : Ix.Kernel.EnvExt env ⟨cn :: env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hat := h.fams fam hfam
  obtain ⟨hSI, hRS, hRK, hTT, hET, -, hTL, hAR, -⟩ :=
    Ix.Kernel.Model.storeFacts_lateTa hrun h.store h.recShape h.recK h.thmTyped h.etaTowers
      h.strong.1 h.thmLevels h.storeArR hat.tele.arRes hat.lps
  have heta := Decl.etaShape_step_noEta hext h.etaCtorStored h.etaShape
    (Ix.Kernel.Model.nativeRecLate_newSat (Q := Decl.NoEtaInd)
      (fun _ _ _ _ _ _ h => nomatch h) hrun)
  have hstrong : Decl.StrongEnvProps ⟨cn :: env.consts⟩ :=
    Decl.strongEnvProps_step_noProj hext.find h.strong
      (Ix.Kernel.Model.nativeRecLate_newSat (Q := Ix.Kernel.Model.NotProj)
        (fun _ _ _ _ _ h => nomatch h) hrun)
  have hbase : cn.name.base = cn.name := by
    rw [hname]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t a₀)
  have hne : cn.name ≠ Core.unresolvedKey := by
    rw [hname]
    exact Core.Resolved.ne
  have hkeys : HashKeyed t ⟨cn :: env.consts⟩ :=
    HashKeyed.append (new := [cn]) h.tableWf h.hashKeyed fun ci hci => by
      obtain rfl := List.mem_singleton.mp hci
      exact Or.inl ⟨a₀, hname, hsz⟩
  have hunres : (⟨cn :: env.consts⟩ : Ix.Kernel.Env .anon).find? Core.unresolvedKey = none := by
    rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]
    exact h.unresolved
  exact
    { model := fun V _ => Ix.Kernel.Model.EnvModelN.late V (h.model V) hfam hrun
      store := hSI
      recShape := hRS
      recK := hRK
      thmTyped := hTT
      etaTowers := hET
      thmLevels := hTL
      storeArR := hAR
      strong := hstrong
      fams := fun f hf => (h.fams f hf).ext hL hext
      complete := fun P cm ip cv' caps hf hr hcm hinfo hnat =>
        h.complete P cm ip cv' caps (find_ind_cons_old hind hf) hr hcm hinfo hnat
      hashKeyed := hkeys
      auxRoot := h.auxRoot.cons_of_root_stored (Or.inl hbase)
      etaCtorStored := heta.1
      etaShape := heta.2
      etaStable := h.etaStable.cons_value hfresh hnt hind hctor
      unresolved := hunres
      tableWf := h.tableWf
      companions := hcomp
      loads := Decl.storedLoads_cons_value (c := ⟨E, env, t, lim⟩) h.loads hname hfresh hnt
        hind hctor hproj h.etaStable hreload }

end Steps

/-- **`UnitStep` for a standalone recursor record of a native family, keeping the clause**, at
any limit. The parent's predicate `Q` is produced by the first interface; the second receives
the level clauses at the step's environment and the family the registry holds at the parent,
read off the parent's record. The registered family need not have its telescope constant
stored. -/
theorem unitStep_recLate_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop)
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc) (hsz : A.hash.size = 32)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip ∧ Q P)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → LvClauses env →
      RecParent t E env P ip → Q P → FamReadAt L t E env P ip fam →
      RecLateOut t E₀ E A env fam) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  have hC : FoldClauseWith.{u} L t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨P, ip, hpar, hQ⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hread⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep hlv ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ hQ hread
  have hcomp := late_companions_read ht hinv.companions hread hcm hcmi hrun
  have hC' : FoldClauseWith.{u} L t E lim ⟨cn :: env.consts⟩ Reg :=
    hC.lateRec hL hReg hrun (hname.trans (LoadedReads.keyOf_eq t A).symm) hsz hcomp hreload
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], List.nodup_singleton _, ?_, hC'.prefixInv, hC'.extra, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

end IxVM.Refinement.Typing
