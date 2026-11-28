module

public import IxCK.Kernel.Model.Inductives.NativeAt
public import IxCK.Kernel.Model.StoreArLate
public import IxCK.Kernel.Model.ThmLevels

@[expose] public section

/-!
# A recursor for a family installed at a given index count

The route `NativeAtRunJ` (`Model/Inductives/NativeAt.lean`) installs a one-type block without
its recursor record at an index count given from outside, which also covers a former declared
at a definition: the stored former `cvS` is then the declared constant and the telescope
constant `cvTa` the later stages read is another constant, checked from scratch
(`SumIndRunJ`'s second branch, `FormerStoredJ`'s right disjunct). `EnvModelN.nativeAt`
registers the family `⟨p, cvS, cvTa, ctorsA⟩`.

The late recursor's step applies to such a family as it is: neither the step
(`DeclNativeRecLateRunJ`), nor the family's data (`NativeFamOk`, `NativeFamAt`), nor the model
step (`declNativeRecLateJ`, `EnvModelN.late`), nor the six store facts
(`storeFacts_declNativeRecLateRunJ`), nor `thmLevels_late` relate `cvS` and `cvTa` or read a
recogniser. The one late-step theorem that does is `storeArR_nativeRecLate`, which reads the
telescope constant's arity off the stored former (`htele : fam.cvTa = fam.cvS`).

* `EnvModelN.nativeAtLate`: the install registered by `EnvModelN.nativeAt`, then the late step
  for the registered family, keeps the fold invariant with the family registered.
* `storeArR_nativeRecLateTa`: the late step keeps `StoreArR` given the telescope constant's type
  arity-correct and resolving at the step's environment (`htty`), in place of `htele`;
  `storeArR_nativeRecLate` is its instance at `htele`. The former's stage gives `htty`
  (`arRes_sumIndRunJ`, the telescope constant is checked), the lookups keep it (`ArRes.mono`),
  and the stored former has the family's level parameters (`storedFormer_lps`).
* Along a step over `IndRoutesAJ`: `ThmLevels` (`thmLevels_declRunJA`), `StoreArR` at the route
  (`storeArR_nativeAtRunJ`), the seven store facts (`storeFacts_declRunJA`) and their fold over a
  run (`storeFacts_declsRunJA`); along the late step at a family whose telescope constant is
  arity-correct: the eight facts (`storeFacts_lateTa`); across the install and the late step:
  `storeFacts_nativeAtLate`.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.LevelRen
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (CheckMode Env Key Expr Level ConstantInfo ConstantVal RecFieldKind IndCaps
  NativeParts InductiveShape RecRule Declaration EtaFamiliesClosed EnvExt ThmLevels)

universe w

/-! ## The model -/

/-- **The install at a given index count, then the late recursor for its family**: the install
registers the family (`EnvModelN.nativeAt`, over its own hypotheses), and the late step for the
registered family keeps the registry (`EnvModelN.late`). The stored former `cvS` and the
telescope constant `cvTa` are the install's, unrelated beyond the former's stage. -/
theorem EnvModelN.nativeAtLate {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ env₃ : Env md}
    {block : List (ConstantInfo md)} {nPd nIdx : Nat} {p₀ : NativeParts md}
    {R : NativeFam md → Prop} (h : EnvModelN V μ env R)
    (hdp : nativePartsAt? nPd nIdx block = some p₀)
    {isRec : Bool} {cvS cvTa : ConstantVal md} {caps : IndCaps md} {p₁ : InductiveShape md}
    {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {kinds : List (List RecFieldKind)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    (hnd₀ : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ rulesJ env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩
      ⟨.indInfo cvS caps :: env.consts⟩
      p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors ctorsA
      sortss)
    (hK : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams
      p.nP p.nIdx ctorsA = .ok kinds)
    (hcaps : Ix.Kernel.nativeCaps p = Ix.Kernel.nativeCapsAt p₁ isRec)
    (hopT2 : Ix.Kernel.openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest))
    (hsorts : FieldSortsJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩ true false p.resSort p.nP
      (tfvs.drop p.nP) [] p.nIdx isorts)
    (hFOk : Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true)
    (hFR : FormerReadJ ⟨.indInfo cvS caps :: env.consts⟩ p cvTa ctorsA)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂)
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hrun : DeclNativeRecLateRunJ rulesJ env₂ ⟨p, cvS, cvTa, ctorsA⟩ cvR mI rP rules env₃) :
    EnvModelN V μ env₃ (fun f => R f ∨ f = ⟨p, cvS, cvTa, ctorsA⟩) :=
  EnvModelN.late V
    (EnvModelN.nativeAt V h hdp hnd₀ hInd hp hCtors hK hcaps hopT2 hsorts hFOk hFR hTbl)
    (Or.inr rfl) hrun

/-! ## The telescope constant's arity -/

/-- **The telescope constant's type is arity-correct and resolves** where the former's stage
runs: the stage checks it (the declared former, or a constant checked from scratch). -/
theorem arRes_sumIndRunJ {env envI : Env md} {sh p' : InductiveShape md}
    {capsOf : InductiveShape md → IndCaps md} {cvTa : ConstantVal md}
    (h : SumIndRunJ rulesJ env sh capsOf envI cvTa p') : ArRes env cvTa.type := by
  obtain ⟨_, _, -, -, hck, -⟩ := h.shape
  exact arRes_of_cvCheck hck

/-- **The stored former carries the family's level parameters**, at the completed record: the
former's stage stores the telescope constant or the checked declared former, both at the
declared level parameters. -/
theorem storedFormer_lps {env : Env md} {p₀ : NativeParts md} {isRec : Bool}
    {cvS cvTa : ConstantVal md} {caps : IndCaps md} {p₁ : InductiveShape md}
    {p : NativeParts md} {kinds : List (List RecFieldKind)}
    (hInd : SumIndRunJ rulesJ env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds) :
    cvS.levelParams = p.cvT.levelParams := by
  have hF := hInd.former
  obtain ⟨_, s, -, -, -, hp₁, ⟨cvS', henv, hSt⟩, -⟩ := hInd.shape
  injection henv with h1
  injection h1 with h2
  injection h2 with h3
  subst h3 hp hp₁
  exact (StoredFormer.name_lps ⟨hF.1, hF.2.1⟩ hSt).2.trans hF.2.1

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySimpa false in
/-- **A late recursor's install keeps `StoreArR`**, where the family's telescope constant has an
arity-correct, resolving type at the step's environment (`htty`) and the stored former carries
the family's level parameters. `storeArR_nativeRecLate` is the instance where the telescope
constant is the stored former, whose type `StoreArR` makes arity-correct; at a former declared
at a definition the telescope constant is not stored, and `htty` comes from its check
(`arRes_sumIndRunJ`) along the lookups (`ArRes.mono`). The proof is that theorem's with `htty`
taken as given. -/
theorem storeArR_nativeRecLateTa {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)} (h : StoreArR env)
    (htty : ArRes env fam.cvTa.type) (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂) : StoreArR env₂ := by
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hFS, -, -, hRec, rfl⟩ := hrun
  obtain ⟨cvRg, rhsG, ⟨-, -, cvRi, recTy, hck, hty, -, hres, -, -, -, hrules, hcvRg⟩, hst⟩ := hRec
  -- the family's parts at `env`
  have hFormer := hFS.former
  have hT : ArRes env (.const fam.p.cvT.name (fam.p.cvT.levelParams.map .param)) := by
    refine ⟨arOk_const_of (fun ci hci => ?_), by simp [Expr.constsResolve, hFormer]⟩
    rw [hFormer] at hci
    obtain rfl := Option.some.inj hci
    simp [hlps, Ix.Kernel.ConstantInfo.toConstantVal]
  have hcs : ∀ c ∈ Ix.Kernel.nativeCtors4 fam.ctorsA fam.p.kinds,
      ArRes env (.const c.1 (fam.p.cvT.levelParams.map .param)) ∧ ArRes env c.2.2.1 := by
    intro c hc
    obtain ⟨cA, hcA, h1, h2⟩ := mem_nativeCtors4 hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨hfC, hlC, -⟩ := hFS.ctor j cA hj
    have har : Expr.arOk env (.const cA.1.name (fam.p.cvT.levelParams.map .param)) = true :=
      arOk_const_of (fun ci hci => by
        rw [hfC] at hci
        obtain rfl := Option.some.inj hci
        simp [hlC, Ix.Kernel.ConstantInfo.toConstantVal])
    have hres' : (Expr.const cA.1.name (fam.p.cvT.levelParams.map .param)).constsResolve env =
        true := by
      simp [Expr.constsResolve, hfC]
    rw [h1, h2]
    exact ⟨⟨har, hres'⟩, (h.const hfC).type⟩
  -- the recursor's name is fresh
  have hfresh : env.find? pR.cvR.name = none := hck.fresh
  -- the generated rules at the environment holding the recursor
  have hpT : pR.cvT = fam.p.cvT := by rw [hpR]; rfl
  have hpK : pR.kinds = fam.p.kinds := by rw [hpR]; rfl
  let cvG : ConstantVal md := ⟨pR.cvR.name, pR.cvR.levelParams, recTy⟩
  let envR : Env md := ⟨.recInfo cvG pR.majorIdx pR.rulePrefix [] :: env.consts⟩
  have hR : ∀ {e : Expr md}, ArRes env e → ArRes envR e := fun he =>
    he.mono (find?_cons_fresh_ext (c := .recInfo cvG pR.majorIdx pR.rulePrefix []) hfresh)
  have hTR : ArP envR (.const pR.cvT.name (pR.cvT.levelParams.map .param)) := by
    rw [hpT]; exact (arP_iff _).mpr (hR hT).ar
  have httyR : ArP envR fam.cvTa.type := (arP_iff _).mpr (hR htty).ar
  have hcsR : Ctors4Ar envR pR.cvT.levelParams (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds) := by
    intro c hc
    rw [hpK] at hc
    rw [hpT]
    exact ⟨(arP_iff _).mpr (hR (hcs c hc).1).ar, (arP_iff _).mpr (hR (hcs c hc).2).ar⟩
  have hrecR : ArP envR (.const pR.cvR.name (pR.cvR.levelParams.map .param)) := by
    intro ci hci
    have hs : envR.find? pR.cvR.name = some (.recInfo cvG pR.majorIdx pR.rulePrefix []) :=
      Ix.Kernel.Env.find?_cons_self (ConstantInfo.recInfo cvG pR.majorIdx pR.rulePrefix []) env
    rw [hs] at hci
    obtain rfl := Option.some.inj hci
    simp [cvG, Ix.Kernel.ConstantInfo.toConstantVal]
  have hG : ∀ r ∈ rhsG, ArRes envR r ∧ r.hasFvar = false := by
    intro r hr
    obtain ⟨hlen, hall⟩ := Ix.Kernel.checkNativeRules_inv hrules
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
    have hi' : i < (Ix.Kernel.nativeCtors4 fam.ctorsA pR.kinds).length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
    obtain ⟨rhs, hrhs, hgen, -, hres', -, hfv⟩ := hall i hi'
    rw [hi] at hrhs
    obtain rfl := Option.some.inj hrhs
    exact ⟨⟨(arP_iff _).mp (arP_structRecRhsR hTR httyR hcsR hrecR hgen), hres'⟩, hfv⟩
  -- both ways of storing the recursor
  have hstore : ArRes envR cvRa.type ∧ (∀ r ∈ rhss, ArRes envR r) ∧
      cvRa.name = pR.cvR.name ∧ cvRa.levelParams = pR.cvR.levelParams := by
    rcases hst with ⟨rfl, rfl⟩ | ⟨cvRi', hck', rfl, -, hW, hlet, -, -, -, -⟩
    · subst hcvRg
      refine ⟨⟨(arP_iff _).mp (arP_structRecTyR hTR httyR hcsR hty), ?_⟩,
        fun r hr => (hG r hr).1, rfl, rfl⟩
      exact Ix.Kernel.Expr.constsResolve_mono hres
    · refine ⟨hR (show ArRes env cvRi'.type from arRes_of_cvCheck hck'), fun r hr => ?_, rfl, rfl⟩
      obtain ⟨g, hg, hgr⟩ := forall₂_mem_right hW r hr
      exact arRes_of_wrapRel hgr (hG g hg).2 (hlet r hr) (hG g hg).1
  obtain ⟨hTy, hRh, hname, hlp⟩ := hstore
  -- the cons
  have hfreshA : env.find? (ConstantInfo.recInfo cvRa pR.majorIdx pR.rulePrefix
      (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
        fam.ctorsA rhss)).name = none := by
    show env.find? cvRa.name = none
    rw [hname]
    exact hfresh
  have hlen : ∀ {n : Key md} {ci : ConstantInfo md}, envR.find? n = some ci →
      ∃ ci', Env.find? ⟨.recInfo cvRa pR.majorIdx pR.rulePrefix
          (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
            fam.ctorsA rhss) :: env.consts⟩ n = some ci' ∧
        ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length :=
    find?_cons_same_len (by show pR.cvR.name = cvRa.name; rw [hname])
      (by show pR.cvR.levelParams = cvRa.levelParams; rw [hlp])
  refine storeArR_cons h hfreshA (ConstArR.of_rec (arRes_mono_len hlen hTy) ?_)
    (fun ⟨_, _, _, he⟩ => nomatch he)
  intro rl hrl
  obtain ⟨hmem, hnn⟩ := sumRules_mem hrl
  exact ⟨arRes_mono_len hlen (hRh _ hmem), fun lvls pins hf => absurd hf (hnn lvls pins)⟩

/-! ## The store facts along a step over the routes -/

/-- **The route at a given index count keeps `StoreArR`** (the no-recursor install's). -/
theorem storeArR_nativeAtRunJ {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat}
    (h : StoreArR env) (hA : NativeAtRunJ rulesJ env block nP env₂) : StoreArR env₂ :=
  let ⟨_, _, _, hN⟩ := hA
  storeArR_nativeNoRec h hN

/-- **One declaration step over the routes keeps `ThmLevels`**: a step of `IndRoutesJ`
(`thmLevels_declRunJ`), or the route at a given index count, which stores no theorem. -/
theorem thmLevels_declRunJA {env env₂ : Env md} {d : Declaration md} (h : ThmLevels env)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) : ThmLevels env₂ := by
  rcases declRunJA_cases hrun with h' | ⟨block, nP, rfl, -, _, _, -, hN⟩
  · exact thmLevels_declRunJ h h'
  · exact ThmLevels.step_noThm h (nativeNoRec_newSat (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h) hN)

/-- **One declaration step over the routes keeps the seven store facts**: the store invariant,
the recursors' shape and K facts, the typed theorems, the η towers, the tables' bodies and the
theorems' level parameters. -/
theorem storeFacts_declRunJA {env env₂ : Env md} {d : Declaration md}
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂)
    (hS : StoreInv env) (hR : RecShape env) (hK : RecK env) (hT : ThmTyped env)
    (hE : EtaTowers env) (hB : TableBodies env) (hL : ThmLevels env) :
    StoreInv env₂ ∧ RecShape env₂ ∧ RecK env₂ ∧ ThmTyped env₂ ∧ EtaTowers env₂ ∧
      TableBodies env₂ ∧ ThmLevels env₂ :=
  ⟨storeInv_declRunJA judgeFrames_rulesJ hS hrun, recShape_declRunJA hS hR hrun,
    recK_declRunJA hS hK hrun, thmTyped_declRunJA hT hrun, etaTowers_declRunJA hE hrun,
    tableBodies_declRunJA hS hB hrun, thmLevels_declRunJA hL hrun⟩

/-- **Along a run over the routes, the seven store facts hold**, from an environment where they
hold. -/
theorem storeFacts_declsRunJA {env env' : Env md} {ds : List (Declaration md)}
    (hds : DeclsRunJ rulesJ (IndRoutesAJ rulesJ) env ds env') :
    StoreInv env → RecShape env → RecK env → ThmTyped env → EtaTowers env → TableBodies env →
      ThmLevels env →
      StoreInv env' ∧ RecShape env' ∧ RecK env' ∧ ThmTyped env' ∧ EtaTowers env' ∧
        TableBodies env' ∧ ThmLevels env' := by
  induction hds with
  | nil => exact fun hS hR hK hT hE hB hL => ⟨hS, hR, hK, hT, hE, hB, hL⟩
  | cons hd _ ih =>
    intro hS hR hK hT hE hB hL
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := storeFacts_declRunJA hd hS hR hK hT hE hB hL
    exact ih h1 h2 h3 h4 h5 h6 h7

/-! ## The store facts along the late step -/

/-- **The late recursor's step keeps the eight store facts** at a family whose telescope
constant's type is arity-correct and resolves at the step's environment and whose stored former
carries the family's level parameters; the telescope constant's fact is kept too. -/
theorem storeFacts_lateTa {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂)
    (hS : StoreInv env) (hR : RecShape env) (hK : RecK env) (hT : ThmTyped env)
    (hE : EtaTowers env) (hB : TableBodies env) (hL : ThmLevels env) (hA : StoreArR env)
    (htty : ArRes env fam.cvTa.type) (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams) :
    StoreInv env₂ ∧ RecShape env₂ ∧ RecK env₂ ∧ ThmTyped env₂ ∧ EtaTowers env₂ ∧
      TableBodies env₂ ∧ ThmLevels env₂ ∧ StoreArR env₂ ∧ ArRes env₂ fam.cvTa.type := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := storeFacts_declNativeRecLateRunJ hrun hS hR hK hT hE hB
  exact ⟨h1, h2, h3, h4, h5, h6, thmLevels_late hL hrun,
    storeArR_nativeRecLateTa hA htty hlps hrun,
    htty.mono (declNativeRecLateRunJ_envExt hrun).find⟩

/-- **The install at a given index count, then the late recursor for its family, keep the
eight store facts**, over `EnvModelN.nativeAt`'s hypotheses at an unpinned block: the install
is a declaration step over the routes (`storeFacts_declRunJA`, `storeArR_nativeAtRunJ`); the
telescope constant is checked by the former's stage (`arRes_sumIndRunJ`) and the install keeps
the lookups, and the stored former carries the family's level parameters (`storedFormer_lps`),
so the late step keeps them (`storeFacts_lateTa`). -/
theorem storeFacts_nativeAtLate {env env₂ env₃ : Env md}
    {block : List (ConstantInfo md)} {nPd nIdx : Nat} {p₀ : NativeParts md}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hdp : nativePartsAt? nPd nIdx block = some p₀)
    {isRec : Bool} {cvS cvTa : ConstantVal md} {caps : IndCaps md} {p₁ : InductiveShape md}
    {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {kinds : List (List RecFieldKind)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    (hnd₀ : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ rulesJ env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩
      ⟨.indInfo cvS caps :: env.consts⟩
      p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors ctorsA
      sortss)
    (hK : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM md) p.cvT.name p.cvT.levelParams
      p.nP p.nIdx ctorsA = .ok kinds)
    (hcaps : Ix.Kernel.nativeCaps p = Ix.Kernel.nativeCapsAt p₁ isRec)
    (hopT2 : Ix.Kernel.openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest))
    (hsorts : FieldSortsJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩ true false p.resSort p.nP
      (tfvs.drop p.nP) [] p.nIdx isorts)
    (hFOk : Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true)
    (hFR : FormerReadJ ⟨.indInfo cvS caps :: env.consts⟩ p cvTa ctorsA)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂)
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hrun : DeclNativeRecLateRunJ rulesJ env₂ ⟨p, cvS, cvTa, ctorsA⟩ cvR mI rP rules env₃)
    (hS : StoreInv env) (hR : RecShape env) (hK' : RecK env) (hT : ThmTyped env)
    (hE : EtaTowers env) (hB : TableBodies env) (hL : ThmLevels env) (hA : StoreArR env) :
    StoreInv env₃ ∧ RecShape env₃ ∧ RecK env₃ ∧ ThmTyped env₃ ∧ EtaTowers env₃ ∧
      TableBodies env₃ ∧ ThmLevels env₃ ∧ StoreArR env₃ := by
  have hN : DeclNativeNoRecRunJ rulesJ env p₀ env₂ :=
    ⟨hnd₀, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hInd, hp, hCtors,
      hK, hcaps, hopT2, hsorts, hFOk, hTbl, hFR⟩
  have hAt : NativeAtRunJ rulesJ env block nPd env₂ := ⟨nIdx, p₀, hdp, hN⟩
  have hd : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env (.indDecl block nPd) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr hAt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := storeFacts_declRunJA hd hS hR hK' hT hE hB hL
  have htty : ArRes env₂ cvTa.type :=
    (arRes_sumIndRunJ hInd).mono (declNativeNoRecRunJ_envExt hN).find
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -⟩ := storeFacts_lateTa hrun h1 h2 h3 h4 h5 h6 h7
    (storeArR_nativeAtRunJ hA hAt) htty (storedFormer_lps hInd hp)
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩

end Ix.Kernel.Model
