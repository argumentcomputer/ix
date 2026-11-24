module

public import IxCK.Kernel.Model.Inductives.DeclNativeRecLate
public import IxCK.Kernel.Model.Inductives.DeclNative
public import IxCK.Kernel.Model.JudgeRules
public section

/-!
# The fold invariant with the native families registered so far

`EnvModelT` (`Model/FoldJ.lean`) forgets which model a step extended, so a family's data kept at
one model are not available at the next. `EnvModelN V μ env R` keeps one model for every
registered family: the model's stored theorem values are read, every family `R` names has its
data there (`NativeFamOk`), and the η families are closed. `R` is ghost state, not a function of
`env`: the store records no constructor list, so registration is the caller's.

* `EnvModelN.empty`, `EnvModelN.toT`: the start, and the projection to `EnvModelT`;
* `EnvModelN.step`, `EnvModelN.stepReg`: a step that extends whatever model it is given keeps
  the registry (the data cross every model extension, `NativeFamOk.ext`), and one that also
  gives a family's data at the new model registers it;
* `EnvModelN.declRunJ`: every declaration step over the derivation package keeps the registry
  (`declStep_preservesJ` at the four inductive routes);
* `EnvModelN.nativeCore`: a native install, stated over `declNativeCoreJ`'s own hypotheses so
  that the caller names the summary, registers its family;
* `EnvModelN.late`: a recursor for a registered family keeps the registry
  (`declNativeRecLateJ`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps
  NativeParts InductiveShape RecRule Declaration EtaFamiliesClosed)

universe w

/-- **The fold invariant with the families registered so far**: `EnvModelT` whose model also
keeps every registered family's data. `R` is ghost state; it is not a function of `env`. -/
@[expose] def EnvModelN (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env md)
    (R : NativeFam md → Prop) : Prop :=
  (∃ mp : EnvModelM V μ env, ThmValOk mp ∧ ∀ fam, R fam → NativeFamOk mp fam) ∧
    EtaFamiliesClosed env

/-- The empty environment, with no family registered. -/
theorem EnvModelN.empty {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] (μ : CheckMode) :
    EnvModelN V μ (Env.empty : Env md) (fun _ => False) :=
  ⟨⟨EnvModelM.empty V μ, ThmValOk.empty _, fun _ h => h.elim⟩, EtaFamiliesClosed.empty⟩

/-- The registry forgotten: the restated fold invariant. -/
theorem EnvModelN.toT {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env : Env md} {R : NativeFam md → Prop} (h : EnvModelN V μ env R) : EnvModelT V μ env :=
  let ⟨⟨mp, hT, _⟩, hE⟩ := h
  ⟨⟨mp, hT⟩, hE⟩

/-- **The generic step**: a step that extends whatever model it is given keeps the registry. -/
theorem EnvModelN.step {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {R : NativeFam md → Prop} (h : EnvModelN V μ env R)
    (hstep : ∀ mp : EnvModelM V μ env, ThmValOk mp → EtaFamiliesClosed env →
      EtaFamiliesClosed env₂ ∧ ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂) :
    EnvModelN V μ env₂ R := by
  obtain ⟨⟨mp, hT, hR⟩, hE⟩ := h
  obtain ⟨hE₂, mp₂, hext⟩ := hstep mp hT hE
  exact ⟨⟨mp₂, hT.of_ext hext, fun fam hf => (hR fam hf).ext hext⟩, hE₂⟩

/-- **The generic step with a registration**: a step that also gives a family's data at the
model it builds registers the family. -/
theorem EnvModelN.stepReg {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {R : NativeFam md → Prop} {fam : NativeFam md}
    (h : EnvModelN V μ env R)
    (hstep : ∀ mp : EnvModelM V μ env, ThmValOk mp → EtaFamiliesClosed env →
      EtaFamiliesClosed env₂ ∧
        ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ ∧ NativeFamOk mp₂ fam) :
    EnvModelN V μ env₂ (fun f => R f ∨ f = fam) := by
  obtain ⟨⟨mp, hT, hR⟩, hE⟩ := h
  obtain ⟨hE₂, mp₂, hext, hfam⟩ := hstep mp hT hE
  refine ⟨⟨mp₂, hT.of_ext hext, fun f hf => ?_⟩, hE₂⟩
  rcases (show R f ∨ f = fam from hf) with hf' | rfl
  · exact (hR f hf').ext hext
  · exact hfam

/-- **Every declaration step keeps the registry** (no registration): the step extends the model
it is given (`declStep_preservesJ`, at the four inductive routes over derivations). -/
theorem EnvModelN.declRunJ {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {d : Declaration md} {R : NativeFam md → Prop}
    (h : EnvModelN V μ env R) (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    EnvModelN V μ env₂ R :=
  EnvModelN.step V h fun mp hT hE =>
    declStep_preservesJ rulesJ_thmValue mp (judgeSound_rulesJ_of mp) (axiomBits_rulesJ env) hE
      (fun hI => by
        rcases hI with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT'
        · exact nativeStep_rulesJ mp hT hE hdp hN
        · exact modeledStep_rulesJ mp hE hM
        · exact nativeNoRecStep_rulesJ mp hT hE hdp hN
        · exact twinStep_rulesJ mp hE hT') hrun

/-- **A native install registers its family.** Stated over `declNativeCoreJ`'s own hypotheses,
so that the caller names the summary (it is existentially bound inside `DeclNativeRunJ` and
`DeclNativeNoRecRunJ`); `htail` is that theorem's last hypothesis, either tail. The η half is
the route's own (`declNativeRunJ_etaClosed`, `declNativeNoRecRunJ_etaClosed`), at the record
the hypotheses assemble. -/
theorem EnvModelN.nativeCore {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md}
    {block : List (ConstantInfo md)} {nPd : Nat} {p₀ : NativeParts md}
    {R : NativeFam md → Prop} (h : EnvModelN V μ env R)
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
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
    (htail :
      (∃ (cvRa : ConstantVal md) (rhss : List (Expr md)),
        (p.large = true →
          (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ p.ctors.length < 2) ∧
        NativeRecJ rulesJ (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩)
          p cvTa ctorsA cvRa rhss ∧
        Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
          ⟨.recInfo cvRa p.majorIdx p.rulePrefix
            (Ix.Kernel.sumRules
              (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).find?
              cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
            :: (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts⟩
          = .ok env₂) ∨
      Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂) :
    EnvModelN V μ env₂ (fun f => R f ∨ f = ⟨p, cvS, cvTa, ctorsA⟩) := by
  refine EnvModelN.stepReg V h fun mp hT hE => ?_
  obtain ⟨mp₂, hext⟩ := declNativeCoreJ judgeFrames_rulesJ (fun m => judgeSound_rulesJ_of m)
    judgeInv_rulesJ (fun m φ => sortClaim_rulesJ_of m φ) mp hE hdp hnd₀ hInd hp hCtors hK hcaps
    hopT2 hsorts hFOk hFR htail
  obtain ⟨hext', hfam⟩ := hext hT
  refine ⟨?_, mp₂, hext', hfam cvS caps rfl⟩
  -- the η half, at the route the tail takes
  rcases htail with ⟨cvRa, rhss, hwl, hRec, hTbl⟩ | hTbl
  · exact declNativeRunJ_etaClosed hE ⟨hnd₀, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa,
      rhss, tfvs, trest, isorts, hInd, hp, hCtors, hK, hcaps, hwl, hopT2, hsorts, hFOk, hRec,
      hTbl, hFR⟩
  · exact declNativeNoRecRunJ_etaClosed hE ⟨hnd₀, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds,
      tfvs, trest, isorts, hInd, hp, hCtors, hK, hcaps, hopT2, hsorts, hFOk, hTbl, hFR⟩

/-- **A recursor for a registered family keeps the registry**: the late step extends the model
at which the family's data are kept (`declNativeRecLateJ`), and keeps the η families closed. -/
theorem EnvModelN.late {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {R : NativeFam md → Prop} {fam : NativeFam md} {cvR : ConstantVal md}
    {mI rP : Nat} {rules : List (RecRule md)} (h : EnvModelN V μ env R) (hR : R fam)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂) :
    EnvModelN V μ env₂ R := by
  obtain ⟨⟨mp, hT, hReg⟩, hE⟩ := h
  obtain ⟨mp₂, hext⟩ := declNativeRecLateJ V judgeFrames_rulesJ
    (fun m => judgeSound_rulesJ_of m) (fun m φ => sortClaim_rulesJ_of m φ) mp hE (hReg fam hR)
    hrun
  exact ⟨⟨mp₂, hT.of_ext hext, fun f hf => (hReg f hf).ext hext⟩,
    declNativeRecLateRunJ_etaClosed hE hrun⟩

end Ix.Kernel.Model
