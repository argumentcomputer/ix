module

public import IxCK.Kernel.Model.FoldLate
public import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateSplitJ
import IxCK.Kernel.Rules.Transport
public section

/-!
# The late route against the with-recursor install, at the derivation package

At the derivation package (`rulesJ`) inference and sort derivations weaken along an
extension (`Rules.Infer.weaken`, `Rules.Red.weaken`), so a with-recursor native record off a
structure-like block splits with no further hypothesis (`declNativeRunJ_split_rulesJ`).

`EnvModelN.nativeLate`: over `declNativeJ`'s hypotheses and the side condition, the
no-recursor install registers the family (`EnvModelN.nativeCore` at its table tail) and the
late step (`EnvModelN.late`) ends at the record's environment with that family registered.
`EnvModelN.nativeLateCore` is the same over `EnvModelN.nativeCore`'s hypotheses with the
with-recursor tail; its conclusion is that theorem's conclusion on that tail, the same
proposition, reached by the two steps.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps
  NativeParts InductiveShape RecRule EnvExt)

universe w

/-- The derivation package's inference weakens along an extension. -/
theorem rulesJ_infer_ext {md : Ix.Kernel.Mode} {e e' : Env md} (hx : EnvExt e e') {d : Nat}
    {a t : Expr md} (h : (rulesJ (md := md)).infer e d a t) : (rulesJ (md := md)).infer e' d a t :=
  Ix.Kernel.Rules.Infer.weaken hx h

/-- The derivation package's sort judgement weakens along an extension. -/
theorem rulesJ_sort_ext {md : Ix.Kernel.Mode} {e e' : Env md} (hx : EnvExt e e') {d : Nat}
    {t : Expr md} {u : Level} (h : (rulesJ (md := md)).sort e d t u) :
    (rulesJ (md := md)).sort e' d t u :=
  Ix.Kernel.Rules.Red.weaken hx h

/-- **The split at the derivation package**: a with-recursor native record off a
structure-like block is the no-recursor install followed by the late recursor step for the
block's recursor record, with the same output environment. -/
theorem declNativeRunJ_split_rulesJ {md : Ix.Kernel.Mode} {env env₂ : Env md} {nPd : Nat}
    {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hnt : ¬ (p₀.ctors.length = 1 ∧ p₀.nIdx = 0))
    (h : DeclNativeRunJ rulesJ env p₀ env₂) :
    ∃ (fam : NativeFam md) (env₁ : Env md) (cvR : ConstantVal md) (mI rP : Nat)
      (rules : List (RecRule md)),
      block.getLast? = some (.recInfo cvR mI rP rules) ∧
      DeclNativeNoRecRunJ rulesJ env p₀ env₁ ∧
      NativeFamStored env₁ fam ∧
      DeclNativeRecLateRunJ rulesJ env₁ fam cvR mI rP rules env₂ :=
  declNativeRunJ_split rulesJ_infer_ext rulesJ_sort_ext hdp hnt h

/-- **The fold invariant along the two steps, over `EnvModelN.nativeCore`'s hypotheses with the
with-recursor tail**: off a structure-like block, the no-recursor install registers the
family and the late step keeps the registry, so the invariant at `env₂` with the family
registered, `EnvModelN.nativeCore`'s conclusion on that tail, is reached by the two steps. -/
theorem EnvModelN.nativeLateCore {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V]
    {μ : CheckMode} {env env₂ : Env md} {block : List (ConstantInfo md)} {nPd : Nat}
    {p₀ : NativeParts md} {R : NativeFam md → Prop} (h : EnvModelN V μ env R)
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    {isRec : Bool} {cvS cvTa : ConstantVal md} {caps : IndCaps md} {p₁ : InductiveShape md}
    {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {kinds : List (List RecFieldKind)}
    {tfvs : List (Expr md)} {trest : Expr md} {isorts : List Level}
    {cvRa : ConstantVal md} {rhss : List (Expr md)}
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
    (hwl : p.large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ p.ctors.length < 2)
    (hRec : NativeRecJ rulesJ (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩)
      p cvTa ctorsA cvRa rhss)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (Ix.Kernel.sumRules
          (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).find?
          cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts⟩
      = .ok env₂)
    (hnt : ¬ (p₀.ctors.length = 1 ∧ p₀.nIdx = 0)) :
    EnvModelN V μ env₂ (fun f => R f ∨ f = ⟨p, cvS, cvTa, ctorsA⟩) := by
  obtain ⟨cvR, mI, rP, rules, hF⟩ := lateFront_of hdp rfl hnd₀ hInd hp hCtors hK hcaps hwl hopT2
    hsorts hFOk hRec hFR
  obtain ⟨-, hL⟩ := hF.late rulesJ_infer_ext rulesJ_sort_ext hnt hTbl
  have hnt' : ¬ (ctorsA.length = 1 ∧ p.nIdx = 0) := by rw [hF.lenC, hF.idx0]; exact hnt
  have h₁ := EnvModelN.nativeCore V h hdp hnd₀ hInd hp hCtors hK hcaps hopT2 hsorts hFOk hFR
    (Or.inr (checkNativeTable_pure hnt' _))
  exact EnvModelN.late V h₁ (Or.inr rfl) hL

/-- **The fold invariant along the two steps**, over `declNativeJ`'s hypotheses (the model, its
stored theorem values and its η families inside `EnvModelN`, the recogniser and the record)
and the side condition: the no-recursor install registers the family, and the late step from
there ends at the record's environment with the invariant and the family registered. The
family is the record's own summary, the one `EnvModelN.nativeCore` registers on the
with-recursor tail (`EnvModelN.nativeLateCore`). -/
theorem EnvModelN.nativeLate {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {env env₂ : Env md} {R : NativeFam md → Prop} {nPd : Nat} {block : List (ConstantInfo md)}
    {p₀ : NativeParts md} (h : EnvModelN V μ env R)
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀)
    (hnt : ¬ (p₀.ctors.length = 1 ∧ p₀.nIdx = 0))
    (hrun : DeclNativeRunJ rulesJ env p₀ env₂) :
    ∃ (fam : NativeFam md) (env₁ : Env md) (cvR : ConstantVal md) (mI rP : Nat)
      (rules : List (RecRule md)),
      block.getLast? = some (.recInfo cvR mI rP rules) ∧
      DeclNativeNoRecRunJ rulesJ env p₀ env₁ ∧
      NativeFamStored env₁ fam ∧
      EnvModelN V μ env₁ (fun f => R f ∨ f = fam) ∧
      DeclNativeRecLateRunJ rulesJ env₁ fam cvR mI rP rules env₂ ∧
      EnvModelN V μ env₂ (fun f => R f ∨ f = fam) := by
  obtain ⟨hnd, isRec, envF, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest, isorts,
    hInd, hp, hCtors, hK, hcaps, hwl, hopT, hsorts, hFOk, hRec, hTbl, hFR⟩ := hrun
  obtain ⟨_, _, -, -, -, -, ⟨cvS, henvF, -⟩, -⟩ := hInd.shape
  subst henvF
  obtain ⟨cvR, mI, rP, rules, hF⟩ := lateFront_of hdp rfl hnd hInd hp hCtors hK hcaps hwl hopT
    hsorts hFOk hRec hFR
  obtain ⟨hN, hL⟩ := hF.late rulesJ_infer_ext rulesJ_sort_ext hnt hTbl
  have hnt' : ¬ (ctorsA.length = 1 ∧ p.nIdx = 0) := by rw [hF.lenC, hF.idx0]; exact hnt
  have h₁ := EnvModelN.nativeCore V h hdp hnd hInd hp hCtors hK hcaps hopT hsorts hFOk hFR
    (Or.inr (checkNativeTable_pure hnt' _))
  exact ⟨⟨p, cvS, cvTa, ctorsA⟩, _, cvR, mI, rP, rules, hF.last, hN, hF.stored, h₁, hL,
    EnvModelN.late V h₁ (Or.inr rfl) hL⟩

end Ix.Kernel.Model
