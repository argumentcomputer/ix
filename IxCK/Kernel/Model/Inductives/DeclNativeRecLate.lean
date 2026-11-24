module

public import IxCK.Kernel.Model.Inductives.NativeFam
public import IxCK.Kernel.Model.Inductives.SumData
public import IxCK.Kernel.Model.Inductives.NativeJudge
public import IxCK.Kernel.Model.JudgeSound
public import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateExtJ
import IxCK.Kernel.Model.Inductives.DeclRecTwin
import IxCK.Kernel.Model.Inductives.StructRecKit2
import IxCK.Kernel.Model.Inductives.StructCtorFrames
import IxCK.Kernel.Model.Inductives.StructBits
import IxCK.Kernel.Model.Inductives.RecStored
import IxCK.Kernel.Model.Inductives.StructRows
import IxCK.Kernel.Model.Annot.BitLevels
import IxCK.Kernel.Model.Annot.BitLemmas
import IxCK.Kernel.Verify.Level
public section

/-!
# A recursor for a stored native family: the model step

`declNativeRecLateJ`: the late recursor's step (`DeclNativeRecLateRunJ`) extends any model of
the environment at which the family's data are kept (`NativeFamOk`, exported by the native
install and carried along every model extension, `Model/Inductives/NativeFam.lean`).

* The recursor's stage (`stageFixRecJ`) is fed by the family's data (`NativeFamAt.stageRec`):
  the readings, the leaves and the frames are the bundle's; the two lookups are the relation's
  (`NativeFamStored`); the generated recursor's run and the elimination restriction are the
  relation's.
* The constructors' data are kept at the small eliminator, so at a large eliminator the field
  sources are re-derived. At a family that is not syntactically propositional every field lies
  in the family's universe (`fieldsBound`), so any sources do; at a syntactically propositional
  family the sources are read off the recursor's own field sorts (`FixCtorDataI.largeProp`),
  which the relation carries at the current environment.
* The stored recursor is the generated one or the declared one (`recStoredStep`); its cons is
  fresh and is neither a table nor a theorem, so the model extends (`ModelExt.plain`).
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory Ix.Kernel.SetTheory.Tower
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BinderMeta NativeParts RecRule EtaFamiliesClosed)

universe w

/-! ## The field sources at a large eliminator -/

/-- Fields bounded by the universe `0` are propositions, whatever their sources. -/
theorem fieldsBoundSrc_of_fieldsBound {V : Type w} [SetTheory V] :
    ∀ (Fs : List AnnotTerm) (srcs : List (Option Nat)) (ρ : Nat → V),
      FieldsBound 0 ρ Fs → FieldsBoundSrc ρ Fs srcs
  | [], srcs, _, _ => by cases srcs <;> simp [FieldsBoundSrc]
  | _ :: _, [], _, _ => by simp [FieldsBoundSrc]
  | F :: Fs, s :: ss, ρ, h => by
    simp only [FieldsBound] at h
    simp only [FieldsBoundSrc]
    exact ⟨fun _ => h.1, fun a ha => fieldsBoundSrc_of_fieldsBound Fs ss _ (h.2 a ha)⟩

/-- **The constructor's data at the large eliminator of a propositional family**: the data at
the small eliminator, with the field sources read off the recursor's own field sorts
(`srcsOf`). A field whose sort is not `Prop` at every assignment is one of the residual's index
arguments, so it has a source; every unsourced field is a proposition, read through the sort
claim at the constructor's opened telescope (the argument of `sumCtorDataJ`'s last clause, at
the stored data's opening). -/
theorem FixCtorDataI.largeProp {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {env : Env md}
    {m : EnvModel V env} {J : Judgements md} (_hJ : JudgeSound J m) (hS : ∀ ψ, SortClaimJ J m ψ)
    {env₀ : Env md} {T : Key md} {lps : List LevelParam} {cvC : ConstantVal md}
    {nP nF nIdx : Nat} {resSort : Level} {isProp : Bool} {idxArgs : List (Expr md)}
    {ds : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (LevelParam → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    {ks : List RecFieldKind} {fvsP xFvs : List (Expr md)} {xrest : Expr md}
    {Eiss : (LevelParam → Nat) → List (List AnnotTerm)}
    {tss : (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))} {sorts : List Level}
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp false idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss)
    (htf : cvC.type.hasFvar = false) (htb : cvC.type.looseBVarsBounded 0 = true)
    (hsorts : FieldSortsJ J env true true resSort nP xFvs idxArgs nF sorts) :
    FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp true idxArgs ds Es
      (srcsOf xFvs idxArgs sorts nF) ks fvsP xFvs xrest Eiss tss := by
  have hlenP : fvsP.length = nP := h.pLen
  have hlenX : xFvs.length = nF := h.xLen
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll := openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨-, hfields⟩ := hsorts
  refine h.withSrcs (srcsOf_length _ _ _ _) ?_ ?_ ?_
  · -- the sources are index positions
    intro s hs l hsl
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hj
    have hj' := Option.some.inj hj
    rw [hsl] at hj'
    split at hj'
    · exact nomatch hj'
    · have := firstIdx_some hj'
      rw [← h.idxLen]
      exact (List.getElem?_eq_some_iff.mp this).1
  · -- an index source reads to the field variable
    intro j l hjl ψ
    have hjn : j < nF := by
      have := (List.getElem?_eq_some_iff.mp hjl).1
      rwa [srcsOf_length] at this
    rw [srcsOf_getElem? _ _ _ _ _ hjn] at hjl
    have hjl' := Option.some.inj hjl
    split at hjl'
    · exact nomatch hjl'
    · have hidxl := firstIdx_some hjl'
      obtain ⟨fv, hfv⟩ : ∃ fv, xFvs[j]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, rfl⟩ := h.xIdx j fv hfv
      rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some] at hidxl
      obtain ⟨v, hv, hread⟩ := DenoteMetaSpine.getElem? (h.idxRead ψ) hidxl
      rw [denoteMeta_fvar, show nP + nF - 1 - (nP + j) = nF - 1 - j from by omega] at hread
      rw [hv, Option.some.inj hread]
  · -- the unsourced fields are propositional at a family instantiated at `Prop`
    intro _ ψ _ ρ hρ
    have hC := opened_of_peel hopAll htf htb (h.read ψ) (h.len ψ) (h.okTy ψ)
    have hlenDs : (ds ψ).length = nP + nF := h.len ψ
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by
      rw [List.length_reverse, List.length_map, hlenDs]
    have hρ' : Sat V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    rw [← hFsEq]
    have hfb := fieldsBoundSrc_of_frame (Γ := ((ds ψ).map (·.2.2)).reverse)
      (srcs := srcsOf xFvs idxArgs sorts nF) rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
    · rw [List.drop_zero] at hfb; exact hfb
    intro j hj hsj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, -, hz⟩ := hfields j hj
    have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
    have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hC.doms (nP + j) fv hfvA
    have hmem := (sortRowJ (hS ψ) hi hens hws hb hL hCtx hread ρ hρ).2
    -- the source is `none`: the sort evaluates to `0`
    have hu0 : u.eval ψ = 0 := by
      rw [srcsOf_getElem? _ _ _ _ _ hj] at hsj
      have hsj' := Option.some.inj hsj
      have hsu : sorts.getD j .zero = u := by
        rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
      rw [hsu] at hsj'
      split at hsj'
      · next hequ => exact Level.isEquiv_sound (beq_iff_eq.mp hequ) ψ
      · rcases hz rfl rfl with h' | h'
        · exact h' ψ
        · exfalso
          have hfvx : xFvs.getD j default = fv := by
            rw [List.getD_eq_getElem?_getD, hfv, Option.getD_some]
          rw [hfvx] at hsj'
          obtain ⟨i, hi'⟩ := firstIdx_of_mem (List.contains_iff_mem.mp h')
          rw [hi'] at hsj'
          exact nomatch hsj'
    rw [hu0] at hmem
    exact hmem

/-! ## The recursor's stage, fed by the family's data -/

/-- **The recursor's stage at a later environment**: `stageFixRecJ` for a record that is the
family's with its recursor fields replaced, from the family's data, the two lookups, the stage's
package facts, the generated recursor's run, the elimination restriction, and the constructors'
data at the record's eliminator with some field sources (`hsrc`). -/
theorem NativeFamAt.stageRec {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env md}
    {mp : EnvModelM V μ env}
    {p : NativeParts md} {cvS cvTa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)}
    {env₀ : Env md} {bsT : List (Expr md × BinderMeta)}
    {ppsAll : (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {uAV : (LevelParam → Nat) → Nat} {fssZ : (LevelParam → Nat) → List (List AnnotTerm)}
    {idxF : Nat → List (Expr md)}
    {dsF : Nat → (LevelParam → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (LevelParam → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List (Expr md)}
    {xrestF : Nat → Expr md}
    {eissF : Nat → (LevelParam → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (LevelParam → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : NativeFamAt mp p cvS cvTa ctorsA env₀ bsT ppsAll uAV fssZ idxF dsF esF srcsF ksF fvsPF
      xFvsF xrestF eissF tssF)
    {J : Judgements md} (hJ : JudgeSound J mp.base2) (hS : ∀ ψ, SortClaimJ J mp.base2 ψ)
    (hE : Ix.Kernel.EtaFamiliesClosedExcept env p.cvT.name)
    {caps : IndCaps md}
    (hfT : env.find? p.cvT.name = some (.indInfo cvS caps))
    (hfC : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2))
    {cvR : ConstantVal md} {elim : LevelParam} {large : Bool} {rhs₀ : List (Expr md)} {pin : Bool}
    (pR : NativeParts md)
    (hpR : pR =
      { p with
        cvR := cvR, elim := elim, large := large, rhss := rhs₀, recPinned := pin })
    {cvRa : ConstantVal md} {rhss : List (Expr md)}
    (hRec : NativeRecRunJ J env pR cvTa ctorsA cvRa rhss)
    (hwl : large = true →
      (∀ φ : LevelParam → Nat, Level.eval φ p.resSort ≠ 0) ∨ ctorsA.length < 2)
    (srcs' : Nat → List (Option Nat))
    (hsrc : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      FixCtorDataI mp.base2 env₀ p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort
        p.isProp large (idxF j) (dsF j) (esF j) (srcs' j) (ksF j) (fvsPF j) (xFvsF j)
        (xrestF j) (eissF j) (tssF j)) :
    ∃ (sAV : (LevelParam → Nat) → Nat)
      (mp' : EnvModelM V μ ⟨.recInfo cvRa pR.majorIdx pR.rulePrefix
        (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type ctorsA
          rhss) :: env.consts⟩),
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fixLeafAV mp.base2 pR ppsAll dsF esF ksF eissF tssF ctorsA sAV) := by
  subst hpR
  obtain ⟨helim, hRlps⟩ := hRec.pins
  obtain ⟨hRn, -, hRf, hRsh⟩ := hRec.recursor
  have hRfresh : env.find? cvRa.name = none := by rw [hRn]; exact hRf
  have hRshape : cvRa.name.isProjFnShape = false := by rw [hRn]; exact hRsh
  have hRJ : NativeRecJ J env
      { p with cvR := cvR, elim := elim, large := large, rhss := rhs₀, recPinned := pin }
      cvTa ctorsA cvRa rhss := ⟨cvRa, rhss, hRec, Or.inl ⟨rfl, rfl⟩⟩
  have hplAll := hRJ.plain ⟨cvS, caps, hfT⟩ h.lenK.symm h.lenA h.lpsA
  obtain ⟨tfvs, trest, hopT⟩ := openPisAtFvars_of_stripPis_isSome p.nP 0
    (Ix.Kernel.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [h.stripT]; rfl))
  exact stageFixRecJ (fssZ := fssZ) (srcsF := srcs')
    (p := { p with cvR := cvR, elim := elim, large := large, rhss := rhs₀, recPinned := pin })
    hE mp hJ hS
    (by show p.nP + 1 + p.ctors.length + p.nIdx = p.nP + 1 + ctorsA.length + p.nIdx; rw [h.lenA])
    (by show p.nP + 1 + p.ctors.length = p.nP + 1 + ctorsA.length; rw [h.lenA])
    rfl rfl hRec hplAll h.stripT hfT
    (fun m₂ hag _ _ _ => by
      have hac : m₂.acval = acvalWith mp.base2.acval cvRa.name (m₂.acval cvRa.name) := by
        funext n
        by_cases hn : n = cvRa.name
        · subst hn; rw [acvalWith_self]
        · rw [acvalWith_ne hn]; exact hag n hn
      have hcaps := capsOk_cons_rec_nonproj mp hRfresh hRshape m₂ hac
      exact ⟨fun he hfam => hcaps.1 _ _ _ (Ix.Kernel.Env.find?_cons_of_fresh hRfresh hfT) he
          h.resT hfam,
        fun hu => hcaps.2 _ _ _ (Ix.Kernel.Env.find?_cons_of_fresh hRfresh hfT) hu h.resT⟩)
    h.lpsT h.lpsS hopT helim hRlps h.former h.lenK h.ks
    (fun i cA hi => ⟨hfC i cA hi, h.lpsA cA (List.mem_of_getElem? hi), hsrc i cA hi⟩)
    h.idxRes h.uParams h.leafT h.leafC h.paramsIff h.frames hwl

/-! ## The model step -/

/-- **A recursor for a stored native family extends the model**, over a package: at a model
where the family's data are kept (`NativeFamOk`), the recursor's stage gives a model storing the
generated recursor (`NativeFamAt.stageRec`), the declared one is stored with the same leaf
(`recStoredStep`), and the recursor's cons is fresh and neither a table nor a theorem. No
`ThmValOk` premise: the head is a recursor. -/
theorem declNativeRecLateJ {md : Ix.Kernel.Mode} (V : Type w) [SetTheory V] {μ : CheckMode}
    {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    (hS : ∀ {e : Env md} (m : EnvModelM V μ e) ψ, SortClaimJ J m.base2 ψ)
    {env env₂ : Env md} (mp : EnvModelM V μ env) (hE : EtaFamiliesClosed env)
    {fam : NativeFam md} (hfam : NativeFamOk mp fam)
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (h : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hst, hwl, hprop, hRec, rfl⟩ := h
  unfold NativeFamOk at hfam
  obtain ⟨env₀, bsT, ppsAll, uAV, fssZ, idxF, dsF, esF, srcsF, ksF, fvsPF, xFvsF, xrestF, eissF,
    tssF, hA⟩ := hfam
  obtain ⟨hfTR, hctorR, hlenAR, hkR⟩ := hst.atRec hpR
  -- the field sources at the record's eliminator: the stored ones, or at a large eliminator of
  -- a syntactically propositional family the recursor's own
  have hex : ∀ j : Nat, ∃ s : List (Option Nat), ∀ cA : ConstantVal md × Nat,
      fam.ctorsA[j]? = some cA →
      FixCtorDataI mp.base2 env₀ fam.p.cvT.name fam.p.cvT.levelParams cA.1 fam.p.nP cA.2
        fam.p.nIdx fam.p.resSort fam.p.isProp large (idxF j) (dsF j) (esF j) s (ksF j)
        (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j) := by
    intro j
    by_cases hLP : large = true ∧ fam.p.isProp = true
    · cases hcj : fam.ctorsA[j]? with
      | none => exact ⟨[], fun _ hcA => nomatch hcA⟩
      | some cA₀ =>
        obtain ⟨fvsP, crest, xFvs, xrest, sorts, hopP, hopX, hsorts⟩ :=
          hprop hLP.1 hLP.2 j cA₀ hcj
        have hD := hA.ctor j cA₀ hcj
        -- the relation's opening is the data's
        obtain ⟨crest', hopP', hopX'⟩ := hD.opens
        obtain ⟨-, hcr⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopP'))
        rw [hcr] at hopX
        obtain ⟨hxF, hxr⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX'))
        rw [hxF, hxr, ← hD.idxEq] at hsorts
        -- the stored constructor is closed
        have hwf := mp.base2.wf _ (List.mem_of_find?_eq_some (hst.ctor j cA₀ hcj).1)
        refine ⟨srcsOf (xFvsF j) (idxF j) sorts cA₀.2, fun cA hcA => ?_⟩
        obtain rfl := Option.some.inj hcA
        rw [hLP.1]
        exact FixCtorDataI.largeProp V (hJ mp) (hS mp) hD hwf.1 hwf.2.2.2.1 hsorts
    · refine ⟨srcsF j, fun cA hcA => ?_⟩
      have hD := hA.ctor j cA hcA
      refine hD.withSrcs hD.srcLen hD.srcBnd hD.srcIdx (fun hl ψ hw ρ hρ => ?_)
      have hnp : fam.p.isProp = false := by
        cases hp : fam.p.isProp with
        | false => rfl
        | true => exact (hLP ⟨hl, hp⟩).elim
      have hb := hA.fieldsBound hnp j cA hcA ψ ρ hρ
      exact fieldsBoundSrc_of_fieldsBound _ _ _
        ((congrArg (fun w => FieldsBound w ρ (((dsF j ψ).drop fam.p.nP).map (·.2.2))) hw).mp hb)
  have hsrc : ∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
      FixCtorDataI mp.base2 env₀ fam.p.cvT.name fam.p.cvT.levelParams cA.1 fam.p.nP cA.2
        fam.p.nIdx fam.p.resSort fam.p.isProp large (idxF j) (dsF j) (esF j)
        (Classical.choose (hex j)) (ksF j) (fvsPF j) (xFvsF j) (xrestF j) (eissF j) (tssF j) :=
    fun j => Classical.choose_spec (hex j)
  -- the stage's generated recursor and rules, and the stored ones
  obtain ⟨cvRg, rhsG, hRecG, hstd⟩ := id hRec
  obtain ⟨sAV, mp₃g, hac₃g⟩ := hA.stageRec (hJ mp) (hS mp) (hE.except fam.p.cvT.name)
    hst.former (fun j cA hj => (hst.ctor j cA hj).1) (cvR := cvR) (elim := elim) (large := large)
    (rhs₀ := List.map (fun x : RecRule md => x.rhs) rules) (pin := true) pR hpR hRecG hwl
    (fun j => Classical.choose (hex j)) hsrc
  -- every rule fires, at the generated type and at the stored one
  have hlpsR : ∀ c ∈ fam.ctorsA, c.1.levelParams = pR.cvT.levelParams := fun c hc =>
    let ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    (hctorR j c hj).2.1
  have hplG : fam.ctorsA.all (fun c => Expr.recRulePlain cvRg.type pR.majorIdx pR.rulePrefix
      pR.nP c.1.levelParams) = true :=
    NativeRecJ.plain ⟨cvRg, rhsG, hRecG, Or.inl ⟨rfl, rfl⟩⟩ ⟨fam.cvS, _, hfTR⟩ hkR hlenAR hlpsR
  have hplAll : fam.ctorsA.all (fun c => Expr.recRulePlain cvRa.type pR.majorIdx pR.rulePrefix
      pR.nP c.1.levelParams) = true :=
    hRec.plain ⟨fam.cvS, _, hfTR⟩ hkR hlenAR hlpsR
  have hctorC : ∀ (j : Nat) (cA : ConstantVal md × Nat), fam.ctorsA[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 pR.nP cA.2) ∧
        Expr.ctorTeleOk cA.1.type (pR.nP + cA.2) = true := by
    intro j cA hj
    obtain ⟨hf, -, cbs, es, hres, -⟩ := hctorR j cA hj
    exact ⟨hf, Ix.Kernel.Expr.ctorTeleOk_of hres (by rw [Ix.Kernel.Expr.getAppFn_mkAppN]; rfl)⟩
  -- the model storing the recursor: the generated one, or the declared one
  obtain ⟨mp₃, hac₃⟩ : ∃ mp₃ : EnvModelM V μ ⟨.recInfo cvRa pR.majorIdx pR.rulePrefix
        (Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
          fam.ctorsA rhss) :: env.consts⟩,
      mp₃.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fixLeafAV mp.base2 pR ppsAll dsF esF ksF eissF tssF fam.ctorsA sAV) := by
    rcases hstd with ⟨rfl, rfl⟩ | hdecl
    · exact ⟨mp₃g, hac₃g⟩
    · exact recStoredStep mp (hfr _) (hJ mp) hRecG hdecl hplG hplAll hctorC mp₃g hac₃g
  -- the recursor's cons is fresh: the model extends
  have hRfresh : env.find? cvRa.name = none := by
    obtain ⟨hRn, -, hRf, -⟩ := hRec.recursor
    rw [hRn]; exact hRf
  exact ⟨mp₃, ModelExt.plain .refl hac₃ hRfresh⟩

end Ix.Kernel.Model
