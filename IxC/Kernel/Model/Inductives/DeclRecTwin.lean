module

public import IxC.Kernel.Model.Inductives.WrapModel
public import IxC.Kernel.Model.Inductives.NativeJudge
public import IxC.Kernel.Model.JudgeSound
public import IxC.Kernel.Model.ThmVal
public import IxC.Kernel.Semantics.Inductives.DeclNativeExtJ
public import IxC.Kernel.Verify.Extend.Recs
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.Annot.BitLemmas
import IxC.Kernel.Model.IndCons
import IxC.Kernel.Model.IndCaps
import IxC.Kernel.Model.IndRename
import IxC.Kernel.Model.Swap
import IxC.Kernel.Model.Caps
import IxC.Kernel.Model.RecRulesCons
import IxC.Kernel.Model.Rules.RedSoundKit
import IxC.Kernel.Semantics.IndRecsCore
import IxC.Kernel.Semantics.IndBlockFacts
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.Inductives.StructRec
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Level

public section

/-!
# The twin recursor route, at a model

`DeclRecTwinRunJ` (`Semantics/Inductives/DeclNativeJ.lean`) installs a non-empty
block of recursors whose inductive family and canonical recursor are already
stored in the environment. This file proves `declRecTwinJ`, extending an
environment model `EnvModelM V μ env` across the three stages of the route:

* **Model companions (`twinModels`)**: for each twin of a modeled canonical
  recursor, its stored model companion `auxKey kC .model` is copied to
  `auxKey cvW.name .model` with the canonical companion's leaf;
* **Provisioning (`twinProv`)**: each twin recursor is installed with empty rule
  list at the canonical recursor's leaf `mp.base2.acval kC`, reading its
  declared type against the canonical recursor's type along `WrapRel`;
* **Rule attachment (`twinRecs`)**: the peer renaming `f` satisfies `RenameOk`
  at the provisioned environment, each twin rule's `RecRuleLaw` is transported
  from its canonical rule along `WrapRel` and `f`, and `EnvModelM.swapP`
  attaches the checked rule lists while preserving every leaf (`ModelExt`).
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level LevelParam ConstantInfo ConstantVal
  RecRule IndCaps ReducibilityHint)
open Ix.Kernel.Model.Rules (PiChain piChain_succ_inv teleFit_of_teleFitPA PiChain.inst)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

private theorem constsBound_mono {env₁ env₂ : Env md}
    (hle : ∀ n, (env₁.find? n).isSome = true → (env₂.find? n).isSome = true) :
    ∀ {e : Expr md}, ConstsBound env₁ e → ConstsBound env₂ e := by
  intro e
  induction e with
  | bvar _ => intro _; simp
  | sort _ => intro _; simp
  | const n _ => simp only [constsBound_const]; exact hle n
  | fvar _ _ ih => simp only [constsBound_fvar]; exact ih
  | lit _ => intro _; simp
  | app _ _ ihf iha => simp only [constsBound_app]; exact fun ⟨hf, ha⟩ => ⟨ihf hf, iha ha⟩
  | lam _ _ _ iht ihb => simp only [constsBound_lam]; exact fun ⟨ht, hb⟩ => ⟨iht ht, ihb hb⟩
  | forallE _ _ _ iht ihb => simp only [constsBound_forallE]; exact fun ⟨ht, hb⟩ => ⟨iht ht, ihb hb⟩
  | letE _ _ _ _ iht ihv ihb =>
    simp only [constsBound_letE]; exact fun ⟨ht, hv, hb⟩ => ⟨iht ht, ihv hv, ihb hb⟩
  | proj _ _ _ ihe => simp only [constsBound_proj]; exact ihe

/-! ## Closed inference readings -/

/-- A closed subject accepted by `J.infer` reads and is graded at every assignment. -/
theorem inferClosed_reads_graded {J : Judgements md} {E : Env md} (m : EnvModel V E)
    (hJ : JudgeSound J m) {e t : Expr md} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) (hinf : J.infer E 0 e t) (ψ : LevelParam → Nat) :
    ∃ ea, denoteMeta m.acval E ψ 0 e = some ea ∧ ∀ ρ : Nat → V, WellDenotedV V ρ ea := by
  have hws : Expr.WScoped 0 e := Expr.WScoped.of_not_hasFvar hf
  have hnl : e.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hf
  have hL : Expr.LeavesBounded e := fun l hl => by rw [hnl] at hl; exact nomatch hl
  obtain ⟨ea, hea⟩ := hJ.accepted ψ hinf hws hb hL
  obtain ⟨ta, hta⟩ := hJ.reads ψ hinf hws hb hL (CtxOk.nil hnl) hea
  have hsem := (hJ.infer ψ hinf hws hb hL (CtxOk.nil hnl) hea hta).1
  exact ⟨ea, hea, fun ρ => hsem ρ (Sat_nil V ρ)⟩

/-! ## Phase 1: Model companion copies -/

private theorem auxKey_not_mem_natOpNames (k : Key md) (d : Ix.Kernel.Derived) :
    Ix.Kernel.auxKey k d ∉ Ix.Kernel.natOpNames := by
  simp [Ix.Kernel.natOpNames, Ix.Kernel.auxKey, Ix.Kernel.roleKey,
    Ix.Kernel.natPredName, Ix.Kernel.natAddName, Ix.Kernel.natSubName,
    Ix.Kernel.natMulName, Ix.Kernel.natPowName, Ix.Kernel.natBeqName,
    Ix.Kernel.natBleName]

private theorem auxKey_not_mem_natDivModNames (k : Key md) (d : Ix.Kernel.Derived) :
    Ix.Kernel.auxKey k d ∉ Ix.Kernel.natDivModNames := by
  simp [Ix.Kernel.natDivModNames, Ix.Kernel.auxKey, Ix.Kernel.roleKey,
    Ix.Kernel.natDivName, Ix.Kernel.natModName, Ix.Kernel.natGcdName,
    Ix.Kernel.natLandName, Ix.Kernel.natLorName, Ix.Kernel.natXorName,
    Ix.Kernel.natShiftLeftName, Ix.Kernel.natShiftRightName]

/-- Copying an already-stored model companion definition to a fresh `.model` key
extends the model with the source companion's leaf. -/
theorem installModelCopy {E : Env md} (mpE : EnvModelM V μ E)
    {recName kM : Key md} {cvm : ConstantVal md} {mval : Expr md} {hint : ReducibilityHint}
    (hfresh : E.find? (Ix.Kernel.auxKey recName .model) = none)
    (hsrc : E.find? kM = some (.defnInfo cvm mval hint)) :
    let c₀ : ConstantInfo md :=
      .defnInfo ⟨Ix.Kernel.auxKey recName .model, cvm.levelParams, cvm.type⟩ mval hint
    ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name (mpE.base2.acval kM) ∧
      ModelExt mpE mp' := by
  intro c₀
  have hmem : ConstantInfo.defnInfo cvm mval hint ∈ E.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hsrc
  have hnm : cvm.name = kM := Ix.Kernel.Semantics.Env.find?_name hsrc
  obtain ⟨htf, htp, htr, htb, hdef, -, -, -⟩ := mpE.base2.wf _ hmem
  obtain ⟨hvf, hvp, hvr, hvb⟩ := hdef cvm mval hint rfl
  have hnres : Ix.Kernel.reservedBasisNames.contains c₀.name = false :=
    Ix.Kernel.reservedBasisNames_contains_auxKey recName .model
  have hcbT : ConstsBound E cvm.type := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound E mval := constsBound_of_constsResolve _ hvr
  let A := mpE.base2.acval kM
  have hcomp : ∀ (ψ : LevelParam → Nat) (e : Expr md), ConstsBound E e →
      ∀ {ea : AnnotTerm}, denoteMeta mpE.base2.acval E ψ 0 e = some ea →
      denoteMeta (acvalWith mpE.base2.acval c₀.name A) ⟨c₀ :: E.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 e hcb h
  have hstep : ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name A := by
    refine declStep_preserves_of_cons mpE (c₀ := c₀) (A := A) hfresh
      (ConsHead.ofFresh
        (Ix.Kernel.EnvWF.cons mpE.base2.wf (Ix.Kernel.structConstWF htf htp
          (Ix.Kernel.Expr.constsResolve_mono htr) htb
          (fun _ _ _ heq => by
            obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
            exact ⟨hvf, hvp, Ix.Kernel.Expr.constsResolve_mono hvr, hvb⟩)
          (fun _ _ _ _ heq => nomatch heq)
          (fun _ heq => nomatch heq)
          (fun _ _ heq => nomatch heq)))
        (fun ψ => mpE.base2.cval_closedL kM ψ)
        hnres
        (fun _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
      (fun ψ k => mpE.base2.acval_closed kM ψ k)
      (fun ψ₁ ψ₂ hp => mpE.base2.acval_params kM _ hsrc ψ₁ ψ₂ hp)
      (fun ψ ρ => mpE.base2.acval_wellDenoted kM ψ ρ)
      (fun ψ ρ => mpE.acval_validV kM ψ ρ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mpE.type_reads _ hmem ψ
      exact ⟨ta, hcomp ψ cvm.type hcbT hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem ψ
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ cvm.type hcbT hta₀))
      rw [htaEq]
      exact mpE.type_wellDenotedV _ hmem ψ ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem ψ
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ cvm.type hcbT hta₀))
      have hm := mpE.mem_type _ hmem ψ ta₀ hta₀ ρ
      change interp V ρ (mpE.base2.acval cvm.name ψ) ∈ˢ interp V ρ ta₀ at hm
      rw [hnm] at hm
      rwa [htaEq]
    · intro ψ cv2 value2 ⟨hint2, hdt⟩
      injection hdt with h1 h2 h3
      rw [h2]
      have hv := mpE.defn_reads ψ cvm mval ⟨hint, hmem⟩
      rw [hnm] at hv
      exact hcomp ψ mval hcbV hv
    · exact fun φ => natHeads_cons_offNat mpE
        (ne_of_notReserved hnres reserved_natName)
        (ne_of_notReserved hnres reserved_natZeroName)
        (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
    · exact fun φ => natOps_cons_fresh mpE (mpE.nat_ops φ) (c₀ := c₀) (A := A) hfresh
        (hntc := fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (Or.inr (auxKey_not_mem_natOpNames recName .model)) _ rfl
    · exact fun φ => divMod_cons_fresh (mpE.div_mod φ) (c₀ := c₀) (A := A) hfresh
        (Or.inr (auxKey_not_mem_natDivModNames recName .model)) _ rfl
    · exact eqLaw_cons_valueKind mpE.eq_law (c₀ := c₀) (A := A)
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact capsOk_cons_fresh mpE mpE.caps_ok (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact fun φ => recRules_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
    · exact fun φ => towerOk_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
  obtain ⟨mp', hac⟩ := hstep
  exact ⟨mp', hac, (ModelExt.refl (mp₁ := mpE)).plain hac hfresh⟩

/-- Installing `twinModels ws` preserves `EnvModelM`, old lookups, old leaves, and
readings of `env`-bound terms. -/
theorem installTwinModels {env : Env md} (mp : EnvModelM V μ env) :
    ∀ (ws : List (TwinRecPart md)),
      ((twinModels ws).map (·.name)).Nodup →
      (∀ ci ∈ twinModels ws, env.find? ci.name = none) →
      (∀ w ∈ ws, ∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
        env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint)) →
      let envM : Env md := ⟨twinModels ws ++ env.consts⟩
      ∃ mpM : EnvModelM V μ envM,
        ModelExt mp mpM ∧
        (∀ k ci, env.find? k = some ci → envM.find? k = some ci) ∧
        (∀ k, (env.find? k).isSome = true → mpM.base2.acval k = mp.base2.acval k) ∧
        (∀ ψ d (e : Expr md), ConstsBound env e →
          ∀ {ea}, denoteMeta mp.base2.acval env ψ d e = some ea →
          denoteMeta mpM.base2.acval envM ψ d e = some ea)
  | [], _, _, _ =>
    ⟨mp, .refl, fun _ _ h => h, fun _ _ => rfl, fun _ _ _ _ {_} h => h⟩
  | w :: ws, hnd, hfr, hsrc => by
    cases hm : w.model? with
    | none =>
      have htm : twinModels (w :: ws) = twinModels ws := by
        simp [twinModels, TwinRecPart.modelInfo?, hm]
      rw [htm] at hnd hfr ⊢
      exact installTwinModels mp ws hnd hfr
        (fun w' hw' => hsrc w' (List.mem_cons_of_mem w hw'))
    | some q =>
      obtain ⟨cvm, mval, hint⟩ := q
      have htm : twinModels (w :: ws) =
          .defnInfo ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint ::
            twinModels ws := by
        simp [twinModels, TwinRecPart.modelInfo?, hm]
      rw [htm] at hnd hfr ⊢
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨mp₀, hext₀, hfind₀, hac₀, hmono₀⟩ := installTwinModels mp ws hnd.2
        (fun ci hci => hfr ci (List.mem_cons_of_mem _ hci))
        (fun w' hw' => hsrc w' (List.mem_cons_of_mem w hw'))
      let c₀ : ConstantInfo md :=
        .defnInfo ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint
      have hfresh₀ : (⟨twinModels ws ++ env.consts⟩ : Env md).find? c₀.name = none :=
        find?_append_none_of_not_mem hnd.1 (hfr c₀ List.mem_cons_self)
      have hsrc₀ : (⟨twinModels ws ++ env.consts⟩ : Env md).find? (Ix.Kernel.auxKey w.kC .model) =
          some (.defnInfo cvm mval hint) :=
        hfind₀ _ _ (hsrc w List.mem_cons_self cvm mval hint hm)
      obtain ⟨mp₁, hac₁, hext₁⟩ := installModelCopy mp₀ hfresh₀ hsrc₀
      refine ⟨mp₁, hext₀.trans hext₁, ?_, ?_, ?_⟩
      · intro k ci hk
        exact Ix.Kernel.Env.find?_cons_of_fresh hfresh₀ (hfind₀ k ci hk)
      · intro k hk
        have hk₀ : ((⟨twinModels ws ++ env.consts⟩ : Env md).find? k).isSome = true := by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
          rw [hfind₀ k ci hci]; rfl
        have hne : k ≠ c₀.name := fun heq => by rw [heq, hfresh₀] at hk₀; exact nomatch hk₀
        rw [hac₁, acvalWith_ne hne, hac₀ k hk]
      · intro ψ d e hcb ea hea
        rw [hac₁]
        exact denoteMeta_cons_fresh_mono (c₀ := c₀) hfresh₀
          (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ d e
          (constsBound_mono (fun n hn => by
            obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
            rw [hfind₀ n ci hci]; rfl) hcb)
          (hmono₀ ψ d e hcb hea)

/-! ## Phase 2: Provisioning rule-less twin recursors -/

/-- `CapsOk` survives a fresh recursor cons whose name is not a projection-slot name. -/
theorem capsOk_cons_rec_nonproj {E : Env md} (mpE : EnvModelM V μ E)
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {A : (LevelParam → Nat) → AnnotTerm}
    (hfresh : E.find? cvR.name = none)
    (hpshape : cvR.name.isProjFnShape = false)
    (m₂ : EnvModel V ⟨.recInfo cvR mI rP rules :: E.consts⟩)
    (hac : m₂.acval = acvalWith mpE.base2.acval cvR.name A) :
    CapsOk m₂ := by
  let c₀ : ConstantInfo md := .recInfo cvR mI rP rules
  have hdown : ∀ n : Key md, n ≠ cvR.name →
      (⟨c₀ :: E.consts⟩ : Env md).find? n = E.find? n := by
    intro n hn
    rw [Ix.Kernel.Env.find?_cons]
    exact if_neg (fun hh => hn hh.symm)
  constructor
  · intro T cvT caps hf hcape hres hfam φ' C hC us hlen
    have hnT : T ≠ cvR.name := by
      intro hh; subst hh
      have h0 := (Ix.Kernel.Env.find?_cons_self c₀ E).symm.trans hf
      exact nomatch Option.some.inj h0
    have hfE : E.find? T = some (.indInfo cvT caps) := by rwa [hdown T hnT] at hf
    obtain ⟨C', hCe, hCres, ⟨cvC, cnP, cnF, hfC⟩, hfP⟩ := hfam
    have hCe' : C' = C := Option.some.inj (hCe.symm.trans hC)
    rw [hCe'] at hfC hCres
    have hnC : C ≠ cvR.name := by
      intro hh; subst hh
      have h0 := (Ix.Kernel.Env.find?_cons_self c₀ E).symm.trans hfC
      exact nomatch Option.some.inj h0
    have hnP : ∀ j, j < caps.etaFields → Ix.Kernel.projFnName T j ≠ cvR.name :=
      fun _ _ => Ix.Kernel.projFnName_ne_of_shape hpshape
    have hfamE : Ix.Kernel.EtaFamilyStored E T caps := by
      refine ⟨C, hC, hCres, ⟨cvC, cnP, cnF, by rwa [hdown C hnC] at hfC⟩, fun j hj => ?_⟩
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      rw [hdown _ (hnP j hj)] at hf2
      exact ⟨cv2, mI2, rP2, rules2, hf2⟩
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mpE.caps_ok.1 T cvT caps hfE hcape hres hfamE φ' C hC us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_fresh_mono (c₀ := c₀) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ 0 _
        (constsBound_instType mpE.base2.wf (Ix.Kernel.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT] at hmem
      have hfab : etaFabArgsV
            (fun n => interp V ρ (m₂.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields
          = etaFabArgsV
            (fun n => interp V ρ (mpE.base2.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields := by
        unfold etaFabArgsV projSpines
        refine congrArg _ (List.map_congr_left fun j hj => ?_)
        dsimp only
        rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
      rw [hfab, hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
  · intro T cvT caps hf hcapu hres φ' us hlen
    have hnT : T ≠ cvR.name := by
      intro hh; subst hh
      have h0 := (Ix.Kernel.Env.find?_cons_self c₀ E).symm.trans hf
      exact nomatch Option.some.inj h0
    have hfE : E.find? T = some (.indInfo cvT caps) := by rwa [hdown T hnT] at hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      mpE.caps_ok.2 T cvT caps hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_fresh_mono (c₀ := c₀) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ 0 _
        (constsBound_instType mpE.base2.wf (Ix.Kernel.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hmx hmy
      rw [hac, acvalWith_ne hnT] at hmx hmy
      exact hlaw ρ ts rest x y hlents hfit hmx hmy

/-- Type reading and membership facts for one twin recursor at the base environment `env`. -/
theorem twinTypeAtBase {J : Judgements md} {env : Env md}
    (mp : EnvModelM V μ env) (hJ : JudgeSound J mp.base2)
    {w : TwinRecPart md} {tyG : Expr md}
    (hfkC : env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC))
    (hlfW' : letFree w.cvW'.type = true)
    (hWC : WrapRel env.find? tyG w.cvC.type)
    (hWW' : WrapRel env.find? tyG w.cvW'.type)
    (htyG : tyG = w.cvC.type ∨
      (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
        tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
        ∃ sty, J.infer env 0 tyG sty))
    (ψ : LevelParam → Nat) :
    ∃ TVg TVc TVw',
      denoteMeta mp.base2.acval env ψ 0 tyG = some TVg ∧
      denoteMeta mp.base2.acval env ψ 0 w.cvC.type = some TVc ∧
      denoteMeta mp.base2.acval env ψ 0 w.cvW'.type = some TVw' ∧
      ConstsBound env tyG ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ TVg) ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ TVw') ∧
      (∀ ρ : Nat → V, interp V ρ (mp.base2.acval w.kC ψ) ∈ˢ interp V ρ TVw') ∧
      AW TVg TVc ∧ AW TVg TVw' := by
  have hmemC : ConstantInfo.recInfo w.cvC w.mI w.rP w.rulesC ∈ env.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hfkC
  have hnmC : w.cvC.name = w.kC := Ix.Kernel.Semantics.Env.find?_name hfkC
  obtain ⟨-, -, htrC, -⟩ := mp.base2.wf _ hmemC
  obtain ⟨TVc, hTVc⟩ := mp.type_reads _ hmemC ψ
  have hokC : ∀ ρ : Nat → V, WellDenotedV V ρ TVc := mp.type_wellDenotedV _ hmemC ψ TVc hTVc
  have hmemTypeC : ∀ ρ : Nat → V, interp V ρ (mp.base2.acval w.kC ψ) ∈ˢ interp V ρ TVc := by
    intro ρ
    have hm := mp.mem_type _ hmemC ψ TVc hTVc ρ
    change interp V ρ (mp.base2.acval w.cvC.name ψ) ∈ˢ interp V ρ TVc at hm
    rwa [hnmC] at hm
  have hlfC : letFree w.cvC.type = true :=
    letFree_of_denoteMeta (w.cvC.type.sizeB + 1) w.cvC.type (Nat.lt_succ_self _) 0 TVc hTVc
  rcases htyG with rfl | ⟨hgfv, -, hgres, hgbv, sty, hginf⟩
  · obtain ⟨TVw', hTVw', hAWW'⟩ :=
      wrapRel_read (fun _ _ h => h) mp.defn_reads hWW' hlfW' hTVc
    refine ⟨TVc, TVc, TVw', hTVc, hTVc, hTVw', constsBound_of_constsResolve _ htrC,
      hokC, fun ρ => (hAWW'.sem ρ (hokC ρ)).1, ?_, .refl TVc, hAWW'⟩
    intro ρ
    rw [← (hAWW'.sem ρ (hokC ρ)).2]
    exact hmemTypeC ρ
  · obtain ⟨TVg, hTVg, hokG⟩ := inferClosed_reads_graded mp.base2 hJ hgfv hgbv hginf ψ
    obtain ⟨TVc', hTVc', hAWC⟩ :=
      wrapRel_read (fun _ _ h => h) mp.defn_reads hWC hlfC hTVg
    have hTVcEq : TVc' = TVc := Option.some.inj (hTVc'.symm.trans hTVc)
    rw [hTVcEq] at hAWC
    obtain ⟨TVw', hTVw', hAWW'⟩ :=
      wrapRel_read (fun _ _ h => h) mp.defn_reads hWW' hlfW' hTVg
    refine ⟨TVg, TVc, TVw', hTVg, hTVc, hTVw', constsBound_of_constsResolve _ hgres,
      hokG, fun ρ => (hAWW'.sem ρ (hokG ρ)).1, ?_, hAWC, hAWW'⟩
    intro ρ
    rw [← (hAWW'.sem ρ (hokG ρ)).2, (hAWC.sem ρ (hokG ρ)).2]
    exact hmemTypeC ρ

/-- Provisioning one rule-less twin recursor at leaf `mp.base2.acval w.kC`. -/
theorem installTwinProvOne {J : Judgements md} {env E : Env md}
    (mp : EnvModelM V μ env) (hfr : JudgeFrames J env) (hJ : JudgeSound J mp.base2)
    (mpE : EnvModelM V μ E)
    (hfindE : ∀ k ci, env.find? k = some ci → E.find? k = some ci)
    (hmonoE : ∀ ψ d (e : Expr md), ConstsBound env e →
      ∀ {ea}, denoteMeta mp.base2.acval env ψ d e = some ea →
      denoteMeta mpE.base2.acval E ψ d e = some ea)
    {w : TwinRecPart md}
    (hfresh : E.find? w.cvW'.name = none)
    (hcv : ConstantValCheckJ J env w.cvW w.cvW')
    (hlfW' : letFree w.cvW'.type = true)
    (hfkC : env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC))
    (hlps : w.cvW.levelParams = w.cvC.levelParams)
    {tyG : Expr md}
    (hWC : WrapRel env.find? tyG w.cvC.type)
    (hWW' : WrapRel env.find? tyG w.cvW'.type)
    (htyG : tyG = w.cvC.type ∨
      (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
        tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
        ∃ sty, J.infer env 0 tyG sty)) :
    let c₀ : ConstantInfo md := .recInfo w.cvW' w.mI w.rP []
    ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval w.cvW'.name (mp.base2.acval w.kC) ∧
      ModelExt mpE mp' := by
  intro c₀
  obtain ⟨-, hnresW, hshW, -, -, -, _⟩ := hcv.inv
  obtain ⟨htf, htp, htr, htb⟩ := ConstantValCheckJ.typeWF hfr hcv
  have hnres : Ix.Kernel.reservedBasisNames.contains w.cvW'.name = false := by
    rw [hcv.name_eq]; exact hnresW
  have hsh : w.cvW'.name.isProjFnShape = false := by
    rw [hcv.name_eq]; exact hshW
  have hlps' : w.cvW'.levelParams = w.cvC.levelParams := hcv.levelParams_eq.trans hlps
  have htrE : w.cvW'.type.constsResolve E = true :=
    Ix.Kernel.Expr.constsResolve_le (fun n hn => by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      rw [hfindE n ci hci]; rfl) htr
  let A := mp.base2.acval w.kC
  have hcbW' : ConstsBound env w.cvW'.type := constsBound_of_constsResolve _ htr
  have hcbW'E : ConstsBound E w.cvW'.type := constsBound_of_constsResolve _ htrE
  have hstep : ∃ mp' : EnvModelM V μ ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name A := by
    refine declStep_preserves_of_ind_rec_cons mpE (c₀ := c₀) (A := A) hfresh hnres
      ⟨w.cvW', w.mI, w.rP, [], rfl⟩
      (ConsHead.ofFresh
        (Ix.Kernel.EnvWF.cons mpE.base2.wf (Ix.Kernel.structConstWF htf htp
          (Ix.Kernel.Expr.constsResolve_mono htrE) htb
          (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ heq r hr => by
            obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj heq
            exact nomatch hr)))
        (fun ψ => mp.base2.cval_closedL w.kC ψ)
        hnres
        (fun _ heq => nomatch heq)
        (fun _ _ _ _ heq r hr => by
          obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj heq
          exact nomatch hr))
      (fun ψ k => mp.base2.acval_closed w.kC ψ k)
      (fun ψ₁ ψ₂ hp => mp.base2.acval_params w.kC _ hfkC ψ₁ ψ₂
        (fun q hq => hp q (by show q ∈ w.cvW'.levelParams; rw [hlps']; exact hq)))
      (fun ψ ρ => mp.base2.acval_wellDenoted w.kC ψ ρ)
      (fun ψ ρ => mp.acval_validV w.kC ψ ρ)
      ?_ ?_ ?_
      (fun m₂ hm₂ => capsOk_cons_rec_nonproj mpE hfresh hsh m₂ hm₂)
      (fun m₂ hm₂ φ => recRules_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ heq => by
          obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj heq
          rfl) m₂ hm₂ φ)
    · intro ψ
      obtain ⟨_, _, TVw', -, -, hTVw', -, -, -, -, -, -⟩ :=
        twinTypeAtBase mp hJ hfkC hlfW' hWC hWW' htyG ψ
      exact ⟨TVw', denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 w.cvW'.type hcbW'E
        (hmonoE ψ 0 w.cvW'.type hcbW' hTVw')⟩
    · intro ψ ta hta ρ
      obtain ⟨_, _, TVw', -, -, hTVw', -, -, hokW', -, -, -⟩ :=
        twinTypeAtBase mp hJ hfkC hlfW' hWC hWW' htyG ψ
      have hTVw'1 := denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 w.cvW'.type hcbW'E
        (hmonoE ψ 0 w.cvW'.type hcbW' hTVw')
      obtain rfl : ta = TVw' := Option.some.inj (hta.symm.trans hTVw'1)
      exact hokW' ρ
    · intro ψ ta hta ρ
      obtain ⟨_, _, TVw', -, -, hTVw', -, -, -, hmemW', -, -⟩ :=
        twinTypeAtBase mp hJ hfkC hlfW' hWC hWW' htyG ψ
      have hTVw'1 := denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 w.cvW'.type hcbW'E
        (hmonoE ψ 0 w.cvW'.type hcbW' hTVw')
      obtain rfl : ta = TVw' := Option.some.inj (hta.symm.trans hTVw'1)
      exact hmemW' ρ
  obtain ⟨mp', hac⟩ := hstep
  exact ⟨mp', hac, (ModelExt.refl (mp₁ := mpE)).plain hac hfresh⟩

/-- Provisioning `twinProv ws` on top of `envM` installs each twin at leaf `mp.base2.acval w.kC`. -/
theorem installTwinProv {J : Judgements md} {env envM : Env md}
    (mp : EnvModelM V μ env) (hfr : JudgeFrames J env) (hJ : JudgeSound J mp.base2)
    (mpM : EnvModelM V μ envM)
    (hfindM : ∀ k ci, env.find? k = some ci → envM.find? k = some ci)
    (hacM : ∀ k, (env.find? k).isSome = true → mpM.base2.acval k = mp.base2.acval k)
    (hmonoM : ∀ ψ d (e : Expr md), ConstsBound env e →
      ∀ {ea}, denoteMeta mp.base2.acval env ψ d e = some ea →
      denoteMeta mpM.base2.acval envM ψ d e = some ea) :
    ∀ (ws : List (TwinRecPart md)),
      ((twinProv ws).map (·.name)).Nodup →
      (∀ ci ∈ twinProv ws, envM.find? ci.name = none) →
      (∀ w ∈ ws,
        ConstantValCheckJ J env w.cvW w.cvW' ∧
        letFree w.cvW'.type = true ∧
        env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) ∧
        w.cvW.levelParams = w.cvC.levelParams ∧
        ∃ tyG : Expr md,
          WrapRel env.find? tyG w.cvC.type ∧
          WrapRel env.find? tyG w.cvW'.type ∧
          (tyG = w.cvC.type ∨
            (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
              tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
              ∃ sty, J.infer env 0 tyG sty))) →
      let envSelf : Env md := ⟨twinProv ws ++ envM.consts⟩
      ∃ mpSelf : EnvModelM V μ envSelf,
        ModelExt mpM mpSelf ∧
        (∀ k ci, env.find? k = some ci → envSelf.find? k = some ci) ∧
        (∀ k, (env.find? k).isSome = true → mpSelf.base2.acval k = mp.base2.acval k) ∧
        (∀ w ∈ ws, mpSelf.base2.acval w.cvW.name = mp.base2.acval w.kC) ∧
        (∀ ψ d (e : Expr md), ConstsBound env e →
          ∀ {ea}, denoteMeta mp.base2.acval env ψ d e = some ea →
          denoteMeta mpSelf.base2.acval envSelf ψ d e = some ea)
  | [], _, _, _ =>
    ⟨mpM, .refl, hfindM, hacM, (fun _ h => absurd h List.not_mem_nil), hmonoM⟩
  | w :: ws, hnd, hfrM, hall => by
    simp only [twinProv, List.map_cons, List.nodup_cons] at hnd
    have hnd' : ((twinProv ws).map (·.name)).Nodup := hnd.2
    obtain ⟨mp₀, hext₀, hfind₀, hac₀, hleaf₀, hmono₀⟩ :=
      installTwinProv mp hfr hJ mpM hfindM hacM hmonoM ws hnd'
        (fun ci hci => hfrM ci (List.mem_cons_of_mem _ hci))
        (fun w' hw' => hall w' (List.mem_cons_of_mem w hw'))
    obtain ⟨hcv, hlfW', hfkC, hlps, tyG, hWC, hWW', htyG⟩ := hall w List.mem_cons_self
    let c₀ : ConstantInfo md := .recInfo w.cvW' w.mI w.rP []
    have hfresh₀ : (⟨twinProv ws ++ envM.consts⟩ : Env md).find? w.cvW'.name = none :=
      find?_append_none_of_not_mem hnd.1 (hfrM c₀ List.mem_cons_self)
    obtain ⟨mp₁, hac₁, hext₁⟩ :=
      installTwinProvOne mp hfr hJ mp₀ hfind₀ hmono₀ hfresh₀ hcv hlfW' hfkC hlps hWC hWW' htyG
    refine ⟨mp₁, hext₀.trans hext₁, ?_, ?_, ?_, ?_⟩
    · intro k ci hk
      exact Ix.Kernel.Env.find?_cons_of_fresh hfresh₀ (hfind₀ k ci hk)
    · intro k hk
      have hk₀ : ((⟨twinProv ws ++ envM.consts⟩ : Env md).find? k).isSome = true := by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
        rw [hfind₀ k ci hci]; rfl
      have hne : k ≠ w.cvW'.name := fun heq => by rw [heq, hfresh₀] at hk₀; exact nomatch hk₀
      rw [hac₁, acvalWith_ne hne, hac₀ k hk]
    · intro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · rw [hac₁, ← hcv.name_eq, acvalWith_self]
      · have hcv' := (hall w' (List.mem_cons_of_mem w hw')).1
        have hmemP : w'.cvW'.name ∈ (twinProv ws).map (·.name) :=
          List.mem_map.mpr ⟨.recInfo w'.cvW' w'.mI w'.rP [],
            List.mem_map.mpr ⟨w', hw', rfl⟩, rfl⟩
        have hne : w'.cvW.name ≠ w.cvW'.name := by
          rw [← hcv'.name_eq]
          intro heq
          apply hnd.1
          show w.cvW'.name ∈ (twinProv ws).map (·.name)
          rw [← heq]
          exact hmemP
        rw [hac₁, acvalWith_ne hne, hleaf₀ w' hw']
    · intro ψ d e hcb ea hea
      rw [hac₁]
      exact denoteMeta_cons_fresh_mono (c₀ := c₀) hfresh₀
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ d e
        (constsBound_mono (fun n hn => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
          rw [hfind₀ n ci hci]; rfl) hcb)
        (hmono₀ ψ d e hcb hea)

/-! ## Phase 3: Peer renaming, rule laws, and group swap -/

/-- `twinProv ws ++ rest` and `twinRecs ws ++ rest` form a `SwapShList`. -/
theorem twinSwapShList (rest : List (ConstantInfo md)) :
    ∀ (ws : List (TwinRecPart md)),
      Ix.Kernel.SwapShList (twinProv ws ++ rest) (twinRecs ws ++ rest)
  | [] => Ix.Kernel.SwapShList.of_eq rest
  | w :: ws =>
    Ix.Kernel.SwapShList.cons (Or.inr ⟨w.cvW', w.mI, w.rP, w.rulesW', rfl, rfl⟩)
      (twinSwapShList rest ws)

/-- The canonical-to-twin peer renaming `f` satisfies `RenameOk` at `envSelf`. -/
theorem twinRenameOk {J : Judgements md} {env envM : Env md}
    {acvalBase acvalSelf : Key md → (LevelParam → Nat) → AnnotTerm}
    {ws : List (TwinRecPart md)} {f : Key md → Key md}
    (hndP : ((twinProv ws).map (·.name)).Nodup)
    (hfindSelf : ∀ k ci, env.find? k = some ci →
      (⟨twinProv ws ++ envM.consts⟩ : Env md).find? k = some ci)
    (hacOld : ∀ k, (env.find? k).isSome = true → acvalSelf k = acvalBase k)
    (hacTwin : ∀ w ∈ ws, acvalSelf w.cvW.name = acvalBase w.kC)
    (hf : ∀ k, f k = k ∨ ∃ w' ∈ ws, k = w'.kC ∧ f k = w'.cvW.name)
    (hall : ∀ w ∈ ws,
      ConstantValCheckJ J env w.cvW w.cvW' ∧
      env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) ∧
      w.cvW.levelParams = w.cvC.levelParams) :
    RenameOk acvalSelf ⟨twinProv ws ++ envM.consts⟩ f := by
  let envSelf : Env md := ⟨twinProv ws ++ envM.consts⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n ci hfS
    rcases hf n with heq | ⟨w', hw', rfl, hfn⟩
    · rw [heq]; exact ⟨ci, hfS, rfl⟩
    · obtain ⟨hcv', hfkC', hlps'⟩ := hall w' hw'
      have hfC := hfindSelf w'.kC _ hfkC'
      obtain rfl : ci = .recInfo w'.cvC w'.mI w'.rP w'.rulesC :=
        Option.some.inj (hfS.symm.trans hfC)
      have hmemP : ConstantInfo.recInfo w'.cvW' w'.mI w'.rP [] ∈ twinProv ws :=
        List.mem_map.mpr ⟨w', hw', rfl⟩
      have hfW := find?_mem_of_nodup (rest := envM.consts) hndP hmemP
      rw [hfn, ← hcv'.name_eq]
      exact ⟨.recInfo w'.cvW' w'.mI w'.rP [], hfW, hcv'.levelParams_eq.trans hlps'⟩
  · intro n hfS
    rcases hf n with heq | ⟨w', hw', rfl, -⟩
    · rwa [heq]
    · obtain ⟨-, hfkC', -⟩ := hall w' hw'
      rw [hfindSelf w'.kC _ hfkC'] at hfS
      exact nomatch hfS
  · intro n ψ
    rcases hf n with heq | ⟨w', hw', rfl, hfn⟩
    · rw [heq]
    · obtain ⟨-, hfkC', -⟩ := hall w' hw'
      rw [hfn, hacTwin w' hw', hacOld w'.kC (by rw [hfkC']; rfl)]

/-- Transporting `RecRuleLaw` from the canonical rule `rC` to the twin rule `rW'`
at the provisioned model `mpSelf`. -/
theorem RecRuleLaw.wrapTwin {J : Judgements md} {env envSelf : Env md}
    (mp : EnvModelM V μ env) (hJ : JudgeSound J mp.base2)
    (mpSelf : EnvModelM V μ envSelf)
    (hfindSelf : ∀ k ci, env.find? k = some ci → envSelf.find? k = some ci)
    (hmonoSelf : ∀ ψ d (e : Expr md), ConstsBound env e →
      ∀ {ea}, denoteMeta mp.base2.acval env ψ d e = some ea →
      denoteMeta mpSelf.base2.acval envSelf ψ d e = some ea)
    {f : Key md → Key md} (hro : RenameOk mpSelf.base2.acval envSelf f)
    {w : TwinRecPart md} {tyG : Expr md}
    (hcv : ConstantValCheckJ J env w.cvW w.cvW')
    (hlfTyW' : letFree w.cvW'.type = true)
    (hfkC : env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC))
    (hlps : w.cvW.levelParams = w.cvC.levelParams)
    (hacN : mpSelf.base2.acval w.cvW'.name = mpSelf.base2.acval w.kC)
    (hWC : WrapRel env.find? tyG w.cvC.type)
    (hWW' : WrapRel env.find? tyG w.cvW'.type)
    (htyG : tyG = w.cvC.type ∨
      (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
        tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
        ∃ sty, J.infer env 0 tyG sty))
    {rW rW' rC : RecRule md}
    (hrC : rC ∈ w.rulesC)
    (hrule : TwinRuleJ J env envSelf f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP rW rW' rC)
    (hfireW' : rW'.fire ≠ .inert)
    (φ : LevelParam → Nat) :
    RecRuleLaw mpSelf.base2 φ w.cvW'.name w.cvW' w.mI w.rP rW' := by
  obtain ⟨-, -, -, -, -, -, -, hlfRhsW', hctor, hnf, hcp, hfireEq, -, hpb, -,
    hplainShape, hnestShape, rhsG, hRhsC, hRhsW', hrhsG⟩ := hrule
  have hlps' : w.cvW'.levelParams = w.cvC.levelParams := hcv.levelParams_eq.trans hlps
  have hcbC : ConstsBound env w.cvC.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfkC)).2.2.1
  have hcbW' : ConstsBound env w.cvW'.type :=
    constsBound_of_constsResolve _ (ConstantValCheckJ.typeWF hJ.toJudgeFrames hcv).2.2.1
  -- `w.cvW'.type.stripPis (w.mI + 1)` is `some`, hence `(tyG.stripPis (w.mI + 1)).isSome = true`
  have hissG : (tyG.stripPis (w.mI + 1)).isSome = true := by
    have hmajW' : ∃ pre dom body bm,
        w.cvW'.type.stripPis w.mI = some (pre, .forallE dom body bm) := by
      cases hfr0 : rW'.fire with
      | inert => exact absurd hfr0 hfireW'
      | plain =>
        obtain ⟨⟨cvj0, hfc0, -⟩, -⟩ := mp.base2.rec_ctors w.kC w.cvC w.mI w.rP w.rulesC hfkC rC hrC
        rw [← hctor] at hfc0
        obtain ⟨pre, dom, body, bm, _, hs, -⟩ :=
          Ix.Kernel.recRulePlain_shapeT (hplainShape hfr0 cvj0 rC.ctorParams rC.nfields hfc0)
        exact ⟨pre, dom, body, bm, hs⟩
      | nested lvls pins =>
        obtain ⟨pre, dom, body, bm, _, hs, -⟩ := hnestShape lvls pins hfr0
        exact ⟨pre, dom, body, bm, hs⟩
    obtain ⟨pre, dom, body, bm, hsW'⟩ := hmajW'
    have hsW'1 : w.cvW'.type.stripPis (w.mI + 1) = some (pre ++ [(dom, bm)], body) :=
      Ix.Kernel.stripPis_append w.mI hsW'
        (show (Expr.forallE dom body bm).stripPis 1 = some ([(dom, bm)], body) from rfl)
    obtain ⟨bsG, bodyG, hsG, -⟩ := WrapT.stripPis_back (w.mI + 1) (hWW'.toWrapT hlfTyW') hsW'1
    rw [hsG]; rfl
  -- canonical rule law at `mpSelf`
  have hlawC := mpSelf.rec_rules φ w.kC w.cvC w.mI w.rP w.rulesC
    (hfindSelf w.kC _ hfkC) rC hrC (fun hc => hfireW' (hfireEq.trans hc))
  unfold RecRuleLaw at hlawC ⊢
  obtain ⟨hle, hC⟩ := hlawC
  have hcmp : Ix.Kernel.recFireComparands rW' = Ix.Kernel.recFireComparands rC := by
    funext lps0 us0 cvjLps0 args0 rP0
    unfold Ix.Kernel.recFireComparands
    rw [hfireEq, hcp]
  refine ⟨hle, fun us hus => ?_⟩
  have husC : us.length = w.cvC.levelParams.length := by rw [← hlps']; exact hus
  let ψ := Level.substFn φ w.cvC.levelParams us
  obtain ⟨Rc, hRcInst, hokRc, hpinsC, hbodyC⟩ := hC us husC
  have hRc : denoteMeta mpSelf.base2.acval envSelf ψ 0 rC.rhs = some Rc := by
    rwa [denotePInstLevels mpSelf.base2] at hRcInst
  -- RHS reading and semantic agreement at `mpSelf`
  have hRhsRel : ∃ Rw',
      denoteMeta mpSelf.base2.acval envSelf ψ 0 rW'.rhs = some Rw' ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Rw' ∧ interp V ρ Rc = interp V ρ Rw' := by
    rcases hrhsG with rfl | ⟨hrfv, -, hrres, hrbv, rty, hrinf⟩
    · have hren : denoteMeta mpSelf.base2.acval envSelf ψ 0 (rC.rhs.renameConsts f) = some Rc := by
        rw [denoteMeta_renameConsts hro]; exact hRc
      obtain ⟨Rw', hRw', hAWW'⟩ :=
        wrapRel_read hfindSelf mpSelf.defn_reads hRhsW' hlfRhsW' hren
      exact ⟨Rw', hRw', fun ρ => hAWW'.sem ρ (hokRc ρ)⟩
    · obtain ⟨Rg₀, hRg₀, hokRg⟩ := inferClosed_reads_graded mp.base2 hJ hrfv hrbv hrinf ψ
      have hRg := hmonoSelf ψ 0 rhsG (constsBound_of_constsResolve _ hrres) hRg₀
      have hlfRc : letFree rC.rhs = true :=
        letFree_of_denoteMeta (rC.rhs.sizeB + 1) rC.rhs (Nat.lt_succ_self _) 0 Rc hRc
      obtain ⟨Rc', hRc', hAWC⟩ :=
        wrapRel_read hfindSelf mpSelf.defn_reads hRhsC hlfRc hRg
      have hRcEq : Rc' = Rc := Option.some.inj (hRc'.symm.trans hRc)
      rw [hRcEq] at hAWC
      have hren : denoteMeta mpSelf.base2.acval envSelf ψ 0 (rhsG.renameConsts f) = some Rg₀ := by
        rw [denoteMeta_renameConsts hro]; exact hRg
      obtain ⟨Rw', hRw', hAWW'⟩ :=
        wrapRel_read hfindSelf mpSelf.defn_reads hRhsW' hlfRhsW' hren
      refine ⟨Rw', hRw', fun ρ => ?_⟩
      obtain ⟨hokW', heqGW'⟩ := hAWW'.sem ρ (hokRg ρ)
      obtain ⟨-, heqGC⟩ := hAWC.sem ρ (hokRg ρ)
      exact ⟨hokW', heqGC.symm.trans heqGW'⟩
  obtain ⟨Rw', hRw', hsemR⟩ := hRhsRel
  -- Type readings and `PiChain` at `mpSelf`
  obtain ⟨TVg, TVc, TVw', hTVg₀, hTVc₀, hTVw'₀, hcbG, hokG, -, -, hAWTyC, hAWTyW'⟩ :=
    twinTypeAtBase mp hJ hfkC hlfTyW' hWC hWW' htyG ψ
  have hTVg := hmonoSelf ψ 0 tyG hcbG hTVg₀
  have hTVc := hmonoSelf ψ 0 w.cvC.type hcbC hTVc₀
  have hTVw' := hmonoSelf ψ 0 w.cvW'.type hcbW' hTVw'₀
  have hpcG : PiChain (w.mI + 1) TVg := Rules.piChain_of_stripPis (w.mI + 1) hissG hTVg
  have hpcGrP : PiChain w.rP TVg := piChain_of_le (Nat.le_trans hle (Nat.le_succ w.mI)) hpcG
  refine ⟨Rw', ?_, fun ρ => (hsemR ρ).1, ?_, ?_⟩
  · rw [denotePInstLevels mpSelf.base2, hlps']; exact hRw'
  · intro lvls pins hfr i hi
    obtain ⟨vpa, hvpa, hgrC⟩ := hpinsC lvls pins (hfireEq.symm.trans hfr) i (hcp ▸ hi)
    refine ⟨vpa, by rw [hlps']; exact hvpa, ?_⟩
    intro ρ zs TVa restR hzl hzok hTVa hfitW'
    rw [denotePInstLevels mpSelf.base2, hlps'] at hTVa
    have hTVaEq : TVa = TVw' := Option.some.inj (hTVa.symm.trans hTVw')
    rw [hTVaEq] at hfitW'
    have hpcW'rP : PiChain zs.length TVw' := by
      rw [hzl]; exact hAWTyW'.piChain w.rP hpcGrP
    have hfitVw' := teleFit_of_teleFitPA hpcW'rP hfitW'
    obtain ⟨_, hfitVg⟩ := AW.teleFit (zs.map (interp V ρ)) hAWTyW' (hokG ρ) hfitVw'
    obtain ⟨_, hfitVc⟩ := AW.teleFit_fwd (zs.map (interp V ρ)) hAWTyC (hokG ρ) hfitVg
    have hpcCrP : PiChain zs.length TVc := by
      rw [hzl]; exact hAWTyC.piChain w.rP hpcGrP
    obtain ⟨restC_pins, hfitPAc⟩ := teleFitPA_of_teleFit hpcCrP hfitVc
    exact hgrC ρ zs TVc restC_pins hzl hzok
      (by rw [denotePInstLevels mpSelf.base2]; exact hTVc) hfitPAc
  · intro cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxl hyl hujl hlev hplain hnested hidx
      hTVa hTVja hfitR hfitC
    rw [denotePInstLevels mpSelf.base2, hlps'] at hTVa
    have hTVaEq : TVa = TVw' := Option.some.inj (hTVa.symm.trans hTVw')
    rw [hTVaEq] at hfitR
    let majArg := AnnotTerm.mkAppN
      (mpSelf.base2.acval rW'.ctor (Level.substFn φ cvj.levelParams usj)) ys
    have hlenS : (xs ++ [majArg]).length = w.mI + 1 := by simp [hxl]
    have hpcW' : PiChain (xs ++ [majArg]).length TVw' := by
      rw [hlenS]; exact hAWTyW'.piChain (w.mI + 1) hpcG
    have hfitVw' := teleFit_of_teleFitPA hpcW' hfitR
    obtain ⟨_, hfitVg⟩ := AW.teleFit ((xs ++ [majArg]).map (interp V ρ)) hAWTyW' (hokG ρ) hfitVw'
    obtain ⟨_, hfitVc⟩ := AW.teleFit_fwd ((xs ++ [majArg]).map (interp V ρ)) hAWTyC (hokG ρ) hfitVg
    have hpcC : PiChain (xs ++ [majArg]).length TVc := by
      rw [hlenS]; exact hAWTyC.piChain (w.mI + 1) hpcG
    obtain ⟨restRc, hfitPAc⟩ := teleFitPA_of_teleFit hpcC hfitVc
    have hfcC : envSelf.find? rC.ctor = some (.ctorInfo cvj cnP cnF) := by rwa [← hctor]
    have hylC : ys.length = rC.ctorParams + rC.nfields := by rwa [← hcp, ← hnf]
    have hlevC : Level.substFn φ cvj.levelParams usj =
        Level.substFn φ cvj.levelParams
          (Ix.Kernel.recFireComparands rC w.cvC.levelParams us cvj.levelParams [] w.rP).1 := by
      rwa [← hcmp, ← hlps']
    have hplainC : rC.paramsBlind = false → rC.fire = .plain →
        ∀ i, i < rC.ctorParams → i < w.mI →
          interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default) := by
      intro hpbC hfpC i hi hm
      exact hplain (hpb.trans hpbC) (hfireEq.trans hfpC) i (hcp.symm ▸ hi) hm
    have hnestedC : ∀ lvls pins, rC.fire = .nested lvls pins →
        ∀ i, i < rC.ctorParams → ∀ vpa : AnnotTerm,
          denoteMeta mpSelf.base2.acval envSelf φ w.rP
            (Ix.Kernel.Verify.openRev 0 w.rP
              ((pins.getD i default).instantiateLevelParams w.cvC.levelParams us)) = some vpa →
          interp V ρ (ys.getD i default) =
            interp V ρ (AnnotTerm.instRevChain (xs.take w.rP) vpa) := by
      intro lvls pins hfnC i hi vpa hvpa
      exact hnested lvls pins (hfireEq.trans hfnC) i (hcp.symm ▸ hi) vpa
        (by rw [hlps']; exact hvpa)
    have hidxC : IotaIndexPin (V := V) ρ restC rC.ctorParams w.mI w.rP xs := by
      rwa [← hcp]
    have hfitPAc' : TeleFitPA V ρ TVc
        (xs ++ [AnnotTerm.mkAppN
          (mpSelf.base2.acval rC.ctor (Level.substFn φ cvj.levelParams usj)) ys]) restRc := by
      simpa [majArg, hctor] using hfitPAc
    obtain ⟨heq, hwd⟩ := hbodyC cvj cnP cnF hfcC usj ρ xs ys TVc TVja restRc restC
      hxl hylC hujl hlevC hplainC hnestedC hidxC
      (by rw [denotePInstLevels mpSelf.base2]; exact hTVc) hTVja hfitPAc' hfitC
    rw [hacN, hlps', hctor, hcp]
    refine ⟨heq.trans ?_, fun hxs hys => ?_⟩
    · rw [interp_mkAppN, interp_mkAppN, (hsemR ρ).2]
    · exact wellDenotedV_mkAppN_congr _ (hsemR ρ).1 (hsemR ρ).2 (hwd hxs hys)

/-- `RuleFacts` at `envSelf` for one checked twin rule, derived from `TwinRuleJ`
and its already-established `RecRuleLaw`. -/
theorem twinRuleFacts {J : Judgements md} {env envSelf : Env md}
    (hfrSelf : JudgeFrames J envSelf)
    (hwfEnv : Ix.Kernel.EnvWF env)
    (hrcEnv : Ix.Kernel.RecCtorsStored env)
    (mpSelf : EnvModelM V μ envSelf)
    (hfindSelf : ∀ k ci, env.find? k = some ci → envSelf.find? k = some ci)
    {f : Key md → Key md} {w : TwinRecPart md}
    (hcvName : w.cvW'.name = w.cvW.name)
    (hlps' : w.cvW'.levelParams = w.cvC.levelParams)
    (hfkC : env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC))
    {rW rW' rC : RecRule md}
    (hrC : rC ∈ w.rulesC)
    (hrule : TwinRuleJ J env envSelf f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP rW rW' rC)
    (hlaw : rW'.fire ≠ .inert → ∀ φ, RecRuleLaw mpSelf.base2 φ w.cvW'.name w.cvW' w.mI w.rP rW') :
    RuleFacts envSelf mpSelf.base2.cvalE w.cvW' w.mI w.rP rW' := by
  obtain ⟨-, -, hrbv, hrfv, hann, hrlp, hrres, -, hctor, hnf, hcp, hfireEq, hkEq, -, hetaEq,
    hplainShape, hnestShape, -⟩ := hrule
  obtain ⟨hrfv', hrbv'⟩ := hfrSelf.annot_syntax hann hrfv hrbv
  have hkeep : ∀ (m : Key md) (ci : ConstantInfo md),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? m = some ci → envSelf.find? m = some ci :=
    fun m ci _ hf => hfindSelf m ci hf
  have hsomeLe : ∀ n, (env.find? n).isSome = true → (envSelf.find? n).isSome = true := by
    intro n hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hfindSelf n ci hci]; rfl
  obtain ⟨⟨cvj, hfcEnv, -, hnestLenC, hnInertC, hteleC⟩, hkC, -⟩ :=
    hrcEnv w.kC w.cvC w.mI w.rP w.rulesC hfkC rC hrC
  refine ⟨hrfv', by rw [hlps']; exact hrlp, hrres, hrbv', ?_, ?_, ?_, ?_, ?_⟩
  · intro lvls pins hfr
    have hmemRecC := Ix.Kernel.Semantics.Env.find?_mem hfkC
    obtain ⟨-, -, -, -, -, hrecWF, -, -⟩ := hwfEnv _ hmemRecC
    obtain ⟨-, -, -, -, hnestWF⟩ := hrecWF w.cvC w.mI w.rP w.rulesC rfl rC hrC
    obtain ⟨hle, hlvls, hpins, -⟩ := hnestWF lvls pins (hfireEq.symm.trans hfr)
    refine ⟨hle, fun l hl => by rw [hlps']; exact hlvls l hl, fun pin hpin => ?_,
      hnestShape lvls pins hfr⟩
    obtain ⟨p1, p2, p3, p4⟩ := hpins pin hpin
    exact ⟨p1, by rw [hlps']; exact p2, Ix.Kernel.Expr.constsResolve_le hsomeLe p3, p4⟩
  · refine ⟨cvj, ?_, fun hp => ?_, fun lvls pins hfn => ?_,
      fun hin => hnInertC (hfireEq.symm.trans hin), ?_⟩
    · rw [hctor, hcp, hnf]; exact hfindSelf _ _ hfcEnv
    · exact hplainShape hp cvj rC.ctorParams rC.nfields (by rw [hctor]; exact hfcEnv)
    · rw [hcp]; exact hnestLenC lvls pins (hfireEq.symm.trans hfn)
    · rw [hcp, hnf]; exact hteleC
  · intro hfire
    have hL0 := hlaw hfire (fun _ => 0)
    refine ⟨hL0.1, fun φ => ?_⟩
    obtain ⟨_, hLφ⟩ := hlaw hfire φ
    obtain ⟨Ra, hRa, -⟩ := hLφ (w.cvW'.levelParams.map Level.param) (by simp)
    rw [denotePInstLevels mpSelf.base2, Ix.Kernel.Level.substFn_param_self] at hRa
    exact ⟨Ra.erase, denoteMeta_erase mpSelf.base2.acval_erase 0 rW'.rhs hRa⟩
  · intro hk
    rw [hctor]
    exact Ix.Kernel.recRuleKOf_mono hkeep (hkC (hkEq.symm.trans hk))
  · intro heta
    rw [hetaEq] at heta
    rw [hcvName, hctor]
    exact Ix.Kernel.recRuleEtaOf_mono hkeep heta

/-! ## The twin recursor step -/

set_option maxHeartbeats 1600000 in
/-- **A twin recursor block extends the model**, over a judgement package. -/
theorem declRecTwinJ {J : Judgements md}
    (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {env env₂ : Env md} {block : List (ConstantInfo md)}
    (mp : EnvModelM V μ env)
    (h : DeclRecTwinRunJ J env block env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ := by
  obtain ⟨ws, f, -, -, rfl, hnd, hfrAll, hf, hall⟩ := h
  have hnamesEq : (twinProv ws).map (·.name) = (twinRecs ws).map (·.name) := by
    simp only [twinProv, twinRecs, List.map_map]; rfl
  rw [List.map_append] at hnd
  obtain ⟨hndR, hndM, hdisj⟩ := List.nodup_append.mp hnd
  -- Phase 1: install model companion copies
  obtain ⟨mpM, hextM, hfindM, hacM, hmonoM⟩ := installTwinModels mp ws hndM
    (fun ci hci => hfrAll ci (List.mem_append_right _ hci))
    (fun w hw cvm mval hint hm => by
      have hmod := (hall w hw).2.2.2.2.1
      rw [hm] at hmod
      exact hmod)
  -- Phase 2: install rule-less provisioned twin recursors
  have hndP : ((twinProv ws).map (·.name)).Nodup := by rwa [hnamesEq]
  have hfrProvM : ∀ ci ∈ twinProv ws,
      (⟨twinModels ws ++ env.consts⟩ : Env md).find? ci.name = none := by
    intro ci hci
    have hmemN : ci.name ∈ (twinRecs ws).map (·.name) := by
      rw [← hnamesEq]; exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨cR, hcR, hnR⟩ := List.mem_map.mp hmemN
    have hnotM : ci.name ∉ (twinModels ws).map (·.name) := fun hm => hdisj ci.name hmemN ci.name hm rfl
    refine find?_append_none_of_not_mem hnotM ?_
    rw [← hnR]
    exact hfrAll cR (List.mem_append_left _ hcR)
  obtain ⟨mpSelf, hextP, hfindSelf, hacSelf, hacTwin, hmonoSelf⟩ :=
    installTwinProv mp (hfr env) (hJ mp) mpM hfindM hacM hmonoM ws hndP hfrProvM
      (fun w hw => by
        obtain ⟨hcv, hlf, hfkC, hlps, -, htyG, -⟩ := hall w hw
        exact ⟨hcv, hlf, hfkC, hlps, htyG⟩)
  -- Phase 3: peer renaming, rule laws, rule facts, and swap
  let envM : Env md := ⟨twinModels ws ++ env.consts⟩
  let envSelf : Env md := ⟨twinProv ws ++ envM.consts⟩
  let env₃ : Env md := ⟨twinRecs ws ++ envM.consts⟩
  have hro : RenameOk mpSelf.base2.acval envSelf f :=
    twinRenameOk hndP hfindSelf hacSelf hacTwin hf
      (fun w hw => ⟨(hall w hw).1, (hall w hw).2.2.1, (hall w hw).2.2.2.1⟩)
  have hsw : Ix.Kernel.SwapShList envSelf.consts env₃.consts := twinSwapShList envM.consts ws
  have hcg : Ix.Kernel.SwapCongr envSelf env₃ := Ix.Kernel.SwapShList.congr hsw
  -- Per-twin rule laws and `RuleFacts` at `envSelf`
  have htwinLaws : ∀ w ∈ ws, ∀ rl ∈ w.rulesW',
      (rl.fire ≠ .inert → ∀ φ, RecRuleLaw mpSelf.base2 φ w.cvW'.name w.cvW' w.mI w.rP rl) ∧
      RuleFacts envSelf mpSelf.base2.cvalE w.cvW' w.mI w.rP rl := by
    intro w hw rl hrl
    obtain ⟨hcv, hlf, hfkC, hlps, -, ⟨tyG, hWC, hWW', htyG⟩, hlenW, hrules⟩ := hall w hw
    obtain ⟨rW, rC, hrC, hrule⟩ := forall₂_zip_mem_snd hlenW hrules rl hrl
    have hacN : mpSelf.base2.acval w.cvW'.name = mpSelf.base2.acval w.kC := by
      rw [hcv.name_eq, hacTwin w hw, hacSelf w.kC (by rw [hfkC]; rfl)]
    have hlaw : rl.fire ≠ .inert →
        ∀ φ, RecRuleLaw mpSelf.base2 φ w.cvW'.name w.cvW' w.mI w.rP rl :=
      fun hfire φ => RecRuleLaw.wrapTwin mp (hJ mp) mpSelf hfindSelf hmonoSelf hro
        hcv hlf hfkC hlps hacN hWC hWW' htyG hrC hrule hfire φ
    exact ⟨hlaw, twinRuleFacts (hfr envSelf) mp.base2.wf mp.base2.rec_ctors mpSelf hfindSelf
      hcv.name_eq (hcv.levelParams_eq.trans hlps) hfkC hrC hrule hlaw⟩
  have hnresR : SwapNResS envSelf env₃ := by
    intro n cv mI rP rules hf₀ hf₃
    by_cases hm : n ∈ (twinRecs ws).map (·.name)
    · obtain ⟨cR, hcR, hnR⟩ := List.mem_map.mp hm
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcR
      obtain ⟨-, hnresW, -⟩ := (hall w hw).1.inv
      have hnR' : w.cvW'.name = n := hnR
      rw [← hnR', (hall w hw).1.name_eq]
      exact Or.inr hnresW
    · have hmP : n ∉ (twinProv ws).map (·.name) := by rwa [hnamesEq]
      rw [find?_append_of_not_mem (env := envM) hmP] at hf₀
      rw [find?_append_of_not_mem (env := envM) hm, hf₀] at hf₃
      obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf₃)
      exact Or.inl rfl
  have hentR : ∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
      ∃ (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
        c = .recInfo cv mI rP rules ∧
        ∀ rl ∈ rules, RuleFacts envSelf mpSelf.base2.cvalE cv mI rP rl := by
    intro c hc
    rcases List.mem_append.mp hc with hrec | hrest
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
      exact Or.inr ⟨w.cvW', w.mI, w.rP, w.rulesW', rfl, fun rl hrl => (htwinLaws w hw rl hrl).2⟩
    · exact Or.inl (List.mem_append_right _ hrest)
  have hentF : ∀ (n : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      envSelf.find? n = some (.recInfo cv mI rP rules) ∨
      (∀ rl ∈ rules,
        (rl.fire ≠ .inert → ∀ φ, RecRuleLaw mpSelf.base2 φ cv.name cv mI rP rl) ∧
        RuleFacts envSelf mpSelf.base2.cvalE cv mI rP rl) := by
    intro n cv mI rP rules hf₃
    by_cases hm : n ∈ (twinRecs ws).map (·.name)
    · obtain ⟨cR, hcR, hnR⟩ := List.mem_map.mp hm
      have hfR := find?_mem_of_nodup (rest := envM.consts) hndR hcR
      rw [hnR, hf₃] at hfR
      obtain rfl := Option.some.inj hfR
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hcR
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      exact Or.inr (fun rl hrl => htwinLaws w hw rl hrl)
    · have hmP : n ∉ (twinProv ws).map (·.name) := by rwa [hnamesEq]
      rw [find?_append_of_not_mem (env := envM) hm] at hf₃
      rw [find?_append_of_not_mem (env := envM) hmP]
      exact Or.inl hf₃
  obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
    swapEnvFacts mpSelf.base2.wf mpSelf.base2.rec_ctors mpSelf.base2.basis_pinned
      mpSelf.base2.proj_ok hsw hnresR hentR
      (fun n cv mI rP rules hf₃ => (hentF n cv mI rP rules hf₃).imp id
        (fun h rl hrl => (h rl hrl).2))
  have hrecP : ∀ m₃ : EnvModel V env₃, m₃.acval = mpSelf.base2.acval →
      ∀ φ : LevelParam → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf₃ rl hrl hfire
    rcases hentF n cv mI rP rules hf₃ with hfS | hlaws
    · exact RecRuleLaw.swapP hcg hac (mpSelf.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Ix.Kernel.Semantics.Env.find?_name hf₃]
      exact RecRuleLaw.swapP hcg hac ((hlaws rl hrl).1 hfire φ)
  obtain ⟨mp₃, hacc, -⟩ := EnvModelM.swapP mpSelf hsw hwf₃ hctors₃ hbp₃ hproj₃ hrecP
  have hext₃ : ModelExt mp mp₃ :=
    ModelExt.swap (hextM.trans hextP)
      (fun n hn => by rw [← hcg.isSomeEq n]; exact hn)
      (fun cv v hmem => by
        rcases hentR _ hmem with h | ⟨_, _, _, _, heq, -⟩
        · exact h
        · exact nomatch heq)
      (fun ψ d e => denoteMeta_swap hcg ψ d e) hacc
  exact ⟨mp₃, hext₃⟩

end Ix.Kernel.Model
