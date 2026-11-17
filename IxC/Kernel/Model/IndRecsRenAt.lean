module

public import IxC.Kernel.Model.IndRenAt
public import IxC.Kernel.Model.IndBlockRunAt
public import IxC.Kernel.Model.IndMembersAt
public import IxC.Kernel.Model.IotaRuleAt
public import IxC.Kernel.Model.IndRecsRen
public import IxC.Kernel.Semantics.IndRecsCore
public import IxC.Kernel.Model.Swap
public import IxC.Kernel.Model.IndRecs
import IxC.Kernel.Semantics.IndBlockRun
import IxC.Kernel.Model.IndMembers
import IxC.Kernel.Model.Capstone
import IxC.Kernel.Model.JudgeSound
import IxC.Kernel.Model.IndRenJudge
import IxC.Kernel.Model.IotaRuleRen
import IxC.Kernel.Verify.Denote.IndFrame
import IxC.Kernel.Verify.Leaves
public section

/-!
# The recursor-group phase, with the rule typings renamed, at given model and theorem keys

`Model/IndRecsRen.lean` over `IndRecsRenRunJAt` (`Model/IndRenAt.lean`): provision the group
without rules (`provisionRecsPMAt`), fire each rule against its `iota` theorem at `thmKey R j`
(`iotaRulesRenAt`), attach the rules. The renaming's idempotence comes from `hout` (the model
key maps block names outside the block) where the original used the members' `isModelSuffix`
guard.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics Ix.Kernel.SetModel
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}
variable {g : Key md → Key md} {thmKey : Key md → Nat → Key md}

set_option maxHeartbeats 1600000 in
/-- **The provisioning and the install fold, run together at the reading**, over the renamed
record (`indRecsFold` with `iotaRulesRenAt`). -/
theorem indRecsFoldRenAt {J K : Judgements md}
    {blockNames : List (Key md)} {envSelf envBase : Env md}
    (mp : EnvModelM V μ envSelf) (hJ : JudgeSound J mp.base2)
    (hIS : BlockInstalledTTAt g blockNames envSelf mp.base2.cvalE)
    (hroT : RenameOk mp.base2.acval envSelf (blockRenAt g blockNames))
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    (hupB : FoldUpS envBase envSelf)
    (heqfB : envBase.find? eqName = some eqA) :
    ∀ (recs : List (ConstantInfo md)) {envP envF env₃ : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      (∀ (n : Key md) (cv : ConstantVal md) (mI rP : Nat)
        (rules : List (RecRule md)),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsRen mp.base2 cv mI rP rules) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRunJAt K g blockNames envP recs envSelf checked →
      IndRecsFoldRenRunJAt J g thmKey blockNames envBase envSelf
        envF checked env₃ →
      ∀ (n : Key md) (cv : ConstantVal md) (mI rP : Nat)
        (rules : List (RecRule md)),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsRen mp.base2 cv mI rP rules := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact hentF
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', hcv, hcvAdef, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvAdef]
    have hselfA : envSelf.find? cvA.name
        = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_monoAt rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    -- this recursor's rules, fired from their renamed typings
    have hfacts : RecLawsRen mp.base2 cvA mI rP rules' :=
      fun rl hrl hfire φ =>
        iotaRulesRenAt mp hJ rfl hroT (blockRenAt_idem hout) hIS hupB hbnA hselfA
          heqfB 0 rules rules' hiot rl hrl hfire φ
    refine ih ?_ (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci))
      hprov' hfold'
    intro n cv mI₀ rP₀ rules₀ hfx
    rw [Env.find?_cons] at hfx
    split at hfx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj hfx)
      exact Or.inr hfacts
    · exact hentF n cv mI₀ rP₀ rules₀ hfx

set_option maxHeartbeats 1600000 in
/-- **The recursor-group phase, with the rule typings renamed** (`indRecsRen` at the model key
`g` and the theorem key `thmKey`): provision, fire, swap. `hout` (the model key maps block names
outside the block) makes the block renaming idempotent; `BlockNoEta` replaces `BlockEtaPinned`. -/
theorem indRecsRenAt
    {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    (hJ : ∀ {e : Env md} (m : EnvModelM V μ e), JudgeSound J m.base2)
    {blockNames : List (Key md)} {env₂ env₃ : Env md}
    {recs : List (ConstantInfo md)}
    (mp : EnvModelM V μ env₂)
    (hI : BlockInstalledTTAt g blockNames env₂ mp.base2.cvalE)
    (hIA : BlockAcvalInstalledAt g blockNames env₂ mp.base2.acval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hout : ∀ n, blockNames.contains n = true → blockNames.contains (g n) = false)
    (hEC : Ix.Kernel.EtaFamiliesClosedO blockNames env₂)
    (hNE : BlockNoEta blockNames env₂)
    (h : IndRecsRenRunJAt J g thmKey blockNames env₂ recs env₃) :
    ∃ mp₃ : EnvModelM V μ env₃,
      BlockInstalledTTAt g blockNames env₃ mp₃.base2.cvalE ∧
      BlockAcvalInstalledAt g blockNames env₃ mp₃.base2.acval ∧
      ModelExt mp mp₃ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, heqf, envSelf, checked,
    hprov, hfold⟩
  · exact ⟨mp, hI, hIA, .refl⟩
  -- the provisioning, at both tiers (generic in its package)
  obtain ⟨mS, hIS, hIAS, hECS, hBPS, hextS⟩ :=
    provisionRecsPMAt (fun e => judgeFrames_renameJ (hfr e)) hout recs mp hbn hprov
      hI hIA hEC hNE
  -- every block member is stored in the provisional environment
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsRunS_monoAt recs hprov n ci hf]; rfl
    · exact provisionRecsRunS_storedAt recs hprov ci hci
  -- the block renaming, at both tiers
  have hroP := blockRenameOkAt hIS hIAS hnames
  -- the stored-data facts, over the shape package
  have hprovS := provisionRecsRunJ_shapeAt hprov
  have hfoldS := indRecsFoldRenRunJ_shapeAt hfold
  -- the rule rhs's reading, from its typing or its renamed typing
  have hdenS : ∀ e : Expr md, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', (shapeJ (blockRenAt g blockNames) J).infer envSelf 0 e t') →
      ∀ φ : LevelParam → Nat,
        ∃ Rv, denoteClosed mS.base2.cvalE envSelf φ e = some Rv := by
    intro e hef heb hrun φ
    obtain ⟨t', hrun'⟩ := hrun
    have hws : Expr.WScoped 0 e := Expr.WScoped.of_not_hasFvar hef
    have hL : Expr.LeavesBounded e := fun l hl => absurd hl (fun h' => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hef] at h'
      exact nomatch h')
    obtain ⟨ea, hea⟩ : ∃ ea, denoteMeta mS.base2.acval envSelf φ 0 e = some ea := by
      rcases hrun' with hj | hj
      · exact (hJ mS).accepted φ hj hws heb hL
      · obtain ⟨ea, hea⟩ := (hJ mS).accepted φ hj (wscoped_renameConsts e hws)
          ((Expr.looseBVarsBounded_renameConsts _ e 0).trans heb)
          (leavesBounded_renameConsts e hL)
        exact ⟨ea, (denoteMeta_renameConsts hroP e 0).symm.trans hea⟩
    exact ⟨ea.erase, denoteMeta_erase mS.base2.acval_erase 0 e hea⟩
  obtain ⟨hswR, hnresR, hentR, hentFR⟩ :=
    indRecsFoldFactsRunAt (J := shapeJ (blockRenAt g blockNames) J)
      (RuleFacts envSelf mS.base2.cvalE)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsRunAt
          (fun n ci hf =>
            Or.inl (provisionRecsRunS_monoAt recs hprov n ci hf))
          hdenS (judgeFrames_shapeJ (hfr envSelf)).annot_syntax 0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf =>
        Or.inl (provisionRecsRunS_monoAt recs hprov n ci hf))
      (provisionRecsRunS_monoAt recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsRunS_memAt recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsRunS_monoAt recs hprov n _ hf))
      hbn hprovS hfoldS
  have hcg : Ix.Kernel.SwapCongr envSelf env₃ := SwapShList.congr hswR
  -- the P rows at the group's output, from the renamed typings
  have hentF := indRecsFoldRenAt (V := V) mS (hJ mS) hIS hroP hout
    (fun n ci hf => Or.inl (provisionRecsRunS_monoAt recs hprov n ci hf))
    heqf recs
    (fun n cv mI rP rules hf =>
      Or.inl (provisionRecsRunS_monoAt recs hprov n _ hf))
    hbn hprov hfold
  -- `rec_rules` at the swapped carrier
  have hrecP : ∀ m₃ : EnvModel V env₃, m₃.acval = mS.base2.acval →
      ∀ φ : LevelParam → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hlaws
    · exact RecRuleLaw.swapP hcg hac
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Env.find?_name hf]
      exact RecRuleLaw.swapP hcg hac (hlaws rl hrl hfire φ)
  -- the swap
  obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
    swapEnvFacts mS.base2.wf mS.base2.rec_ctors mS.base2.basis_pinned
      mS.base2.proj_ok hswR hnresR hentR hentFR
  obtain ⟨mp₃, hacc, hcval₃⟩ :=
    EnvModelM.swapP mS hswR hwf₃ hctors₃ hbp₃ hproj₃ hrecP
  -- the swap keeps every leaf, every stored name and every stored theorem
  have hext₃ : ModelExt mp mp₃ :=
    ModelExt.swap hextS (fun n hn => by rw [← hcg.isSomeEq n]; exact hn)
      (fun cv v hmem => by
        rcases hentR _ hmem with h | ⟨_, _, _, _, heq, -⟩
        · exact h
        · exact nomatch heq)
      (fun ψ d e => denoteMeta_swap hcg ψ d e) hacc
  refine ⟨mp₃, ?_, by rw [hacc]; exact blockAcvalInstalled_swapAt hcg hIAS, hext₃⟩
  -- the block invariant survives the swap
  rw [hcval₃]
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq |
    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)),
      hlps, hren, hv⟩



end Ix.Kernel.Model
