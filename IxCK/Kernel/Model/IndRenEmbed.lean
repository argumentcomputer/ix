module

public import IxCK.Kernel.Model.IndRenRecord
public import IxCK.Kernel.Model.DeclIndRen
public import IxCK.Kernel.Semantics.IndBlockRun
import IxCK.Kernel.Model.JudgeSound

public section

/-!
# The public record embeds in the renamed one, at canonical rules

`DeclIndRenRunJ` (`Model/IndRenRecord.lean`) takes every judgement of `DeclIndRunJ` over
`renameJ f J`, which adjoins the renamed judgements to `J`'s, and a nested rule's pins renamed.
So a public record whose rules are all canonical is a renamed record: each judgement enters
`renameJ f J` as `J`'s own (`Or.inl`), and the one form `renameJ` cannot take, the nested pin
typing, does not occur.

"All rules canonical" is said of what the step stores: no recursor of the block, as stored at the
step's output, has a rule that fires nested (`NoNestedRules`). The fold stores each recursor with
the rules its kits return, and a kit's fire mode is its branch, so the condition reaches every kit.

`declIndRun_modeled_toRen` applies this to the kernel's own records: every modeled block the
kernel's fold installs with no nested rule satisfies the renamed record at the kernel's runs, so
`declIndRenJ` applies to it (`declIndRenJ_kernel`).
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel.Term Ix.Kernel.Verify

/-- **No recursor of the block, as stored, fires a rule nested.** -/
@[expose] def NoNestedRules (blockNames : List (Key md)) (env₂ : Env md) : Prop :=
  ∀ (n : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
    blockNames.contains n = true →
    env₂.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, ∀ (lvls : List Level) (pins : List (Expr md)),
      RecRule.fire rl ≠ .nested lvls pins

section Embed

variable {J : Judgements md} {f : Key md → Key md}

theorem IotaRunsJ.renameJ_of {envSelf : Env md} {depth : Nat}
    {idxL idxR domL domR preL preR lamL lamR : List (Expr md)}
    {rhsS rhsApplied alphaS lhsS : Expr md}
    (h : IotaRunsJ J envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS) :
    IotaRunsJ (renameJ f J) envSelf depth idxL idxR domL domR preL preR lamL lamR
      rhsS rhsApplied alphaS lhsS :=
  let ⟨h1, h2, h3, h4, h5, ⟨tl, hl, hdl⟩, ⟨tr, hr, hdr⟩⟩ := h
  ⟨h1.renameJ_of, h2.renameJ_of, h3.renameJ_of, h4.renameJ_of, Or.inl h5,
    ⟨tl, Or.inl hl, Or.inl hdl⟩, ⟨tr, Or.inl hr, Or.inl hdr⟩⟩

theorem constantValRunJ_renameJ_of {env : Env md} {cv : ConstantVal md} {type' : Expr md}
    (h : ConstantValRunJ J env cv type') :
    ConstantValRunJ (renameJ f J) env cv type' :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, stype, u, hi, hs⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, stype, u, Or.inl hi, hs⟩

theorem memberValRunJ_renameJ_of {env : Env md} {blockNames : List (Key md)}
    {cv cvA : ConstantVal md} (h : MemberValRunJ J env blockNames cv cvA) :
    MemberValRunJ (renameJ f J) env blockNames cv cvA :=
  let ⟨ty, hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩ := h
  ⟨ty, constantValRunJ_renameJ_of hc, heq, hsuffix, cvm, value, hint, hfind, hlevels, htype⟩

theorem indMembersRunJ_renameJ_of {blockNames : List (Key md)} {caps : IndCaps md} :
    ∀ {env : Env md} {members : List (ConstantInfo md)} {env₂ : Env md},
      IndMembersRunJ J blockNames caps env members env₂ →
      IndMembersRunJ (renameJ f J) blockNames caps env members env₂
  | _, [], _, h => h
  | _, ci :: _, _, h => by
    obtain ⟨cvA, hmv, hm⟩ := h
    refine ⟨cvA, memberValRunJ_renameJ_of hmv, ?_⟩
    cases ci with
    | indInfo _ _ => exact indMembersRunJ_renameJ_of hm
    | ctorInfo _ _ _ => exact indMembersRunJ_renameJ_of hm
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ => exact hm

theorem provisionRecsRunJ_renameJ_of {blockNames : List (Key md)} :
    ∀ {env : Env md} {recs : List (ConstantInfo md)} {envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames env recs envSelf checked →
      ProvisionRecsRunJ (renameJ f J) blockNames env recs envSelf checked
  | _, [], _, _, h => h
  | _, _ :: _, _, _, h => by
    obtain ⟨cvA, mI, rP, rules, rest, hci, hmv, hrec, hchecked⟩ := h
    exact ⟨cvA, mI, rP, rules, rest, hci, memberValRunJ_renameJ_of hmv,
      provisionRecsRunJ_renameJ_of hrec, hchecked⟩

theorem iotaThmRunJ_renameJ_of {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r : RecRule md} {cvj : ConstantVal md} {cnP cnF : Nat} {rhsA : Expr md}
    (h : IotaThmRunJ J env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA) :
    IotaThmRunJ (renameJ f J) env envSelf f cvName lps tyA mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨cvt, fvs, tbody, h1, h2, h3, h4, h5, ?_⟩
  dsimp only at h6 ⊢
  obtain ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7, k8, k9⟩ := h6
  exact ⟨g1, g2, g3, g4, g5, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP,
    crest2, ldoms, lrest, k1, k2, k3, k4, k5, k6, ldomsL, lrest2, k7,
    k8.renameJ_of, k9.renameJ_of⟩

/-- **A public rule kit that does not fire nested is a renamed one.** -/
theorem iotaRuleRunJ_toRen {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP j : Nat}
    {r r' : RecRule md}
    (h : IotaRuleRunJ J env envSelf f cvName lps tyA mI rP j r r')
    (hnn : ∀ (lvls : List Level) (pins : List (Expr md)),
      RecRule.fire r' ≠ .nested lvls pins) :
    IotaRuleRenRunJ J env envSelf f cvName lps tyA mI rP j r r' := by
  obtain ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, ⟨ty, h9⟩, fire, h10,
    hbr⟩ := h
  refine ⟨cvj, cnP, cnF, rhsA, h1, h2, h3, h4, h5, h6, h7, h8, ⟨ty, Or.inl h9⟩, fire, h10, ?_⟩
  rcases hbr with ⟨hp, hf, ht⟩ | ⟨-, lvls, pins, hf, -⟩
  · exact Or.inl ⟨hp, hf, iotaThmRunJ_renameJ_of ht⟩
  · exfalso
    have hfr : RecRule.fire r' = fire := by rw [h10]; rfl
    exact hnn lvls pins (hfr.trans hf)

theorem iotaRulesRunJ_toRen {env envSelf : Env md}
    {cvName : Key md} {lps : List LevelParam} {tyA : Expr md} {mI rP : Nat} :
    ∀ {j : Nat} {rules rules' : List (RecRule md)},
      IotaRulesRunJ J env envSelf f cvName lps tyA mI rP j rules rules' →
      (∀ rl ∈ rules', ∀ (lvls : List Level) (pins : List (Expr md)),
        RecRule.fire rl ≠ .nested lvls pins) →
      IotaRulesRenRunJ J env envSelf f cvName lps tyA mI rP j rules rules'
  | _, [], _, h, _ => h
  | _, _ :: _, _, h, hnn => by
    obtain ⟨r', rest, hr, hrest, rfl⟩ := h
    exact ⟨r', rest, iotaRuleRunJ_toRen hr (hnn r' List.mem_cons_self),
      iotaRulesRunJ_toRen hrest (fun rl hrl => hnn rl (List.mem_cons_of_mem _ hrl)), rfl⟩

end Embed

/-- **The install fold, public to renamed**: each recursor is stored at the fold's output with
the rules its kits return (no later recursor of the group shares its name), so the output's
`NoNestedRules` reaches every kit. -/
theorem indRecsFoldRunJ_toRen {J : Judgements md} {blockNames : List (Key md)}
    {envBase envSelf out : Env md} :
    ∀ (recs : List (ConstantInfo md)) {envP acc : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames envP recs envSelf checked →
      IndRecsFoldRunJ J blockNames envBase envSelf acc checked out →
      NoNestedRules blockNames out →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      IndRecsFoldRenRunJ J blockNames envBase envSelf acc checked out := by
  intro recs
  induction recs with
  | nil =>
    intro envP acc checked hprov hfold _ _
    obtain ⟨-, rfl⟩ := hprov
    exact hfold
  | cons ci₀ rest ih =>
    intro envP acc checked hprov hfold hcan hbn
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', -, hcvAdef, -⟩ := hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvAdef]; rfl
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    -- no later recursor of the group shares this one's name
    have hne : ∀ c ∈ rest', c.1.name ≠ cvA.name := by
      intro c hc heq
      have hnone := provisionRecsRun_checkedFresh rest hprov' c hc
      have hs : (⟨.recInfo cvA mI rP [] :: envP.consts⟩ : Env md).find? cvA.name
          = some (.recInfo cvA mI rP []) :=
        Env.find?_cons_self (.recInfo cvA mI rP []) envP
      rw [heq, hs] at hnone
      exact nomatch hnone
    -- so the output stores it with the rules its kits returned
    have hstored : out.find? cvA.name = some (.recInfo cvA mI rP rules') := by
      rw [indRecsFoldRun_keep rest' hfold' cvA.name hne]
      exact Env.find?_cons_self (.recInfo cvA mI rP rules') acc
    refine ⟨rules', iotaRulesRunJ_toRen hiot
      (hcan cvA.name cvA mI rP rules' hbnA hstored), ?_⟩
    exact ih hprov' hfold' hcan (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci))

theorem indRecsRunJ_toRen {J : Judgements md} {blockNames : List (Key md)}
    {env₂ env₃ : Env md} {recs : List (ConstantInfo md)}
    (h : IndRecsRunJ J blockNames env₂ recs env₃)
    (hcan : NoNestedRules blockNames env₃)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true) :
    IndRecsRenRunJ J blockNames env₂ recs env₃ := by
  rcases h with h | ⟨hne, heq, envSelf, checked, hprov, hfold⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, heq, envSelf, checked, provisionRecsRunJ_renameJ_of hprov,
      indRecsFoldRunJ_toRen recs hprov hfold hcan hbn⟩

/-- **The public record embeds in the renamed one at canonical rules**: a `DeclIndRunJ` step
whose block's recursors, as stored, fire no rule nested is a `DeclIndRenRunJ` step. -/
theorem DeclIndRunJ.toRen {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclIndRunJ J env block env₂)
    (hcan : NoNestedRules (block.map (·.name)) env₂) :
    DeclIndRenRunJ J env block env₂ := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  have hbn : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp hci).1
    simpa using hmm
  exact ⟨hsplit, envM, indMembersRunJ_renameJ_of hmem, indRecsRunJ_toRen hrecs hcan hbn⟩

/-- **The kernel's modeled records, renamed**: a block the kernel installs by `DeclIndRun`'s
modeled case, with no nested rule, satisfies the renamed record at the kernel's runs. -/
theorem declIndRun_modeled_toRen {μ : CheckMode} {F : Nat} {env env₂ : Env md}
    {block : List (ConstantInfo md)}
    (h : DeclIndRun μ F env block env₂)
    (hmod : ¬ (∃ cvT capsT cvC nP nF,
      block.filter (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
      block.filter (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false) = [.ctorInfo cvC nP nF]))
    (hcan : NoNestedRules (block.map (·.name)) env₂) :
    DeclIndRenRunJ (runJ μ F) env block env₂ :=
  (declIndRun_modeled_runJ h hmod).toRen hcan

end Ix.Kernel.Semantics

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel (CheckMode Env ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-- **`declIndRenJ` applies to the kernel's modeled blocks with canonical rules**: its premise
holds at the kernel's runs whenever the kernel installs a modeled block none of whose stored
rules fires nested. -/
theorem declIndRenJ_kernel {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env env₂ : Env md} {block : List (ConstantInfo md)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRun μ F env block env₂)
    (hmod : ¬ (∃ cvT capsT cvC nP nF,
      block.filter (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
      block.filter (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false) = [.ctorInfo cvC nP nF]))
    (hcan : NoNestedRules (block.map (·.name)) env₂) :
    ∃ mp₂ : EnvModelM V μ env₂, ModelExt mp mp₂ :=
  declIndRenJ (fun _ => judgeFrames_runJ F) (fun m => judgeSound_runJ hμ m F) mp hE
    (declIndRun_modeled_toRen h hmod hcan)

end Ix.Kernel.Model
