import IxVMRefinement.TwinFamily.Step

/-! # The twin step's target from facts about the twin record

`TwinStepTarget`'s conclusion is the second record's declaration as read, IxC's twin record at
the positional package, each member stored as its reading, and a model companion at each member.
This module states what the circuit side has to hand for it, part by part
(`TwinPartsFacts`), and proves the conclusion from that, the reading, and the block's family
record installed (`twinTarget_of_facts`); with a producer of the facts at every hypothesis of
the target, the target itself (`twinStepTarget_of_facts`).

The facts are those of IxC's record that are about the second record (its front door, its
comparison with the canonical recursor, its rules, its stored annotation), with the canonical
recursor of each part named as a member of the block's family record. The model companions are
not facts: the family record is installed, so each canonical recursor has a companion, which
the record copies to the twin (`DeclRecTwinRunJ`'s `some` branch); this module proves it. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart twinModels twinRecs twinProv TwinRuleJ
  ConstantValCheckJ Forall₂)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-- **What the circuit side hands for a twin record**, over the parts `ws` of the record and the
peer renaming `f`: the block is the parts' declared recursors; the names the step stores are
distinct and fresh; the renaming sends each canonical recursor to its twin and fixes the rest;
each part's canonical recursor is a member of the block's family record `rb`, and its stored
companion is the one the part copies; and for each part IxC's twin record's own conjuncts: the
front door at the positional package, no `let` in the checked type, the canonical recursor
stored with the part's counts and rules, the level parameters, the generated type, the rules
(`TwinRuleJ`), and the checked recursor storing the declared one (`ValStored`, `RuleStored`). -/
structure TwinPartsFacts (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (rb : _root_.Address) (crb : Ixon.Constant) (blk : List (ConstantInfo .anon))
    (ws : List (TwinRecPart .anon)) (f : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon) : Prop where
  nonempty : ws ≠ []
  block : blk = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW)
  names : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup
  fresh : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none
  peer : ∀ k, f k = k ∨ ∃ w' ∈ ws, k = w'.kC ∧ f k = w'.cvW.name
  canonAt : ∀ w ∈ ws, ∃ x, ConstAddrOf rb crb x ∧ w.kC = keyOf t x
  model : ∀ w ∈ ws, ∀ cvm mval hint,
    env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
      w.model? = some (cvm, mval, hint)
  front : ∀ w ∈ ws, ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW'
  letFree : ∀ w ∈ ws, Ix.Kernel.Semantics.letFree w.cvW'.type = true
  canonical : ∀ w ∈ ws, env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC)
  lvls : ∀ w ∈ ws, w.cvW.levelParams = w.cvC.levelParams
  tyGen : ∀ w ∈ ws, TwinTypeGen twinPosRulesJ env w.cvC w.cvW'
  rulesLen : ∀ w ∈ ws, w.rulesW.length = w.rulesW'.length
  rules : ∀ w ∈ ws, Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
    TwinRuleJ twinPosRulesJ env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ f w.cvW.name
      w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC) (w.rulesW.zip w.rulesW') w.rulesC
  stored : ∀ w ∈ ws, ValStored w.cvW' w.cvW ∧ List.Forall₂ RuleStored w.rulesW' w.rulesW

/-- **The target's conclusion from the facts** (module docstring): IxC's twin record, each
member stored as its reading, and a model companion at each member, after the step. -/
theorem twinTarget_of_facts {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {rb : _root_.Address} {crb : Ixon.Constant} {blk : List (ConstantInfo .anon)}
    {ws : List (TwinRecPart .anon)} {f : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    (hF : TwinPartsFacts t env rb crb blk ws f) (hinst : FamilyInstalled t env rb crb) :
    ∃ env₂ : Ix.Kernel.Env .anon,
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name) := by
  -- each part's canonical recursor has a companion, which the part copies
  have hmod : ∀ w ∈ ws, ∃ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) ∧
        w.model? = some (cvm, mval, hint) := by
    intro w hw
    obtain ⟨x, hx, hk⟩ := hF.canonAt w hw
    obtain ⟨-, cvm, mval, hint, hf⟩ := hinst x hx
    rw [← hk] at hf
    exact ⟨cvm, mval, hint, hf, hF.model w hw cvm mval hint hf⟩
  have hfind : ∀ ci ∈ twinRecs ws ++ twinModels ws,
      (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some ci := by
    intro ci hci
    have h := Ix.Kernel.Semantics.find?_mem_of_nodup (rest := env.consts) hF.names hci
    rw [List.append_assoc] at h
    exact h
  refine ⟨⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩, ?_, ?_, ?_⟩
  · refine ⟨ws, f, hF.nonempty, hF.block, rfl, hF.names, hF.fresh, hF.peer, fun w hw => ?_⟩
    obtain ⟨cvm, mval, hint, hfm, hm⟩ := hmod w hw
    refine ⟨hF.front w hw, hF.letFree w hw, hF.canonical w hw, hF.lvls w hw, ?_, hF.tyGen w hw,
      hF.rulesLen w hw, hF.rules w hw⟩
    rw [hm]
    exact hfm
  · intro ci hci
    rw [hF.block] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    obtain ⟨hvs, hrs⟩ := hF.stored w hw
    refine ⟨.recInfo w.cvW' w.mI w.rP w.rulesW', ?_, hvs, rfl, rfl, hrs⟩
    have h := hfind _ (List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩))
    show (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? w.cvW.name =
      some (.recInfo w.cvW' w.mI w.rP w.rulesW')
    rw [← (hF.front w hw).name_eq]
    exact h
  · intro ci hci
    rw [hF.block] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    obtain ⟨cvm, mval, hint, -, hm⟩ := hmod w hw
    have hmi : TwinRecPart.modelInfo? w = some (.defnInfo
        ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint) := by
      unfold TwinRecPart.modelInfo?
      rw [hm]
      rfl
    have hmem : ConstantInfo.defnInfo ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams,
        cvm.type⟩ mval hint ∈ twinRecs ws ++ twinModels ws :=
      List.mem_append_right _ (List.mem_filterMap.mpr ⟨w, hw, hmi⟩)
    exact ⟨_, mval, hint, hfind _ hmem⟩

/-- **The twin step's target from a producer of the facts**: at every hypothesis of the target,
the circuit side hands the second record's declaration as read and the facts of its parts. -/
theorem twinStepTarget_of_facts
    (hseam : ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
      (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
      (cb crb crb' : Ixon.Constant) (ms rs' : Array Ixon.MutConst) (lim : Option Nat)
      (cs : List (Call F)),
      t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
      FamBlockRecord E₀ B cb ms → FamRecRecord E₀ rb' crb' rs' →
      rs'.size ≠ 0 → rb' ≠ rb →
      FamilyCallAtLim calls bAddr t B rb' lim cs →
      ModeledRouteAt calls B →
      Decl.PrefixInv.{u} E t lim env →
      (∀ x, UsedRef E₀ rb' x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf rb' crb' x ∨ ¬ NeedOk E₀ x) →
      FamilyInstalled t env rb crb →
      InertClause t crb' →
      (∀ x, ConstAddrOf rb' crb' x → env.find? (keyOf t x) = none) →
      (∀ x, ConstAddrOf rb' crb' x → Decl.KeyFree (keyOf t x)) →
      ∃ (blk : List (ConstantInfo .anon)) (ws : List (TwinRecPart .anon))
        (f : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon),
        TwinDeclReads t E₀ rb' crb' blk ∧ TwinPartsFacts t env rb crb blk ws f) :
    TwinStepTarget.{u} := by
  intro calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs' lim cs ht hRS hSS hB hrb' hsz
    hne hcall hroute hinv href hinst hinert hfresh hkey
  obtain ⟨blk, ws, f, hreads, hF⟩ := hseam calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs'
    lim cs ht hRS hSS hB hrb' hsz hne hcall hroute hinv href hinst hinert hfresh hkey
  obtain ⟨env₂, hrun, hstored, hmodel⟩ := twinTarget_of_facts hF hinst
  exact ⟨blk, env₂, hreads, hrun, hstored, hmodel⟩

end IxVM.Refinement.Typing.TwinFamily
