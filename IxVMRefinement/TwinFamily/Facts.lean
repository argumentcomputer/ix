import IxVMRefinement.TwinFamily.Companions
import IxVMRefinement.TwinFamily.Reload

/-! # The twin step's target from facts about the twin record

`TwinStepTarget`'s conclusion is the second record's declaration as read, IxC's twin record at
the positional package, each member stored as its reading, a model companion at each member,
and the scoped core's companions after the step. This module states what the circuit side has
to hand for it, part by part (`TwinPartsFacts`), and proves the conclusion from that, the
reading, the block's family record installed, and the companions before the step
(`twinTarget_of_facts`); with a producer of the facts at every hypothesis of the target, the
target itself (`twinStepTarget_of_facts`).

The facts are those of IxC's record that are about the second record (its front door, its rules'
stages, its stored annotation) and, member by member, the second record against the canonical
one (`TwinMemberCmp`), with the canonical recursor of each part named as a member of the block's
family record. The circuit checks each member of each record on its own against the block's
reconstruction, accepting it as the reconstruction or as its full consumption, so the two
records' members at one place are comparable either way:

* the canonical member above the twin's (`CanonAbove`: the two equal up to `WrapRel`, or the
  canonical one the reconstruction and the twin's its full consumption): the canonical terms
  are the generated ones IxC's record asks, and nothing is typed
  (`twinTypeGen_of_canonical_above`, `twinRuleGen_of_canonical_above`);
* the twin's member above the canonical one (`TwinAbove`): the twin's type is the generated
  type, typed by its own front door (`twinTypeGen_of_twin_above`), and each rule carries its
  generated right-hand side (`TwinRuleGen`, typed where it is not the canonical one).

Beside the parts, the circuit side hands what the reload of each checked twin recursor needs
(`TwinLoadFacts`: the second record's references stored, each member loaded as its checked
recursor), from which the reload is proved (`twinMember_reloads`). Two things are not facts of
the second record:

* the model companions: the family record is installed, so each canonical recursor has a
  companion, which the record copies to the twin (`DeclRecTwinRunJ`'s `some` branch);
* the companions after the step: the canonical recursor owes them, and the second record has
  its counts, its rule constructors and its major-premise domain (`coreCompanions_twin`). -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart twinModels twinRecs twinProv TwinRuleJ
  ConstantValCheckJ Forall₂ Judgements WrapRel)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-! ## Lists -/

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → (∀ a b, R a b → S a b) → Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons hab hr, h => .cons (h _ _ hab) (forall₂_imp hr h)

/-- A `Forall₂` over a zip, read at the zip's right list. -/
theorem forall₂_zip_right {α β γ : Type} {P : α × β → γ → Prop} {Q : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, l₁.length = l₂.length →
      Forall₂ P (l₁.zip l₂) l₃ → (∀ p c, P p c → Q p.2 c) → List.Forall₂ Q l₂ l₃
  | [], [], _, _, h, _ => by
    have h' : Forall₂ P [] _ := h
    cases h'
    exact .nil
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, l₃, hl, h, hPQ => by
    have h' : Forall₂ P ((a, b) :: l₁.zip l₂) l₃ := h
    cases h' with
    | cons hab h'' => exact .cons (hPQ _ _ hab) (forall₂_zip_right (Nat.succ.inj hl) h'' hPQ)

/-- A `Forall₂` over a zip and one over its right list, together. -/
theorem forall₂_zip_and {α β γ : Type} {P : α × β → γ → Prop} {Q : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, l₁.length = l₂.length →
      Forall₂ P (l₁.zip l₂) l₃ → List.Forall₂ Q l₂ l₃ →
      Forall₂ (fun p c => P p c ∧ Q p.2 c) (l₁.zip l₂) l₃
  | [], [], _, _, h, _ => by
    have h' : Forall₂ P [] _ := h
    cases h'
    exact .nil
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, l₃, hl, h, hq => by
    have h' : Forall₂ P ((a, b) :: l₁.zip l₂) l₃ := h
    cases h' with
    | cons hab h'' =>
      cases hq with
      | cons hq₁ hq₂ =>
        show Forall₂ _ ((a, b) :: l₁.zip l₂) _
        exact .cons ⟨hab, hq₁⟩ (forall₂_zip_and (Nat.succ.inj hl) h'' hq₂)

/-- A `List.Forall₂` against a mapped list, at the unmapped one. -/
theorem lforall₂_of_map_right {α β γ : Type} {R : α → γ → Prop} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ (l₂.map g) →
      List.Forall₂ (fun a b => R a (g b)) l₁ l₂
  | [], [], _ => .nil
  | [], b :: l₂, h => by
    have h' : List.Forall₂ R [] (g b :: l₂.map g) := h
    cases h'
  | _ :: _, [], h => by
    have h' : List.Forall₂ R _ [] := h
    cases h'
  | a :: l₁, b :: l₂, h => by
    have h' : List.Forall₂ R (a :: l₁) (g b :: l₂.map g) := h
    cases h' with
    | cons h₁ h₂ => exact .cons h₁ (lforall₂_of_map_right h₂)

/-! ## A rule's stage without its generated right-hand side -/

/-- **A twin rule's stage, but for the generated right-hand side**: the conjuncts of `TwinRuleJ`
before its last one (the declared rule closed, annotated, scoped, `let`-free; the installed
rule with the canonical rule's constructor, counts, fire mode, parameter blindness, K bit and
η verdict; a plain rule's major premise; a nested rule's major-premise domain). -/
def TwinRuleFront (J : Judgements .anon) (env envSelf : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (recName : KKey) (lps : List LevelParam) (cvW' : ConstantVal .anon) (mI rP : Nat)
    (rW rW' rC : RecRule .anon) : Prop :=
  rW.ctor = rW'.ctor ∧ rW.nfields = rW'.nfields ∧
  rW.rhs.looseBVarsBounded 0 = true ∧ rW.rhs.hasFvar = false ∧
  J.annot envSelf 0 rW.rhs rW'.rhs ∧
  rW'.rhs.allLevelParamsDefined lps = true ∧
  rW'.rhs.constsResolve envSelf = true ∧
  Ix.Kernel.Semantics.letFree rW'.rhs = true ∧
  rW'.ctor = rC.ctor ∧ rW'.nfields = rC.nfields ∧
  rW'.ctorParams = rC.ctorParams ∧ rW'.fire = rC.fire ∧
  rW'.k = rC.k ∧ rW'.paramsBlind = rC.paramsBlind ∧
  rW'.eta = Ix.Kernel.recRuleEtaOf env.find? recName rC.ctor ∧
  (rW'.fire = .plain → ∀ cvj cnP cnF,
    env.find? rW'.ctor = some (.ctorInfo cvj cnP cnF) →
    Ix.Kernel.Expr.recRulePlain cvW'.type mI rP rW'.ctorParams cvj.levelParams = true) ∧
  (∀ lvls pins, rW'.fire = .nested lvls pins →
    ∃ pre dom body bm D,
      cvW'.type.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Ix.Kernel.Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map (fun i => Ix.Kernel.Expr.bvar (mI - rP - 1 - i)))

/-- With a generated right-hand side for the rule, the stage is IxC's. -/
theorem twinRuleJ_of_front {J : Judgements .anon} {env envSelf : Ix.Kernel.Env .anon}
    {f : KKey → KKey} {recName : KKey} {lps : List LevelParam} {cvW' : ConstantVal .anon}
    {mI rP : Nat} {rW rW' rC : RecRule .anon}
    (h : TwinRuleFront J env envSelf f recName lps cvW' mI rP rW rW' rC)
    (hg : TwinRuleGen J env f lps rC rW') :
    TwinRuleJ J env envSelf f recName lps cvW' mI rP rW rW' rC := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨g, hg1, hg2, hg3⟩ := hg
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, g,
    hg1, hg2, hg3⟩

/-- A `List.Forall₂` under an implication. -/
theorem lforall₂_imp {α β : Type} {R S : α → β → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (H _ _ hr) (lforall₂_imp H hs)

/-! ## The facts -/

/-- **The canonical member above the twin's**: the twin's checked type is the canonical type up
to `WrapRel` (equal, or with wrappers the canonical type keeps consumed), and each checked rule is
the canonical rule, renamed to the twin's peers, up to `WrapRel`. -/
def CanonAbove (env : Ix.Kernel.Env .anon) (f : KKey → KKey) (w : TwinRecPart .anon) : Prop :=
  WrapRel env.find? w.cvC.type w.cvW'.type ∧
    List.Forall₂ (fun (rW' rC : RecRule .anon) =>
      WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs) w.rulesW' w.rulesC

/-- **The twin's member above the canonical one**: the canonical type is the twin's checked type
up to `WrapRel`, and each rule has a generated right-hand side above the canonical rule and,
renamed to the twin's peers, above the checked rule, typed where it is not the canonical one
(`TwinRuleGen`). -/
def TwinAbove (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (w : TwinRecPart .anon) : Prop :=
  WrapRel env.find? w.cvW'.type w.cvC.type ∧
    List.Forall₂ (fun (rW' rC : RecRule .anon) =>
      TwinRuleGen J env f w.cvC.levelParams rC rW') w.rulesW' w.rulesC

/-- **A twin's member against its canonical member**, as the circuit's two family checks of the
block give them (each record's member compared with the block's reconstruction on its own, as
the reconstruction or its full consumption): the major-premise domain of the twin's checked type
has the canonical type's head, and its arguments where those are bound variables (the circuit
never consumes the major premise's domain); and the canonical member is above the twin's, or the
twin's above the canonical one. -/
structure TwinMemberCmp (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (w : TwinRecPart .anon) : Prop where
  major : ∃ DW DC, Core.piDomAt w.mI w.cvW'.type = some DW ∧
    Core.piDomAt w.mI w.cvC.type = some DC ∧ DW.getAppFn = DC.getAppFn ∧
    ((∀ a ∈ DC.getAppArgs, ∃ i, a = .bvar i) → DW.getAppArgs = DC.getAppArgs)
  form : CanonAbove env f w ∨ TwinAbove J env f w

/-- **What the circuit side hands for a twin record**, over the parts `ws` of the record and a
peer renaming `f` (taken as `Decl.twinPeerRename ws`, which sends each canonical recursor to its
twin and fixes the rest): each part's canonical recursor is a member `x` of the block's family
record `rb`, and the part is comparable with it (`TwinMemberCmp`); and for each part IxC's twin
record's own conjuncts but the generated terms: the front door at the positional package, no
`let` in the checked type, the canonical recursor stored with the part's counts and rules, the
level parameters, the rules' stages (`TwinRuleFront`), and the checked recursor storing the
declared one (`ValStored`, `RuleStored`). The block (the parts' declared recursors), the
companion each part copies, and that the names the step stores are distinct and fresh are not
handed: the parts are built from the members' data at the environment (`Decl.mkTwinRecParts`),
and the rest is proved (`twinStepTarget_of_facts`). -/
structure TwinPartsFacts (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (rb : _root_.Address) (crb : Ixon.Constant) (ws : List (TwinRecPart .anon))
    (f : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon) : Prop where
  canonAt : ∀ w ∈ ws, ∃ x, ConstAddrOf rb crb x ∧ w.kC = keyOf t x ∧
    TwinMemberCmp twinPosRulesJ env f w
  front : ∀ w ∈ ws, ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW'
  letFree : ∀ w ∈ ws, Ix.Kernel.Semantics.letFree w.cvW'.type = true
  canonical : ∀ w ∈ ws, env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC)
  lvls : ∀ w ∈ ws, w.cvW.levelParams = w.cvC.levelParams
  rulesLen : ∀ w ∈ ws, w.rulesW.length = w.rulesW'.length
  rules : ∀ w ∈ ws, Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
    TwinRuleFront twinPosRulesJ env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ f w.cvW.name
      w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC) (w.rulesW.zip w.rulesW') w.rulesC
  stored : ∀ w ∈ ws, ValStored w.cvW' w.cvW ∧ List.Forall₂ RuleStored w.rulesW' w.rulesW

/-- A constant of an environment is found under its name. -/
theorem find_isSome_of_mem {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon}
    (h : ci ∈ env.consts) : (env.find? ci.name).isSome = true := by
  unfold Ix.Kernel.Env.find?
  exact List.find?_isSome.mpr ⟨ci, h, by simp⟩

/-- **The target's conclusion from the facts** (module docstring): IxC's twin record, each
member stored as its reading, a model companion at each member, the companions, and the reload
of each new constant at the key of an address, after the step, given that the block is the
parts' declared recursors, the names the step stores distinct and fresh, the companion each
part copies the canonical recursor's, and the reload of each checked twin recursor
(`twinMember_reloads`). -/
theorem twinTarget_of_facts {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {rb : _root_.Address} {crb : Ixon.Constant}
    {blk : List (ConstantInfo .anon)} {ws : List (TwinRecPart .anon)}
    (hF : TwinPartsFacts t env rb crb ws (Decl.twinPeerRename ws))
    (hblock : blk = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW)) (hblk : blk ≠ [])
    (hnames : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup)
    (hfresh : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none)
    (hmodel : ∀ w ∈ ws, ∀ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
        w.model? = some (cvm, mval, hint))
    (hinst : FamilyInstalled t env rb crb)
    (hcomp : Decl.CoreCompanions ⟨E, env, t, lim⟩)
    (hrel : ∀ w ∈ ws, Decl.ReloadsAs E t ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
      (.recInfo w.cvW' w.mI w.rP w.rulesW')) :
    ∃ env₂ : Ix.Kernel.Env .anon,
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
      Decl.CoreCompanions ⟨E, env₂, t, lim⟩ ∧
      (∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) := by
  -- each part's canonical recursor has a companion, which the part copies
  have hmod : ∀ w ∈ ws, ∃ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) ∧
        w.model? = some (cvm, mval, hint) := by
    intro w hw
    obtain ⟨x, hx, hk, -⟩ := hF.canonAt w hw
    obtain ⟨-, cvm, mval, hint, hf⟩ := hinst x hx
    rw [← hk] at hf
    exact ⟨cvm, mval, hint, hf, hmodel w hw cvm mval hint hf⟩
  -- each part's generated type and rule right-hand sides, from its comparison with the
  -- canonical member
  have hgen : ∀ w ∈ ws, TwinTypeGen twinPosRulesJ env w.cvC w.cvW' ∧
      List.Forall₂ (fun (rW' rC : RecRule .anon) =>
        TwinRuleGen twinPosRulesJ env (Decl.twinPeerRename ws) w.cvC.levelParams rC rW')
        w.rulesW' w.rulesC := by
    intro w hw
    obtain ⟨x, -, -, hcmp⟩ := hF.canonAt w hw
    rcases hcmp.form with ⟨hty, hrl⟩ | ⟨hty, hrl⟩
    · exact ⟨twinTypeGen_of_canonical_above hty,
        lforall₂_imp (fun rW' rC h => twinRuleGen_of_canonical_above h) hrl⟩
    · exact ⟨twinTypeGen_of_twin_above (Decl.judgeFrames_twinPosRulesJ env) (hF.front w hw)
        (hF.lvls w hw) hty, hrl⟩
  have hfind : ∀ ci ∈ twinRecs ws ++ twinModels ws,
      (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some ci := by
    intro ci hci
    have h := Ix.Kernel.Semantics.find?_mem_of_nodup (rest := env.consts) hnames hci
    rw [List.append_assoc] at h
    exact h
  have hrun : DeclRecTwinRunJ twinPosRulesJ env blk
      ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ := by
    have hne : ws ≠ [] := fun h => hblk (by rw [hblock, h, List.map_nil])
    refine ⟨ws, Decl.twinPeerRename ws, hne, hblock, rfl, hnames, hfresh,
      Decl.twinPeerRename_spec ws, fun w hw => ?_⟩
    obtain ⟨cvm, mval, hint, hfm, hm⟩ := hmod w hw
    obtain ⟨hty, hrl⟩ := hgen w hw
    have hz := forall₂_zip_and (hF.rulesLen w hw) (hF.rules w hw) hrl
    refine ⟨hF.front w hw, hF.letFree w hw, hF.canonical w hw, hF.lvls w hw, ?_,
      hty, hF.rulesLen w hw, forall₂_imp hz fun p rC h => twinRuleJ_of_front h.1 h.2⟩
    rw [hm]
    exact hfm
  refine ⟨⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩, hrun, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    obtain ⟨hvs, hrs⟩ := hF.stored w hw
    refine ⟨.recInfo w.cvW' w.mI w.rP w.rulesW', ?_, hvs, rfl, rfl, hrs⟩
    have h := hfind _ (List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩))
    show (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? w.cvW.name =
      some (.recInfo w.cvW' w.mI w.rP w.rulesW')
    rw [← (hF.front w hw).name_eq]
    exact h
  · intro ci hci
    rw [hblock] at hci
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
  · refine coreCompanions_twin (c := ⟨E, env, t, lim⟩) hcomp
      (Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun) fun w hw => ?_
    obtain ⟨x, -, -, hcmp⟩ := hF.canonAt w hw
    have hrc : List.Forall₂ (fun rW' rC : RecRule .anon => rW'.ctor = rC.ctor ∧ rW'.fire = rC.fire)
        w.rulesW' w.rulesC :=
      forall₂_zip_right (hF.rulesLen w hw) (hF.rules w hw) fun p rC h => by
        obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, h12, -⟩ := h
        exact ⟨h9, h12⟩
    exact ⟨hF.canonical w hw, hrc, hcmp.major⟩
  · -- a new constant at the key of an address is a twin recursor: a model copy's key is derived
    intro ci hci hnone x hx
    have hmem : ci ∈ twinRecs ws ++ (twinModels ws ++ env.consts) :=
      Ix.Kernel.Semantics.Env.find?_mem hci
    rcases List.mem_append.mp hmem with hr | hrest
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact hrel w hw
    · rcases List.mem_append.mp hrest with hm | henv
      · obtain ⟨w, -, hmi⟩ := List.mem_filterMap.mp hm
        unfold TwinRecPart.modelInfo? at hmi
        obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
        exact (keyOf_nonAux t x w.cvW.name .model hx.symm).elim
      · have hs := find_isSome_of_mem henv
        rw [hnone] at hs
        cases hs

/-- **The circuit-side seam of the twin step**, at a record form `RForm`: at every hypothesis of
the target, the second record's declaration as read and the facts of its parts. What the circuit
side needs of the second record's references beyond the hypotheses (that none is the reference of
an inert axiom) it takes from the second record's own family check. Where the family record is
in the form `RForm` whenever the second record is, and `RForm` is the reconstruction's form at
every member, each part's canonical member is above it (`CanonAbove`). -/
def TwinSeam (RForm : RecordFormPred) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
    (cb crb crb' : Ixon.Constant) (ms rs' : Array Ixon.MutConst) (lim : Option Nat)
    (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    FamBlockRecord E₀ B cb ms → FamRecOfBlock calls bAddr t E₀ B rb crb lim →
    FamRecRecord E₀ rb' crb' rs' →
    rs'.size ≠ 0 → rb' ≠ rb →
    FamilyCallAtLim calls bAddr t B rb' lim cs →
    (RForm calls bAddr t E₀ B rb' lim → RForm calls bAddr t E₀ B rb lim) →
    ModeledRouteAt calls B →
    Decl.PrefixInv.{u} E t lim env →
    (∀ x, UsedRef E₀ rb' x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf rb' crb' x ∨ ¬ NeedOk E₀ x) →
    FamilyInstalled t env rb crb →
    (∀ x, ConstAddrOf rb' crb' x → env.find? (keyOf t x) = none) →
    (∀ x, ConstAddrOf rb' crb' x → Decl.KeyFree (keyOf t x)) →
    ∃ ds : List Decl.TwinMemberData,
      TwinDeclReads t E₀ rb' crb' (ds.map fun d => .recInfo d.cvW d.mI d.rP d.rulesW) ∧
      TwinPartsFacts t env rb crb (Decl.mkTwinRecParts env ds)
        (Decl.twinPeerRename (Decl.mkTwinRecParts env ds)) ∧
      TwinLoadFacts t E₀ env rb' crb' (Decl.mkTwinRecParts env ds)

/-- The key of an address is its own base: a role key or an address key. -/
theorem keyOf_base (t : Ix.Kernel.RoleTable) (a : _root_.Address) : (keyOf t a).base = keyOf t a := by
  rcases keyOf_cases t a with ⟨hk, -⟩ | ⟨r, -, hk⟩ <;> rw [hk] <;> rfl

/-- **The twin step's target from the seam** (`TwinSeam`): the parts are the members' data with
the companions the environment stores (`Decl.mkTwinRecParts`), so the block is the parts'
declared recursors and each part copies the canonical recursor's companion; the names the step
stores are the second record's keys, distinct by its reading, and their model copies' keys,
derived from them; all are fresh, a model copy's key because its root is not stored
(`Decl.AuxRootSynced`). -/
theorem twinStepTarget_of_facts {RForm : RecordFormPred} (hseam : TwinSeam.{u} RForm) :
    TwinStepTarget.{u} RForm := by
  intro calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs' lim cs ht hRS hSS hB hrbB hrb' hsz
    hne hcall hpref hroute hinv haux href hinst hfresh hkey
  obtain ⟨ds, hreads, hF, hLd⟩ := hseam calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs'
    lim cs ht hRS hSS hB hrbB hrb' hsz hne hcall hpref hroute hinv href hinst hfresh hkey
  -- the parts copy the companions the environment stores
  have hmodel : ∀ w ∈ Decl.mkTwinRecParts env ds, ∀ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
        w.model? = some (cvm, mval, hint) := by
    intro w hw cvm mval hint h
    unfold Decl.mkTwinRecParts at hw
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hw
    exact Decl.lookupModelInfo?_eq_some.mpr h
  -- the block is the parts' declared recursors
  have hblock : ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) =
      (Decl.mkTwinRecParts env ds).map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW) := by
    unfold Decl.mkTwinRecParts
    simp only [List.map_map] <;> rfl
  obtain ⟨ws, hws⟩ : ∃ ws, ws = Decl.mkTwinRecParts env ds := ⟨_, rfl⟩
  rw [← hws] at hF hLd hmodel hblock
  obtain ⟨blk, hb⟩ : ∃ blk, blk = ds.map (fun d => ConstantInfo.recInfo d.cvW d.mI d.rP d.rulesW) :=
    ⟨_, rfl⟩
  rw [← hb] at hreads hblock
  -- each part's name is the key of a constant address of the second record
  have hkeyOf : ∀ w ∈ ws, ∃ x, ConstAddrOf rb' crb' x ∧ w.cvW.name = keyOf t x := by
    intro w hw
    have hci : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ blk := by
      rw [hblock]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 _ hci
    exact ⟨x, hx, hn⟩
  have hname_eq : ∀ w ∈ ws, w.cvW'.name = w.cvW.name := fun w hw => (hF.front w hw).name_eq
  have hnd : (ws.map (·.cvW.name)).Nodup := by
    have h := hreads.1
    rw [hblock, List.map_map] at h
    exact h
  have hnames : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup :=
    Decl.twinRecs_append_twinModels_nodup hnd hname_eq fun w hw k tk h => by
      obtain ⟨x, -, hn⟩ := hkeyOf w hw
      exact keyOf_nonAux t x k tk (hn.symm.trans h)
  have hfresh₂ : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none :=
    Decl.twinRecs_append_twinModels_fresh hname_eq
      (fun w hw => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        exact hfresh x hx)
      (fun w hw _ => by
        obtain ⟨x, hx, hn⟩ := hkeyOf w hw
        rw [hn]
        apply haux.fresh_of_base_none
        show env.find? (keyOf t x).base = none
        rw [keyOf_base]
        exact hfresh x hx)
  -- the record has a member, whose constant address the block reads
  have hblk : blk ≠ [] := by
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hsz]⟩
    obtain ⟨ci, hci, -⟩ := hreads.2.2 _ (Or.inr ⟨rs', 0, m, hrb'.muts, hm, Or.inl rfl⟩)
    exact List.ne_nil_of_mem hci
  -- each checked twin recursor reloads after the step
  have hrelW : ∀ w ∈ ws, Decl.ReloadsAs E t ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩
      (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
    refine twinMember_reloads ht hSS hrb' hreads hblock hF.front hLd
      (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinRecs ws))
      fun ci hci => ?_
    rw [hblock] at hci
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hci
    have hmem : ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈
        twinRecs ws ++ (twinModels ws ++ env.consts) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h := find_isSome_of_mem (env := ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩) hmem
    have hn : (ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW').name =
        (ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW).name := (hF.front w hw).name_eq
    rw [hn] at h
    exact h
  obtain ⟨env₂, hrun, hstored, hmodel, hcomp, hrel⟩ :=
    twinTarget_of_facts (lim := lim) hF hblock hblk hnames hfresh₂ hmodel hinst hinv.companions
      hrelW
  exact ⟨blk, env₂, hreads, hrun, hstored, hmodel, hcomp, hrel⟩

end IxVM.Refinement.Typing.TwinFamily
