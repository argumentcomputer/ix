import IxVMRefinement.TwinFamily.Companions

/-! # The twin step's target from facts about the twin record

`TwinStepTarget`'s conclusion is the second record's declaration as read, IxC's twin record at
the positional package, each member stored as its reading, a model companion at each member,
and the scoped core's companions after the step. This module states what the circuit side has
to hand for it, part by part (`TwinPartsFacts`), and proves the conclusion from that, the
reading, the block's family record installed and in the reconstruction's form, and the
companions before the step (`twinTarget_of_facts`); with a producer of the facts at every
hypothesis of the target, the target itself (`twinStepTarget_of_facts`).

The facts are those of IxC's record that are about the second record (its front door, its rules'
stages, its stored annotation) and the second record's own comparison with the reconstruction
(`TwinBelowRecon`: its type and rules the reconstruction's up to consumed wrappers, its
major-premise domain the reconstruction's), with the canonical recursor of each part named as a
member of the block's family record. Three things are not facts of the second record:

* the model companions: the family record is installed, so each canonical recursor has a
  companion, which the record copies to the twin (`DeclRecTwinRunJ`'s `some` branch);
* the generated type and rule right-hand sides IxC's record asks: the canonical record is in the
  reconstruction's form (`CanonReconForm`), so its own terms are above the second record's and
  are the generated ones, and nothing is typed (`twinTypeGen_of_canonical_above`);
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

/-- With the canonical rule, renamed to the twin's peers, above the twin's rule, the stage is
IxC's: the canonical right-hand side is the generated one. -/
theorem twinRuleJ_of_front {J : Judgements .anon} {env envSelf : Ix.Kernel.Env .anon}
    {f : KKey → KKey} {recName : KKey} {lps : List LevelParam} {cvW' : ConstantVal .anon}
    {mI rP : Nat} {rW rW' rC : RecRule .anon}
    (h : TwinRuleFront J env envSelf f recName lps cvW' mI rP rW rW' rC)
    (hW : WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs) :
    TwinRuleJ J env envSelf f recName lps cvW' mI rP rW rW' rC := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, rC.rhs,
    WrapRel.refl _ _, hW, Or.inl rfl⟩

/-! ## The facts -/

/-- **The second record's own comparison with the reconstruction** `g` (its type, its rules'
right-hand sides at the canonical record's peers) for one part: the twin's checked type is
below `g.1` (the reconstruction or a consumption of its wrappers); each checked rule is below
the reconstruction's rule renamed to the twin's peers; and the major-premise domain of the
twin's type has the reconstruction's head, and its arguments where those are bound
variables. -/
structure TwinBelowRecon (env : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (g : KExpr × List KExpr) (w : TwinRecPart .anon) : Prop where
  ty : WrapRel env.find? g.1 w.cvW'.type
  rules : List.Forall₂ (fun (rW' : RecRule .anon) (gr : KExpr) =>
    WrapRel env.find? (gr.renameConsts f) rW'.rhs) w.rulesW' g.2
  major : ∃ DW DR, Core.piDomAt w.mI w.cvW'.type = some DW ∧ Core.piDomAt w.mI g.1 = some DR ∧
    DW.getAppFn = DR.getAppFn ∧
    ((∀ a ∈ DR.getAppArgs, ∃ i, a = .bvar i) → DW.getAppArgs = DR.getAppArgs)

/-- **What the circuit side hands for a twin record**, over the parts `ws` of the record and a
peer renaming `f` (taken as `Decl.twinPeerRename ws`, which sends each canonical recursor to its
twin and fixes the rest): the block is the parts' declared recursors; the names the step stores
are distinct and fresh; each part's canonical recursor is a member `x` of the block's family record `rb`, and the part
is below the reconstruction `recon x`; its stored companion is the one the part copies; and for
each part IxC's twin record's own conjuncts but the generated terms: the front door at the
positional package, no `let` in the checked type, the canonical recursor stored with the part's
counts and rules, the level parameters, the rules' stages (`TwinRuleFront`), and the checked
recursor storing the declared one (`ValStored`, `RuleStored`). -/
structure TwinPartsFacts (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (rb : _root_.Address) (crb : Ixon.Constant) (recon : _root_.Address → KExpr × List KExpr)
    (blk : List (ConstantInfo .anon)) (ws : List (TwinRecPart .anon))
    (f : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon) : Prop where
  block : blk = ws.map (fun w => .recInfo w.cvW w.mI w.rP w.rulesW)
  names : ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup
  fresh : ∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none
  canonAt : ∀ w ∈ ws, ∃ x, ConstAddrOf rb crb x ∧ w.kC = keyOf t x ∧
    TwinBelowRecon env f (recon x) w
  model : ∀ w ∈ ws, ∀ cvm mval hint,
    env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) →
      w.model? = some (cvm, mval, hint)
  front : ∀ w ∈ ws, ConstantValCheckJ twinPosRulesJ env w.cvW w.cvW'
  letFree : ∀ w ∈ ws, Ix.Kernel.Semantics.letFree w.cvW'.type = true
  canonical : ∀ w ∈ ws, env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC)
  lvls : ∀ w ∈ ws, w.cvW.levelParams = w.cvC.levelParams
  rulesLen : ∀ w ∈ ws, w.rulesW.length = w.rulesW'.length
  rules : ∀ w ∈ ws, Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
    TwinRuleFront twinPosRulesJ env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ f w.cvW.name
      w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC) (w.rulesW.zip w.rulesW') w.rulesC
  stored : ∀ w ∈ ws, ValStored w.cvW' w.cvW ∧ List.Forall₂ RuleStored w.rulesW' w.rulesW

/-- **The target's conclusion from the facts** (module docstring): IxC's twin record, each
member stored as its reading, a model companion at each member, and the companions, after the
step. -/
theorem twinTarget_of_facts {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {rb : _root_.Address} {crb : Ixon.Constant}
    {recon : _root_.Address → KExpr × List KExpr} {blk : List (ConstantInfo .anon)}
    {ws : List (TwinRecPart .anon)}
    (hF : TwinPartsFacts t env rb crb recon blk ws (Decl.twinPeerRename ws)) (hblk : blk ≠ [])
    (hinst : FamilyInstalled t env rb crb)
    (hform : CanonReconForm t env rb crb recon)
    (hcomp : Decl.CoreCompanions ⟨E, env, t, lim⟩) :
    ∃ env₂ : Ix.Kernel.Env .anon,
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
      Decl.CoreCompanions ⟨E, env₂, t, lim⟩ := by
  -- each part's canonical recursor has a companion, which the part copies
  have hmod : ∀ w ∈ ws, ∃ cvm mval hint,
      env.find? (Ix.Kernel.auxKey w.kC .model) = some (.defnInfo cvm mval hint) ∧
        w.model? = some (cvm, mval, hint) := by
    intro w hw
    obtain ⟨x, hx, hk, -⟩ := hF.canonAt w hw
    obtain ⟨-, cvm, mval, hint, hf⟩ := hinst x hx
    rw [← hk] at hf
    exact ⟨cvm, mval, hint, hf, hF.model w hw cvm mval hint hf⟩
  -- each part's canonical terms are the reconstruction's
  have hrec : ∀ w ∈ ws, ∃ x, TwinBelowRecon env (Decl.twinPeerRename ws) (recon x) w ∧
      w.cvC.type = (recon x).1 ∧ w.rulesC.map (·.rhs) = (recon x).2 := by
    intro w hw
    obtain ⟨x, hx, hk, hb⟩ := hF.canonAt w hw
    have hc := hF.canonical w hw
    rw [hk] at hc
    obtain ⟨hty, hrls⟩ := hform x hx _ _ _ _ hc
    exact ⟨x, hb, hty, hrls⟩
  have hfind : ∀ ci ∈ twinRecs ws ++ twinModels ws,
      (⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? ci.name =
        some ci := by
    intro ci hci
    have h := Ix.Kernel.Semantics.find?_mem_of_nodup (rest := env.consts) hF.names hci
    rw [List.append_assoc] at h
    exact h
  have hrun : DeclRecTwinRunJ twinPosRulesJ env blk
      ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ := by
    have hne : ws ≠ [] := fun h => hblk (by rw [hF.block, h, List.map_nil])
    refine ⟨ws, Decl.twinPeerRename ws, hne, hF.block, rfl, hF.names, hF.fresh,
      Decl.twinPeerRename_spec ws, fun w hw => ?_⟩
    obtain ⟨cvm, mval, hint, hfm, hm⟩ := hmod w hw
    obtain ⟨x, hb, hty, hrls⟩ := hrec w hw
    have hW : List.Forall₂ (fun (rW' : RecRule .anon) (rC : RecRule .anon) =>
        WrapRel env.find? (rC.rhs.renameConsts (Decl.twinPeerRename ws)) rW'.rhs)
        w.rulesW' w.rulesC := by
      have h := hb.rules
      rw [← hrls] at h
      exact lforall₂_of_map_right h
    have hz := forall₂_zip_and (hF.rulesLen w hw) (hF.rules w hw) hW
    have hty' : WrapRel env.find? w.cvC.type w.cvW'.type := by
      rw [hty]
      exact hb.ty
    refine ⟨hF.front w hw, hF.letFree w hw, hF.canonical w hw, hF.lvls w hw, ?_,
      twinTypeGen_of_canonical_above (J := twinPosRulesJ) hty', hF.rulesLen w hw,
      forall₂_imp hz fun p rC h => twinRuleJ_of_front h.1 h.2⟩
    rw [hm]
    exact hfm
  refine ⟨⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩, hrun, ?_, ?_, ?_⟩
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
  · refine coreCompanions_twin (c := ⟨E, env, t, lim⟩) hcomp
      (Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun) fun w hw => ?_
    obtain ⟨x, hb, hty, -⟩ := hrec w hw
    obtain ⟨DW, DR, hDW, hDR, hfn, hargs⟩ := hb.major
    have hrc : List.Forall₂ (fun rW' rC : RecRule .anon => rW'.ctor = rC.ctor ∧ rW'.fire = rC.fire)
        w.rulesW' w.rulesC :=
      forall₂_zip_right (hF.rulesLen w hw) (hF.rules w hw) fun p rC h => by
        obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, h12, -⟩ := h
        exact ⟨h9, h12⟩
    have hDC : Core.piDomAt w.mI w.cvC.type = some DR := by
      rw [hty]
      exact hDR
    exact ⟨hF.canonical w hw, hrc, DW, DR, hDW, hDC, hfn, hargs⟩

/-- **The circuit-side seam of the twin step**: at every hypothesis of the target but the
canonical record's form, the second record's declaration as read and the facts of its parts. -/
def TwinSeam (recon : _root_.Address → KExpr × List KExpr) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
    (cb crb crb' : Ixon.Constant) (ms rs' : Array Ixon.MutConst) (lim : Option Nat)
    (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    FamBlockRecord E₀ B cb ms → FamRecOfBlock calls t E₀ B rb crb →
    FamRecRecord E₀ rb' crb' rs' →
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
    ∃ (blk : List (ConstantInfo .anon)) (ws : List (TwinRecPart .anon)),
      TwinDeclReads t E₀ rb' crb' blk ∧
      TwinPartsFacts t env rb crb recon blk ws (Decl.twinPeerRename ws)

/-- **The twin step's target from the seam** (`TwinSeam`). -/
theorem twinStepTarget_of_facts {recon : _root_.Address → KExpr × List KExpr}
    (hseam : TwinSeam.{u} recon) :
    TwinStepTarget.{u} recon := by
  intro calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs' lim cs ht hRS hSS hB hrbB hrb' hsz
    hne hcall hroute hinv href hinst hform hinert hfresh hkey
  obtain ⟨blk, ws, hreads, hF⟩ := hseam calls bAddr t E₀ E env B rb rb' cb crb crb' ms rs'
    lim cs ht hRS hSS hB hrbB hrb' hsz hne hcall hroute hinv href hinst hinert hfresh hkey
  -- the record has a member, whose constant address the block reads
  have hblk : blk ≠ [] := by
    obtain ⟨m, hm⟩ : ∃ m, rs'[0]? = some m := ⟨rs'[0], by simp [Nat.pos_of_ne_zero hsz]⟩
    obtain ⟨ci, hci, -⟩ := hreads.2.2 _ (Or.inr ⟨rs', 0, m, hrb'.muts, hm, Or.inl rfl⟩)
    exact List.ne_nil_of_mem hci
  obtain ⟨env₂, hrun, hstored, hmodel, hcomp⟩ :=
    twinTarget_of_facts (E := E) (lim := lim) hF hblk hinst hform hinv.companions
  exact ⟨blk, env₂, hreads, hrun, hstored, hmodel, hcomp⟩

end IxVM.Refinement.Typing.TwinFamily
