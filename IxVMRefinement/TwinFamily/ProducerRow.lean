import IxVMRefinement.TwinFamily.CheckExtract
import IxVMRefinement.TwinFamily.StoredTwinRow
import IxVMRefinement.TwinFamily.GraphClosed
import IxVMRefinement.Binding.FamilyReconStore
import IxVMRefinement.Assembly.TypingRecLateNativeScope
import IxVMRefinement.Assembly.FoldClauseAlias
import IxVMRefinement.FamilyAlias.BlockRowCheck

/-! # Twin recursor step producer for `FamilyTwinRowFam`

Assembles `TwinDeclReads`, `TwinPartsFacts`, and `TwinLoadFacts` for a second family record `A` of
a modeled block `B` against its canonical family record `rb` (either the graph's record `fam B =
some rb` or a stored record `StoredTwinCanon`), and exports `familyTwin_of_premises` producing
`FamilyTwinRowFam Binding.FamilyRecon.RFormS FormerOpenTraceAt`.

* **Isolated upstream interfaces**:
  - `TwinCallFlat`: positional flattened family (`FamilyOfBlock`, `RecordFlat`, `BlockDerivedFlat`,
    and recursor level-count agreement with the elimination offset) from an accepted `check_family`
    call;
  - `RecordWrapConsObs`, `TwinCallRecon`: reconstruction or observed wrapper-consumption form
    (`RFormS ∨ RecordWrapConsObs`) from an accepted `check_family` call;
  - `StoredRecLvlsOk`: level-count agreement of a stored family recursor with its block's
    elimination offset;
  - `GraphStoreClosed`: a closed predecessor set excluding `rb` on the graph arm when both
    records are in observed full-consumption form.
* **Pure reconstruction and expression bridges**:
  - `recTypeAt_majorDom_info`: extracts the major-premise domain and depth of `recTypeAt`;
  - `wrapAt_mono`, `wrapAt_iprj`: monotonicity and non-definition property of `wrapAt`;
  - `ruleFollows_congr_exprLvEq`, `constsResolve_of_wrapRel`, `constsResolve_renameConsts_envSelf`,
    `allLevelParamsDefined_renameConsts`, `canonRules_k_false`.
* **Unified member assembly**: `CanonMemberAt` abstracts over canonical members coming from
  `StoredFamilyRecs` (`canonMemberAt_of_stored`) or from an accepted `check_family` call
  (`canonMemberAt_of_extracted`); `twinParts_of_canon_extracted` builds `TwinDeclReads`,
  `TwinPartsFacts`, and `TwinLoadFacts` in one pass across both sources.
* **Typing-half row**: `twinOnStoredFlat_of_premise` and `familyTwin_of_premises`. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Core (KExpr KLevel KKey ExprLvEq)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim coveredAt_stored)
open IxVM.Refinement.Binding (StoredFamiliesRForm StoredFamilyRecs)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry RecordFlat BlockDerivedFlat FlatView
  mutsRoot loadedAt peelForalls binderDomAfter hasBVarIn keyAddr)
open IxVM.Refinement.Binding.FamilyRecon (ReconView IndData wrapAt consumeAt Consumes FullCons
  LamsAlong RuleFollows recTypeAt ruleBodiesAt ctorsBefore elimLevel recAddrs MemberRecon
  RecordReconWith RFormS appSpine appBVarsDec appBVarsDown specParamsLifted wrapForalls liftIndices)
open Ix.Kernel (ConstantInfo ConstantVal RecRule Level LevelParam Expr)
open Ix.Kernel.Semantics (ConstantValCheckJ DeclRecTwinRunJ TwinRecPart twinProv twinModels twinRecs
  WrapRel WrapDom SymWrapT TwinRuleMatch Forall₂ letFree consumeWrapper)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Isolated upstream interfaces -/

/-- **Positional flattened family from an accepted `KernelModeled::check_family` call**: a
non-empty recursor block `r` accepted for an in-logic block `B` is the block's family over the
flattened family `es` derived from `B` at its elimination offset `off`, with `RecordFlat`,
`BlockDerivedFlat`, and every recursor's level count equal to `ind₀.lvls + off`. -/
def TwinCallFlat : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (B r : _root_.Address) (cr : Ixon.Constant)
    (rs : Array Ixon.MutConst) (lim : Option Nat) (cs : List (Call F)),
    t.check = .ok () → Bounded calls →
    LoadedReads.RunStore calls E₀ → LoadedReads.HashedRecordsStored calls E₀ →
    FamRecRecord E₀ r cr rs → rs.size ≠ 0 →
    (∀ cb, recordOf E₀ B = some cb → InLogic cb) →
    FamilyCallAtLim calls bAddr t B r lim cs →
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
      FamilyOfBlock E₀ B cb ms r cr rs (es.map FlatEntry.addr) ∧
      RecordFlat t E₀ r cr rs es ∧ BlockDerivedFlat t E₀ B off es ∧
      ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off

/-- **Observed wrapper-consumption record form**: every recursor of `rb` for block `B` in store `E`
has minor count matching the family's total constructor count and is an observed wrapper consumption
of the block's reconstruction, with wrapper arities witnessed in `calls`. -/
def RecordWrapConsObs (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (B rb : _root_.Address) : Prop :=
  ∃ (crb : Ixon.Constant) (rs : Array Ixon.MutConst) (es : List FlatEntry) (off fuel : Nat),
    recordOf E rb = some crb ∧
    crb.info = .muts rs ∧
    RecordFlat t E rb crb rs es ∧
    BlockDerivedFlat t E B off es ∧
    ∀ k r, rs[k]? = some (.recr r) →
      ctorsBefore (ReconView.ofStore t E) es es.length = some r.minors.toNat ∧
      MemberRecon (fun ty R => WrapConsObs (wrapAt t E) (WrapperObserved calls t) R ty)
        t E rb crb rs es off fuel k r

/-- **Reconstruction or observed wrapper-consumption form from an accepted `check_family` call**:
every non-empty recursor block `r` accepted for a block `B` satisfies either `RFormS` or
`RecordWrapConsObs` over `E₀`. -/
def TwinCallRecon : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (B r : _root_.Address) (cb cr : Ixon.Constant)
    (ms rs : Array Ixon.MutConst) (lim : Option Nat) (cs : List (Call F)),
    t.check = .ok () → Bounded calls →
    LoadedReads.RunStore calls E₀ → LoadedReads.HashedRecordsStored calls E₀ →
    FamBlockRecord E₀ B cb ms → FamRecRecord E₀ r cr rs → rs.size ≠ 0 →
    FamilyCallAtLim calls bAddr t B r lim cs →
    RFormS t E₀ B r ∨ RecordWrapConsObs calls t E₀ B r

/-- **Stored family recursor level-count agreement**: every recursor of a stored family record
for `B` has level count equal to the first inductive's level count plus the block's elimination
offset `off`. -/
def StoredRecLvlsOk : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (B rb : _root_.Address) (cb crb : Ixon.Constant)
    (ms rs : Array Ixon.MutConst) (es : List FlatEntry) (off : Nat),
    cb.info = .muts ms → crb.info = .muts rs →
    StoredFamilyRecs t R env B cb rb crb →
    BlockDerivedFlat t R B off es →
    ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
      ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
      rc.lvls.toNat = ind₀.lvls.toNat + off

/-- **Closed predecessor set excluding a claimed family record** (used on the graph arm only when
both the graph's canonical record `rb` and the twin `A` are in observed full-consumption form):
there is a set `S` of addresses closed under `ReconView.ofStore t E₀` and `FlatView.ofStore t E₀`,
containing `B`, and excluding every recursor projection of `rb`. -/
def GraphStoreClosed : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (B rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst),
        fam B = some rb → FamRecRecord E₀ rb crb rs →
        ∃ S : _root_.Address → Prop,
          (ReconView.ofStore t E₀).ClosedOn S ∧
          (FlatView.ofStore t E₀).ClosedOn S ∧
          S B ∧
          (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))

/-! ## Pure expression, `WrapRel`, and reconstruction helpers -/

private theorem hasBVarIn_mono_hi {lo hi₁ hi₂ : Nat} (hle : hi₁ ≤ hi₂) :
    ∀ (e : KExpr), hasBVarIn lo hi₂ e = false → hasBVarIn lo hi₁ e = false
  | .bvar i, h => by
    simp only [hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, h => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at h ⊢
    exact ⟨hasBVarIn_mono_hi hle f h.1, hasBVarIn_mono_hi hle a h.2⟩
  | .lam t b _, h => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at h ⊢
    exact ⟨hasBVarIn_mono_hi hle t h.1, hasBVarIn_mono_hi (Nat.add_le_add_right hle 1) b h.2⟩
  | .forallE t b _, h => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at h ⊢
    exact ⟨hasBVarIn_mono_hi hle t h.1, hasBVarIn_mono_hi (Nat.add_le_add_right hle 1) b h.2⟩
  | .letE t v b _, h => by
    simp only [hasBVarIn, Bool.or_eq_false_iff] at h ⊢
    exact ⟨⟨hasBVarIn_mono_hi hle t h.1.1, hasBVarIn_mono_hi hle v h.1.2⟩,
      hasBVarIn_mono_hi (Nat.add_le_add_right hle 1) b h.2⟩
  | .proj _ _ e, h => hasBVarIn_mono_hi hle e h

private theorem allLevelParamsDefined_renameConsts (f : KKey → KKey) (lps : List LevelParam) :
    ∀ (e : KExpr), (e.renameConsts f).allLevelParamsDefined lps = e.allLevelParamsDefined lps
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ t => allLevelParamsDefined_renameConsts f lps t
  | .app g a => by
    simp [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f lps g, allLevelParamsDefined_renameConsts f lps a]
  | .lam t b _ => by
    simp [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f lps t, allLevelParamsDefined_renameConsts f lps b]
  | .forallE t b _ => by
    simp [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f lps t, allLevelParamsDefined_renameConsts f lps b]
  | .letE t v b _ => by
    simp [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f lps t, allLevelParamsDefined_renameConsts f lps v,
      allLevelParamsDefined_renameConsts f lps b]
  | .proj _ _ e => allLevelParamsDefined_renameConsts f lps e

private theorem constsResolve_instantiateLevelParams (env : Ix.Kernel.Env .anon)
    (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ps us).constsResolve env = e.constsResolve env
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ t => constsResolve_instantiateLevelParams env ps us t
  | .app g a => by
    simp [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ps us g,
      constsResolve_instantiateLevelParams env ps us a]
  | .lam t b _ => by
    simp [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ps us t,
      constsResolve_instantiateLevelParams env ps us b]
  | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ps us t,
      constsResolve_instantiateLevelParams env ps us b]
  | .letE t v b _ => by
    simp [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ps us t,
      constsResolve_instantiateLevelParams env ps us v,
      constsResolve_instantiateLevelParams env ps us b]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ps us e]

private theorem letFree_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), letFree (e.instantiateLevelParams ps us) = letFree e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ _ => rfl
  | .app g a => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams ps us g, letFree_instantiateLevelParams ps us a]
  | .lam t b _ => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams ps us t, letFree_instantiateLevelParams ps us b]
  | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams ps us t, letFree_instantiateLevelParams ps us b]
  | .letE _ _ _ _ => rfl
  | .proj _ _ e => letFree_instantiateLevelParams ps us e

private theorem constsResolve_renameConsts_map {env env' : Ix.Kernel.Env .anon} {f : KKey → KKey}
    (hf : ∀ k, (env.find? k).isSome = true → (env'.find? (f k)).isSome = true)
    (hkeep : ∀ k, (env.find? k).isSome = true → (env'.find? k).isSome = true) :
    ∀ (e : KExpr), e.constsResolve env = true → (e.renameConsts f).constsResolve env' = true
  | .bvar _, _ | .sort _, _ => rfl
  | .lit (.natVal _), h => by
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hkeep _ h.1.1, hkeep _ h.1.2⟩, hkeep _ h.2⟩
  | .lit (.strVal _), h => by
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hkeep _ h.1.1.1.1.1.1.1.1.1, hkeep _ h.1.1.1.1.1.1.1.1.2⟩,
      hkeep _ h.1.1.1.1.1.1.1.2⟩, hkeep _ h.1.1.1.1.1.1.2⟩, hkeep _ h.1.1.1.1.1.2⟩,
      hkeep _ h.1.1.1.1.2⟩, hkeep _ h.1.1.1.2⟩, hkeep _ h.1.1.2⟩, hkeep _ h.1.2⟩, hkeep _ h.2⟩
  | .fvar _ t, h => constsResolve_renameConsts_map hf hkeep t h
  | .const k _, h => hf k h
  | .app g a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_renameConsts_map hf hkeep g h.1,
      constsResolve_renameConsts_map hf hkeep a h.2⟩
  | .lam t b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_renameConsts_map hf hkeep t h.1,
      constsResolve_renameConsts_map hf hkeep b h.2⟩
  | .forallE t b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_renameConsts_map hf hkeep t h.1,
      constsResolve_renameConsts_map hf hkeep b h.2⟩
  | .letE t v b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨constsResolve_renameConsts_map hf hkeep t h.1.1,
      constsResolve_renameConsts_map hf hkeep v h.1.2⟩,
      constsResolve_renameConsts_map hf hkeep b h.2⟩
  | .proj s _ e, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨hkeep s h.1, constsResolve_renameConsts_map hf hkeep e h.2⟩

private theorem constsResolve_getAppArgs {env : Ix.Kernel.Env .anon} :
    ∀ (e : KExpr), e.constsResolve env = true →
      ∀ a ∈ e.getAppArgs, a.constsResolve env = true
  | .app f x, h, a, ha => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact constsResolve_getAppArgs f h.1 a ha
    · exact h.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha
  | .lit _, _, _, ha | .proj _ _ _, _, _, ha => by
    simp [Expr.getAppArgs] at ha

private theorem constsResolve_consumeWrapper {find? : KKey → Option (ConstantInfo .anon)}
    {env : Ix.Kernel.Env .anon} {t t' : KExpr}
    (hc : consumeWrapper find? t = some t') (ht : t.constsResolve env = true) :
    t'.constsResolve env = true := by
  unfold consumeWrapper at hc
  cases hfn : t.getAppFn with
  | const k _ =>
    rw [hfn] at hc
    cases hargs : t.getAppArgs with
    | nil => simp [hargs] at hc
    | cons a rest =>
      rw [hargs] at hc
      dsimp only at hc
      split at hc
      · injection hc with ha
        subst ha
        exact constsResolve_getAppArgs t ht a (by rw [hargs]; exact List.mem_cons_self)
      · cases hc
  | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _
  | forallE _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
    rw [hfn] at hc; cases hc

private theorem hasFvar_renameConsts (f : KKey → KKey) :
    ∀ (e : KExpr), (e.renameConsts f).hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ _ => rfl
  | .app g a => by simp [Expr.renameConsts, Expr.hasFvar, hasFvar_renameConsts f g, hasFvar_renameConsts f a]
  | .lam t b _ => by simp [Expr.renameConsts, Expr.hasFvar, hasFvar_renameConsts f t, hasFvar_renameConsts f b]
  | .forallE t b _ => by simp [Expr.renameConsts, Expr.hasFvar, hasFvar_renameConsts f t, hasFvar_renameConsts f b]
  | .letE t v b _ => by
    simp [Expr.renameConsts, Expr.hasFvar, hasFvar_renameConsts f t,
      hasFvar_renameConsts f v, hasFvar_renameConsts f b]
  | .proj _ _ e => hasFvar_renameConsts f e

private theorem hasFvar_getAppArgs :
    ∀ (e : KExpr), e.hasFvar = false → ∀ a ∈ e.getAppArgs, a.hasFvar = false
  | .app f x, h, a, ha => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hasFvar_getAppArgs f h.1 a ha
    · exact h.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha
  | .lit _, _, _, ha | .proj _ _ _, _, _, ha => by
    simp [Expr.getAppArgs] at ha

private theorem hasFvar_consumeWrapper {find? : KKey → Option (ConstantInfo .anon)}
    {t t' : KExpr} (hc : consumeWrapper find? t = some t') (ht : t.hasFvar = false) :
    t'.hasFvar = false := by
  unfold consumeWrapper at hc
  cases hfn : t.getAppFn with
  | const k _ =>
    rw [hfn] at hc
    cases hargs : t.getAppArgs with
    | nil => simp [hargs] at hc
    | cons a rest =>
      rw [hargs] at hc
      dsimp only at hc
      split at hc
      · injection hc with ha; subst ha
        exact hasFvar_getAppArgs t ht a (by rw [hargs]; exact List.mem_cons_self)
      · cases hc
  | bvar _ | fvar _ _ | sort _ | app _ _ | lam _ _ _
  | forallE _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
    rw [hfn] at hc; cases hc

mutual
private theorem constsResolve_of_wrapRel {find? : KKey → Option (ConstantInfo .anon)}
    {env : Ix.Kernel.Env .anon} :
    ∀ {g d : KExpr}, WrapRel find? g d → g.hasFvar = false → letFree d = true →
      g.constsResolve env = true → d.constsResolve env = true
  | _, _, .bvar _, _, _, _ => rfl
  | _, _, .fvar _, hfv, _, _ => by simp [Expr.hasFvar] at hfv
  | _, _, .sort _, _, _, _ => rfl
  | _, _, .const _, _, _, h => h
  | _, _, .lit _, _, _, h => h
  | _, _, .app hf ha, hfv, hlf, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [letFree, Bool.and_eq_true] at hlf
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_of_wrapRel hf hfv.1 hlf.1 h.1,
      constsResolve_of_wrapRel ha hfv.2 hlf.2 h.2⟩
  | _, _, .lam _ hd hb, hfv, hlf, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [letFree, Bool.and_eq_true] at hlf
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_of_wrapDom hd hfv.1 hlf.1 h.1,
      constsResolve_of_wrapRel hb hfv.2 hlf.2 h.2⟩
  | _, _, .forallE _ hd hb, hfv, hlf, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [letFree, Bool.and_eq_true] at hlf
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨constsResolve_of_wrapDom hd hfv.1 hlf.1 h.1,
      constsResolve_of_wrapRel hb hfv.2 hlf.2 h.2⟩
  | _, _, .letE _ _ _, _, hlf, _ => by simp [letFree] at hlf
  | _, _, .proj he, hfv, hlf, h => by
    simp only [Expr.hasFvar] at hfv
    simp only [letFree] at hlf
    simp only [Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, constsResolve_of_wrapRel he hfv hlf h.2⟩
  | _, _, .zeta _, _, hlf, _ => by simp [letFree] at hlf

private theorem constsResolve_of_wrapDom {find? : KKey → Option (ConstantInfo .anon)}
    {env : Ix.Kernel.Env .anon} :
    ∀ {t t' : KExpr}, WrapDom find? t t' → t.hasFvar = false → letFree t' = true →
      t.constsResolve env = true → t'.constsResolve env = true
  | _, _, .keep hr, hfv, hlf, h => constsResolve_of_wrapRel hr hfv hlf h
  | _, _, .consume hc hd, hfv, hlf, h =>
    constsResolve_of_wrapDom hd (hasFvar_consumeWrapper hc hfv) hlf (constsResolve_consumeWrapper hc h)
end

private theorem constsResolve_renameConsts_envSelf {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)}
    (hname : ∀ w ∈ ws, w.cvW'.name = w.cvW.name)
    {e : KExpr} (he : e.constsResolve env = true) :
    (e.renameConsts (Decl.twinPeerRename ws)).constsResolve
      ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ = true := by
  refine constsResolve_renameConsts_map (fun k hk => ?_)
    (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinProv ws)) e he
  rcases Decl.twinPeerRename_spec ws k with hfix | ⟨w', hw', -, hmap⟩
  · rw [hfix]
    exact find_isSome_append (find_isSome_append hk (twinModels ws)) (twinProv ws)
  · rw [hmap]
    have hmem : ConstantInfo.recInfo w'.cvW' w'.mI w'.rP [] ∈
        twinProv ws ++ (twinModels ws ++ env.consts) :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w', hw', rfl⟩)
    have h := find_isSome_of_mem
      (env := ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩) hmem
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hname w' hw'] using h

private theorem constsResolve_envSelf {env : Ix.Kernel.Env .anon}
    {ws : List (TwinRecPart .anon)} {e : KExpr} (he : e.constsResolve env = true) :
    e.constsResolve ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ = true := by
  have h := constsResolve_renameConsts_map (f := id)
    (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinProv ws))
    (fun k hk => find_isSome_append (find_isSome_append hk (twinModels ws)) (twinProv ws)) e he
  rwa [renameConsts_eq_self_of_not_mentions e (fun _ hne => (hne rfl).elim)] at h

private theorem canonRules_k_false {src : Ixon.Constant} {ps : List LevelParam} {cParams : Nat} :
    ∀ {root : F} {rus : List Ixon.RecursorRule} {rules₀ rls : List (RecRule .anon)},
      LoadedReads.canonRules src ps false cParams root rus rules₀ = some rls →
      ∀ rl ∈ rls, rl.k = false
  | _, [], [], _, h, rl, hm => by
    simp [LoadedReads.canonRules] at h; subst h; cases hm
  | _, [], _ :: _, _, h, _, _ => by simp [LoadedReads.canonRules] at h
  | _, _ :: _, [], _, h, _, _ => by simp [LoadedReads.canonRules] at h
  | root, ru :: rus, rl₀ :: rules₀, rls, h, rl, hm => by
    unfold LoadedReads.canonRules at h
    cases ha : LoadedReads.canonAnn src ps root ru.rhs rl₀.rhs with
    | none => rw [ha] at h; cases h
    | some rhs' =>
      rw [ha] at h; simp only [Option.bind_some] at h
      cases hr : LoadedReads.canonRules src ps false cParams (root + 1) rus rules₀ with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hm with rfl | hm'
        · rfl
        · exact canonRules_k_false hr rl hm'

private theorem exprLvEq_peelForalls :
    ∀ (n : Nat) {e₁ e₂ r₁ : KExpr}, ExprLvEq e₁ e₂ → peelForalls n e₁ = some r₁ →
      ∃ r₂, peelForalls n e₂ = some r₂ ∧ ExprLvEq r₁ r₂
  | 0, _, _, _, h, h1 => by
    simp only [peelForalls, Option.some.injEq] at h1
    subst h1; exact ⟨_, rfl, h⟩
  | n + 1, _, _, _, h, h1 => by
    cases h with
    | forallE _ hb => exact exprLvEq_peelForalls n hb h1
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [peelForalls] at h1

private theorem exprLvEq_binderDomAfter {n : Nat} {e₁ e₂ d₁ : KExpr}
    (h : ExprLvEq e₁ e₂) (hd : binderDomAfter n e₁ = some d₁) :
    ∃ d₂, binderDomAfter n e₂ = some d₂ ∧ ExprLvEq d₁ d₂ := by
  unfold binderDomAfter at hd ⊢
  cases hp : peelForalls n e₁ with
  | none => simp [hp] at hd
  | some r₁ =>
    rw [hp] at hd
    cases r₁ with
    | forallE d b m =>
      simp only [Option.some.injEq] at hd; subst hd
      obtain ⟨r₂, hp₂, hr⟩ := exprLvEq_peelForalls n h hp
      cases hr with
      | forallE hd₂ _ =>
        rw [hp₂]; exact ⟨_, rfl, hd₂⟩
    | _ => simp at hd

private theorem exprLvEq_getAppFn {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    ExprLvEq e₁.getAppFn e₂.getAppFn := by
  induction h with
  | app _ _ ihf _ => exact ihf
  | bvar => exact .bvar
  | fvar ht => exact .fvar ht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lam ht hb => exact .lam ht hb
  | forallE ht hb => exact .forallE ht hb
  | letE ht hv hb => exact .letE ht hv hb
  | lit => exact .lit
  | proj he => exact .proj he

private theorem forall₂_append_pr {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r₁ r₂ : List β},
      List.Forall₂ R l₁ r₁ → List.Forall₂ R l₂ r₂ → List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h h₁, h₂ => .cons h (forall₂_append_pr h₁ h₂)

private theorem exprLvEq_getAppArgs {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    List.Forall₂ ExprLvEq e₁.getAppArgs e₂.getAppArgs := by
  induction h with
  | app _ ha ihf _ =>
    simp only [Expr.getAppArgs]
    exact forall₂_append_pr ihf (.cons ha .nil)
  | bvar | fvar | sort | const | lam | forallE | letE | lit | proj =>
    exact .nil

private theorem lamsAlong_congr_exprLvEq {elim : KLevel} :
    ∀ {n : Nat} {l₁ l₂ p₁ p₂ r₁ : KExpr},
      LamsAlong elim n l₁ p₁ r₁ → ExprLvEq l₁ l₂ → ExprLvEq p₁ p₂ →
      ∃ r₂, LamsAlong elim n l₂ p₂ r₂ ∧ ExprLvEq r₁ r₂
  | 0, _, _, _, _, _, .zero, hl, _ => ⟨_, .zero, hl⟩
  | _ + 1, _, _, _, _, _, .succ hpw hdl hrest, hl, hp => by
    cases hl with
    | lam hdl' hbl' =>
      cases hp with
      | forallE hdp' hbp' =>
        obtain ⟨r₂, hrest', hr⟩ := lamsAlong_congr_exprLvEq hrest hbl' hbp'
        exact ⟨r₂, .succ hpw ((hdl'.symm.trans hdl).trans hdp') hrest', hr⟩

private theorem exprLvEq_liftLooseBVars_pr {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    ∀ (n c : Nat), ExprLvEq (e₁.liftLooseBVars n c) (e₂.liftLooseBVars n c) := by
  induction h with
  | bvar => intro n c; simp only [Expr.liftLooseBVars]; split <;> exact .bvar
  | fvar ht _ => intro _ _; exact .fvar ht
  | sort hu => intro _ _; exact .sort hu
  | const hus => intro _ _; exact .const hus
  | app _ _ ihf iha => intro n c; exact .app (ihf n c) (iha n c)
  | lam _ _ iht ihb => intro n c; exact .lam (iht n c) (ihb n (c + 1))
  | forallE _ _ iht ihb => intro n c; exact .forallE (iht n c) (ihb n (c + 1))
  | letE _ _ _ iht ihv ihb => intro n c; exact .letE (iht n c) (ihv n c) (ihb n (c + 1))
  | lit => intro _ _; exact .lit
  | proj _ ihe => intro n c; exact .proj (ihe n c)

private theorem ruleFollows_congr_exprLvEq {ty₁ ty₂ rhs₁ rhs₂ cb : KExpr}
    {nP nMot nMin minor nf : Nat} {elim : KLevel}
    (h : RuleFollows ty₁ nP nMot nMin minor nf elim rhs₁ cb)
    (hty : ExprLvEq ty₁ ty₂) (hrhs : ExprLvEq rhs₁ rhs₂) :
    RuleFollows ty₂ nP nMot nMin minor nf elim rhs₂ cb := by
  obtain ⟨after₁, mdom₁, rest₁, sb₁, mm₁, hlam1, hpeel, hlam2, hsb⟩ := h
  obtain ⟨after₂, hlam1', hafter⟩ := lamsAlong_congr_exprLvEq hlam1 hrhs hty
  obtain ⟨r₂, hpeel', hr₂⟩ := exprLvEq_peelForalls (nP + nMot + minor) hty hpeel
  cases hr₂ with
  | forallE hmdom _ =>
    obtain ⟨sb₂, hlam2', hsb'⟩ := lamsAlong_congr_exprLvEq hlam2 hafter
      (exprLvEq_liftLooseBVars_pr hmdom (nMin - minor) 0)
    exact ⟨after₂, _, _, sb₂, _, hlam1', hpeel', hlam2', hsb'.symm.trans hsb⟩

private theorem wrapAt_mono {t : Ix.Kernel.RoleTable} {E E' : Ixon.Env}
    (hR : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hB : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {w : KKey} {x : Option Nat} (h : wrapAt t E w = some x) : wrapAt t E' w = some x := by
  unfold wrapAt at h ⊢
  cases hk : keyAddr t w with
  | none => simp only [hk] at h ⊢; exact h
  | some a =>
    simp only [hk] at h ⊢
    cases hd : Binding.FamilyRecon.defnAt t E a with
    | none => simp [hd] at h
    | some y =>
      rw [Binding.FamilyRecon.defnAt_mono (Ok := fun _ => True)
        (fun a c _ hc => hR a c hc) (fun _ _ _ _ => trivial) hB trivial hd]
      rw [hd] at h
      exact h

private theorem wrapAt_iprj {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (hc : recordOf E a = some c) (hi : c.info = .iPrj p) :
    wrapAt t E (keyOf t a) = some none := by
  unfold wrapAt
  rw [Binding.FamilyFlat.keyAddr_keyOf hwf a]
  simp only [Binding.FamilyRecon.defnAt, hc, hi]

private theorem consumes_eq_self_of_iprj {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (hc : recordOf E a = some c) (hi : c.info = .iPrj p)
    {d d' : KExpr} {us : List KLevel}
    (hfn : d.getAppFn = .const (keyOf t a) us)
    (hcs : Consumes (wrapAt t E) d d') : d' = d := by
  cases hcs with
  | refl => rfl
  | step hstep _ =>
    rename_i mid _
    unfold consumeAt Binding.FamilyRecon.consumeOf Binding.FamilyRecon.appHead at hstep
    rw [hfn] at hstep
    cases hargs : d.getAppArgs with
    | nil => simp [hargs] at hstep
    | cons _ _ =>
      rw [hargs] at hstep
      dsimp only at hstep
      rw [wrapAt_iprj hwf hc hi] at hstep
      simp at hstep

private theorem peelForalls_max_eq_of_exprLvEq :
    ∀ {n₁ n₂ : Nat} {e₁ e₂ c₁ c₂ : KExpr},
      ExprLvEq e₁ e₂ →
      peelForalls n₁ e₁ = some c₁ → (∀ d b m, c₁ ≠ .forallE d b m) →
      peelForalls n₂ e₂ = some c₂ → (∀ d b m, c₂ ≠ .forallE d b m) →
      n₁ = n₂
  | 0, 0, _, _, _, _, _, _, _, _, _ => rfl
  | 0, _ + 1, _, _, _, _, h, h1, hnc1, h2, _ => by
    simp only [peelForalls, Option.some.injEq] at h1; subst h1
    cases h with
    | forallE _ _ => exact absurd rfl (hnc1 _ _ _)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [peelForalls] at h2
  | _ + 1, 0, _, _, _, _, h, h1, _, h2, hnc2 => by
    simp only [peelForalls, Option.some.injEq] at h2; subst h2
    cases h with
    | forallE _ _ => exact absurd rfl (hnc2 _ _ _)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [peelForalls] at h1
  | _ + 1, _ + 1, _, _, _, _, h, h1, hnc1, h2, hnc2 => by
    cases h with
    | forallE _ hb =>
      exact congrArg Nat.succ (peelForalls_max_eq_of_exprLvEq hb h1 hnc1 h2 hnc2)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [peelForalls] at h1

private theorem exprLvEq_bvar_eq {i : Nat} {e : KExpr} (h : ExprLvEq (.bvar i) e) : e = .bvar i := by
  cases h; rfl

private theorem wrapForalls_peelForalls (body : KExpr) (elim : KLevel) :
    ∀ (doms : List KExpr), peelForalls doms.length (wrapForalls body doms elim) = some body
  | [] => rfl
  | _ :: ds => wrapForalls_peelForalls body elim ds

private theorem peelForalls_add :
    ∀ (a b : Nat) (e : KExpr),
      peelForalls (a + b) e = (peelForalls a e).bind (peelForalls b)
  | 0, b, e => by simp [peelForalls]
  | a + 1, b, .forallE _ body _ => by
    rw [Nat.add_right_comm]
    exact peelForalls_add a b body
  | a + 1, b, .bvar _ | a + 1, b, .fvar _ _ | a + 1, b, .sort _ | a + 1, b, .const _ _
  | a + 1, b, .app _ _ | a + 1, b, .lam _ _ _ | a + 1, b, .letE _ _ _ _ | a + 1, b, .lit _
  | a + 1, b, .proj _ _ _ => by
    rw [Nat.add_right_comm]; rfl

private theorem collectDoms_length_le {V : ReconView} {f : Nat} :
    ∀ (n : Nat) (ty : KExpr) (doms : List KExpr) (rest : KExpr),
      Binding.FamilyRecon.collectDoms V f n ty = some (doms, rest) → doms.length ≤ n
  | 0, _, doms, _, h => by
    simp only [Binding.FamilyRecon.collectDoms, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact Nat.le_refl 0
  | n + 1, ty, doms, rest, h => by
    simp only [Binding.FamilyRecon.collectDoms] at h
    cases hb : Binding.FamilyRecon.binderOf V f ty with
    | none => rw [hb] at h; cases h
    | some opt =>
      rw [hb] at h
      cases opt with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Nat.zero_le _
      | some triple =>
        obtain ⟨d, b, m⟩ := triple
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨ds, r⟩, hrec, hpair⟩ := h
        injection hpair with hdoms _
        subst hdoms
        have hle := collectDoms_length_le n b ds r hrec
        simp only [List.length_cons]; omega

private theorem allMotives_length {V : ReconView} {f : Nat} {elim : KLevel} {nrp : Nat} :
    ∀ (es : List FlatEntry) (j : Nat) (ms : List KExpr),
      Binding.FamilyRecon.allMotives V f elim nrp es j = some ms → ms.length = es.length
  | [], _, ms, h => by
    simp only [Binding.FamilyRecon.allMotives, Option.some.injEq] at h; rw [← h]; rfl
  | e :: rest, j, ms, h => by
    simp only [Binding.FamilyRecon.allMotives] at h
    cases hi : V.ind e.addr with
    | none => rw [hi] at h; cases h
    | some opt =>
      rw [hi] at h
      cases opt with
      | none => cases h
      | some ind =>
        dsimp only at h
        cases hm : Binding.FamilyRecon.motiveType V f e.addr ind.ty ind.np ind.ni e.levels elim nrp
            e.aux e.params with
        | none => rw [hm] at h; cases h
        | some mt =>
          rw [hm] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ms', hrec, rfl⟩ := h
          simp [allMotives_length rest (j + 1) ms' hrec]

private theorem liftIndices_length (doms : List KExpr) (shift : Nat) :
    (liftIndices doms shift).length = doms.length := by
  simp [liftIndices]

private theorem appSpine_getAppArgs :
    ∀ (args : List KExpr) (head : KExpr),
      (appSpine head args).getAppArgs = head.getAppArgs ++ args
  | [], head => by simp [appSpine]
  | a :: rest, head => by
    simp only [appSpine, List.foldl_cons]
    have ih := appSpine_getAppArgs rest (.app head a)
    simp only [appSpine, Expr.getAppArgs, List.append_assoc, List.singleton_append] at ih
    exact ih

private theorem appSpine_getAppFn :
    ∀ (args : List KExpr) (head : KExpr),
      (appSpine head args).getAppFn = head.getAppFn
  | [], _ => rfl
  | a :: rest, head => by
    simp only [appSpine, List.foldl_cons]
    have ih := appSpine_getAppFn rest (.app head a)
    simp only [appSpine, Expr.getAppFn] at ih
    exact ih

private theorem appBVarsDec_getAppArgs (n : Nat) (head : KExpr) (top : Nat) :
    (appBVarsDec head n top).getAppArgs =
      head.getAppArgs ++ (List.range n).map (fun i => .bvar (top - i)) :=
  appSpine_getAppArgs _ head

private theorem appBVarsDec_getAppFn (n : Nat) (head : KExpr) (top : Nat) :
    (appBVarsDec head n top).getAppFn = head.getAppFn :=
  appSpine_getAppFn _ head

private theorem appBVarsDown_getAppArgs (n : Nat) (head : KExpr) :
    (appBVarsDown head n).getAppArgs =
      head.getAppArgs ++ (List.range n).map (fun i => .bvar (n - 1 - i)) :=
  appSpine_getAppArgs _ head

private theorem appBVarsDown_getAppFn (n : Nat) (head : KExpr) :
    (appBVarsDown head n).getAppFn = head.getAppFn :=
  appSpine_getAppFn _ head

private theorem specParamsLifted_getAppArgs (shift : Nat) (sp : List KExpr) (head : KExpr) :
    (specParamsLifted head sp shift).getAppArgs =
      head.getAppArgs ++ sp.map (fun p => p.liftLooseBVars shift 0) :=
  appSpine_getAppArgs _ head

private theorem specParamsLifted_getAppFn (shift : Nat) (sp : List KExpr) (head : KExpr) :
    (specParamsLifted head sp shift).getAppFn = head.getAppFn :=
  appSpine_getAppFn _ head

/-- **Major-premise structure of `recTypeAt`**: unpacks the exact leading-binder count `depthR`,
minor count `nMin`, major-premise domain `domR`, and non-`forallE` conclusion of `recTypeAt`. -/
private theorem recTypeAt_majorDom_info {V : ReconView} {fuel : Nat} {es : List FlatEntry}
    {off nP k : Nat} {R : KExpr} {ek : FlatEntry} {self : IndData}
    (hR : recTypeAt V fuel es off nP k = some R)
    (hek : es[k]? = some ek) (hself : V.ind ek.addr = some (some self)) :
    ∃ (depthR nMin : Nat) (domR concl : KExpr) (mR : Ix.Kernel.BinderMeta),
      depthR ≤ nP + es.length + nMin + self.ni ∧
      peelForalls depthR R = some (.forallE domR concl mR) ∧
      (∀ d b m, concl ≠ .forallE d b m) ∧
      domR.getAppFn = .const (V.key ek.addr) ek.levels ∧
      (ek.aux = false →
        domR.getAppArgs.length = nP + self.ni ∧
        ∀ a ∈ domR.getAppArgs, ∃ i, a = .bvar i) ∧
      (ek.aux = true →
        domR.getAppArgs.length = ek.params.length + self.ni ∧
        domR.getAppArgs.drop ek.params.length =
          (List.range self.ni).map (fun i => .bvar (self.ni - 1 - i)) ∧
        ∀ P ∈ domR.getAppArgs.take ek.params.length,
          hasBVarIn 0 (es.length + nMin + self.ni) P = false) := by
  unfold recTypeAt at hR
  cases h0 : es[0]? with
  | none => simp [h0] at hR
  | some e0 =>
    simp only [h0, hek] at hR
    cases hp : V.ind e0.addr with
    | none => simp [hp] at hR
    | some po =>
      cases po with
      | none => simp [hp] at hR
      | some prim =>
        simp only [hp, hself] at hR
        cases hc1 : Binding.FamilyRecon.collectDoms V fuel nP
            (Binding.FamilyFlat.exprInstLevels
              ((List.range prim.nl).map fun i => Level.param (off + i)) prim.ty) with
        | none => simp [hc1] at hR
        | some pDoms =>
          obtain ⟨paramDoms, _⟩ := pDoms
          simp only [hc1] at hR
          cases hmot : Binding.FamilyRecon.allMotives V fuel (elimLevel off) nP es 0 with
          | none => simp [hmot] at hR
          | some motDoms =>
            cases hfop : Binding.FamilyRecon.flatOwnParams V es with
            | none => simp [hmot, hfop] at hR
            | some fop =>
              simp only [hmot, hfop] at hR
              cases hmin : Binding.FamilyRecon.allMinors V fuel es fop nP es.length nP
                  (elimLevel off) es 0 0 with
              | none => simp [hmin] at hR
              | some minDoms =>
                simp only [hmin] at hR
                cases hsa : Binding.FamilyRecon.peelMotiveParams nP ek.aux ek.params self.np 0
                    (Binding.FamilyFlat.exprInstLevels ek.levels self.ty) with
                | none => simp [hsa] at hR
                | some selfAfter =>
                  simp only [hsa] at hR
                  cases hci : Binding.FamilyRecon.collectDoms V fuel self.ni selfAfter with
                  | none => simp [hci] at hR
                  | some iDoms =>
                    obtain ⟨idxRaw, _⟩ := iDoms
                    simp only [hci, Option.some.injEq] at hR
                    subst hR
                    have hp_le := collectDoms_length_le nP _ paramDoms _ hc1
                    have hm_eq := allMotives_length es 0 motDoms hmot
                    have hi_le := collectDoms_length_le self.ni _ idxRaw _ hci
                    let depthR := paramDoms.length + motDoms.length + minDoms.length + idxRaw.length
                    let pre := nP + es.length + minDoms.length + self.ni
                    let head : KExpr := .const (V.key ek.addr) ek.levels
                    let withArgs := if ek.aux then specParamsLifted head ek.params
                      (es.length + minDoms.length + self.ni) else appBVarsDec head nP (pre - 1)
                    let domR := appBVarsDown withArgs self.ni
                    let concl : KExpr :=
                      .app (Binding.FamilyRecon.conclIndices (.bvar (pre - (nP + k))) self.ni) (.bvar 0)
                    have hpeel : peelForalls depthR
                        (wrapForalls (wrapForalls (wrapForalls (wrapForalls
                          (.forallE domR concl (Core.bmeta (elimLevel off)))
                          (liftIndices idxRaw (es.length + minDoms.length)) (elimLevel off))
                          minDoms (elimLevel off)) motDoms (elimLevel off)) paramDoms (elimLevel off)) =
                        some (.forallE domR concl (Core.bmeta (elimLevel off))) := by
                      dsimp only [depthR]
                      rw [peelForalls_add, peelForalls_add, peelForalls_add,
                        wrapForalls_peelForalls]
                      simp only [Option.bind_some]
                      rw [wrapForalls_peelForalls]
                      simp only [Option.bind_some]
                      rw [wrapForalls_peelForalls]
                      simp only [Option.bind_some]
                      have hli : idxRaw.length =
                          (liftIndices idxRaw (es.length + minDoms.length)).length :=
                        (liftIndices_length _ _).symm
                      rw [hli, wrapForalls_peelForalls]
                    refine ⟨depthR, minDoms.length, domR, concl, Core.bmeta (elimLevel off),
                      (by omega), hpeel, (fun d b m h => by simp [concl] at h), ?_, ?_, ?_⟩
                    · dsimp only [domR, withArgs, head]
                      rw [appBVarsDown_getAppFn]
                      cases ek.aux
                      · simp [appBVarsDec_getAppFn, Expr.getAppFn]
                      · simp [specParamsLifted_getAppFn, Expr.getAppFn]
                    · intro haux
                      have hwa : withArgs = appBVarsDec head nP (pre - 1) := by
                        simp [withArgs, haux]
                      have hargs : domR.getAppArgs =
                          (List.range nP).map (fun i => .bvar (pre - 1 - i)) ++
                          (List.range self.ni).map (fun i => .bvar (self.ni - 1 - i)) := by
                        simp [domR, hwa, appBVarsDown_getAppArgs, appBVarsDec_getAppArgs, head,
                          Expr.getAppArgs]
                      refine ⟨by simp [hargs], fun a ha => ?_⟩
                      rw [hargs, List.mem_append] at ha
                      rcases ha with ha | ha
                      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; exact ⟨_, rfl⟩
                      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; exact ⟨_, rfl⟩
                    · intro haux
                      have hwa : withArgs = specParamsLifted head ek.params
                          (es.length + minDoms.length + self.ni) := by
                        simp [withArgs, haux]
                      have hargs : domR.getAppArgs =
                          ek.params.map (fun p => p.liftLooseBVars (es.length + minDoms.length + self.ni) 0) ++
                          (List.range self.ni).map (fun i => .bvar (self.ni - 1 - i)) := by
                        simp [domR, hwa, appBVarsDown_getAppArgs, specParamsLifted_getAppArgs, head,
                          Expr.getAppArgs]
                      have hlen_l : ek.params.length = (ek.params.map (fun p =>
                          p.liftLooseBVars (es.length + minDoms.length + self.ni) 0)).length :=
                        (List.length_map ..).symm
                      refine ⟨by simp [hargs], ?_, ?_⟩
                      · rw [hargs, hlen_l, List.drop_left]
                      · rw [hargs, hlen_l, List.take_left]
                        intro P hP
                        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hP
                        simpa using hasBVarIn_liftLooseBVars_false p
                          (es.length + minDoms.length + self.ni) 0

private theorem forall₂_getElem?_eq_of_bvar {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {l₁ l₂ : List KExpr} (h : List.Forall₂ (WrapConsObs W ObsW) l₁ l₂)
    (hb : ∀ a ∈ l₁, ∃ i, a = .bvar i) : l₂ = l₁ := by
  induction h with
  | nil => rfl
  | cons hd _ ih =>
    obtain ⟨i, rfl⟩ := hb _ List.mem_cons_self
    rw [WrapConsObs.bvar_eq hd, ih fun a ha => hb a (List.mem_cons_of_mem _ ha)]

private theorem forall₂_exprLvEq_eq_of_bvar {l₁ l₂ : List KExpr}
    (h : List.Forall₂ ExprLvEq l₁ l₂) (hb : ∀ a ∈ l₁, ∃ i, a = .bvar i) : l₂ = l₁ := by
  induction h with
  | nil => rfl
  | cons hd _ ih =>
    obtain ⟨i, rfl⟩ := hb _ List.mem_cons_self
    rw [exprLvEq_bvar_eq hd, ih fun a ha => hb a (List.mem_cons_of_mem _ ha)]

private theorem forall₂_drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.drop n) (l₂.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ ht => forall₂_drop n ht

private theorem wrapConsObs_eq_args_of_bvars {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {d₁ d₂ : KExpr}
    (h : WrapConsObs W ObsW d₁ d₂) (hb : ∀ a ∈ d₁.getAppArgs, ∃ i, a = .bvar i) :
    d₂.getAppArgs = d₁.getAppArgs :=
  forall₂_getElem?_eq_of_bvar (WrapConsObs.getAppArgs h) hb

private theorem exprLvEq_eq_args_of_bvars {d₁ d₂ : KExpr} (h : ExprLvEq d₁ d₂)
    (hb : ∀ a ∈ d₁.getAppArgs, ∃ i, a = .bvar i) : d₂.getAppArgs = d₁.getAppArgs :=
  forall₂_exprLvEq_eq_of_bvar (exprLvEq_getAppArgs h) hb

private theorem wrapConsObs_drop_eq_of_bvars {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {d₁ d₂ : KExpr}
    {n : Nat} (h : WrapConsObs W ObsW d₁ d₂) (hb : ∀ a ∈ d₁.getAppArgs.drop n, ∃ i, a = .bvar i) :
    d₂.getAppArgs.drop n = d₁.getAppArgs.drop n :=
  forall₂_getElem?_eq_of_bvar (forall₂_drop n (WrapConsObs.getAppArgs h)) hb

private theorem exprLvEq_drop_eq_of_bvars {d₁ d₂ : KExpr} {n : Nat} (h : ExprLvEq d₁ d₂)
    (hb : ∀ a ∈ d₁.getAppArgs.drop n, ∃ i, a = .bvar i) :
    d₂.getAppArgs.drop n = d₁.getAppArgs.drop n :=
  forall₂_exprLvEq_eq_of_bvar (forall₂_drop n (exprLvEq_getAppArgs h)) hb

private theorem exprLvEq_of_wrapConsObs_or_eq_dom {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {E_rec : Ixon.Env} {ObsW : KKey → Nat → Prop}
    {a : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductiveProj}
    (hc : recordOf E_rec a = some c) (hi : c.info = .iPrj p)
    {mI : Nat} {R ty dR dT : KExpr} {us : List KLevel}
    (hR : binderDomAfter mI R = some dR) (hT : binderDomAfter mI ty = some dT)
    (hfn : dR.getAppFn = .const (keyOf t a) us)
    (hrel : ExprLvEq ty R ∨ WrapConsObs (wrapAt t E_rec) ObsW R ty) :
    ExprLvEq dR dT ∨ WrapConsObs (wrapAt t E_rec) ObsW dR dT := by
  rcases hrel with hlv | hwc
  · obtain ⟨dR', hR', hd⟩ := exprLvEq_binderDomAfter hlv hT
    have heq : dR' = dR := Option.some.inj (hR'.symm.trans hR)
    subst heq
    exact Or.inl hd.symm
  · unfold binderDomAfter at hR hT
    cases hpR : peelForalls mI R with
    | none => simp [hpR] at hR
    | some rR =>
      rw [hpR] at hR
      cases rR with
      | forallE domR bR mR =>
        simp only [Option.some.injEq] at hR; subst hR
        obtain ⟨rT, hpT, hr⟩ := WrapConsObs.peelForalls mI hwc hpR
        rw [hpT] at hT
        cases hr with
        | forallE _ hcs hwc_dom _ =>
          simp only [Option.some.injEq] at hT; subst hT
          have hcm : _ = domR := consumes_eq_self_of_iprj hwf hc hi hfn hcs.toConsumes
          rw [hcm] at hwc_dom
          exact Or.inr hwc_dom
      | _ => simp at hR

private theorem recAddrs_getElem? {rb : _root_.Address} {rs : Array Ixon.MutConst} {j : Nat}
    {m : Ixon.MutConst} (hj : rs[j]? = some m) :
    (recAddrs rb rs)[j]? = some (memberAddr rb j m) := by
  unfold recAddrs
  rw [List.getElem?_map, List.getElem?_zipIdx]
  have h1 : rs.toList[j]? = some m := by rwa [Array.getElem?_toList]
  rw [h1]
  simp

private theorem recAddrs_length (rb : _root_.Address) (rs : Array Ixon.MutConst) :
    (recAddrs rb rs).length = rs.size := by
  simp [recAddrs]

private theorem ruleReads_ctor_eq {t : Ix.Kernel.RoleTable}
    {rd : Ix.Kernel.Reader.MemberReader .anon} {im : Nat}
    {B_m : _root_.Address} :
    ∀ {j : Nat} {rus : List Ixon.RecursorRule} {rls : List (RecRule .anon)},
      List.Forall₂ (RuleReads t rd B_m im) (rus.zipIdx j) rls →
      ∀ (c : Nat) (rl : RecRule .anon), rls[c]? = some rl →
        rl.ctor = keyOf t (ctorAddr B_m im (j + c))
  | _, [], _, h, _, _, hget => by
    cases h; simp at hget
  | j, _ :: rus, _, h, c, rl, hget => by
    cases h with
    | cons hhd htl =>
      obtain ⟨rhs, -, hrl⟩ := hhd
      cases c with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget; rw [hrl]; simp
      | succ c' =>
        simp only [List.getElem?_cons_succ] at hget
        have ih := ruleReads_ctor_eq htl c' rl hget
        have hadd : j + 1 + c' = j + (c' + 1) := by omega
        rwa [hadd] at ih

theorem memberRecon_grow {TyRel : KExpr → KExpr → Prop} {t : Ix.Kernel.RoleTable}
    {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {es : List FlatEntry}
    {off fuel k : Nat} {r : Ixon.Recursor}
    (h : MemberRecon TyRel t E rb crb rs es off fuel k r) :
    MemberRecon TyRel t E' rb crb rs es off fuel k r :=
  Binding.FamilyRecon.memberRecon_transport
    (Binding.FamilyRecon.reconOfStore_le hle hblob)
    (Binding.FamilyRecon.ReconView.closedOn_true _)
    hblob (fun _ _ => ⟨trivial, fun _ _ _ _ _ _ => trivial⟩) h

theorem recordWrapConsObs_grow {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E E' : Ixon.Env}
    (hle : ∀ y c, recordOf E y = some c → recordOf E' y = some c)
    (hblob : ∀ y b, E.blobs.get? y = some b → E'.blobs.get? y = some b)
    {B rb : _root_.Address} (h : RecordWrapConsObs calls t E B rb) :
    RecordWrapConsObs calls t E' B rb := by
  obtain ⟨crb, rs, es, off, fuel, hrb, hrs, hRF, hBD, hM⟩ := h
  refine ⟨crb, rs, es, off, fuel, hle _ _ hrb, hrs, hRF.of_blobs hblob,
    Binding.FamilyFlat.blockDerivedFlat_grow hle hblob hBD, fun k r hr => ?_⟩
  obtain ⟨htot, hMR⟩ := hM k r hr
  obtain ⟨ty, R, bodies, cbk, hty, hR, hrel, hb, hcb, hrules⟩ :=
    memberRecon_grow hle hblob hMR
  exact ⟨Binding.FamilyRecon.ctorsBefore_leOn (Binding.FamilyRecon.reconOfStore_le hle hblob)
      es es.length r.minors.toNat (fun _ _ => ⟨trivial, fun _ _ _ _ _ _ => trivial⟩) htot,
    ty, R, bodies, cbk, hty, hR,
    hrel.mono (fun w x hw => wrapAt_mono hle hblob hw) (fun _ _ h => h), hb, hcb, hrules⟩

private theorem eq_of_annotates_exprLvEq :
    ∀ {e₁ e₂ e₀ : KExpr}, Annotates e₁ e₀ → Annotates e₂ e₀ → ExprLvEq e₁ e₂ → e₁ = e₂
  | _, _, _, .bvar, .bvar, _ => rfl
  | _, _, _, .fvar h1, .fvar h2, .fvar hlv => by rw [eq_of_annotates_exprLvEq h1 h2 hlv]
  | _, _, _, .sort, .sort, _ => rfl
  | _, _, _, .const, .const, _ => rfl
  | _, _, _, .lit, .lit, _ => rfl
  | _, _, _, .app hf1 ha1, .app hf2 ha2, .app hlvf hlva => by
    rw [eq_of_annotates_exprLvEq hf1 hf2 hlvf, eq_of_annotates_exprLvEq ha1 ha2 hlva]
  | _, _, _, .lam ht1 hb1, .lam ht2 hb2, .lam hlvt hlvb => by
    rw [eq_of_annotates_exprLvEq ht1 ht2 hlvt, eq_of_annotates_exprLvEq hb1 hb2 hlvb]
  | _, _, _, .forallE ht1 hb1, .forallE ht2 hb2, .forallE hlvt hlvb => by
    rw [eq_of_annotates_exprLvEq ht1 ht2 hlvt, eq_of_annotates_exprLvEq hb1 hb2 hlvb]
  | _, _, _, .proj h1, .proj h2, .proj hlv => by rw [eq_of_annotates_exprLvEq h1 h2 hlv]
  | _, _, _, .letE h1, .letE h2, hlv => eq_of_annotates_exprLvEq h1 h2 hlv

private theorem liftLooseBVars_instantiateLevelParams_pr (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (n c : Nat),
      (e.liftLooseBVars n c).instantiateLevelParams ps us =
        (e.instantiateLevelParams ps us).liftLooseBVars n c
  | .bvar i, n, c => by simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_pr ps us f n c,
      liftLooseBVars_instantiateLevelParams_pr ps us a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_pr ps us t n c,
      liftLooseBVars_instantiateLevelParams_pr ps us b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_pr ps us t n c,
      liftLooseBVars_instantiateLevelParams_pr ps us b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_pr ps us t n c,
      liftLooseBVars_instantiateLevelParams_pr ps us v n c,
      liftLooseBVars_instantiateLevelParams_pr ps us b n (c + 1)]
  | .proj _ _ e, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_pr ps us e n c]

private theorem instantiate1Lift_instantiateLevelParams_pr (ps : List LevelParam) (us : List KLevel)
    (v : KExpr) :
    ∀ (b : KExpr) (d : Nat),
      (b.instantiate1Lift v d).instantiateLevelParams ps us =
        (b.instantiateLevelParams ps us).instantiate1Lift (v.instantiateLevelParams ps us) d
  | .bvar i, d => by
    simp only [Expr.instantiate1Lift, Expr.instantiateLevelParams]
    split
    · exact liftLooseBVars_instantiateLevelParams_pr ps us v d 0
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, d => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams_pr ps us v f d,
      instantiate1Lift_instantiateLevelParams_pr ps us v a d]
  | .lam t b _, d => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams_pr ps us v t d,
      instantiate1Lift_instantiateLevelParams_pr ps us v b (d + 1)]
  | .forallE t b _, d => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams_pr ps us v t d,
      instantiate1Lift_instantiateLevelParams_pr ps us v b (d + 1)]
  | .letE t w b _, d => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams_pr ps us v t d,
      instantiate1Lift_instantiateLevelParams_pr ps us v w d,
      instantiate1Lift_instantiateLevelParams_pr ps us v b (d + 1)]
  | .proj _ _ e, d => by
    simp [Expr.instantiate1Lift, Expr.instantiateLevelParams,
      instantiate1Lift_instantiateLevelParams_pr ps us v e d]

private theorem annotates_instantiateLevelParams_pr (ps : List LevelParam) (us : List KLevel)
    {a e : KExpr} (h : Annotates a e) :
    Annotates (a.instantiateLevelParams ps us) (e.instantiateLevelParams ps us) := by
  induction h with
  | bvar => exact .bvar
  | fvar _ ih => exact .fvar ih
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | proj _ ih => exact .proj ih
  | letE _ ih =>
    refine .letE ?_
    rwa [← instantiate1Lift_instantiateLevelParams_pr]

private theorem memberAddr_recr_eq (rb : _root_.Address) (i : Nat) (rc : Ixon.Recursor) :
    memberAddr rb i (.recr rc) = Core.rprjAddr rb i := rfl

private theorem memberAddr_indc_eq (B : _root_.Address) (i : Nat) (ind : Ixon.Inductive) :
    memberAddr B i (.indc ind) = Core.iprjAddr B i := rfl

private theorem list_getElem?_zip {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (i : Nat),
    (l₁.zip l₂)[i]? = match l₁[i]?, l₂[i]? with
      | some a, some b => some (a, b)
      | _, _ => none
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, 0 => rfl
  | _ :: l₁, _ :: l₂, i + 1 => by simpa using list_getElem?_zip l₁ l₂ i

private theorem ruleReads_det_pr {t : Ix.Kernel.RoleTable} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {B : _root_.Address} {i : Nat} :
    ∀ {xs : List (Ixon.RecursorRule × Nat)} {r₁ r₂ : List (RecRule .anon)},
      List.Forall₂ (RuleReads t mr B i) xs r₁ → List.Forall₂ (RuleReads t mr B i) xs r₂ →
      r₁ = r₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    obtain ⟨rhs₁, hr₁, e₁⟩ := h₁
    obtain ⟨rhs₂, hr₂, e₂⟩ := h₂
    rw [hr₁] at hr₂; cases hr₂; subst e₁ e₂
    rw [ruleReads_det_pr t₁ t₂]

private theorem reads_rprj_det_pr {t : Ix.Kernel.RoleTable}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {E₀ : Ixon.Env} {rb : _root_.Address} {k : Nat} {rc : Ixon.Recursor}
    {ci₁ ci₂ : ConstantInfo .anon}
    (hP : recordOf E₀ (Core.rprjAddr rb k) = some (memberProjection rb k (.recr rc)))
    (h1 : Reads t E₀ (Core.rprjAddr rb k) ci₁)
    (h2 : Reads t E₀ (Core.rprjAddr rb k) ci₂) : ci₁ = ci₂ := by
  obtain ⟨cb₁, ms₁, rc₁, hMA₁, hRR₁⟩ := reads_rprj hP rfl h1
  obtain ⟨cb₂, ms₂, rc₂, hMA₂, hRR₂⟩ := reads_rprj hP rfl h2
  obtain ⟨hcb₁, hms₁, hmem₁, -, -, -⟩ := hMA₁
  obtain ⟨hcb₂, hms₂, hmem₂, -, -, -⟩ := hMA₂
  have ecb : cb₁ = cb₂ := Option.some.inj (hcb₁.symm.trans hcb₂)
  subst ecb
  have ems : ms₁ = ms₂ := Ixon.ConstantInfo.muts.inj (hms₁.symm.trans hms₂)
  subst ems
  have erc : rc₁ = rc₂ := Ixon.MutConst.recr.inj (Option.some.inj (hmem₁.symm.trans hmem₂))
  subst erc
  obtain ⟨tyP₁, ty₁, kF₁, kM₁, Bf₁, Bm₁, iF₁, iM₁, indF₁, indM₁, ps₁, rls₁,
    htyP₁, hfamK₁, hindF₁, hmajK₁, hindM₁, hps₁, hty₁, -, hrr₁, hci₁⟩ := hRR₁
  obtain ⟨tyP₂, ty₂, kF₂, kM₂, Bf₂, Bm₂, iF₂, iM₂, indF₂, indM₂, ps₂, rls₂,
    htyP₂, hfamK₂, hindF₂, hmajK₂, hindM₂, hps₂, hty₂, -, hrr₂, hci₂⟩ := hRR₂
  have etyP : tyP₁ = tyP₂ := Except.ok.inj (htyP₁.symm.trans htyP₂)
  subst etyP
  have ekF : kF₁ = kF₂ := Option.some.inj (hfamK₁.symm.trans hfamK₂)
  subst ekF
  have ekM : kM₁ = kM₂ := Option.some.inj (hmajK₁.symm.trans hmajK₂)
  subst ekM
  have hindF_eq : indF₁ = indF₂ := by
    obtain ⟨a1, c1, p1, cb1, ms1, hk1, hr1, hi1, hb1, hix1, hcb1, hm1, hg1, -, -, -⟩ := hindF₁
    obtain ⟨a2, c2, p2, cb2, ms2, hk2, hr2, hi2, hb2, hix2, hcb2, hm2, hg2, -, -, -⟩ := hindF₂
    have ea : a1 = a2 := keyOf_inj hroles (hk1.symm.trans hk2)
    subst ea
    have ec : c1 = c2 := Option.some.inj (hr1.symm.trans hr2)
    subst ec
    have ep : p1 = p2 := Ixon.ConstantInfo.iPrj.inj (hi1.symm.trans hi2)
    subst ep
    have hcb1' : recordOf E₀ p1.block = some cb1 := by rwa [hb1] at hcb1
    have hcb2' : recordOf E₀ p1.block = some cb2 := by rwa [hb2] at hcb2
    have ecb : cb1 = cb2 := Option.some.inj (hcb1'.symm.trans hcb2')
    subst ecb
    have ems : ms1 = ms2 := Ixon.ConstantInfo.muts.inj (hm1.symm.trans hm2)
    subst ems
    rw [hix1] at hg1; rw [hix2] at hg2
    exact Ixon.MutConst.indc.inj (Option.some.inj (hg1.symm.trans hg2))
  subst hindF_eq
  have hindM_eq : Bm₁ = Bm₂ ∧ iM₁ = iM₂ := by
    obtain ⟨a1, c1, p1, _, _, hk1, hr1, hi1, hb1, hix1, -, -, -, -, -, -⟩ := hindM₁
    obtain ⟨a2, c2, p2, _, _, hk2, hr2, hi2, hb2, hix2, -, -, -, -, -, -⟩ := hindM₂
    have ea : a1 = a2 := keyOf_inj hroles (hk1.symm.trans hk2)
    subst ea
    have ec : c1 = c2 := Option.some.inj (hr1.symm.trans hr2)
    subst ec
    have ep : p1 = p2 := Ixon.ConstantInfo.iPrj.inj (hi1.symm.trans hi2)
    subst ep
    exact ⟨hb1.trans hb2.symm, hix1.trans hix2.symm⟩
  obtain ⟨rfl, rfl⟩ := hindM_eq
  have eps : ps₁ = ps₂ := hps₁.trans hps₂.symm
  subst eps
  have ety : ty₁ = ty₂ := Except.ok.inj (hty₁.symm.trans hty₂)
  subst ety
  have erls : rls₁ = rls₂ := ruleReads_det_pr hrr₁ hrr₂
  subst erls
  exact hci₁.trans hci₂.symm

private theorem majorKey_of_annotates_pr {rc : Ixon.Recursor} {e₁ e₂ : KExpr} {k : KKey}
    (h : majorKey rc e₂ = some k) (ha : Annotates e₁ e₂) : majorKey rc e₁ = some k := by
  unfold majorKey binderDom headKey at h ⊢
  have hstrip : ∀ (n : Nat) {a b : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {dom body : KExpr} {m : Ix.Kernel.BinderMeta},
      Annotates a b → b.stripPis n = some (bs, .forallE dom body m) →
      ∃ bs' dom' body' m', a.stripPis n = some (bs', .forallE dom' body' m') ∧
        Annotates dom' dom := by
    intro n
    induction n with
    | zero =>
      intro a b bs dom body m ha hs
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      cases ha with
      | forallE hd _ => exact ⟨[], _, _, _, rfl, hd⟩
    | succ n ih =>
      intro a b bs dom body m ha hs
      obtain ⟨d, bd, md, bs0, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv hs
      cases ha with
      | forallE _ hb =>
        obtain ⟨bs', dom', body', m', hs', hd⟩ := ih hb hs0
        exact ⟨_, dom', body', m', Ix.Kernel.Semantics.stripPis_succ_forallE hs', hd⟩
  have hhead : ∀ {a b : KExpr} {k : KKey} {us : List KLevel},
      Annotates a b → b.getAppFn = .const k us → a.getAppFn = .const k us := by
    intro a b k us ha
    induction ha with
    | app hf _ ihf _ => exact ihf
    | const => intro h; exact h
    | bvar | fvar | sort | lam | forallE | letE | lit | proj =>
      intro h; simp [Expr.getAppFn] at h
  cases hs : e₂.stripPis (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) with
  | none => rw [hs] at h; cases h
  | some p =>
    rw [hs] at h
    rcases p with ⟨bs_p, r_p⟩
    cases r_p with
    | forallE dom body m =>
      obtain ⟨bs', dom', body', m', hs', hd⟩ := hstrip _ ha hs
      rw [hs']
      simp only [Option.bind_some] at h ⊢
      cases hfn : dom.getAppFn with
      | const k' us =>
        rw [hfn] at h
        rw [hhead hd hfn]
        exact h
      | _ => rw [hfn] at h; cases h
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ =>
      simp only [Option.bind_some] at h
      cases h

/-! ## Unified canonical-member view -/

/-- **What the twin step needs of canonical recursor member `k`** of `rb` (`crb`, members `rs`) in
environment `env` over the common reconstruction store `E_rec`:
the stored recursor `(cvC, mI, rP, rulesC)` with its `RecReads` reading, canonical loaded
expressions matching `loadedAt` in `E_rec`, self-reference exclusion,
non-`forallE` motive conclusion, header counts, and `MemberRecon` (in `RFormS` or
`WrapConsObs`, with the optional `hasBVarIn` pin bound needed in the `WrapConsObs` case). -/
structure CanonMemberAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E_rec : Ixon.Env)
    (env : Ix.Kernel.Env .anon) (B rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) (es : List FlatEntry) (off fuel : Nat)
    (ind₀ : Ixon.Inductive) (k : Nat) : Type where
  rc : Ixon.Recursor
  hmem : rs[k]? = some (.recr rc)
  cvC : ConstantVal .anon
  mI : Nat
  rP : Nat
  rulesC : List (RecRule .anon)
  cvC₀ : ConstantVal .anon
  rulesC₀ : List (RecRule .anon)
  hfind : env.find? (keyOf t (Core.rprjAddr rb k)) = some (.recInfo cvC mI rP rulesC)
  hstored : StoredAs (.recInfo cvC mI rP rulesC) (.recInfo cvC₀ mI rP rulesC₀)
  hrecReads : RecReads t (recordOf E_rec) (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs)
    (keyOf t (Core.rprjAddr rb k)) rc (.recInfo cvC₀ mI rP rulesC₀)
  hcvC_name : cvC.name = keyOf t (Core.rprjAddr rb k)
  hcvC_lps : cvC.levelParams =
    Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind₀.lvls.toNat + 1))
      (List.range ind₀.lvls.toNat)
  hlvls_eq : rc.lvls.toNat = ind₀.lvls.toNat + off
  hrnp : rc.params.toNat = ind₀.params.toNat
  hnmot : rc.motives.toNat = rs.size
  hmI_def : mI = rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat
  hrP_def : rP = rc.params.toNat + rc.motives.toNat + rc.minors.toNat
  hnoSelf : ∀ j < rs.size, cvC.type.mentionsConst (keyOf t (Core.rprjAddr rb j)) = false
  hmotiveConcl : ∃ bs concl,
    (Core.posOf cvC.levelParams cvC.type).stripPis (mI + 1) = some (bs, concl) ∧
    ∀ d b m, concl ≠ .forallE d b m
  ty_ld : KExpr
  R : KExpr
  bodies : List KExpr
  cbk : Nat
  hty_ld : loadedAt t (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
    (mutsRoot rs k) rc.typ = some ty_ld
  hty_pos : Core.posOf cvC.levelParams cvC.type = ty_ld
  hR : recTypeAt (ReconView.ofStore t E_rec) fuel es off rc.params.toNat k = some R
  hbodies : ruleBodiesAt (ReconView.ofStore t E_rec) fuel es off rc.params.toNat rc.motives.toNat
    rc.minors.toNat rc.lvls.toNat k (recAddrs rb rs) = some bodies
  hcbk : ctorsBefore (ReconView.ofStore t E_rec) es k = some cbk
  hrules_len : rulesC.length = rc.rules.size
  hrules_rec : ∀ (c : Nat) (ru : Ixon.RecursorRule) (rC : RecRule .anon),
    rc.rules[c]? = some ru → rulesC[c]? = some rC →
    ∃ rhs_ld cb,
      loadedAt t (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
        (mutsRoot rs k + 1 + ((c : Nat) : F)) ru.rhs = some rhs_ld ∧
      ExprLvEq (Core.posOf cvC.levelParams rC.rhs) rhs_ld ∧
      bodies[c]? = some cb ∧
      RuleFollows ty_ld rc.params.toNat rc.motives.toNat rc.minors.toNat
        (cbk + c) ru.fields.toNat (elimLevel off) rhs_ld cb
  hty_rel : ExprLvEq ty_ld R ∨
    (WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty_ld ∧
      letFree ty_ld = true ∧
      ctorsBefore (ReconView.ofStore t E_rec) es es.length = some rc.minors.toNat ∧
      ∀ (dC : KExpr) (n : Nat), binderDomAfter mI ty_ld = some dC →
        dC.getAppArgs.length = n + rc.indices.toNat →
        ∀ P ∈ dC.getAppArgs.take n,
          hasBVarIn 0 (rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) P = false)
  hni_eq : ∀ (ek : FlatEntry) (self : IndData), es[k]? = some ek →
    (ReconView.ofStore t E_rec).ind ek.addr = some (some self) →
    rc.indices.toNat = self.ni

private theorem except_bind_eq_ok_pr {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem convExpr_unshare_pr {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (k n : Nat) (e : Ixon.Expr) (E : KExpr),
      n ≤ k → n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      ∃ n', n' ≤ n ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n'))
          (Binding.FamilyOf.unshare c k e) = .ok E ∧
        ∀ i, Binding.FamilyOf.unshare c k e ≠ .share i
  | 0, n, e, E, hnk, _, hconv => by
    have hn0 : n = 0 := by omega
    subst hn0
    cases e with
    | share i =>
      simp [Ix.Kernel.Reader.convExpr, L1.buildShareTbl, L1.buildShareTblGo,
        Ix.Kernel.Reader.malformed] at hconv
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ =>
      exact ⟨0, Nat.le_refl _, hconv, fun _ h => by cases h⟩
  | k + 1, n, e, E, hnk, hns, hconv => by
    cases e with
    | share i =>
      have hsz : (L1.buildShareTbl ecx (c.sharing.toList.take n)).size = n := by
        rw [L1.buildShareTbl_size, List.length_take, Array.length_toList, Nat.min_eq_left hns]
      by_cases hi : i.toNat < n
      · have hlt_sh : i.toNat < c.sharing.size := by omega
        have hget_arr : c.sharing[i.toNat]? = some c.sharing[i.toNat] :=
          Array.getElem?_eq_getElem hlt_sh
        have hget_list : c.sharing.toList[i.toNat]? = some c.sharing[i.toNat] := by
          rw [Array.getElem?_toList]; exact hget_arr
        have htbl_get := L1.buildShareTbl_take_getElem? ecx c.sharing.toList hi hget_list
        simp only [Ix.Kernel.Reader.convExpr, htbl_get] at hconv
        obtain ⟨n', hn'le, hconv', hns'⟩ :=
          convExpr_unshare_pr hsrc k i.toNat c.sharing[i.toNat] E (by omega) (by omega) hconv
        refine ⟨n', by omega, ?_, ?_⟩
        · simpa only [Binding.FamilyOf.unshare, hget_arr] using hconv'
        · simpa only [Binding.FamilyOf.unshare, hget_arr] using hns'
      · have hnone : (L1.buildShareTbl ecx (c.sharing.toList.take n))[i.toNat]? = none :=
          Array.getElem?_eq_none (by omega)
        simp [Ix.Kernel.Reader.convExpr, hnone, Ix.Kernel.Reader.malformed] at hconv
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ =>
      exact ⟨n, Nat.le_refl _, hconv, fun _ h => by cases h⟩

private theorem convExpr_node_pr {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) {n : Nat} {e : Ixon.Expr} {E : KExpr}
    (hns : n ≤ c.sharing.size)
    (hconv : Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E) :
    ∃ n', n' ≤ n ∧
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n'))
        (Binding.FamilyOf.node c e) = .ok E ∧
      ∀ i, Binding.FamilyOf.node c e ≠ .share i :=
  convExpr_unshare_pr hsrc (c.sharing.size + 1) n e E (by omega) hns hconv

private theorem convExpr_peel_pr {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (m n : Nat) (e e' : Ixon.Expr) (E : KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.peel c m e = some e' →
      ∃ bs E' n', n' ≤ n ∧ E.stripPis m = some (bs, E') ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n')) e' = .ok E'
  | 0, n, e, e', E, _, hconv, hpeel => by
    simp only [Binding.FamilyOf.peel, Option.some.injEq] at hpeel
    subst hpeel
    exact ⟨[], E, n, Nat.le_refl _, rfl, hconv⟩
  | m + 1, n, e, e', E, hns, hconv, hpeel => by
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node_pr hsrc hns hconv
    unfold Binding.FamilyOf.peel at hpeel
    cases hnd : Binding.FamilyOf.node c e with
    | all d b =>
      rw [hnd] at hpeel hconv₁
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨dE, hdE, h1⟩ := except_bind_eq_ok_pr hconv₁
      obtain ⟨bE, hbE, h2⟩ := except_bind_eq_ok_pr h1
      have hE : E = .forallE dE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
      obtain ⟨bs, E', n₂, hn₂, hstrip, hconv₂⟩ :=
        convExpr_peel_pr hsrc m n₁ b e' bE (by omega) hbE hpeel
      refine ⟨(dE, Ix.Kernel.BinderMeta.leanNever) :: bs, E', n₂, by omega, ?_, hconv₂⟩
      rw [hE, Ix.Kernel.Expr.stripPis, hstrip]
      rfl
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hpeel; cases hpeel

private theorem convExpr_not_forall_pr {ecx : Ix.Kernel.Reader.ECx .anon}
    {tbl : Array (Ix.Kernel.Reader.ReadM KExpr)} {e : Ixon.Expr} {E : KExpr}
    (hns : ∀ i, e ≠ .share i) (hna : ∀ d b, e ≠ .all d b)
    (hconv : Ix.Kernel.Reader.convExpr ecx tbl e = .ok E) :
    ∀ d b bm, E ≠ .forallE d b bm := by
  cases e with
  | all d b => exact (hna d b rfl).elim
  | share i => exact (hns i rfl).elim
  | var _ =>
    simp only [Ix.Kernel.Reader.convExpr, Ix.Kernel.Expr.mkBvar_eq] at hconv
    have hE := Except.ok.inj hconv; subst hE; intro _ _ _ h; cases h
  | sort _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | ref _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | recur i _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hs : ecx.self i.toNat with
    | none => simp [hs, Ix.Kernel.Reader.malformed] at hconv
    | some m =>
      rw [hs] at hconv
      obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
      obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
      have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | prj _ _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | str _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨bs, -, h1⟩ := except_bind_eq_ok_pr hconv
    cases hs : String.fromUTF8? bs with
    | none => simp [hs, Ix.Kernel.Reader.malformed] at h1
    | some s =>
      simp only [hs] at h1
      have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | nat _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    have hE := Except.ok.inj h1; subst hE; intro _ _ _ h; cases h
  | app _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | lam _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
    have hE := Except.ok.inj h2; subst hE; intro _ _ _ h; cases h
  | letE _ _ _ _ _ =>
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨_, -, h1⟩ := except_bind_eq_ok_pr hconv
    obtain ⟨_, -, h2⟩ := except_bind_eq_ok_pr h1
    obtain ⟨_, -, h3⟩ := except_bind_eq_ok_pr h2
    have hE := Except.ok.inj h3; subst hE; intro _ _ _ h; cases h

private theorem convExpr_lastDom_pr {c : Ixon.Constant} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hsrc : ecx.src = c) :
    ∀ (k n : Nat) (e d : Ixon.Expr) (E : KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.lastDom c k e = some d →
      ∃ dE n', n' ≤ n ∧ lastBinderDom E = some dE ∧
        Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n')) d = .ok dE
  | 0, _, _, _, _, _, _, hld => by simp [Binding.FamilyOf.lastDom] at hld
  | k + 1, n, e, d, E, hns, hconv, hld => by
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node_pr hsrc hns hconv
    unfold Binding.FamilyOf.lastDom at hld
    cases hnd : Binding.FamilyOf.node c e with
    | all d' b' =>
      rw [hnd] at hld hconv₁
      dsimp only at hld
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨dE, hdE, h1⟩ := except_bind_eq_ok_pr hconv₁
      obtain ⟨bE, hbE, h2⟩ := except_bind_eq_ok_pr h1
      have hE : E = .forallE dE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
      obtain ⟨n₂, hn₂, hbE₂, hns₂⟩ := convExpr_node_pr hsrc (by omega) hbE
      cases hbnd : Binding.FamilyOf.node c b' with
      | all d'' b'' =>
        rw [hbnd] at hld hbE₂
        simp only [Ix.Kernel.Reader.convExpr] at hbE₂
        obtain ⟨dE2, -, h1'⟩ := except_bind_eq_ok_pr hbE₂
        obtain ⟨bE2, -, h2'⟩ := except_bind_eq_ok_pr h1'
        have hbE_eq : bE = .forallE dE2 bE2 Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2').symm
        obtain ⟨dE_out, n₃, hn₃, hl_b, hconv_out⟩ :=
          convExpr_lastDom_pr hsrc k n₁ b' d bE (by omega) hbE hld
        refine ⟨dE_out, n₃, by omega, ?_, hconv_out⟩
        rw [hE, hbE_eq]
        simpa [lastBinderDom, hbE_eq] using hl_b
      | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
      | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
        rw [hbnd] at hld hbE₂ hns₂
        have hd_eq : d' = d := Option.some.inj hld
        subst hd_eq
        have hnotf := convExpr_not_forall_pr hns₂ (fun _ _ h => by cases h) hbE₂
        refine ⟨dE, n₁, hn₁, ?_, hdE⟩
        rw [hE]
        cases bE with
        | forallE d0 b0 bm0 => exact (hnotf d0 b0 bm0 rfl).elim
        | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
        | letE _ _ _ _ | lit _ | proj _ _ _ => rfl
    | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
    | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hld; cases hld

private theorem convExpr_spineHead_ref_pr {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {c : Ixon.Constant} {param : Nat → LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {rIdx : UInt64} {uIdxs : Array UInt64} {a : _root_.Address}
    (href : c.refs[rIdx.toNat]? = some a) :
    let ecx : Ix.Kernel.Reader.ECx .anon :=
      ⟨readCtx t blob, c, c.univs.map (Ix.Kernel.Reader.convUniv param), self⟩
    ∀ (k n : Nat) (e : Ixon.Expr) (E : KExpr),
      n ≤ c.sharing.size →
      Ix.Kernel.Reader.convExpr ecx (L1.buildShareTbl ecx (c.sharing.toList.take n)) e = .ok E →
      Binding.FamilyOf.spineHead c k e = .ref rIdx uIdxs →
      headKey E = some (keyOf t a) := by
  intro ecx k
  induction k with
  | zero =>
    intro n e E hns hconv hsp
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node_pr (c := c) rfl hns hconv
    simp only [Binding.FamilyOf.spineHead] at hsp
    rw [hsp] at hconv₁
    simp only [Ix.Kernel.Reader.convExpr] at hconv₁
    obtain ⟨k', hk', h1⟩ := except_bind_eq_ok_pr hconv₁
    obtain ⟨ls, -, h2⟩ := except_bind_eq_ok_pr h1
    have hE : E = .const k' ls := (Except.ok.inj h2).symm
    have hk_eq : k' = keyOf t a := by
      simp only [ecx, Ix.Kernel.Reader.ECx.keyAt, href] at hk'
      rw [readCtx_keyAt ht blob a] at hk'
      exact (Except.ok.inj hk').symm
    rw [hE, hk_eq]
    rfl
  | succ k ih =>
    intro n e E hns hconv hsp
    obtain ⟨n₁, hn₁, hconv₁, -⟩ := convExpr_node_pr (c := c) rfl hns hconv
    unfold Binding.FamilyOf.spineHead at hsp
    cases hnd : Binding.FamilyOf.node c e with
    | app f arg =>
      rw [hnd] at hsp hconv₁
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨fE, hfE, h1⟩ := except_bind_eq_ok_pr hconv₁
      obtain ⟨aE, -, h2⟩ := except_bind_eq_ok_pr h1
      have hE : E = .app fE aE := (Except.ok.inj h2).symm
      rw [hE]
      exact ih n₁ f fE (by omega) hfE hsp
    | ref rIdx' uIdxs' =>
      rw [hnd] at hsp hconv₁
      injection hsp with hr_eq hu_eq
      subst hr_eq hu_eq
      simp only [Ix.Kernel.Reader.convExpr] at hconv₁
      obtain ⟨k', hk', h1⟩ := except_bind_eq_ok_pr hconv₁
      obtain ⟨ls, -, h2⟩ := except_bind_eq_ok_pr h1
      have hE : E = .const k' ls := (Except.ok.inj h2).symm
      have hk_eq : k' = keyOf t a := by
        simp only [ecx, Ix.Kernel.Reader.ECx.keyAt, href] at hk'
        rw [readCtx_keyAt ht blob a] at hk'
        exact (Except.ok.inj hk').symm
      rw [hE, hk_eq]
      rfl
    | var _ | sort _ | recur _ _ | prj _ _ _ | str _ | nat _
    | lam _ _ | all _ _ | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hsp; cases hsp

private theorem familyKey_of_motiveCarrierAt_pr {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {c : Ixon.Constant} {rc : Ixon.Recursor}
    {param : Nat → LevelParam}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {nf : Nat} {a : _root_.Address} {ty : KExpr}
    (hread : (exprReader t blob c param self).read rc.typ = .ok ty)
    (hmot : Binding.FamilyOf.motiveCarrierAt c rc 0 nf = some a) :
    familyKey rc ty = some (keyOf t a) := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) c param self
  unfold exprReader Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := c.sharing.toList), Array.length_toList] at hread
  unfold Binding.FamilyOf.motiveCarrierAt at hmot
  rw [Nat.add_zero] at hmot
  cases hpeel : Binding.FamilyOf.peel c rc.params.toNat rc.typ with
  | none => rw [hpeel] at hmot; simp at hmot
  | some e1 =>
    rw [hpeel] at hmot; dsimp only [bind, Option.bind] at hmot
    cases hdom : Binding.FamilyOf.domOf c e1 with
    | none => rw [hdom] at hmot; simp at hmot
    | some em =>
      rw [hdom] at hmot; dsimp only [bind, Option.bind] at hmot
      cases hld : Binding.FamilyOf.lastDom c nf em with
      | none => rw [hld] at hmot; simp at hmot
      | some ed =>
        rw [hld] at hmot; dsimp only [bind, Option.bind] at hmot
        unfold Binding.FamilyOf.refHeadAt at hmot
        cases hsp : Binding.FamilyOf.spineHead c nf ed with
        | ref rIdx uIdxs =>
          rw [hsp] at hmot
          obtain ⟨bs, E1, n₁, hn₁, hstrip, hconv₁⟩ :=
            convExpr_peel_pr (c := c) rfl rc.params.toNat c.sharing.size rc.typ e1 ty
              (Nat.le_refl _) hread hpeel
          obtain ⟨n₂, hn₂, hconv₂, -⟩ := convExpr_node_pr (c := c) rfl (by omega) hconv₁
          unfold Binding.FamilyOf.domOf at hdom
          cases hnd1 : Binding.FamilyOf.node c e1 with
          | all d1 b1 =>
            rw [hnd1] at hdom hconv₂
            have hem_eq : d1 = em := Option.some.inj hdom
            subst d1
            simp only [Ix.Kernel.Reader.convExpr] at hconv₂
            obtain ⟨mE, hmE, h1⟩ := except_bind_eq_ok_pr hconv₂
            obtain ⟨bE, -, h2⟩ := except_bind_eq_ok_pr h1
            have hE1 : E1 = .forallE mE bE Ix.Kernel.BinderMeta.leanNever := (Except.ok.inj h2).symm
            obtain ⟨dE, n₃, hn₃, hlast, hconv₃⟩ :=
              convExpr_lastDom_pr (c := c) rfl nf n₂ em ed mE (by omega) hmE hld
            have hhead := convExpr_spineHead_ref_pr ht (param := param) (self := self)
              hmot nf n₃ ed dE (by omega) hconv₃ hsp
            unfold familyKey binderDom
            rw [hstrip, hE1]
            simp [hlast, hhead]
          | var _ | sort _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _
          | app _ _ | lam _ _ | letE _ _ _ _ _ | share _ =>
            rw [hnd1] at hdom; cases hdom
        | var _ | sort _ | recur _ _ | prj _ _ _ | str _ | nat _
        | app _ _ | lam _ _ | all _ _ | letE _ _ _ _ _ | share _ =>
          rw [hsp] at hmot; cases hmot

private theorem canonRules_length {src : Ixon.Constant} {ps : List LevelParam}
    {kFlag : Bool} {cParams : Nat} :
    ∀ {root : F} {rus : List Ixon.RecursorRule} {rules₀ rls : List (RecRule .anon)},
      LoadedReads.canonRules src ps kFlag cParams root rus rules₀ = some rls →
      rls.length = rus.length
  | _, [], [], _, h => by simp [LoadedReads.canonRules] at h; subst h; rfl
  | _, [], _ :: _, _, h => by simp [LoadedReads.canonRules] at h
  | _, _ :: _, [], _, h => by simp [LoadedReads.canonRules] at h
  | root, ru :: rus, rl₀ :: rules₀, rls, h => by
    unfold LoadedReads.canonRules at h
    cases ha : LoadedReads.canonAnn src ps root ru.rhs rl₀.rhs with
    | none => rw [ha] at h; cases h
    | some rhs' =>
      rw [ha] at h; simp only [Option.bind_some] at h
      cases hr : LoadedReads.canonRules src ps kFlag cParams (root + 1) rus rules₀ with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp [canonRules_length hr]

private theorem canonRules_getElem?_loadedAt {t : Ix.Kernel.RoleTable}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {kFlag : Bool} {cParams : Nat} :
    ∀ {root : F} {rus : List Ixon.RecursorRule} {rules₀ rls : List (RecRule .anon)},
      LoadedReads.canonRules src ps kFlag cParams root rus rules₀ = some rls →
      List.Forall₂ (fun ru rl₀ =>
        (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read ru.rhs = .ok rl₀.rhs)
        rus rules₀ →
      ∀ (c : Nat) (ru : Ixon.RecursorRule) (rl : RecRule .anon),
        rus[c]? = some ru → rls[c]? = some rl →
        loadedAt t blob src self ps.length (root + ((c : Nat) : F)) ru.rhs =
          some (Core.posOf ps rl.rhs)
  | _, [], [], _, _, _, _, _, _, hget, _ => by simp at hget
  | _, [], _ :: _, _, h, _, _, _, _, _, _ => by simp [LoadedReads.canonRules] at h
  | _, _ :: _, [], _, h, _, _, _, _, _, _ => by simp [LoadedReads.canonRules] at h
  | root, ru :: rus, rl₀ :: rules₀, rls, h, hrd, c, ru', rl, hget_u, hget_r => by
    unfold LoadedReads.canonRules at h
    cases ha : LoadedReads.canonAnn src ps root ru.rhs rl₀.rhs with
    | none => rw [ha] at h; cases h
    | some rhs' =>
      rw [ha] at h; simp only [Option.bind_some] at h
      cases hr : LoadedReads.canonRules src ps kFlag cParams (root + 1) rus rules₀ with
      | none => rw [hr] at h; cases h
      | some rest =>
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
        subst h
        cases hrd with
        | cons hhd htl =>
          cases c with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hget_u hget_r
            subst hget_u hget_r
            simpa only [Nat.cast_zero, add_zero] using posOf_canonAnn_eq_loadedAt hperm hhd ha
          | succ c' =>
            simp only [List.getElem?_cons_succ] at hget_u hget_r
            have ih := canonRules_getElem?_loadedAt hperm hr htl c' ru' rl hget_u hget_r
            have hroot : root + ((c' + 1 : Nat) : F) = (root + 1) + ((c' : Nat) : F) := by
              rw [Nat.cast_succ]; ring
            rwa [hroot]

private theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (i : Nat) (a : α) (b : β), l₁[i]? = some a → l₂[i]? = some b → R a b
  | [], [], .nil, _, _, _, h1, _ => by simp at h1
  | _ :: _, _ :: _, .cons hhd htl, 0, _, _, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2; exact hhd
  | _ :: _, _ :: _, .cons _ htl, i + 1, a, b, h1, h2 =>
    forall₂_getElem? htl i a b h1 h2

private theorem peelForalls_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (e : KExpr),
      peelForalls n (e.instantiateLevelParams ps us) =
        (peelForalls n e).map (Expr.instantiateLevelParams ps us)
  | 0, _ => rfl
  | n + 1, .forallE _ b _ => peelForalls_instantiateLevelParams ps us n b
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _
  | _ + 1, .app _ _ | _ + 1, .lam _ _ _ | _ + 1, .letE _ _ _ _
  | _ + 1, .lit _ | _ + 1, .proj _ _ _ => rfl

private theorem stored_indF_eq {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {R_st E_rec : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} {es : List FlatEntry} {ind₀ indF : Ixon.Inductive}
    {k : Nat} {rc : Ixon.Recursor} {tyP : KExpr} {kF : KKey} {Bf : _root_.Address} {iF : Nat}
    (hR_rec : ∀ a c, recordOf R_st a = some c → recordOf E_rec a = some c)
    (hFOB : FamilyOfBlock R_st B cb ms rb crb rs (es.map FlatEntry.addr))
    (hms0 : ms[0]? = some (.indc ind₀)) (hmem : rs[k]? = some (.recr rc))
    (htyP : (exprReader t (fun x => E_rec.blobs.get? x) crb id (blockSelf t rb rs)).read rc.typ = .ok tyP)
    (hfamK : familyKey rc tyP = some kF)
    (hindF : IndKeyAt t (recordOf E_rec) kF Bf iF indF) : indF = ind₀ := by
  have hflat0 : (es.map FlatEntry.addr)[0]? = some (Core.iprjAddr B 0) := by
    rw [← memberAddr_indc_eq B 0 ind₀]
    exact hFOB.originals 0 (.indc ind₀) hms0
  obtain ⟨nf, hmot0⟩ := hFOB.carriers k rc hmem 0 (Core.iprjAddr B 0) hflat0
  have hfk_eq : kF = keyOf t (Core.iprjAddr B 0) :=
    Option.some.inj (hfamK.symm.trans (familyKey_of_motiveCarrierAt_pr ht htyP hmot0))
  obtain ⟨aF, cF, pF, cbF, msF, haF_key, haF_rec, hcF_info, hpF_blk, hpF_idx,
    hcbF_rec, hcbF_muts, hmsF_get, -, -, -⟩ := hindF
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have haF_eq : aF = Core.iprjAddr B 0 := keyOf_inj hroles (haF_key.symm.trans hfk_eq)
  subst aF
  have hproj0 : recordOf E_rec (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind₀)) := by
    rw [← memberAddr_indc_eq B 0 ind₀]
    exact hR_rec _ _ (hFOB.block.members 0 (.indc ind₀) hms0)
  have hcF_eq : cF = memberProjection B 0 (.indc ind₀) := Option.some.inj (haF_rec.symm.trans hproj0)
  subst cF
  have hpF_eq : pF = ⟨(0 : Nat).toUInt64, B⟩ := Ixon.ConstantInfo.iPrj.inj hcF_info.symm
  subst pF
  have hcbF_eq : cbF = cb :=
    Option.some.inj (hcbF_rec.symm.trans (by rw [hpF_blk]; exact hR_rec _ _ hFOB.block.record))
  subst cbF
  have hmsF_eq : msF = ms := Ixon.ConstantInfo.muts.inj (hcbF_muts.symm.trans hFOB.block.muts)
  subst msF
  have hiF0 : iF = 0 := by simpa using hpF_idx
  subst iF
  exact Ixon.MutConst.indc.inj (Option.some.inj (hmsF_get.symm.trans hms0))

private theorem stored_hni_eq {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {R_st E_rec : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {es : List FlatEntry} {k : Nat} {rc : Ixon.Recursor}
    {cvC : ConstantVal .anon} {mI : Nat} {ty_ld : KExpr}
    (hR_rec : ∀ a c, recordOf R_st a = some c → recordOf E_rec a = some c)
    (hRF_C : RecordFlat t E_rec rb crb rs es) (hmem : rs[k]? = some (.recr rc))
    (hmI_eq : mI = rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
    (hty_ld : loadedAt t (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
      (mutsRoot rs k) rc.typ = some ty_ld)
    (hty_pos_eq : Core.posOf cvC.levelParams cvC.type = ty_ld)
    (hm_ind : ∃ (Bm : _root_.Address) (im : Nat) (cbm : Ixon.Constant) (msm : Array Ixon.MutConst)
      (indm : Ixon.Inductive) (D : KExpr) (lvls : List KLevel),
      im < UInt64.size ∧
      recordOf R_st (memberAddr Bm im (.indc indm)) = some (memberProjection Bm im (.indc indm)) ∧
      recordOf R_st Bm = some cbm ∧ cbm.info = .muts msm ∧ msm[im]? = some (.indc indm) ∧
      Core.piDomAt mI cvC.type = some D ∧
      D.getAppFn = .const (keyOf t (memberAddr Bm im (.indc indm))) lvls ∧
      rc.indices.toNat = indm.indices.toNat)
    {ek : FlatEntry} {self : IndData} (hek : es[k]? = some ek)
    (hself : (ReconView.ofStore t E_rec).ind ek.addr = some (some self)) :
    rc.indices.toNat = self.ni := by
  obtain ⟨Bm, im, cbm, msm, indm, D, lvls, himu, hPm, hBm, hmsm, him, hpi, hfn, hni⟩ := hm_ind
  obtain ⟨ty_rf, d_rf, hty_rf, hbd_rf, hfn_rf, -⟩ := hRF_C k rc ek hmem hek
  have hty_rf_eq : ty_rf = ty_ld := Option.some.inj (hty_rf.symm.trans hty_ld)
  rw [hty_rf_eq] at hbd_rf
  have hpi_pos : binderDomAfter mI ty_ld = some (Core.posOf cvC.levelParams D) := by
    rw [← hty_pos_eq]
    rw [piDomAt_eq_binderDomAfter] at hpi
    unfold binderDomAfter at hpi ⊢
    cases hp : peelForalls mI cvC.type with
    | none => simp [hp] at hpi
    | some r =>
      rw [hp] at hpi
      cases r with
      | forallE d b m =>
        simp only [Option.some.injEq] at hpi; subst hpi
        unfold Core.posOf
        rw [peelForalls_instantiateLevelParams, hp]; rfl
      | _ => simp at hpi
  rw [hmI_eq] at hpi_pos
  have hd_eq : Core.posOf cvC.levelParams D = d_rf := Option.some.inj (hpi_pos.symm.trans hbd_rf)
  have hfn_pos : (Core.posOf cvC.levelParams D).getAppFn =
      .const (keyOf t (memberAddr Bm im (.indc indm)))
        (lvls.map (Level.subst cvC.levelParams ((List.range cvC.levelParams.length).map .param))) := by
    have hfn_inst : ∀ (e : KExpr) (ps : List LevelParam) (us : List KLevel),
        (e.instantiateLevelParams ps us).getAppFn = e.getAppFn.instantiateLevelParams ps us := by
      intro e ps us
      induction e with
      | app f _ ihf _ => exact ihf
      | _ => rfl
    unfold Core.posOf
    rw [hfn_inst, hfn]; rfl
  rw [hd_eq, hfn_rf] at hfn_pos
  injection hfn_pos with hk_eq _
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have ha_eq : memberAddr Bm im (.indc indm) = ek.addr := keyOf_inj hroles hk_eq.symm
  obtain ⟨c_ek, p_ek, cb_ek, ms_ek, ind_ek, hc_ek, hci_ek, hcb_ek, hcbm_ek, hms_ek, hld_ek, -⟩ :=
    Binding.FamilyRecon.indDataAt_inv hself
  have hself_ni : self.ni = ind_ek.indices.toNat := by
    have h := hself
    simp only [ReconView.ofStore, Binding.FamilyRecon.indDataAt, hc_ek, hci_ek, hcb_ek,
      hcbm_ek, hms_ek, hld_ek, Option.some.injEq] at h
    exact (congrArg IndData.ni h).symm
  have hPm' : recordOf E_rec ek.addr = some (memberProjection Bm im (.indc indm)) := by
    rw [← ha_eq]; exact hR_rec _ _ hPm
  have hc_eq : c_ek = memberProjection Bm im (.indc indm) := Option.some.inj (hc_ek.symm.trans hPm')
  subst c_ek
  have hp_eq : p_ek = ⟨im.toUInt64, Bm⟩ := Ixon.ConstantInfo.iPrj.inj hci_ek.symm
  subst p_ek
  have hcb_eq : cb_ek = cbm := Option.some.inj (hcb_ek.symm.trans (hR_rec _ _ hBm))
  subst cb_ek
  have hms_eq : ms_ek = msm := Ixon.ConstantInfo.muts.inj (hcbm_ek.symm.trans hmsm)
  subst ms_ek
  have him64 : im.toUInt64.toNat = im := by
    change (UInt64.ofNat im).toNat = im
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt himu
  rw [him64] at hms_ek
  have hind_eq : indm = ind_ek := Ixon.MutConst.indc.inj (Option.some.inj (him.symm.trans hms_ek))
  rw [hni, hind_eq, hself_ni]

/-- **Build `CanonMemberAt` from `StoredFamilyRecs`, `FamilyOfBlock`, and `RFormS`** (used on the
stored arm and on the binding closure's pre-group stored-family arm). -/
theorem canonMemberAt_of_stored {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {R_st E_rec : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off fuel : Nat} {ind₀ : Ixon.Inductive} {k : Nat}
    (hR_rec : ∀ a c, recordOf R_st a = some c → recordOf E_rec a = some c)
    (hR_blob : ∀ y b, R_st.blobs.get? y = some b → E_rec.blobs.get? y = some b)
    (hFOB : FamilyOfBlock R_st B cb ms rb crb rs (es.map FlatEntry.addr))
    (hRF_C : RecordFlat t E_rec rb crb rs es)
    (hms0 : ms[0]? = some (.indc ind₀))
    (hrecs : StoredFamilyRecs t R_st env B cb rb crb)
    (hBD_R : BlockDerivedFlat t R_st B off es)
    (hLvls : StoredRecLvlsOk)
    (hk_lt : k < rs.size)
    (hMR : ∀ rc, rs[k]? = some (.recr rc) → MemberRecon ExprLvEq t E_rec rb crb rs es off fuel k rc) :
    Nonempty (CanonMemberAt calls t E_rec env B rb crb rs es off fuel ind₀ k) := by
  have hk_get : rs[k]? = some (rs[k]'hk_lt) := Array.getElem?_eq_getElem hk_lt
  obtain ⟨rc, hrc_eq⟩ := hFOB.record.recrs _ (List.mem_of_getElem? (by rwa [Array.getElem?_toList]))
  have hmem : rs[k]? = some (.recr rc) := by rwa [hrc_eq] at hk_get
  obtain ⟨cvC₀, mI, rP, rulesC₀, cvC, rulesC, hku, hRR_R, hfind_R, hnm, hlp, hSA, hTML,
    hns, hnp, hmot, hm_ind, hmconcl⟩ := hrecs.member ms rs k rc hFOB.block.muts hFOB.record.muts hmem
  rw [memberAddr_recr_eq rb k rc] at hRR_R hfind_R
  have hRR : RecReads t (recordOf E_rec) (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs)
      (keyOf t (Core.rprjAddr rb k)) rc (.recInfo cvC₀ mI rP rulesC₀) :=
    ReaderReads.recReads_mono hR_rec hR_blob hRR_R
  have hlvls_eq : rc.lvls.toNat = ind₀.lvls.toNat + off :=
    hLvls t R_st env B rb cb crb ms rs es off hFOB.block.muts hFOB.record.muts hrecs hBD_R
      ind₀ k rc hms0 hmem
  have hRR' := hRR
  obtain ⟨tyP, ty₀, kF, kM, Bf, Bm, iF, iM, indF, indM, ps, rules₀, htyP, hfamK, hindF,
    hmajK, hindM, hps_def, hty_read, hrls_sz, hrules_rr, hci₀⟩ := hRR'
  injection hci₀ with hcv₀_eq hmI_eq hrP_eq hrules₀_eq
  have hindF_eq : indF = ind₀ := stored_indF_eq ht hR_rec hFOB hms0 hmem htyP hfamK hindF
  subst indF
  have hps_perm : ps.Perm (List.range ps.length) := by
    rw [hps_def]; exact Decl.recLps_perm_range _ _
  have hps_len : ps.length = rc.lvls.toNat := by
    have := hTML.lvls; rwa [hcv₀_eq] at this
  have hcvC_name : cvC.name = keyOf t (Core.rprjAddr rb k) := by
    rw [hnm, hcv₀_eq]
  have hcvC_lps : cvC.levelParams =
      Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind₀.lvls.toNat + 1))
        (List.range ind₀.lvls.toNat) := by
    rw [hlp, hcv₀_eq]; exact hps_def
  -- Unpack `MemberRecon`
  obtain ⟨ty_ld, R, bodies, cbk, hty_ld, hR, hty_rel, hbodies, hcbk, hrules_mr⟩ := hMR rc hmem
  have hku_eq : k.toUInt64.toNat = k := by
    change (UInt64.ofNat k).toNat = k
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hku
  have hty_loaded_cvC : loadedAt t (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
      (mutsRoot rs k) rc.typ = some (Core.posOf cvC.levelParams cvC.type) := by
    have hcan := hTML.ty
    rw [hku_eq, hcv₀_eq] at hcan
    have hld := posOf_canonAnn_eq_loadedAt hps_perm hty_read hcan
    rw [hps_len] at hld
    have hlps_eq' : cvC.levelParams = ps := by rw [hlp, hcv₀_eq]
    rw [hlps_eq']
    exact hld
  have hty_pos_eq : Core.posOf cvC.levelParams cvC.type = ty_ld :=
    Option.some.inj (hty_loaded_cvC.symm.trans hty_ld)
  obtain ⟨rls_can, hcR_can, hagree_can, -⟩ := hTML.rules
  rw [hku_eq, hcv₀_eq, hrules₀_eq] at hcR_can
  have hagree_len : rls_can.length = rulesC.length := hagree_can.length_eq
  have hrls_len_eq : rulesC.length = rc.rules.size := by
    have h2 := canonRules_length hcR_can
    rw [← hagree_len, h2, Array.length_toList]
  have hrr_read : List.Forall₂ (fun ru rl₀ =>
      (exprReader t (fun x => E_rec.blobs.get? x) crb (Ix.Kernel.Reader.recParam ps)
        (blockSelf t rb rs)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules₀ :=
    lforall₂_of_zipIdx (fun _ _ h => by obtain ⟨rhs, hrd, hrl⟩ := h; subst hrl; exact hrd) hrules_rr
  have hnoSelf_st : ∀ j < rs.size, cvC.type.mentionsConst (keyOf t (Core.rprjAddr rb j)) = false := by
    intro j hj
    have hj_get : rs[j]? = some (rs[j]'hj) := Array.getElem?_eq_getElem hj
    obtain ⟨rcj, hrcj⟩ := hFOB.record.recrs _
      (List.mem_of_getElem? (by rwa [Array.getElem?_toList]))
    have hmem_j : rs[j]? = some (.recr rcj) := by rwa [hrcj] at hj_get
    rw [← memberAddr_recr_eq rb j rcj]
    exact hns j rcj hmem_j
  have hrules_rec_st : ∀ (c : Nat) (ru : Ixon.RecursorRule) (rC : RecRule .anon),
      rc.rules[c]? = some ru → rulesC[c]? = some rC →
      ∃ rhs_ld cb,
        loadedAt t (fun x => E_rec.blobs.get? x) crb (blockSelf t rb rs) rc.lvls.toNat
          (mutsRoot rs k + 1 + ((c : Nat) : F)) ru.rhs = some rhs_ld ∧
        ExprLvEq (Core.posOf cvC.levelParams rC.rhs) rhs_ld ∧
        bodies[c]? = some cb ∧
        RuleFollows ty_ld rc.params.toNat rc.motives.toNat rc.minors.toNat
          (cbk + c) ru.fields.toNat (elimLevel off) rhs_ld cb := by
    intro c ru rC hru hrC
    have hruL : rc.rules.toList[c]? = some ru := by rwa [Array.getElem?_toList]
    have hc_lt : c < rls_can.length := by
      have := (List.getElem?_eq_some_iff.mp hrC).1
      omega
    obtain ⟨rl_can, hrl_can⟩ : ∃ rl, rls_can[c]? = some rl :=
      ⟨rls_can[c]'hc_lt, List.getElem?_eq_getElem hc_lt⟩
    have hag := forall₂_getElem? hagree_can c rl_can rC hrl_can hrC
    have hld_rl := canonRules_getElem?_loadedAt hps_perm hcR_can hrr_read c ru rl_can hruL hrl_can
    rw [hps_len] at hld_rl
    obtain ⟨rhs_ld, cb_c, hrhs_ld, hcb_c, hrf⟩ := hrules_mr c ru hru
    have hlps_eq' : cvC.levelParams = ps := by rw [hlp, hcv₀_eq]
    have hrhs_eq : Core.posOf cvC.levelParams rC.rhs = rhs_ld := by
      rw [hlps_eq', hag.2]
      exact Option.some.inj (hld_rl.symm.trans hrhs_ld)
    exact ⟨rhs_ld, cb_c, hrhs_ld, by rw [hrhs_eq]; exact ExprLvEq.refl _, hcb_c, hrf⟩
  exact Nonempty.intro
    { rc := rc
      hmem := hmem
      cvC := cvC
      mI := mI
      rP := rP
      rulesC := rulesC
      cvC₀ := cvC₀
      rulesC₀ := rulesC₀
      hfind := hfind_R
      hstored := hSA
      hrecReads := hRR
      hcvC_name := hcvC_name
      hcvC_lps := hcvC_lps
      hlvls_eq := hlvls_eq
      hrnp := hnp ind₀ hms0
      hnmot := hmot
      hmI_def := hmI_eq
      hrP_def := hrP_eq
      hnoSelf := hnoSelf_st
      hmotiveConcl := hmconcl
      ty_ld := ty_ld
      R := R
      bodies := bodies
      cbk := cbk
      hty_ld := hty_ld
      hty_pos := hty_pos_eq
      hR := hR
      hbodies := hbodies
      hcbk := hcbk
      hrules_len := hrls_len_eq
      hrules_rec := hrules_rec_st
      hty_rel := Or.inl hty_rel
      hni_eq := fun _ _ hek hself =>
        stored_hni_eq ht hR_rec hRF_C hmem hmI_eq hty_ld hty_pos_eq hm_ind hek hself }

private theorem extracted_maj_eq_indData {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    {E₀ E_rec : Ixon.Env} {lim : Option Nat}
    {B A : _root_.Address} {cb cA : Ixon.Constant} {ms rs' : Array Ixon.MutConst}
    {es : List FlatEntry} {ind₀ : Ixon.Inductive} {k : Nat}
    (hE₀_rec : ∀ a c, recordOf E₀ a = some c → recordOf E_rec a = some c)
    (hE₀_blob : ∀ y b, E₀.blobs.get? y = some b → E_rec.blobs.get? y = some b)
    (hRF : RecordFlat t E_rec A cA rs' es)
    (mA : ExtractedTwinMember.{u} calls t E₀ lim B A cb cA ms rs' ind₀ k)
    {ek : FlatEntry} {self : IndData}
    (hek : es[k]? = some ek)
    (hself : (ReconView.ofStore t E_rec).ind ek.addr = some (some self)) :
    ∃ (c_ek : Ixon.Constant) (p_ek : Ixon.InductiveProj) (cb_ek : Ixon.Constant)
      (ms_ek : Array Ixon.MutConst) (ind_ek : Ixon.Inductive),
      recordOf E_rec ek.addr = some c_ek ∧
      c_ek.info = .iPrj p_ek ∧
      recordOf E_rec p_ek.block = some cb_ek ∧
      cb_ek.info = .muts ms_ek ∧
      ms_ek[p_ek.idx.toNat]? = some (.indc ind_ek) ∧
      mA.a_maj = ek.addr ∧
      mA.indM = ind_ek ∧
      mA.p_maj = p_ek ∧
      self.np = ind_ek.params.toNat ∧
      self.ni = ind_ek.indices.toNat ∧
      self.nctors = ind_ek.ctors.size ∧
      self.blk = p_ek.block ∧
      self.idx = p_ek.idx.toNat ∧
      mA.rc.indices.toNat = self.ni := by
  obtain ⟨c_ek, p_ek, cb_ek, ms_ek, ind_ek, hc_ek, hci_ek, hcb_ek, hcbm_ek, hms_ek, hld_ek, -⟩ :=
    Binding.FamilyRecon.indDataAt_inv hself
  have hself_fields : self.np = ind_ek.params.toNat ∧ self.ni = ind_ek.indices.toNat ∧
      self.nctors = ind_ek.ctors.size ∧ self.blk = p_ek.block ∧ self.idx = p_ek.idx.toNat := by
    have h := hself
    simp only [ReconView.ofStore, Binding.FamilyRecon.indDataAt, hc_ek, hci_ek, hcb_ek,
      hcbm_ek, hms_ek, hld_ek, Option.some.injEq] at h
    exact ⟨(congrArg IndData.np h).symm, (congrArg IndData.ni h).symm,
      (congrArg IndData.nctors h).symm, (congrArg IndData.blk h).symm,
      (congrArg IndData.idx h).symm⟩
  have htyW_loaded : loadedAt t (fun x => E_rec.blobs.get? x) cA (blockSelf t A rs')
      mA.rc.lvls.toNat (mutsRoot rs' k) mA.rc.typ = some (Core.posOf mA.ps mA.ty') := by
    have h1 := posOf_canonAnn_eq_loadedAt mA.hps_perm mA.hty_read mA.hcanonTy
    rw [mA.hps_len] at h1
    exact Binding.FamilyFlat.loadedAt_mono hE₀_blob h1
  obtain ⟨tyW_rf, dW_pos, htyW_rf, hbdW_rf, hfnW_rf, -⟩ := hRF k mA.rc ek mA.hmem hek
  have htyW_rf_eq : Core.posOf mA.ps mA.ty' = tyW_rf :=
    Option.some.inj (htyW_loaded.symm.trans htyW_rf)
  have ha_maj_eq : mA.a_maj = ek.addr := by
    have hmaj_ann := majorKey_of_annotates_pr mA.hmajKey
      (annotates_instantiateLevelParams_pr _ _ mA.hvalStored.2.2)
    change majorKey mA.rc (Core.posOf mA.ps mA.ty') = some (keyOf t mA.a_maj) at hmaj_ann
    rw [htyW_rf_eq] at hmaj_ann
    unfold majorKey binderDom headKey at hmaj_ann
    unfold binderDomAfter at hbdW_rf
    cases hp : peelForalls (mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat +
        mA.rc.indices.toNat) tyW_rf with
    | none => simp [hp] at hbdW_rf
    | some r =>
      rw [hp] at hbdW_rf
      cases r with
      | forallE d b m =>
        simp only [Option.some.injEq] at hbdW_rf; subst hbdW_rf
        obtain ⟨bs, hs⟩ := (stripPis_iff_peelForalls _ _ _).mp hp
        rw [hs, Option.bind_some, hfnW_rf] at hmaj_ann
        exact keyOf_inj hroles (Option.some.inj hmaj_ann).symm
      | _ => simp at hbdW_rf
  obtain ⟨a1, c1, p1, cb1, ms1, hk1, hrec1, hi1, hp1b, hp1i, hcb1, hcbm1, hms1, -, -, -⟩ :=
    mA.hindKey_M
  have ha1_eq : a1 = ek.addr := (keyOf_inj hroles hk1.symm).trans ha_maj_eq
  subst a1
  have hc1_eq : c1 = c_ek := Option.some.inj ((hE₀_rec _ _ hrec1).symm.trans hc_ek)
  subst c1
  have hp1_eq : p1 = p_ek := Ixon.ConstantInfo.iPrj.inj (hi1.symm.trans hci_ek)
  subst p1
  have hcb1' : recordOf E₀ p_ek.block = some cb1 := by rwa [hp1b] at hcb1
  have hcb1_eq : cb1 = cb_ek := Option.some.inj ((hE₀_rec _ _ hcb1').symm.trans hcb_ek)
  subst cb1
  have hms1_eq : ms1 = ms_ek := Ixon.ConstantInfo.muts.inj (hcbm1.symm.trans hcbm_ek)
  subst ms1
  have hidx_eq : mA.p_maj.idx.toNat = p_ek.idx.toNat := hp1i
  have hblk_eq : mA.p_maj.block = p_ek.block := hp1b
  have hpm_eq : mA.p_maj = p_ek := by
    cases hp_m : mA.p_maj with
    | mk i1 b1 =>
      cases p_ek with
      | mk i2 b2 =>
        simp only [hp_m] at hidx_eq hblk_eq
        subst hblk_eq
        have hi_u : i1 = i2 := UInt64.ext hidx_eq
        subst hi_u; rfl
  rw [hp1i] at hms1
  have hindM_eq : mA.indM = ind_ek :=
    Ixon.MutConst.indc.inj (Option.some.inj (hms1.symm.trans hms_ek))
  have hni_eq : mA.rc.indices.toNat = self.ni := by
    rw [mA.hni_eq, hindM_eq, hself_fields.2.1]
  exact ⟨c_ek, p_ek, cb_ek, ms_ek, ind_ek, hc_ek, hci_ek, hcb_ek, hcbm_ek, hms_ek,
    ha_maj_eq, hindM_eq, hpm_eq, hself_fields.1, hself_fields.2.1, hself_fields.2.2.1,
    hself_fields.2.2.2.1, hself_fields.2.2.2.2, hni_eq⟩

/-- **Build `CanonMemberAt` from an `ExtractedTwinMember` of `rb`** (used on the graph arm and on
the binding closure's in-group selected-family arm). -/
theorem canonMemberAt_of_extracted {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off fuel : Nat} {ind₀ : Ixon.Inductive} {k : Nat}
    (hSS : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hrb : FamRecRecord E₀ rb crb rs)
    (hRF_C : RecordFlat t E₀ rb crb rs es)
    (mC : ExtractedTwinMember.{u} calls t E₀ lim B rb cb crb ms rs ind₀ k)
    (hlvls_off : mC.rc.lvls.toNat = ind₀.lvls.toNat + off)
    (hstoredRb : ∀ x, ConstAddrOf rb crb x →
      ∃ ci ci₀, env.find? (keyOf t x) = some ci ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀)
    (hMR : MemberRecon ExprLvEq t E₀ rb crb rs es off fuel k mC.rc ∨
      (ctorsBefore (ReconView.ofStore t E₀) es es.length = some mC.rc.minors.toNat ∧
        MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
          t E₀ rb crb rs es off fuel k mC.rc)) :
    Nonempty (CanonMemberAt calls t E₀ env B rb crb rs es off fuel ind₀ k) := by
  have hx_k : ConstAddrOf rb crb (Core.rprjAddr rb k) :=
    Or.inr ⟨rs, k, .recr mC.rc, hrb.muts, mC.hmem, Or.inl (memberAddr_recr_eq rb k mC.rc).symm⟩
  obtain ⟨ci, ci₀', hfind_ci, hreads', hSA'⟩ := hstoredRb (Core.rprjAddr rb k) hx_k
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hP_k : recordOf E₀ (Core.rprjAddr rb k) = some (memberProjection rb k (.recr mC.rc)) := by
    rw [← memberAddr_recr_eq rb k mC.rc]
    exact hrb.members k (.recr mC.rc) mC.hmem
  have hci₀_eq : ci₀' = mC.ci₀ := reads_rprj_det_pr hroles hP_k hreads' mC.hreads
  subst hci₀_eq
  rw [mC.hci₀] at hSA'
  cases ci with
  | recInfo cvC mI rP rulesC =>
    obtain ⟨hVS, hmI_eq, hrP_eq, hRS_rules⟩ := hSA'
    subst hmI_eq hrP_eq
    have hcvC_name : cvC.name = keyOf t (Core.rprjAddr rb k) := hVS.1
    have hcvC_lps : cvC.levelParams = mC.ps := hVS.2.1
    obtain ⟨-, -, -, hty_lv_env, hrules_lv_env⟩ :=
      mC.hloaded_at_env E env hSS hinv cvC _ _ rulesC hfind_ci
    have hty_pos_eq_mC : Core.posOf cvC.levelParams cvC.type = Core.posOf mC.ps mC.ty' := by
      rw [hcvC_lps] at hty_lv_env ⊢
      exact eq_of_annotates_exprLvEq
        (annotates_instantiateLevelParams_pr _ _ hVS.2.2)
        (annotates_instantiateLevelParams_pr _ _ mC.hvalStored.2.2)
        hty_lv_env
    have hty_loaded_mC : loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
        mC.rc.lvls.toNat (mutsRoot rs k) mC.rc.typ = some (Core.posOf mC.ps mC.ty') := by
      have h1 := posOf_canonAnn_eq_loadedAt mC.hps_perm mC.hty_read mC.hcanonTy
      rwa [mC.hps_len] at h1
    have hnoSelf_cvC : ∀ j < rs.size, cvC.type.mentionsConst (keyOf t (Core.rprjAddr rb j)) = false := by
      intro j hj
      have h1 := mentionsConst_of_exprLvEq (k := keyOf t (Core.rprjAddr rb j)) hty_lv_env
      have h2 := mC.hnoSelf j hj
      rw [← mentionsConst_posOf (ps := cvC.levelParams), h1, mentionsConst_posOf]
      exact h2
    have hmotiveConcl_cvC : ∃ bs concl,
        (Core.posOf cvC.levelParams cvC.type).stripPis
          (mC.rc.params.toNat + mC.rc.motives.toNat + mC.rc.minors.toNat + mC.rc.indices.toNat + 1) =
            some (bs, concl) ∧
        ∀ d b m, concl ≠ .forallE d b m := by
      rw [hty_pos_eq_mC]
      exact mC.hmotiveConcl
    have hrls_len_eq : rulesC.length = mC.rc.rules.size := by
      rw [hrules_lv_env.length_eq, canonRules_length mC.hcanonRules, Array.length_toList]
    have hrr_read : List.Forall₂ (fun ru rl₀ =>
        (exprReader t (fun x => E₀.blobs.get? x) crb (Ix.Kernel.Reader.recParam mC.ps)
          (blockSelf t rb rs)).read ru.rhs = .ok rl₀.rhs) mC.rc.rules.toList mC.rules₀ :=
      List.Forall₂.imp (fun _ _ h => h.2.1) mC.hrules_read
    have hni_eq_mC : ∀ (ek : FlatEntry) (self : IndData), es[k]? = some ek →
        (ReconView.ofStore t E₀).ind ek.addr = some (some self) →
        mC.rc.indices.toNat = self.ni := by
      intro ek self hek hself
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hni⟩ :=
        extracted_maj_eq_indData hroles (fun _ _ h => h) (fun _ _ h => h) hRF_C mC hek hself
      exact hni
    -- Helper for rules extraction given any `MemberRecon`
    have mk_rules : ∀ {TyRel : KExpr → KExpr → Prop}
        (hM : MemberRecon TyRel t E₀ rb crb rs es off fuel k mC.rc),
        ∃ ty_ld R bodies cbk,
          loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) mC.rc.lvls.toNat
            (mutsRoot rs k) mC.rc.typ = some ty_ld ∧
          Core.posOf cvC.levelParams cvC.type = ty_ld ∧
          recTypeAt (ReconView.ofStore t E₀) fuel es off mC.rc.params.toNat k = some R ∧
          TyRel ty_ld R ∧
          ruleBodiesAt (ReconView.ofStore t E₀) fuel es off mC.rc.params.toNat mC.rc.motives.toNat
            mC.rc.minors.toNat mC.rc.lvls.toNat k (recAddrs rb rs) = some bodies ∧
          ctorsBefore (ReconView.ofStore t E₀) es k = some cbk ∧
          (∀ (c : Nat) (ru : Ixon.RecursorRule) (rC : RecRule .anon),
            mC.rc.rules[c]? = some ru → rulesC[c]? = some rC →
            ∃ rhs_ld cb_c,
              loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) mC.rc.lvls.toNat
                (mutsRoot rs k + 1 + ((c : Nat) : F)) ru.rhs = some rhs_ld ∧
              ExprLvEq (Core.posOf cvC.levelParams rC.rhs) rhs_ld ∧
              bodies[c]? = some cb_c ∧
              RuleFollows ty_ld mC.rc.params.toNat mC.rc.motives.toNat mC.rc.minors.toNat
                (cbk + c) ru.fields.toNat (elimLevel off) rhs_ld cb_c) := by
      intro TyRel hM
      obtain ⟨ty_ld, R, bodies, cbk, hty_ld, hR, hrel, hbodies, hcbk, hrules_mr⟩ := hM
      have hty_eq : Core.posOf mC.ps mC.ty' = ty_ld :=
        Option.some.inj (hty_loaded_mC.symm.trans hty_ld)
      refine ⟨ty_ld, R, bodies, cbk, hty_ld, hty_pos_eq_mC.trans hty_eq, hR, hrel, hbodies, hcbk,
        fun c ru rC hru hrC => ?_⟩
      have hruL : mC.rc.rules.toList[c]? = some ru := by rwa [Array.getElem?_toList]
      have hc_lt : c < mC.rls.length := by
        have := (List.getElem?_eq_some_iff.mp hrC).1
        rw [hrules_lv_env.length_eq] at this; exact this
      obtain ⟨rl_c, hrl_c⟩ : ∃ rl, mC.rls[c]? = some rl :=
        ⟨mC.rls[c]'hc_lt, List.getElem?_eq_getElem hc_lt⟩
      have hlv_c := (forall₂_getElem? hrules_lv_env c rC rl_c hrC hrl_c).2
      have hld_rl := canonRules_getElem?_loadedAt mC.hps_perm mC.hcanonRules hrr_read c ru rl_c
        hruL hrl_c
      rw [mC.hps_len] at hld_rl
      obtain ⟨rhs_ld, cb_c, hrhs_ld, hcb_c, hrf⟩ := hrules_mr c ru hru
      have hrhs_eq : Core.posOf mC.ps rl_c.rhs = rhs_ld :=
        Option.some.inj (hld_rl.symm.trans hrhs_ld)
      exact ⟨rhs_ld, cb_c, hrhs_ld, by rwa [← hrhs_eq], hcb_c, hrf⟩
    -- Helper for `hasBVarIn` pins on `ty_ld` from `mC.hmajorPins`
    have hpins_ty_ld : ∀ (ty_ld : KExpr),
        loadedAt t (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) mC.rc.lvls.toNat
          (mutsRoot rs k) mC.rc.typ = some ty_ld →
        ∀ (dC : KExpr) (n : Nat),
          binderDomAfter
            (mC.rc.params.toNat + mC.rc.motives.toNat + mC.rc.minors.toNat + mC.rc.indices.toNat)
            ty_ld = some dC →
          dC.getAppArgs.length = n + mC.rc.indices.toNat →
          ∀ P ∈ dC.getAppArgs.take n,
            hasBVarIn 0 (mC.rc.motives.toNat + mC.rc.minors.toNat + mC.rc.indices.toNat) P = false := by
      intro ty_ld hty_ld dC n hbd hlen P hP
      have hty_eq : Core.posOf mC.ps mC.ty' = ty_ld :=
        Option.some.inj (hty_loaded_mC.symm.trans hty_ld)
      subst hty_eq
      obtain ⟨a_ind, inp, bs, dom, body, mmaj, lvls_p, As, hstrip, -, hargs, hAs_len, -, hno⟩ :=
        mC.hmajorPins
      have hpeel : peelForalls _ (Core.posOf mC.ps mC.ty') = some (.forallE dom body mmaj) :=
        (stripPis_iff_peelForalls _ _ _).mpr ⟨bs, hstrip⟩
      unfold binderDomAfter at hbd
      rw [hpeel] at hbd
      have hd_eq : dom = dC := Option.some.inj hbd
      subst hd_eq
      rw [hargs] at hlen hP
      have hne : n = inp := by omega
      subst hne
      exact hno P hP
    rcases hMR with hMR_eq | ⟨htot, hMR_obs⟩
    · obtain ⟨ty_ld, R, bodies, cbk, hty_ld, hty_pos, hR, hrel, hbodies, hcbk, hrules_rec⟩ :=
        mk_rules hMR_eq
      exact
        ⟨{ rc := mC.rc
           hmem := mC.hmem
           cvC := cvC
           mI := _
           rP := _
           rulesC := rulesC
           cvC₀ := ⟨keyOf t (Core.rprjAddr rb k), mC.ps, mC.ty₀⟩
           rulesC₀ := mC.rules₀
           hfind := hfind_ci
           hstored := ⟨hVS, rfl, rfl, hRS_rules⟩
           hrecReads := by simpa [mC.hci₀] using mC.hrecReads
           hcvC_name := hcvC_name
           hcvC_lps := hcvC_lps.trans mC.hps_eq
           hlvls_eq := hlvls_off
           hrnp := mC.hrnp
           hnmot := mC.hnmot
           hmI_def := rfl
           hrP_def := rfl
           hnoSelf := hnoSelf_cvC
           hmotiveConcl := hmotiveConcl_cvC
           ty_ld := ty_ld
           R := R
           bodies := bodies
           cbk := cbk
           hty_ld := hty_ld
           hty_pos := hty_pos
           hR := hR
           hbodies := hbodies
           hcbk := hcbk
           hrules_len := hrls_len_eq
           hrules_rec := hrules_rec
           hty_rel := Or.inl hrel
           hni_eq := hni_eq_mC }⟩
    · obtain ⟨ty_ld, R, bodies, cbk, hty_ld, hty_pos, hR, hrel, hbodies, hcbk, hrules_rec⟩ :=
        mk_rules hMR_obs
      have hlf_ty_ld : letFree ty_ld = true := by
        have hty_eq : Core.posOf mC.ps mC.ty' = ty_ld :=
          Option.some.inj (hty_loaded_mC.symm.trans hty_ld)
        rw [← hty_eq]
        unfold Core.posOf
        rw [letFree_instantiateLevelParams]
        exact mC.hty'_letFree
      exact
        ⟨{ rc := mC.rc
           hmem := mC.hmem
           cvC := cvC
           mI := _
           rP := _
           rulesC := rulesC
           cvC₀ := ⟨keyOf t (Core.rprjAddr rb k), mC.ps, mC.ty₀⟩
           rulesC₀ := mC.rules₀
           hfind := hfind_ci
           hstored := ⟨hVS, rfl, rfl, hRS_rules⟩
           hrecReads := by simpa [mC.hci₀] using mC.hrecReads
           hcvC_name := hcvC_name
           hcvC_lps := hcvC_lps.trans mC.hps_eq
           hlvls_eq := hlvls_off
           hrnp := mC.hrnp
           hnmot := mC.hnmot
           hmI_def := rfl
           hrP_def := rfl
           hnoSelf := hnoSelf_cvC
           hmotiveConcl := hmotiveConcl_cvC
           ty_ld := ty_ld
           R := R
           bodies := bodies
           cbk := cbk
           hty_ld := hty_ld
           hty_pos := hty_pos
           hR := hR
           hbodies := hbodies
           hcbk := hcbk
           hrules_len := hrls_len_eq
           hrules_rec := hrules_rec
           hty_rel := Or.inr ⟨hrel, hlf_ty_ld, htot, hpins_ty_ld ty_ld hty_ld⟩
           hni_eq := hni_eq_mC }⟩
  | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _
  | indInfo _ _ | ctorInfo _ _ _ | projInfo _ =>
    simp [StoredAs] at hSA'

/-! ## Unified twin parts producer -/

private theorem list_forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ (i : Nat) (a : α) (b : β), l₁[i]? = some a → l₂[i]? = some b → R a b) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l₁, b :: l₂, h, hall =>
    .cons (hall 0 a b rfl rfl)
      (list_forall₂_of_getElem (Nat.succ.inj h) fun i x y hx hy => hall (i + 1) x y hx hy)

private theorem forall₂_of_list_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → Forall₂ R l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h (forall₂_of_list_forall₂ hr)

private theorem forall₂_take_pr {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.take n) (l₂.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h ht => .cons h (forall₂_take_pr n ht)

private theorem forall₂_mem_right_pr {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons h ht, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right_pr ht b hb'
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

private theorem forall₂_level_equiv_to_lvEqList :
    ∀ {us us' : List KLevel},
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us us' →
      Core.LvEqList us us'
  | [], [], .nil => fun _ => trivial
  | _ :: _, _ :: _, .cons hu ht => fun φ => ⟨hu φ, forall₂_level_equiv_to_lvEqList ht φ⟩

private theorem wrapRel_to_wrapRelSem {find? : KKey → Option (ConstantInfo .anon)}
    {g d : KExpr} (h : WrapRel find? g d) : Decl.WrapRelSem find? g d :=
  WrapRel.rec (find? := find?)
    (motive_1 := fun a b _ => Decl.WrapRelSem find? a b)
    (motive_2 := fun a b _ => Decl.WrapDomSem find? a b)
    (bvar := fun i => .bvar i)
    (fvar := fun _ iht => .fvar iht)
    (sort := fun hu => .sort hu)
    (const := fun hus => .const (forall₂_level_equiv_to_lvEqList hus))
    (lit := fun l => .lit l)
    (app := fun _ _ ihf iha => .app ihf iha)
    (lam := fun hpw _ _ iht ihb => .lam hpw iht ihb)
    (forallE := fun hpw _ _ iht ihb => .forallE hpw iht ihb)
    (letE := fun _ _ _ iht ihv ihb => .letE iht ihv ihb)
    (proj := fun _ ihe => .proj ihe)
    (zeta := fun _ ih => .zeta ih)
    (keep := fun _ ih => .keep ih)
    (consume := fun hc _ ih => .consume hc ih)
    h

private theorem twinParts_member_data {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E E_rec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {B rb A : _root_.Address} {cb crb cA : Ixon.Constant} {ms rs rs' : Array Ixon.MutConst}
    {es : List FlatEntry} {off fuel : Nat} {ind₀ : Ixon.Inductive} {k : Nat}
    (hSS : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hE₀_rec : ∀ a c, recordOf E₀ a = some c → recordOf E_rec a = some c)
    (hE₀_blob : ∀ y b, E₀.blobs.get? y = some b → E_rec.blobs.get? y = some b)
    (hrb_muts : crb.info = .muts rs) (hA : FamRecRecord E₀ A cA rs')
    (hrs_len : rs.size = rs'.size) (hes_len : es.length = rs'.size) (hk_lt : k < rs'.size)
    (hRecFlatC : RecordFlat t E_rec rb crb rs es)
    (hRecFlatA : RecordFlat t E_rec A cA rs' es)
    (cM : CanonMemberAt calls t E_rec env B rb crb rs es off fuel ind₀ k)
    (mA : ExtractedTwinMember.{u} calls t E₀ lim B A cb cA ms rs' ind₀ k)
    (hlvls_A : mA.rc.lvls.toNat = ind₀.lvls.toNat + off)
    (hMA : MemberRecon ExprLvEq t E_rec A cA rs' es off fuel k mA.rc ∨
      MemberRecon (fun ty R => WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty)
        t E_rec A cA rs' es off fuel k mA.rc)
    (hpair :
      ExprLvEq cM.ty_ld cM.R ∨
      (MemberRecon (fun ty R => WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty)
          t E_rec A cA rs' es off fuel k mA.rc ∧
        ∃ S : _root_.Address → Prop,
          (ReconView.ofStore t E_rec).ClosedOn S ∧
          (∀ ek, es[k]? = some ek → Binding.FamilyRecon.REntryAt (ReconView.ofStore t E_rec) S ek) ∧
          (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))))
    (husedA : ∀ i ∈ usedRefIdxs cA, ∀ x, cA.refs.toList[i]? = some x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A cA x)
    (hfreshA : ∀ x, ConstAddrOf A cA x → env.find? (keyOf t x) = none)
    (hkeyA : ∀ x, ConstAddrOf A cA x → Decl.KeyFree (keyOf t x)) :
    let rulesW' : List (RecRule .anon) :=
      (mA.rls.zip cM.rulesC).map fun p =>
        { ctor := p.2.ctor
          nfields := p.2.nfields
          rhs := p.1.rhs
          ctorParams := p.2.ctorParams
          fire := p.2.fire
          k := p.2.k
          paramsBlind := p.2.paramsBlind
          eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A k)) p.2.ctor }
    let d : Decl.TwinMemberData :=
      { cvW := ⟨keyOf t (Core.rprjAddr A k), mA.ps, mA.ty₀⟩
        cvW' := ⟨keyOf t (Core.rprjAddr A k), mA.ps, mA.ty'⟩
        cvC := cM.cvC
        kC := keyOf t (Core.rprjAddr rb k)
        mI := cM.mI
        rP := cM.rP
        rulesW := mA.rules₀
        rulesW' := rulesW'
        rulesC := cM.rulesC }
    Reads t E₀ (Core.rprjAddr A k) (.recInfo d.cvW d.mI d.rP d.rulesW) ∧
    ConstantValCheckJ twinPosRulesJ env d.cvW d.cvW' ∧
    letFree d.cvW'.type = true ∧
    env.find? d.kC = some (.recInfo d.cvC d.mI d.rP d.rulesC) ∧
    d.cvW.levelParams = d.cvC.levelParams ∧
    d.rulesW.length = d.rulesW'.length ∧
    ValStored d.cvW' d.cvW ∧
    List.Forall₂ RuleStored d.rulesW' d.rulesW ∧
    (∃ DW DC, Core.piDomAt d.mI d.cvW'.type = some DW ∧ Core.piDomAt d.mI d.cvC.type = some DC ∧
      DW.getAppFn = DC.getAppFn ∧ DW.getAppArgs = DC.getAppArgs) ∧
    (∀ (f : KKey → KKey) (ws : List (TwinRecPart .anon)),
      f = Decl.twinPeerRename ws →
      (∀ w ∈ ws, w.cvW'.name = w.cvW.name) →
      (∀ (j : Nat) aC, (recAddrs rb rs)[j]? = some aC →
        ∃ aW, (recAddrs A rs')[j]? = some aW ∧ f (keyOf t aC) = keyOf t aW) →
      (∀ q, f q ≠ q → ∃ j rc, rs[j]? = some (.recr rc) ∧ q = keyOf t (memberAddr rb j (.recr rc))) →
      ((WrapRel env.find? d.cvC.type d.cvW'.type ∧
          List.Forall₂ (fun (rW' rC : RecRule .anon) => WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs)
            d.rulesW' d.rulesC) ∨
        (SymWrapT env.find? d.cvC.type d.cvW'.type ∧
          List.Forall₂ (fun (rW' rC : RecRule .anon) =>
            TwinRuleMatch env.find? f d.cvW'.type rC.rhs rW'.rhs) d.rulesW' d.rulesC)) ∧
      Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
        TwinRuleFront twinPosRulesJ env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ f d.cvW.name
          d.cvC.levelParams d.cvW' d.mI d.rP p.1 p.2 rC) (d.rulesW.zip d.rulesW') d.rulesC) ∧
    TwinMemberLoaded cA rs' ⟨k.toUInt64, A⟩ mA.rc d.cvW.levelParams d.cvW.type d.rulesW
      d.cvW' d.rulesW' ∧
    (∀ ro : Ix.Kernel.Role, d.cvW.name ≠ .role ro) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hk_es : k < es.length := by omega
  obtain ⟨ek, hek⟩ : ∃ ek, es[k]? = some ek := ⟨es[k]'hk_es, List.getElem?_eq_getElem hk_es⟩
  -- Unpack `hMA`
  have hMA_unpack : ∃ (tyW_ld R_W : KExpr) (bodiesW : List KExpr) (cbkW : Nat),
      loadedAt t (fun x => E_rec.blobs.get? x) cA (blockSelf t A rs') mA.rc.lvls.toNat
        (mutsRoot rs' k) mA.rc.typ = some tyW_ld ∧
      recTypeAt (ReconView.ofStore t E_rec) fuel es off mA.rc.params.toNat k = some R_W ∧
      (ExprLvEq tyW_ld R_W ∨
        WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R_W tyW_ld) ∧
      ruleBodiesAt (ReconView.ofStore t E_rec) fuel es off mA.rc.params.toNat mA.rc.motives.toNat
        mA.rc.minors.toNat mA.rc.lvls.toNat k (recAddrs A rs') = some bodiesW ∧
      ctorsBefore (ReconView.ofStore t E_rec) es k = some cbkW ∧
      (∀ (c : Nat) (ru : Ixon.RecursorRule), mA.rc.rules[c]? = some ru →
        ∃ rhs_ld cb_c,
          loadedAt t (fun x => E_rec.blobs.get? x) cA (blockSelf t A rs') mA.rc.lvls.toNat
            (mutsRoot rs' k + 1 + ((c : Nat) : F)) ru.rhs = some rhs_ld ∧
          bodiesW[c]? = some cb_c ∧
          RuleFollows tyW_ld mA.rc.params.toNat mA.rc.motives.toNat mA.rc.minors.toNat
            (cbkW + c) ru.fields.toNat (elimLevel off) rhs_ld cb_c) := by
    rcases hMA with h | h
    · obtain ⟨tyW, RW, bsW, cbkW, hty, hR, hrel, hb, hcb, hr⟩ := h
      exact ⟨tyW, RW, bsW, cbkW, hty, hR, Or.inl hrel, hb, hcb, hr⟩
    · obtain ⟨tyW, RW, bsW, cbkW, hty, hR, hrel, hb, hcb, hr⟩ := h
      exact ⟨tyW, RW, bsW, cbkW, hty, hR, Or.inr hrel, hb, hcb, hr⟩
  obtain ⟨tyW_ld, R_W, bodiesW, cbkW, htyW_ld, hR_W, htyW_rel, hbodiesW, hcbkW, hrulesW_mr⟩ :=
    hMA_unpack
  -- `mA.rc.params = cM.rc.params`, so `R_W = cM.R` and `cbkW = cM.cbk`
  have hparams_eq : mA.rc.params.toNat = cM.rc.params.toNat := mA.hrnp.trans cM.hrnp.symm
  have hR_eq : R_W = cM.R := by
    rw [hparams_eq] at hR_W
    exact Option.some.inj (hR_W.symm.trans cM.hR)
  subst hR_eq
  have hcbk_eq : cbkW = cM.cbk := Option.some.inj (hcbkW.symm.trans cM.hcbk)
  subst hcbk_eq
  -- `Core.posOf mA.ps mA.ty' = tyW_ld` and `mA.ps = cM.cvC.levelParams`
  have htyW_loaded : loadedAt t (fun x => E_rec.blobs.get? x) cA (blockSelf t A rs')
      mA.rc.lvls.toNat (mutsRoot rs' k) mA.rc.typ = some (Core.posOf mA.ps mA.ty') := by
    have h1 := posOf_canonAnn_eq_loadedAt mA.hps_perm mA.hty_read mA.hcanonTy
    rw [mA.hps_len] at h1
    exact Binding.FamilyFlat.loadedAt_mono hE₀_blob h1
  have htyW_eq : Core.posOf mA.ps mA.ty' = tyW_ld :=
    Option.some.inj (htyW_loaded.symm.trans htyW_ld)
  have hlvls_eq : mA.rc.lvls.toNat = cM.rc.lvls.toNat := hlvls_A.trans cM.hlvls_eq.symm
  have hlps_eq : mA.ps = cM.cvC.levelParams := by
    rw [mA.hps_eq, cM.hcvC_lps, hlvls_eq]
  have hperm_C : cM.cvC.levelParams.Perm (List.range cM.cvC.levelParams.length) := by
    rw [← hlps_eq]; exact mA.hps_perm
  -- Extract `self : IndData` for `ek.addr` from `cM.hR`
  have hself_ex : ∃ self : IndData, (ReconView.ofStore t E_rec).ind ek.addr = some (some self) := by
    have hR' := cM.hR
    unfold recTypeAt at hR'
    cases h0 : es[0]? with
    | none => simp [h0] at hR'
    | some e0 =>
      simp only [h0, hek] at hR'
      cases h1 : (ReconView.ofStore t E_rec).ind e0.addr with
      | none => simp [h1] at hR'
      | some o1 =>
        cases o1 with
        | none => simp [h1] at hR'
        | some prim =>
          cases h2 : (ReconView.ofStore t E_rec).ind ek.addr with
          | none => simp [h1, h2] at hR'
          | some o2 =>
            cases ho2 : o2 with
            | none => simp [h1, h2, ho2] at hR'
            | some self => exact ⟨self, rfl⟩
  obtain ⟨self, hself⟩ := hself_ex
  obtain ⟨c_ek, p_ek, cb_ek, ms_ek, ind_ek, hc_ek, hci_ek, hcb_ek, hcbm_ek, hms_ek,
    ha_maj_eq, hindM_eq, hp_maj_eq, hself_np, hself_ni, hself_nctors, hself_blk, hself_idx,
    hni_W_self⟩ :=
    extracted_maj_eq_indData hroles hE₀_rec hE₀_blob hRecFlatA mA hek hself
  -- Unpack `recTypeAt_majorDom_info`
  obtain ⟨depthR, nMinR, domR, conclR, mR, hdepthR_le, hpeelR, hncR, hfnR, hauxF, hauxT⟩ :=
    recTypeAt_majorDom_info cM.hR hek hself
  have hpeelR_succ : peelForalls (depthR + 1) cM.R = some conclR := by
    rw [peelForalls_add, hpeelR]; rfl
  -- Compare `depthR`, `mI_W`, `cM.mI`, `indices`, `motives`, `minors`, `rP`
  let mI_W := mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat + mA.rc.indices.toNat
  let rP_W := mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat
  have hdepth_mIW : depthR = mI_W := by
    obtain ⟨bsW, conclW, hsW, hncW⟩ := mA.hmotiveConcl
    have hpW : peelForalls (mI_W + 1) tyW_ld = some conclW := by
      rw [← htyW_eq]; exact (stripPis_iff_peelForalls _ _ _).mpr ⟨bsW, hsW⟩
    rcases htyW_rel with hlv | hobs
    · exact Nat.succ.inj (peelForalls_max_eq_of_exprLvEq hlv.symm hpeelR_succ hncR hpW hncW)
    · exact Nat.succ.inj (WrapConsObs.peelForalls_max_eq hobs hpeelR_succ hncR hpW hncW)
  have hdepth_mIC : depthR = cM.mI := by
    obtain ⟨bsC, conclC, hsC, hncC⟩ := cM.hmotiveConcl
    have hpC : peelForalls (cM.mI + 1) cM.ty_ld = some conclC := by
      rw [← cM.hty_pos]; exact (stripPis_iff_peelForalls _ _ _).mpr ⟨bsC, hsC⟩
    rcases cM.hty_rel with hlv | ⟨hobs, -⟩
    · exact Nat.succ.inj (peelForalls_max_eq_of_exprLvEq hlv.symm hpeelR_succ hncR hpC hncC)
    · exact Nat.succ.inj (WrapConsObs.peelForalls_max_eq hobs hpeelR_succ hncR hpC hncC)
  have hmI_eq : mI_W = cM.mI := hdepth_mIW.symm.trans hdepth_mIC
  have hni_C_self : cM.rc.indices.toNat = self.ni := cM.hni_eq ek self hek hself
  have hni_eq : mA.rc.indices.toNat = cM.rc.indices.toNat := hni_W_self.trans hni_C_self.symm
  have hmot_eq : mA.rc.motives.toNat = cM.rc.motives.toNat := by
    rw [mA.hnmot, cM.hnmot, hrs_len]
  have hmin_eq : mA.rc.minors.toNat = cM.rc.minors.toNat := by
    have := cM.hmI_def
    dsimp only [mI_W] at hmI_eq
    omega
  have hrP_eq : rP_W = cM.rP := by
    have := cM.hrP_def
    dsimp only [rP_W]
    omega
  have hnMin_le : cM.rc.minors.toNat ≤ nMinR := by
    have := cM.hmI_def
    have := cM.hnmot
    omega
  have hshift_eq : mA.rc.motives.toNat + mA.rc.minors.toNat + mA.rc.indices.toNat =
      cM.rc.motives.toNat + cM.rc.minors.toNat + cM.rc.indices.toNat := by omega
  -- `RecordFlat` on `A` and `rb`
  obtain ⟨tyW_rf, dW_pos, htyW_rf, hbdW_rf, hfnW_rf, hauxW_rf⟩ := hRecFlatA k mA.rc ek mA.hmem hek
  have htyW_rf_eq : tyW_rf = tyW_ld := Option.some.inj (htyW_rf.symm.trans htyW_ld)
  subst tyW_rf
  obtain ⟨tyC_rf, dC_pos, htyC_rf, hbdC_rf, hfnC_rf, hauxC_rf⟩ := hRecFlatC k cM.rc ek cM.hmem hek
  have htyC_rf_eq : tyC_rf = cM.ty_ld := Option.some.inj (htyC_rf.symm.trans cM.hty_ld)
  subst tyC_rf
  -- Identify `cM`'s rules count and constructors from `cM.hrecReads`
  have hcM_rules_info : cM.rc.rules.size = ind_ek.ctors.size ∧
      (∀ (c : Nat) (rC₀ : RecRule .anon), cM.rulesC₀[c]? = some rC₀ →
        rC₀.ctor = keyOf t (ctorAddr p_ek.block p_ek.idx.toNat c)) ∧
      (∀ (c : Nat) (ru : Ixon.RecursorRule) (rC₀ : RecRule .anon),
        cM.rc.rules[c]? = some ru → cM.rulesC₀[c]? = some rC₀ →
        rC₀.nfields = ru.fields.toNat) := by
    obtain ⟨tyP_c, ty₀_c, _, kM_c, _, Bm_c, _, iM_c, _, indM_c, ps_c, rules₀_c, htyP_c, _, _,
      hmajK_c, hindM_c, hps_c, hty_c, hrls_sz_c, hrules_rr_c, hci_c⟩ := cM.hrecReads
    injection hci_c with hcv_c _ _ hrl_c
    have hps_c_perm : ps_c.Perm (List.range ps_c.length) := by
      rw [hps_c]; exact Decl.recLps_perm_range _ _
    have hVS_c := cM.hstored.1
    have hcvC_lps_c : cM.cvC.levelParams = ps_c := by
      have h1 : cM.cvC.levelParams = cM.cvC₀.levelParams := hVS_c.2.1
      rw [h1, hcv_c]
    have hty_pos_c : Core.posOf ps_c ty₀_c = tyP_c :=
      Except.ok.inj ((exprReader_posOf hps_c_perm hty_c).symm.trans htyP_c)
    have hmaj_cvC : majorKey cM.rc cM.ty_ld = some kM_c := by
      rw [← cM.hty_pos, hcvC_lps_c]
      have hann : Annotates cM.cvC.type cM.cvC₀.type := hVS_c.2.2
      rw [hcv_c] at hann
      exact majorKey_of_annotates_pr (by rwa [← hty_pos_c] at hmajK_c)
        (annotates_instantiateLevelParams_pr _ _ hann)
    have hmaj_rf : majorKey cM.rc cM.ty_ld = some (keyOf t ek.addr) := by
      unfold majorKey binderDom headKey
      unfold binderDomAfter at hbdC_rf
      cases hp : peelForalls (cM.rc.params.toNat + cM.rc.motives.toNat + cM.rc.minors.toNat +
          cM.rc.indices.toNat) cM.ty_ld with
      | none => simp [hp] at hbdC_rf
      | some r =>
        rw [hp] at hbdC_rf
        cases r with
        | forallE d b m =>
          simp only [Option.some.injEq] at hbdC_rf; subst hbdC_rf
          obtain ⟨bs, hs⟩ := (stripPis_iff_peelForalls _ _ _).mp hp
          rw [hs, Option.bind_some, hfnC_rf]
        | _ => simp at hbdC_rf
    have hkM_eq : kM_c = keyOf t ek.addr := Option.some.inj (hmaj_cvC.symm.trans hmaj_rf)
    obtain ⟨aC, cC, pC, cbC, msC, hkC, hrecC, hiC, hpCb, hpCi, hcbC, hcbmC, hmsC, -, -, -⟩ := hindM_c
    have haC_eq : aC = ek.addr := keyOf_inj hroles (hkC.symm.trans hkM_eq)
    subst aC
    have hcC_eq : cC = c_ek := Option.some.inj (hrecC.symm.trans hc_ek)
    subst cC
    have hpC_eq : pC = p_ek := Ixon.ConstantInfo.iPrj.inj (hiC.symm.trans hci_ek)
    subst pC
    have hcbC' : recordOf E_rec p_ek.block = some cbC := by rwa [hpCb] at hcbC
    have hcbC_eq : cbC = cb_ek := Option.some.inj (hcbC'.symm.trans hcb_ek)
    subst cbC
    have hmsC_eq : msC = ms_ek := Ixon.ConstantInfo.muts.inj (hcbmC.symm.trans hcbm_ek)
    subst msC
    have hindC_eq : indM_c = ind_ek := by
      rw [hpCi] at hmsC
      exact Ixon.MutConst.indc.inj (Option.some.inj (hmsC.symm.trans hms_ek))
    subst indM_c
    refine ⟨hrls_sz_c, fun c rC₀ hrC₀ => ?_, fun c ru rC₀ hru hrC₀ => ?_⟩
    · rw [hrl_c] at hrC₀
      have h1 := ruleReads_ctor_eq hrules_rr_c c rC₀ hrC₀
      simpa [hpCb, hpCi] using h1
    · rw [hrl_c] at hrC₀
      have hrr_nf : List.Forall₂ (fun (ru : Ixon.RecursorRule) (rl : RecRule .anon) =>
          rl.nfields = ru.fields.toNat) cM.rc.rules.toList rules₀_c :=
        lforall₂_of_zipIdx (fun _ _ h => by
          obtain ⟨rhs, -, hrl⟩ := h; subst hrl; rfl) hrules_rr_c
      have hruL : cM.rc.rules.toList[c]? = some ru := by rwa [Array.getElem?_toList]
      exact forall₂_getElem? hrr_nf c ru rC₀ hruL hrC₀
  -- Identify `mA`'s rules constructors from `mA.hrecReads`
  have hmA_rules_ctor : ∀ (c : Nat) (rW : RecRule .anon), mA.rules₀[c]? = some rW →
      rW.ctor = keyOf t (ctorAddr p_ek.block p_ek.idx.toNat c) := by
    obtain ⟨tyP_a, ty₀_a, _, kM_a, _, Bm_a, _, iM_a, _, indM_a, ps_a, rules₀_a, htyP_a, _, _,
      hmajK_a, hindM_a, hps_a, hty_a, -, hrules_rr_a, hci_a⟩ := mA.hrecReads
    rw [mA.hci₀] at hci_a
    injection hci_a with hcv_a _ _ hrl_a
    injection hcv_a with _ hps_a_eq hty₀_a_eq
    rw [← hps_a_eq, ← hty₀_a_eq] at hty_a
    have hty_pos_a : Core.posOf mA.ps mA.ty₀ = tyP_a :=
      Except.ok.inj ((exprReader_posOf mA.hps_perm hty_a).symm.trans htyP_a)
    have hkM_a_eq : kM_a = keyOf t ek.addr := by
      rw [← hty_pos_a] at hmajK_a
      have h1 := Option.some.inj (hmajK_a.symm.trans mA.hmajKey)
      rw [ha_maj_eq] at h1; exact h1
    obtain ⟨aA, cA1, pA, cbA, msA, hkA, hrecA, hiA, hpAb, hpAi, hcbA, hcbmA, -, -, -, -⟩ := hindM_a
    have haA_eq : aA = ek.addr := keyOf_inj hroles (hkA.symm.trans hkM_a_eq)
    subst aA
    have hcA1_eq : cA1 = c_ek := Option.some.inj ((hE₀_rec _ _ hrecA).symm.trans hc_ek)
    subst cA1
    have hpA_eq : pA = p_ek := Ixon.ConstantInfo.iPrj.inj (hiA.symm.trans hci_ek)
    subst pA
    intro c rW hrW
    rw [hrl_a] at hrW
    have h1 := ruleReads_ctor_eq hrules_rr_a c rW hrW
    simpa [hpAb, hpAi] using h1
  -- Rule lengths all agree
  have hrules_size_eq : mA.rc.rules.size = cM.rc.rules.size := by
    rw [mA.hrules_size, hindM_eq, hcM_rules_info.1]
  have hrls_len_A : mA.rls.length = mA.rc.rules.size := by
    rw [canonRules_length mA.hcanonRules, Array.length_toList]
  have hrules₀_len_A : mA.rules₀.length = mA.rc.rules.size := by
    rw [← mA.hrules_read.length_eq, Array.length_toList]
  have hrulesC_len : cM.rulesC.length = cM.rc.rules.size := cM.hrules_len
  -- `rulesW'` definition and length
  let rulesW' : List (RecRule .anon) :=
    (mA.rls.zip cM.rulesC).map fun p =>
      { ctor := p.2.ctor
        nfields := p.2.nfields
        rhs := p.1.rhs
        ctorParams := p.2.ctorParams
        fire := p.2.fire
        k := p.2.k
        paramsBlind := p.2.paramsBlind
        eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A k)) p.2.ctor }
  have hrulesW'_len : rulesW'.length = cM.rulesC.length := by
    dsimp only [rulesW']
    rw [List.length_map, List.length_zip]
    omega
  -- Per-rule agreement: `rC.ctor = rW.ctor` and `rC.nfields = ru_A.fields.toNat = rW.nfields = ru_C.fields.toNat`
  have hrule_match : ∀ (c : Nat) (ruA ruC : Ixon.RecursorRule) (rW rlA rC : RecRule .anon),
      mA.rc.rules[c]? = some ruA → cM.rc.rules[c]? = some ruC →
      mA.rules₀[c]? = some rW → mA.rls[c]? = some rlA → cM.rulesC[c]? = some rC →
      rC.ctor = rW.ctor ∧
      rC.nfields = rW.nfields ∧
      ruA.fields.toNat = rC.nfields ∧
      ruA.fields.toNat = ruC.fields.toNat ∧
      rlA.nfields = rW.nfields ∧
      Annotates rlA.rhs rW.rhs := by
    intro c ruA ruC rW rlA rC hruA hruC hrW hrlA hrC
    have hc_lt_C₀ : c < cM.rulesC₀.length := by
      rw [← cM.hstored.2.2.2.length_eq]; exact (List.getElem?_eq_some_iff.mp hrC).1
    obtain ⟨rC₀, hrC₀⟩ : ∃ r, cM.rulesC₀[c]? = some r :=
      ⟨cM.rulesC₀[c]'hc_lt_C₀, List.getElem?_eq_getElem hc_lt_C₀⟩
    have hrsC := forall₂_getElem? cM.hstored.2.2.2 c rC rC₀ hrC hrC₀
    have hctorC : rC.ctor = keyOf t (ctorAddr p_ek.block p_ek.idx.toNat c) :=
      hrsC.1.trans (hcM_rules_info.2.1 c rC₀ hrC₀)
    have hctorW : rW.ctor = keyOf t (ctorAddr p_ek.block p_ek.idx.toNat c) :=
      hmA_rules_ctor c rW hrW
    have hctor_eq : rC.ctor = rW.ctor := hctorC.trans hctorW.symm
    have hrC_mem : rC ∈ cM.rulesC := List.mem_of_getElem? hrC
    have hrc_ok := hinv.store.store.rec_ctors _ _ _ _ _ cM.hfind _ hrC_mem
    obtain ⟨⟨cvj, hfind_ctor, -, -, -, -⟩, -⟩ := hrc_ok
    have hctor_cprj : ctorAddr p_ek.block p_ek.idx.toNat c =
        Core.cprjAddr mA.p_maj.block mA.p_maj.idx.toNat c := by
      rw [hp_maj_eq]; rfl
    rw [hctorC, hctor_cprj] at hfind_ctor
    have hnfA : ruA.fields.toNat = rC.nfields :=
      mA.hrule_nfields E env hSS hinv c ruA hruA cvj rC.ctorParams rC.nfields hfind_ctor
    have hruAL : mA.rc.rules.toList[c]? = some ruA := by rwa [Array.getElem?_toList]
    have hnfW : rW.nfields = ruA.fields.toNat :=
      (forall₂_getElem? mA.hrules_read c ruA rW hruAL hrW).1
    have hnfC : rC.nfields = ruC.fields.toNat :=
      hrsC.2.1.trans (hcM_rules_info.2.2 c ruC rC₀ hruC hrC₀)
    have hrsA := forall₂_getElem? mA.hruleStored c rlA rW hrlA hrW
    exact ⟨hctor_eq, hnfA.symm.trans hnfW.symm, hnfA, hnfA.trans hnfC, hrsA.2.1, hrsA.2.2⟩
  -- `List.Forall₂ RuleStored rulesW' mA.rules₀`
  have hrulesW'_stored : List.Forall₂ RuleStored rulesW' mA.rules₀ := by
    refine list_forall₂_of_getElem (by omega) fun c rW' rW hrW' hrW => ?_
    have hc_lt : c < mA.rc.rules.size := by
      have := (List.getElem?_eq_some_iff.mp hrW).1; omega
    obtain ⟨ruA, hruA⟩ : ∃ r, mA.rc.rules[c]? = some r :=
      ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
    obtain ⟨ruC, hruC⟩ : ∃ r, cM.rc.rules[c]? = some r :=
      ⟨cM.rc.rules[c]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨rlA, hrlA⟩ : ∃ r, mA.rls[c]? = some r :=
      ⟨mA.rls[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨rC, hrC⟩ : ∃ r, cM.rulesC[c]? = some r :=
      ⟨cM.rulesC[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hrW'_eq : rW' =
        { ctor := rC.ctor, nfields := rC.nfields, rhs := rlA.rhs,
          ctorParams := rC.ctorParams, fire := rC.fire, k := rC.k,
          paramsBlind := rC.paramsBlind,
          eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A k)) rC.ctor } := by
      dsimp only [rulesW'] at hrW'
      rw [List.getElem?_map, list_getElem?_zip, hrlA, hrC] at hrW'
      exact (Option.some.inj hrW').symm
    obtain ⟨hct, hnf, -, -, -, hann⟩ := hrule_match c ruA ruC rW rlA rC hruA hruC hrW hrlA hrC
    rw [hrW'_eq]
    exact ⟨hct, hnf, hann⟩
  -- `hxA_k` and `ConstantValCheckJ` for `mA`
  have hxA_k : ConstAddrOf A cA (Core.rprjAddr A k) :=
    Or.inr ⟨rs', k, .recr mA.rc, hA.muts, mA.hmem, Or.inl (memberAddr_recr_eq A k mA.rc).symm⟩
  have hfront_A : ConstantValCheckJ twinPosRulesJ env
      ⟨keyOf t (Core.rprjAddr A k), mA.ps, mA.ty₀⟩
      ⟨keyOf t (Core.rprjAddr A k), mA.ps, mA.ty'⟩ :=
    mA.hfrontDoor E env hSS hinv husedA (hfreshA _ hxA_k) (hkeyA _ hxA_k)
  have ⟨hmA_ty'_lpd, hmA_ty'_cr⟩ :
      mA.ty'.allLevelParamsDefined mA.ps = true ∧ mA.ty'.constsResolve env = true := by
    obtain ⟨ty_f, hrun_f, hcv_f⟩ := hfront_A
    have hty_f_eq : ty_f = mA.ty' := by
      have := congrArg ConstantVal.type hcv_f; simpa using this.symm
    rw [hty_f_eq] at hrun_f
    exact ⟨hrun_f.2.2.2.2.2.2.2.1, hrun_f.2.2.2.2.2.2.2.2.1⟩
  have hlf_tyW_ld : letFree tyW_ld = true := by
    rw [← htyW_eq]
    unfold Core.posOf
    rw [letFree_instantiateLevelParams]
    exact mA.hty'_letFree
  -- `WrapRel env.find? cM.ty_ld tyW_ld` or `(SymWrapT env.find? cM.ty_ld tyW_ld ∧ ctorsBefore total)`
  have hty_rel_pos :
      WrapRel env.find? cM.ty_ld tyW_ld ∨
      (SymWrapT env.find? cM.ty_ld tyW_ld ∧
        ctorsBefore (ReconView.ofStore t E_rec) es es.length = some cM.rc.minors.toNat) := by
    have hcr_cvC : cM.cvC.type.constsResolve env = true :=
      (hinv.store.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem cM.hfind)).2.2.1
    have hcr_tyC : cM.ty_ld.constsResolve env = true := by
      rw [← cM.hty_pos]
      unfold Core.posOf
      rw [constsResolve_instantiateLevelParams]
      exact hcr_cvC
    have hcr_tyW : tyW_ld.constsResolve env = true := by
      rw [← htyW_eq]
      unfold Core.posOf
      rw [constsResolve_instantiateLevelParams]
      exact hmA_ty'_cr
    rcases hpair with hC_lv | ⟨hMA_obs, -⟩
    · left
      rcases htyW_rel with hW_lv | hW_obs
      · exact Binding.FamilyRecon.exprLvEq_wrapRel env.find? (hC_lv.trans hW_lv.symm)
      · have hcr_R : cM.R.constsResolve env = true := by
          rw [← constsResolve_of_exprLvEq hC_lv]; exact hcr_tyC
        have hwr := hW_obs.toWrapRel
          (fun w n hres hobs => wrapperArity_of_observed hSS hinv hres hobs) hcr_R
        exact wrapRel_congr_exprLvEq_left hC_lv hwr
    · obtain ⟨tyW2, RW2, _, _, htyW2, hRW2, hW_obs2, -, -, -⟩ := hMA_obs
      have htyW2_eq : tyW2 = tyW_ld := Option.some.inj (htyW2.symm.trans htyW_ld)
      have hRW2_eq : RW2 = cM.R := by
        rw [hparams_eq] at hRW2; exact Option.some.inj (hRW2.symm.trans cM.hR)
      subst htyW2_eq hRW2_eq
      rcases cM.hty_rel with hC_lv | ⟨hC_obs, hlf_tyC, htot_C, -⟩
      · left
        have hcr_R : cM.R.constsResolve env = true := by
          rw [← constsResolve_of_exprLvEq hC_lv]; exact hcr_tyC
        have hwr := hW_obs2.toWrapRel
          (fun w n hres hobs => wrapperArity_of_observed hSS hinv hres hobs) hcr_R
        exact wrapRel_congr_exprLvEq_left hC_lv hwr
      · right
        exact ⟨WrapConsObs.toSymWrapT
          (fun w n hres hobs => wrapperArity_of_observed hSS hinv hres hobs)
          hC_obs hW_obs2 hcr_tyC hcr_tyW hlf_tyC hlf_tyW_ld, htot_C⟩
  -- Major-premise syntactic equality (`dW_pos` vs `dC_pos` and `DW` vs `DC`)
  have hbdR : binderDomAfter depthR cM.R = some domR := by
    unfold binderDomAfter; rw [hpeelR]
  have hdW_rel : ExprLvEq domR dW_pos ∨
      WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) domR dW_pos :=
    exprLvEq_of_wrapConsObs_or_eq_dom htwf hc_ek hci_ek
      (by rwa [hdepth_mIW] at hbdR) hbdW_rf hfnR htyW_rel
  have hdC_rel : ExprLvEq domR dC_pos ∨
      WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) domR dC_pos := by
    have hrel' : ExprLvEq cM.ty_ld cM.R ∨
        WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) cM.R cM.ty_ld := by
      rcases cM.hty_rel with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    exact exprLvEq_of_wrapConsObs_or_eq_dom htwf hc_ek hci_ek
      (by rwa [hdepth_mIC, cM.hmI_def] at hbdR) hbdC_rf hfnR hrel'
  have hlen_dW : dW_pos.getAppArgs.length = domR.getAppArgs.length := by
    rcases hdW_rel with h | h
    · exact (exprLvEq_getAppArgs h).length_eq.symm
    · exact (WrapConsObs.getAppArgs h).length_eq.symm
  have hlen_dC : dC_pos.getAppArgs.length = domR.getAppArgs.length := by
    rcases hdC_rel with h | h
    · exact (exprLvEq_getAppArgs h).length_eq.symm
    · exact (WrapConsObs.getAppArgs h).length_eq.symm
  have hdW_eq_dC : dW_pos.getAppFn = dC_pos.getAppFn ∧ dW_pos.getAppArgs = dC_pos.getAppArgs := by
    cases haux : ek.aux with
    | false =>
      obtain ⟨-, hbR⟩ := hauxF haux
      have haW : dW_pos.getAppArgs = domR.getAppArgs := by
        rcases hdW_rel with h | h
        · exact exprLvEq_eq_args_of_bvars h hbR
        · exact wrapConsObs_eq_args_of_bvars h hbR
      have haC : dC_pos.getAppArgs = domR.getAppArgs := by
        rcases hdC_rel with h | h
        · exact exprLvEq_eq_args_of_bvars h hbR
        · exact wrapConsObs_eq_args_of_bvars h hbR
      exact ⟨hfnW_rf.trans hfnC_rf.symm, haW.trans haC.symm⟩
    | true =>
      obtain ⟨hlenR, hdropR, hnoR⟩ := hauxT haux
      have hb_drop : ∀ a ∈ domR.getAppArgs.drop ek.params.length, ∃ i, a = .bvar i := by
        intro a ha
        rw [hdropR] at ha
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
        exact ⟨_, rfl⟩
      have hdropW : dW_pos.getAppArgs.drop ek.params.length =
          (List.range self.ni).map (fun i => .bvar (self.ni - 1 - i)) := by
        rw [← hdropR]
        rcases hdW_rel with h | h
        · exact exprLvEq_drop_eq_of_bvars h hb_drop
        · exact wrapConsObs_drop_eq_of_bvars h hb_drop
      have hdropC : dC_pos.getAppArgs.drop ek.params.length =
          (List.range self.ni).map (fun i => .bvar (self.ni - 1 - i)) := by
        rw [← hdropR]
        rcases hdC_rel with h | h
        · exact exprLvEq_drop_eq_of_bvars h hb_drop
        · exact wrapConsObs_drop_eq_of_bvars h hb_drop
      let shift := cM.rc.motives.toNat + cM.rc.minors.toNat + cM.rc.indices.toNat
      have hlowC : (dC_pos.getAppArgs.take ek.params.length).map (Expr.lowerBVars shift 0) =
          ek.params := hauxC_rf haux
      have hlowW : (dW_pos.getAppArgs.take ek.params.length).map (Expr.lowerBVars shift 0) =
          ek.params := by
        have h1 := hauxW_rf haux
        rwa [hshift_eq] at h1
      have hnoW : ∀ P ∈ dW_pos.getAppArgs.take ek.params.length, hasBVarIn 0 shift P = false := by
        obtain ⟨_, inp, bs, dom, body, mmaj, _, As, hstrip, -, hargs, hAs_len, -, hno⟩ :=
          mA.hmajorPins
        have hpeel : peelForalls mI_W tyW_ld = some (.forallE dom body mmaj) := by
          rw [← htyW_eq]; exact (stripPis_iff_peelForalls _ _ _).mpr ⟨bs, hstrip⟩
        have hd_eq : dom = dW_pos := by
          have h := hbdW_rf; unfold binderDomAfter at h; rw [hpeel] at h
          exact Option.some.inj h
        subst hd_eq
        rw [hargs] at hlen_dW ⊢
        have hinp : inp = ek.params.length := by omega
        subst hinp
        intro P hP
        have := hno P hP
        rwa [hshift_eq] at this
      have hnoC : ∀ P ∈ dC_pos.getAppArgs.take ek.params.length, hasBVarIn 0 shift P = false := by
        rcases cM.hty_rel with hC_lv | ⟨-, -, -, hpinsC⟩
        · have hd_lv : ExprLvEq domR dC_pos := by
            obtain ⟨dR', hR', hd⟩ := exprLvEq_binderDomAfter hC_lv hbdC_rf
            have heq : dR' = domR := Option.some.inj (hR'.symm.trans (by rwa [hdepth_mIC, cM.hmI_def] at hbdR))
            subst heq; exact hd.symm
          have hf2 := forall₂_take_pr ek.params.length (exprLvEq_getAppArgs hd_lv)
          intro P hP
          obtain ⟨P₀, hP₀, hlvP⟩ := forall₂_mem_right_pr hf2 P hP
          rw [← hasBVarIn_eq_of_exprLvEq hlvP]
          have hsh_le : shift ≤ es.length + nMinR + self.ni := by
            have := cM.hnmot; dsimp only [shift]; omega
          exact hasBVarIn_mono_hi hsh_le P₀ (hnoR P₀ hP₀)
        · exact hpinsC dC_pos ek.params.length (by rw [cM.hmI_def]; exact hbdC_rf)
            (by omega)
      exact majorDom_pos_eq_of_pins hfnC_rf hfnW_rf (by omega) (by omega)
        hdropC hdropW hlowC hlowW hnoC hnoW
  have hmaj_dom : ∃ DW DC, Core.piDomAt cM.mI mA.ty' = some DW ∧
      Core.piDomAt cM.mI cM.cvC.type = some DC ∧
      DW.getAppFn = DC.getAppFn ∧ DW.getAppArgs = DC.getAppArgs := by
    have hC_bd : binderDomAfter cM.mI (Core.posOf cM.cvC.levelParams cM.cvC.type) = some dC_pos := by
      rw [cM.hty_pos, cM.hmI_def]; exact hbdC_rf
    have hW_bd : binderDomAfter cM.mI (Core.posOf cM.cvC.levelParams mA.ty') = some dW_pos := by
      rw [← hlps_eq, htyW_eq, ← hmI_eq]; exact hbdW_rf
    exact majorDom_of_posOf_perm hperm_C hC_bd hW_bd hdW_eq_dC.1 hdW_eq_dC.2
  -- Unconditional `hnp_match` for `ruleBodiesAt_renameConsts_of_recTypeAt`
  have hnp_match : ∀ (ek' : FlatEntry) (self' : IndData), es[k]? = some ek' →
      (ReconView.ofStore t E_rec).ind ek'.addr = some (some self') →
      ∀ c cty np, c < self'.nctors →
        (ReconView.ofStore t E_rec).ctor self'.blk self'.idx c = some (cty, np) →
        (ek'.aux = false → np = cM.rc.params.toNat) ∧ (ek'.aux = true → np ≤ ek'.params.length) := by
    intro ek' self' hek' hself' c cty np hc hctor
    have hek_eq : ek' = ek := Option.some.inj (hek'.symm.trans hek)
    subst ek'
    have hself_eq : self' = self := Option.some.inj (Option.some.inj (hself'.symm.trans hself))
    subst self'
    have hctor' := hctor
    simp only [ReconView.ofStore, Binding.FamilyRecon.ctorAt, hself_blk, hself_idx,
      hcb_ek, hcbm_ek, hms_ek] at hctor'
    cases hct : ind_ek.ctors[c]? with
    | none => simp [hct] at hctor'
    | some ct =>
      simp only [hct] at hctor'
      cases hldc : loadedAt t (fun x => E_rec.blobs.get? x) cb_ek (blockSelf t p_ek.block ms_ek)
          ct.lvls.toNat (mutsRoot ms_ek p_ek.idx.toNat + 1 + ((c : Nat) : F)) ct.typ with
      | none => rw [hldc] at hctor'; cases hctor'
      | some ty_c =>
        rw [hldc] at hctor'
        simp only [Option.some.injEq, Prod.mk.injEq] at hctor'
        have hnp_ct : np = ct.params.toNat := hctor'.2.symm
        have hct_ind : ct.params.toNat = ind_ek.params.toNat := by
          have := mA.hctor_params c ct (by rw [hindM_eq]; exact hct)
          rwa [hindM_eq] at this
        -- Also `dW_pos.getAppArgs.length = ind_ek.params.toNat + self.ni` from `mA.hmajor_np`
        have hdW_np : dW_pos.getAppArgs.length = ind_ek.params.toNat + self.ni := by
          unfold binderDomAfter at hbdW_rf
          cases hp : peelForalls (mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat +
              mA.rc.indices.toNat) tyW_ld with
          | none => rw [hp] at hbdW_rf; cases hbdW_rf
          | some r =>
            rw [hp] at hbdW_rf
            cases r with
            | forallE d b m =>
              simp only [Option.some.injEq] at hbdW_rf; subst d
              rw [← htyW_eq] at hp
              obtain ⟨bs, hs⟩ := (stripPis_iff_peelForalls _ _ _).mp hp
              have h1 := mA.hmajor_np bs dW_pos b m hs
              rw [hindM_eq, hni_W_self] at h1
              exact h1
            | _ => cases hbdW_rf
        constructor
        · intro haux
          have hlenR := (hauxF haux).1
          omega
        · intro haux
          have hlenR := (hauxT haux).1
          omega
  -- `k.toUInt64.toNat = k` (since `k < rs'.size = mA.rc.motives.toNat < UInt64.size`)
  have hk_u64 : (⟨k.toUInt64, A⟩ : Ixon.RecursorProj).idx.toNat = k := by
    have hlt : k < UInt64.size := by
      have h1 := mA.rc.motives.toBitVec.isLt
      have h2 := mA.hnmot
      change mA.rc.motives.toNat < UInt64.size at h1
      omega
    change (UInt64.ofNat k).toNat = k
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hlt
  -- Assemble all 12 conjuncts
  refine ⟨?_, hfront_A, mA.hty'_letFree, cM.hfind, hlps_eq,
    by change mA.rules₀.length = rulesW'.length; omega, mA.hvalStored,
    hrulesW'_stored, hmaj_dom, ?_, ?_, mA.hnoRole⟩
  · -- 1. `Reads`
    have h := mA.hreads
    rw [mA.hci₀] at h
    have h1 : mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat + mA.rc.indices.toNat =
        cM.mI := hmI_eq
    have h2 : mA.rc.params.toNat + mA.rc.motives.toNat + mA.rc.minors.toNat = cM.rP := hrP_eq
    rw [h1, h2] at h
    exact h
  · -- 10. Rules block for any coherent `(f, ws)`
    intro f ws hf_eq hws_name hpeers hmove
    -- `cM.ty_ld.renameConsts f = cM.ty_ld`
    have htyC_fix : cM.ty_ld.renameConsts f = cM.ty_ld := by
      refine renameConsts_eq_self_of_not_mentions cM.ty_ld fun q hfq => ?_
      obtain ⟨j, rcj, hj, rfl⟩ := hmove q hfq
      have hj_lt : j < rs.size := by
        cases hj' : rs[j]? with
        | none => rw [hj'] at hj; cases hj
        | some _ =>
          by_contra hge
          have hge' : rs.size ≤ j := Nat.le_of_not_lt hge
          rw [Array.getElem?_eq_none hge'] at hj'
          cases hj'
      have hno := cM.hnoSelf j hj_lt
      rw [memberAddr_recr_eq, ← cM.hty_pos, mentionsConst_posOf]
      exact hno
    -- `bodiesW = cM.bodies.map (Expr.renameConsts f)`
    have hbodies_eq : bodiesW = cM.bodies.map (Expr.renameConsts f) := by
      have hbodies_rename : ruleBodiesAt (ReconView.ofStore t E_rec) fuel es off
          cM.rc.params.toNat cM.rc.motives.toNat cM.rc.minors.toNat cM.rc.lvls.toNat k
          (recAddrs A rs') = some (cM.bodies.map (Expr.renameConsts f)) := by
        rcases hpair with hC_lv | ⟨-, S, hS_cl, hS_ent, hS_excl⟩
        · refine ruleBodiesAt_renameConsts_of_recTypeAt (V := ReconView.ofStore t E_rec)
            hpeers cM.hR (fun q hfq => ?_) hnp_match cM.hbodies
          obtain ⟨j, rcj, hj, rfl⟩ := hmove q hfq
          have hj_lt : j < rs.size := by
            by_contra hge
            rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hj; cases hj
          have hno := cM.hnoSelf j hj_lt
          rw [memberAddr_recr_eq, ← mentionsConst_of_exprLvEq hC_lv, ← cM.hty_pos, mentionsConst_posOf]
          exact hno
        · refine ruleBodiesAt_renameConsts_of_closed (V := ReconView.ofStore t E_rec)
            hS_cl hpeers (fun q hfq => ?_) hS_ent cM.hbodies
          obtain ⟨j, rcj, hj, rfl⟩ := hmove q hfq
          exact ⟨memberAddr rb j (.recr rcj), Binding.FamilyFlat.keyAddr_keyOf htwf _,
            hS_excl j rcj hj⟩
      rw [hparams_eq, hmot_eq, hmin_eq, hlvls_eq] at hbodiesW
      exact Option.some.inj (hbodiesW.symm.trans hbodies_rename)
    have hrr_readA : List.Forall₂ (fun ru rl₀ =>
        (exprReader t (fun x => E₀.blobs.get? x) cA (Ix.Kernel.Reader.recParam mA.ps)
          (blockSelf t A rs')).read ru.rhs = .ok rl₀.rhs) mA.rc.rules.toList mA.rules₀ :=
      List.Forall₂.imp (fun _ _ h => h.2.1) mA.hrules_read
    -- Per-rule comparison (`WrapRel` on `Or.inl`, `TwinRuleMatch` on `Or.inr`)
    have hrule_rel_at : ∀ (c : Nat) (ruA ruC : Ixon.RecursorRule) (rW rlA rC rW' : RecRule .anon),
        mA.rc.rules[c]? = some ruA → cM.rc.rules[c]? = some ruC →
        mA.rules₀[c]? = some rW → mA.rls[c]? = some rlA →
        cM.rulesC[c]? = some rC → rulesW'[c]? = some rW' →
        (∀ hwrap_ty_pos : WrapRel env.find? cM.ty_ld tyW_ld,
          WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs) ∧
        (∀ (hsym_ty_pos : SymWrapT env.find? cM.ty_ld tyW_ld)
           (htot_C : ctorsBefore (ReconView.ofStore t E_rec) es es.length = some cM.rc.minors.toNat),
          TwinRuleMatch env.find? f mA.ty' rC.rhs rW'.rhs) := by
      intro c ruA ruC rW rlA rC rW' hruA hruC hrW hrlA hrC hrW'
      have hrW'_rhs : rW'.rhs = rlA.rhs := by
        dsimp only [rulesW'] at hrW'
        rw [List.getElem?_map, list_getElem?_zip, hrlA, hrC] at hrW'
        have := Option.some.inj hrW'; subst this; rfl
      obtain ⟨-, -, -, hnf_eq, -, -⟩ := hrule_match c ruA ruC rW rlA rC hruA hruC hrW hrlA hrC
      obtain ⟨rhsC_ld, cbC, -, hrhsC_lv, hcbC, hrfC⟩ := cM.hrules_rec c ruC rC hruC hrC
      obtain ⟨rhsW_ld, cbW, hrhsW_ld, hcbW, hrfW⟩ := hrulesW_mr c ruA hruA
      have hruAL : mA.rc.rules.toList[c]? = some ruA := by rwa [Array.getElem?_toList]
      have hrhsW_pos : loadedAt t (fun x => E_rec.blobs.get? x) cA (blockSelf t A rs')
          mA.rc.lvls.toNat (mutsRoot rs' k + 1 + ((c : Nat) : F)) ruA.rhs =
          some (Core.posOf mA.ps rlA.rhs) := by
        have h1 := canonRules_getElem?_loadedAt mA.hps_perm mA.hcanonRules hrr_readA c ruA rlA
          hruAL hrlA
        rw [mA.hps_len] at h1
        exact Binding.FamilyFlat.loadedAt_mono hE₀_blob h1
      have hrhsW_eq : Core.posOf mA.ps rlA.rhs = rhsW_ld :=
        Option.some.inj (hrhsW_pos.symm.trans hrhsW_ld)
      have hcb_eq : cbC.renameConsts f = cbW := by
        rw [hbodies_eq, List.getElem?_map, hcbC] at hcbW
        exact Option.some.inj hcbW
      rw [hparams_eq, hmot_eq, hmin_eq, hnf_eq] at hrfW
      constructor
      · intro hwrap_ty_pos
        have hwr_ld : WrapRel env.find? (rhsC_ld.renameConsts f) rhsW_ld :=
          wrapRel_rule_of_ruleFollows hwrap_ty_pos hlf_tyW_ld htyC_fix hrfC hrfW
            (by rw [hcb_eq]; exact ExprLvEq.refl _)
        have hwr_pos : WrapRel env.find? (Core.posOf cM.cvC.levelParams (rC.rhs.renameConsts f))
            (Core.posOf cM.cvC.levelParams rW'.rhs) := by
          have hrhsW_eq' : Core.posOf cM.cvC.levelParams rW'.rhs = rhsW_ld := by
            rw [hrW'_rhs, ← hlps_eq, hrhsW_eq]
          rw [hrhsW_eq']
          unfold Core.posOf
          rw [← renameConsts_instantiateLevelParams]
          exact wrapRel_congr_exprLvEq_left (exprLvEq_renameConsts f hrhsC_lv) hwr_ld
        exact wrapRel_of_posOf_perm hperm_C hwr_pos
      · intro hsym_ty_pos htot_C
        have hc_lt_self : c < self.nctors := by
          have h1 := (Array.getElem?_eq_some_iff.mp hruC).1
          have h2 := hcM_rules_info.1
          omega
        have hmin_lt : cM.cbk + c < cM.rc.minors.toNat :=
          ctorsBefore_add_lt_total es k cM.cbk cM.rc.minors.toNat ek self c hek hself
            cM.hcbk htot_C hc_lt_self
        exact twinRuleMatch_of_ruleFollows hperm_C hsym_ty_pos htyC_fix
          (by rw [← hlps_eq]; exact htyW_eq) hrhsC_lv
          (by rw [hrW'_rhs, ← hlps_eq]; exact hrhsW_eq)
          (by rw [hrW'_rhs]; exact mA.hrls_letFree rlA (List.mem_of_getElem? hrlA))
          hmin_lt hrfC hrfW (by rw [hcb_eq]; exact ExprLvEq.refl _)
    constructor
    · -- `(WrapRel ∧ Forall₂ WrapRel) ∨ (SymWrapT ∧ Forall₂ TwinRuleMatch)`
      rcases hty_rel_pos with hwrap_ty_pos | ⟨hsym_ty_pos, htot_C⟩
      · left
        refine ⟨wrapRel_of_posOf_perm hperm_C (by rw [cM.hty_pos, ← hlps_eq, htyW_eq]; exact hwrap_ty_pos),
          list_forall₂_of_getElem hrulesW'_len fun c rW' rC hrW' hrC => ?_⟩
        have hc_lt : c < mA.rc.rules.size := by
          have := (List.getElem?_eq_some_iff.mp hrC).1; dsimp only at this; omega
        obtain ⟨ruA, hruA⟩ : ∃ r, mA.rc.rules[c]? = some r :=
          ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
        obtain ⟨ruC, hruC⟩ : ∃ r, cM.rc.rules[c]? = some r :=
          ⟨cM.rc.rules[c]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
        obtain ⟨rW, hrW⟩ : ∃ r, mA.rules₀[c]? = some r :=
          ⟨mA.rules₀[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨rlA, hrlA⟩ : ∃ r, mA.rls[c]? = some r :=
          ⟨mA.rls[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        exact (hrule_rel_at c ruA ruC rW rlA rC rW' hruA hruC hrW hrlA hrC hrW').1 hwrap_ty_pos
      · right
        refine ⟨symWrapT_of_posOf_perm hperm_C (by rw [cM.hty_pos, ← hlps_eq, htyW_eq]; exact hsym_ty_pos),
          list_forall₂_of_getElem hrulesW'_len fun c rW' rC hrW' hrC => ?_⟩
        have hc_lt : c < mA.rc.rules.size := by
          have := (List.getElem?_eq_some_iff.mp hrC).1; dsimp only at this; omega
        obtain ⟨ruA, hruA⟩ : ∃ r, mA.rc.rules[c]? = some r :=
          ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
        obtain ⟨ruC, hruC⟩ : ∃ r, cM.rc.rules[c]? = some r :=
          ⟨cM.rc.rules[c]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
        obtain ⟨rW, hrW⟩ : ∃ r, mA.rules₀[c]? = some r :=
          ⟨mA.rules₀[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨rlA, hrlA⟩ : ∃ r, mA.rls[c]? = some r :=
          ⟨mA.rls[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        exact (hrule_rel_at c ruA ruC rW rlA rC rW' hruA hruC hrW hrlA hrC hrW').2 hsym_ty_pos htot_C
    · -- `Forall₂ TwinRuleFront (mA.rules₀.zip rulesW') cM.rulesC`
      refine forall₂_of_list_forall₂ (list_forall₂_of_getElem
        (by change (mA.rules₀.zip rulesW').length = cM.rulesC.length; rw [List.length_zip]; omega)
        fun c p rC hp hrC => ?_)
      dsimp only at hp hrC
      have hp' : (mA.rules₀.zip rulesW')[c]? = some p := hp
      rw [list_getElem?_zip] at hp'
      cases hrW : mA.rules₀[c]? with
      | none => rw [hrW] at hp'; cases hp'
      | some rW =>
        rw [hrW] at hp'
        cases hrW' : rulesW'[c]? with
        | none => rw [hrW'] at hp'; cases hp'
        | some rW' =>
          rw [hrW'] at hp'
          have hp_eq : p = (rW, rW') := (Option.some.inj hp').symm
          subst p
          have hc_lt : c < mA.rc.rules.size := by
            have := (List.getElem?_eq_some_iff.mp hrC).1
            omega
          obtain ⟨ruA, hruA⟩ : ∃ r, mA.rc.rules[c]? = some r :=
            ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
          obtain ⟨ruC, hruC⟩ : ∃ r, cM.rc.rules[c]? = some r :=
            ⟨cM.rc.rules[c]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
          obtain ⟨rlA, hrlA⟩ : ∃ r, mA.rls[c]? = some r :=
            ⟨mA.rls[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
          have hrW'_eq : rW' =
              { ctor := rC.ctor, nfields := rC.nfields, rhs := rlA.rhs,
                ctorParams := rC.ctorParams, fire := rC.fire, k := rC.k,
                paramsBlind := rC.paramsBlind,
                eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A k)) rC.ctor } := by
            dsimp only [rulesW'] at hrW'
            rw [List.getElem?_map, list_getElem?_zip, hrlA, hrC] at hrW'
            exact (Option.some.inj hrW').symm
          obtain ⟨hct, hnf, -, -, -, hann⟩ := hrule_match c ruA ruC rW rlA rC hruA hruC hrW hrlA hrC
          have hruAL : mA.rc.rules.toList[c]? = some ruA := by rwa [Array.getElem?_toList]
          have hread_c := forall₂_getElem? mA.hrules_read c ruA rW hruAL hrW
          have hrel_c := hrule_rel_at c ruA ruC rW rlA rC rW' hruA hruC hrW hrlA hrC hrW'
          have hwf_rC := (hinv.store.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem cM.hfind)).2.2.2.2.2.1 _ _ _ _ rfl rC
            (List.mem_of_getElem? hrC)
          have hrc_ok := hinv.store.store.rec_ctors _ _ _ _ _ cM.hfind _ (List.mem_of_getElem? hrC)
          obtain ⟨DW, DC, hDW, hDC, hDW_fn, hDW_args⟩ := hmaj_dom
          have hstrip_W : ∃ preW bodyW mW, mA.ty'.stripPis cM.mI = some (preW, .forallE DW bodyW mW) := by
            rw [piDomAt_eq_binderDomAfter] at hDW
            unfold binderDomAfter at hDW
            cases hp1 : peelForalls cM.mI mA.ty' with
            | none => simp [hp1] at hDW
            | some r =>
              rw [hp1] at hDW
              cases r with
              | forallE d b m =>
                simp only [Option.some.injEq] at hDW; subst hDW
                obtain ⟨bs, hs⟩ := (stripPis_iff_peelForalls _ _ _).mp hp1
                exact ⟨bs, b, m, hs⟩
              | _ => simp at hDW
          have hstrip_C : ∃ preC bodyC mC, cM.cvC.type.stripPis cM.mI = some (preC, .forallE DC bodyC mC) := by
            rw [piDomAt_eq_binderDomAfter] at hDC
            unfold binderDomAfter at hDC
            cases hp1 : peelForalls cM.mI cM.cvC.type with
            | none => simp [hp1] at hDC
            | some r =>
              rw [hp1] at hDC
              cases r with
              | forallE d b m =>
                simp only [Option.some.injEq] at hDC; subst hDC
                obtain ⟨bs, hs⟩ := (stripPis_iff_peelForalls _ _ _).mp hp1
                exact ⟨bs, b, m, hs⟩
              | _ => simp at hDC
          rw [hrW'_eq]
          refine ⟨hct.symm, hnf.symm, hread_c.2.2.1, hread_c.2.2.2.2,
            Decl.annot_of_annotates hann hread_c.2.2.2.2 hread_c.2.2.1 0,
            ?_, ?_, mA.hrls_letFree rlA (List.mem_of_getElem? hrlA),
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · -- #6: `allLevelParamsDefined`
            rcases hty_rel_pos with hwrap_ty_pos | ⟨hsym_ty_pos, htot_C⟩
            · have hwr_c := hrel_c.1 hwrap_ty_pos
              rw [hrW'_eq] at hwr_c
              exact Typing.wrapRelSem_annot_allLevelParamsDefined
                (wrapRel_to_wrapRelSem hwr_c)
                (by rw [allLevelParamsDefined_renameConsts]; exact hwf_rC.2.1)
                hann (by rw [← hlps_eq]; exact hread_c.2.2.2.1)
            · have hmatch_c := hrel_c.2 hsym_ty_pos htot_C
              rw [hrW'_eq] at hmatch_c
              exact allLevelParamsDefined_of_twinRuleMatch hmatch_c
                (Decl.annotates_hasFvar_false hann hread_c.2.2.2.2)
                (by rw [← hlps_eq]; exact hmA_ty'_lpd)
                (by rw [allLevelParamsDefined_renameConsts]; exact hwf_rC.2.1)
                hann (by rw [← hlps_eq]; exact hread_c.2.2.2.1)
          · -- #7: `constsResolve envSelf`
            have hcr_ren : (rC.rhs.renameConsts f).constsResolve
                ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩ = true := by
              rw [hf_eq]
              exact constsResolve_renameConsts_envSelf hws_name hwf_rC.2.2.1
            rcases hty_rel_pos with hwrap_ty_pos | ⟨hsym_ty_pos, htot_C⟩
            · have hwr_c := hrel_c.1 hwrap_ty_pos
              rw [hrW'_eq] at hwr_c
              exact constsResolve_of_wrapRel hwr_c
                (by rw [hasFvar_renameConsts]; exact hwf_rC.1)
                (mA.hrls_letFree rlA (List.mem_of_getElem? hrlA))
                hcr_ren
            · have hmatch_c := hrel_c.2 hsym_ty_pos htot_C
              rw [hrW'_eq] at hmatch_c
              exact constsResolve_of_twinRuleMatch hmatch_c
                (Decl.annotates_hasFvar_false hann hread_c.2.2.2.2)
                (constsResolve_envSelf hmA_ty'_cr) hcr_ren
          · -- #16: `.plain`
            intro hpl cvj cnP cnF hfind_c
            obtain ⟨⟨cvj₀, hfind₀, hpl₀, -, -, -⟩, -⟩ := hrc_ok
            rw [hfind₀] at hfind_c
            injection hfind_c with hci_eq
            injection hci_eq with hcvj_eq _ _
            subst hcvj_eq
            obtain ⟨preW, bodyW, mW, hsW⟩ := hstrip_W
            obtain ⟨preC, bodyC, mC, hsC⟩ := hstrip_C
            rw [recRulePlain_of_majorDom_eq hsW hsC hDW_fn hDW_args]
            exact hpl₀ hpl
          · -- #17: `.nested`
            intro lvls pins hnest
            obtain ⟨-, -, -, preC, domC, bodyC, bmC, D, hsC, hfnC, hargsC⟩ :=
              hwf_rC.2.2.2.2 lvls pins hnest
            obtain ⟨preW, bodyW, mW, hsW⟩ := hstrip_W
            obtain ⟨preC', bodyC', mC', hsC'⟩ := hstrip_C
            have hdom_eq : DC = domC := by
              have h1 := Option.some.inj (hsC'.symm.trans hsC)
              have h2 := (Prod.mk.inj h1).2
              injection h2
            subst hdom_eq
            exact ⟨preW, DW, bodyW, mW, D, hsW, hDW_fn.trans hfnC, hDW_args.trans hargsC⟩
  · -- 12. `TwinMemberLoaded`
    refine
      { lvls := mA.hps_len
        tyBounded := mA.hty_lbb
        tyLevels := mA.hty_def
        rulesScoped := fun rl hrl => by
          obtain ⟨c, hget⟩ := List.mem_iff_getElem?.mp hrl
          have hc_lt : c < mA.rc.rules.size := by
            have := (List.getElem?_eq_some_iff.mp hget).1
            dsimp only at this
            omega
          obtain ⟨ru, hru⟩ : ∃ r, mA.rc.rules[c]? = some r :=
            ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
          have hruL : mA.rc.rules.toList[c]? = some ru := by rwa [Array.getElem?_toList]
          have h1 := forall₂_getElem? mA.hrules_read c ru rl hruL hget
          exact ⟨h1.2.2.1, h1.2.2.2.1⟩
        notK := mA.hk_false
        ty := by simpa only [hk_u64] using mA.hcanonTy
        rules := ⟨mA.rls, by simpa only [hk_u64] using mA.hcanonRules, ?_, ?_⟩ }
    · refine list_forall₂_of_getElem (by change mA.rls.length = rulesW'.length; omega) fun c rlA rW' hrlA hrW' => ?_
      have hc_lt : c < mA.rc.rules.size := by
        have := (List.getElem?_eq_some_iff.mp hrlA).1; omega
      obtain ⟨ruA, hruA⟩ : ∃ r, mA.rc.rules[c]? = some r :=
        ⟨mA.rc.rules[c]'hc_lt, Array.getElem?_eq_getElem hc_lt⟩
      obtain ⟨ruC, hruC⟩ : ∃ r, cM.rc.rules[c]? = some r :=
        ⟨cM.rc.rules[c]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
      obtain ⟨rW, hrW⟩ : ∃ r, mA.rules₀[c]? = some r :=
        ⟨mA.rules₀[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨rC, hrC⟩ : ∃ r, cM.rulesC[c]? = some r :=
        ⟨cM.rulesC[c]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hrW'_eq : rW' =
          { ctor := rC.ctor, nfields := rC.nfields, rhs := rlA.rhs,
            ctorParams := rC.ctorParams, fire := rC.fire, k := rC.k,
            paramsBlind := rC.paramsBlind,
            eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A k)) rC.ctor } := by
        dsimp only [rulesW'] at hrW'
        rw [List.getElem?_map, list_getElem?_zip, hrlA, hrC] at hrW'
        exact (Option.some.inj hrW').symm
      obtain ⟨-, hnf, -, -, hnf_rl, -⟩ := hrule_match c ruA ruC rW rlA rC hruA hruC hrW hrlA hrC
      rw [hrW'_eq]
      exact ⟨hnf.trans hnf_rl.symm, rfl⟩
    · intro rl rl' hrls_eq _ hk_t
      have hkf : rl.k = false :=
        canonRules_k_false (by rw [← mA.hk_false]; exact mA.hcanonRules) rl
          (by rw [hrls_eq]; exact List.mem_cons_self)
      exact absurd (hkf.symm.trans hk_t) Bool.false_ne_true

private theorem rprjAddr_inj_of_members {E : Ixon.Env} {rb : _root_.Address}
    {rs : Array Ixon.MutConst}
    (hmem : ∀ i m, rs[i]? = some m → recordOf E (memberAddr rb i m) = some (memberProjection rb i m))
    (hrecr : ∀ m ∈ rs.toList, ∃ rc, m = .recr rc)
    (hsz_lt : rs.size < UInt64.size)
    {i₁ i₂ : Nat} (h₁ : i₁ < rs.size) (h₂ : i₂ < rs.size)
    (heq : Core.rprjAddr rb i₁ = Core.rprjAddr rb i₂) : i₁ = i₂ := by
  obtain ⟨rc₁, hrc₁⟩ := hrecr (rs[i₁]'h₁) (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem h₁))
  obtain ⟨rc₂, hrc₂⟩ := hrecr (rs[i₂]'h₂) (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem h₂))
  have hm₁ : rs[i₁]? = some (.recr rc₁) := by rw [Array.getElem?_eq_getElem h₁, hrc₁]
  have hm₂ : rs[i₂]? = some (.recr rc₂) := by rw [Array.getElem?_eq_getElem h₂, hrc₂]
  have hr₁ := hmem i₁ (.recr rc₁) hm₁
  have hr₂ := hmem i₂ (.recr rc₂) hm₂
  have hma₁ : memberAddr rb i₁ (.recr rc₁) = Core.rprjAddr rb i₁ := rfl
  have hma₂ : memberAddr rb i₂ (.recr rc₂) = Core.rprjAddr rb i₂ := rfl
  rw [hma₁, heq] at hr₁
  rw [hma₂] at hr₂
  have hp_eq : memberProjection rb i₁ (.recr rc₁) = memberProjection rb i₂ (.recr rc₂) :=
    Option.some.inj (hr₁.symm.trans hr₂)
  have hi_u64 : i₁.toUInt64 = i₂.toUInt64 := by
    have hinfo := congrArg Ixon.Constant.info hp_eq
    simp only [memberProjection] at hinfo
    injection hinfo with hp
    injection hp
  have hn1 : i₁.toUInt64.toNat = i₁ := by
    change (UInt64.ofNat i₁).toNat = i₁
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (Nat.lt_trans h₁ hsz_lt)
  have hn2 : i₂.toUInt64.toNat = i₂ := by
    change (UInt64.ofNat i₂).toNat = i₂
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (Nat.lt_trans h₂ hsz_lt)
  rw [← hn1, ← hn2, hi_u64]

/-- **Unified twin parts assembly** (used by both `familyTwin_of_premises` and
`closureTwinSteps_of_premises`): builds `ds : List Decl.TwinMemberData` over all members `0 .. rs'.size - 1`
and proves `TwinDeclReads`, `TwinPartsFacts`, and `TwinLoadFacts` in one pass. -/
theorem twinParts_of_canon_extracted {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E E_rec : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {B rb A : _root_.Address} {cb crb cA : Ixon.Constant} {ms rs rs' : Array Ixon.MutConst}
    {es : List FlatEntry} {off fuel : Nat} {ind₀ : Ixon.Inductive}
    (hSS : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hE₀_rec : ∀ a c, recordOf E₀ a = some c → recordOf E_rec a = some c)
    (hE₀_blob : ∀ y b, E₀.blobs.get? y = some b → E_rec.blobs.get? y = some b)
    (hrb_muts : crb.info = .muts rs)
    (hrb_members : ∀ i m, rs[i]? = some m →
      recordOf E_rec (memberAddr rb i m) = some (memberProjection rb i m))
    (hrb_recrs : ∀ m ∈ rs.toList, ∃ rc, m = .recr rc)
    (hA : FamRecRecord E₀ A cA rs') (hsz : rs'.size ≠ 0)
    (hrs_len : rs.size = rs'.size) (hes_len : es.length = rs'.size)
    (hRecFlatC : RecordFlat t E_rec rb crb rs es)
    (hRecFlatA : RecordFlat t E_rec A cA rs' es)
    (hcanon : ∀ k (hk : k < rs'.size), CanonMemberAt calls t E_rec env B rb crb rs es off fuel ind₀ k)
    (hextract : ∀ k < rs'.size, Nonempty (ExtractedTwinMember.{u} calls t E₀ lim B A cb cA ms rs' ind₀ k))
    (hlvls_A : ∀ (k : Nat) (rc : Ixon.Recursor), rs'[k]? = some (.recr rc) → rc.lvls.toNat = ind₀.lvls.toNat + off)
    (hMA_all : ∀ (k : Nat) (rc : Ixon.Recursor), rs'[k]? = some (.recr rc) →
      MemberRecon ExprLvEq t E_rec A cA rs' es off fuel k rc ∨
      MemberRecon (fun ty R => WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty)
        t E_rec A cA rs' es off fuel k rc)
    (hpair_all :
      (∀ k (hk : k < rs'.size), ExprLvEq (hcanon k hk).ty_ld (hcanon k hk).R) ∨
      ((∀ (k : Nat) (rc : Ixon.Recursor), rs'[k]? = some (.recr rc) →
          MemberRecon (fun ty R => WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty)
            t E_rec A cA rs' es off fuel k rc) ∧
        ∃ S : _root_.Address → Prop,
          (ReconView.ofStore t E_rec).ClosedOn S ∧
          (∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t E_rec) S e) ∧
          (∀ (j : Nat) (rc : Ixon.Recursor), rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))))
    (husedA : ∀ i ∈ usedRefIdxs cA, ∀ x, cA.refs.toList[i]? = some x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A cA x)
    (hfreshA : ∀ x, ConstAddrOf A cA x → env.find? (keyOf t x) = none)
    (hkeyA : ∀ x, ConstAddrOf A cA x → Decl.KeyFree (keyOf t x)) :
    ∃ ds : List Decl.TwinMemberData,
      TwinDeclReads t E₀ A cA (ds.map fun d => .recInfo d.cvW d.mI d.rP d.rulesW) ∧
      TwinPartsFacts t env rb crb (Decl.mkTwinRecParts env ds)
        (Decl.twinPeerRename (Decl.mkTwinRecParts env ds)) ∧
      TwinLoadFacts t E₀ env A cA (Decl.mkTwinRecParts env ds) := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  let mA_of : ∀ (i : Fin rs'.size), ExtractedTwinMember.{u} calls t E₀ lim B A cb cA ms rs' ind₀ i.val :=
    fun i => Classical.choice (hextract i.val i.isLt)
  have hrs'_lt_u64 : rs'.size < UInt64.size := by
    have hpos : 0 < rs'.size := Nat.pos_of_ne_zero hsz
    have h1 := (mA_of ⟨0, hpos⟩).rc.motives.toBitVec.isLt
    change (mA_of ⟨0, hpos⟩).rc.motives.toNat < UInt64.size at h1
    rw [(mA_of ⟨0, hpos⟩).hnmot] at h1
    exact h1
  let mkD : Fin rs'.size → Decl.TwinMemberData := fun i =>
    let cM := hcanon i.val i.isLt
    let mA := mA_of i
    let rulesW' : List (RecRule .anon) :=
      (mA.rls.zip cM.rulesC).map fun p =>
        { ctor := p.2.ctor
          nfields := p.2.nfields
          rhs := p.1.rhs
          ctorParams := p.2.ctorParams
          fire := p.2.fire
          k := p.2.k
          paramsBlind := p.2.paramsBlind
          eta := Ix.Kernel.recRuleEtaOf env.find? (keyOf t (Core.rprjAddr A i.val)) p.2.ctor }
    { cvW := ⟨keyOf t (Core.rprjAddr A i.val), mA.ps, mA.ty₀⟩
      cvW' := ⟨keyOf t (Core.rprjAddr A i.val), mA.ps, mA.ty'⟩
      cvC := cM.cvC
      kC := keyOf t (Core.rprjAddr rb i.val)
      mI := cM.mI
      rP := cM.rP
      rulesW := mA.rules₀
      rulesW' := rulesW'
      rulesC := cM.rulesC }
  obtain ⟨ds, hds⟩ : ∃ ds, ds = (List.finRange rs'.size).map mkD := ⟨_, rfl⟩
  obtain ⟨ws, hws⟩ : ∃ ws, ws = Decl.mkTwinRecParts env ds := ⟨_, rfl⟩
  let f : KKey → KKey := Decl.twinPeerRename ws
  -- Per-member facts from `twinParts_member_data`
  have hmem_data : ∀ (i : Fin rs'.size),
      let d := mkD i
      let mA := mA_of i
      Reads t E₀ (Core.rprjAddr A i.val) (.recInfo d.cvW d.mI d.rP d.rulesW) ∧
      ConstantValCheckJ twinPosRulesJ env d.cvW d.cvW' ∧
      letFree d.cvW'.type = true ∧
      env.find? d.kC = some (.recInfo d.cvC d.mI d.rP d.rulesC) ∧
      d.cvW.levelParams = d.cvC.levelParams ∧
      d.rulesW.length = d.rulesW'.length ∧
      ValStored d.cvW' d.cvW ∧
      List.Forall₂ RuleStored d.rulesW' d.rulesW ∧
      (∃ DW DC, Core.piDomAt d.mI d.cvW'.type = some DW ∧ Core.piDomAt d.mI d.cvC.type = some DC ∧
        DW.getAppFn = DC.getAppFn ∧ DW.getAppArgs = DC.getAppArgs) ∧
      (∀ (f' : KKey → KKey) (ws' : List (TwinRecPart .anon)),
        f' = Decl.twinPeerRename ws' →
        (∀ w ∈ ws', w.cvW'.name = w.cvW.name) →
        (∀ (j : Nat) aC, (recAddrs rb rs)[j]? = some aC →
          ∃ aW, (recAddrs A rs')[j]? = some aW ∧ f' (keyOf t aC) = keyOf t aW) →
        (∀ q, f' q ≠ q → ∃ j rc, rs[j]? = some (.recr rc) ∧ q = keyOf t (memberAddr rb j (.recr rc))) →
        ((WrapRel env.find? d.cvC.type d.cvW'.type ∧
            List.Forall₂ (fun (rW' rC : RecRule .anon) => WrapRel env.find? (rC.rhs.renameConsts f') rW'.rhs)
              d.rulesW' d.rulesC) ∨
          (SymWrapT env.find? d.cvC.type d.cvW'.type ∧
            List.Forall₂ (fun (rW' rC : RecRule .anon) =>
              TwinRuleMatch env.find? f' d.cvW'.type rC.rhs rW'.rhs) d.rulesW' d.rulesC)) ∧
        Forall₂ (fun (p : RecRule .anon × RecRule .anon) rC =>
          TwinRuleFront twinPosRulesJ env ⟨twinProv ws' ++ (twinModels ws' ++ env.consts)⟩ f' d.cvW.name
            d.cvC.levelParams d.cvW' d.mI d.rP p.1 p.2 rC) (d.rulesW.zip d.rulesW') d.rulesC) ∧
      TwinMemberLoaded cA rs' ⟨i.val.toUInt64, A⟩ mA.rc d.cvW.levelParams d.cvW.type d.rulesW
        d.cvW' d.rulesW' ∧
      (∀ ro : Ix.Kernel.Role, d.cvW.name ≠ .role ro) := by
    intro i
    have hpair_i :
        ExprLvEq (hcanon i.val i.isLt).ty_ld (hcanon i.val i.isLt).R ∨
        (MemberRecon (fun ty R => WrapConsObs (wrapAt t E_rec) (WrapperObserved calls t) R ty)
            t E_rec A cA rs' es off fuel i.val (mA_of i).rc ∧
          ∃ S : _root_.Address → Prop,
            (ReconView.ofStore t E_rec).ClosedOn S ∧
            (∀ ek, es[i.val]? = some ek → Binding.FamilyRecon.REntryAt (ReconView.ofStore t E_rec) S ek) ∧
            (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) := by
      rcases hpair_all with h | ⟨hobs, S, hS_cl, hS_ent, hS_excl⟩
      · exact Or.inl (h i.val i.isLt)
      · exact Or.inr ⟨hobs i.val (mA_of i).rc (mA_of i).hmem, S, hS_cl,
          fun ek hek => hS_ent ek (List.mem_of_getElem? hek), hS_excl⟩
    exact twinParts_member_data ht hSS hinv hE₀_rec hE₀_blob hrb_muts hA hrs_len hes_len i.isLt
      hRecFlatC hRecFlatA (hcanon i.val i.isLt) (mA_of i)
      (hlvls_A i.val (mA_of i).rc (mA_of i).hmem)
      (hMA_all i.val (mA_of i).rc (mA_of i).hmem)
      hpair_i husedA hfreshA hkeyA
  -- Helper: unpack `w ∈ ws` into `i : Fin rs'.size`
  have hw_inv : ∀ w ∈ ws, ∃ i : Fin rs'.size, w = (mkD i).toPart env := by
    intro w hw
    rw [hws, Decl.mkTwinRecParts, hds, List.map_map] at hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, rfl⟩
  have hws_name : ∀ w ∈ ws, w.cvW'.name = w.cvW.name := by
    intro w hw; obtain ⟨i, rfl⟩ := hw_inv w hw; rfl
  -- `(ws.map (·.kC)).Nodup`
  have hws_kC_nodup : (ws.map (·.kC)).Nodup := by
    rw [hws, Decl.mkTwinRecParts, hds, List.map_map, List.map_map]
    refine List.Nodup.map ?_ (List.nodup_finRange rs'.size)
    intro i₁ i₂ heq
    have ha_eq : Core.rprjAddr rb i₁.val = Core.rprjAddr rb i₂.val := keyOf_inj hroles heq
    exact Fin.ext (rprjAddr_inj_of_members hrb_members hrb_recrs (by omega)
      (by omega) (by omega) ha_eq)
  -- `hpeers` and `hmove` for `f = Decl.twinPeerRename ws`
  have hpeers : ∀ (j : Nat) aC, (recAddrs rb rs)[j]? = some aC →
      ∃ aW, (recAddrs A rs')[j]? = some aW ∧ f (keyOf t aC) = keyOf t aW := by
    intro j aC hj
    have hj_lt : j < rs.size := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rw [recAddrs_length] at this; exact this
    have hj_lt' : j < rs'.size := by omega
    let ji : Fin rs'.size := ⟨j, hj_lt'⟩
    have hmC : rs[j]? = some (.recr (hcanon j hj_lt').rc) := (hcanon j hj_lt').hmem
    have hmA : rs'[j]? = some (.recr (mA_of ji).rc) := (mA_of ji).hmem
    have haC_eq : aC = Core.rprjAddr rb j := by
      have h1 := recAddrs_getElem? (rb := rb) hmC
      rw [memberAddr_recr_eq] at h1
      exact Option.some.inj (hj.symm.trans h1)
    have haW_get : (recAddrs A rs')[j]? = some (Core.rprjAddr A j) := by
      have h1 := recAddrs_getElem? (rb := A) hmA
      rwa [memberAddr_recr_eq] at h1
    have hw_mem : (mkD ji).toPart env ∈ ws := by
      rw [hws, Decl.mkTwinRecParts, hds]
      exact List.mem_map.mpr ⟨mkD ji, List.mem_map.mpr ⟨ji, List.mem_finRange ji, rfl⟩, rfl⟩
    have hmap := Decl.twinPeerRename_apply_of_nodup hws_kC_nodup hw_mem
    refine ⟨Core.rprjAddr A j, haW_get, ?_⟩
    rw [haC_eq]
    exact hmap
  have hmove : ∀ q, f q ≠ q →
      ∃ j rc, rs[j]? = some (.recr rc) ∧ q = keyOf t (memberAddr rb j (.recr rc)) := by
    intro q hfq
    rcases Decl.twinPeerRename_spec ws q with hfix | ⟨w', hw', hq, -⟩
    · exact absurd hfix hfq
    · obtain ⟨i, rfl⟩ := hw_inv w' hw'
      exact ⟨i.val, (hcanon i.val i.isLt).rc, (hcanon i.val i.isLt).hmem,
        by rw [memberAddr_recr_eq]; exact hq⟩
  -- Build the 3 conclusions
  refine ⟨ds, ?_, ?_, ?_⟩
  · -- `TwinDeclReads`
    refine ⟨?_, ?_, ?_⟩
    · -- `Nodup`
      rw [hds, List.map_map, List.map_map]
      refine List.Nodup.map ?_ (List.nodup_finRange rs'.size)
      intro i₁ i₂ heq
      have ha_eq : Core.rprjAddr A i₁.val = Core.rprjAddr A i₂.val := keyOf_inj hroles heq
      exact Fin.ext (rprjAddr_inj_of_members hA.members hA.recrs hrs'_lt_u64 i₁.isLt i₂.isLt ha_eq)
    · -- Every constant in `blk` is a `Reads` of a `ConstAddrOf A cA`
      intro ci hci
      rw [hds, List.map_map] at hci
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hci
      exact ⟨Core.rprjAddr A i.val,
        Or.inr ⟨rs', i.val, .recr (mA_of i).rc, hA.muts, (mA_of i).hmem,
          Or.inl (memberAddr_recr_eq A i.val _).symm⟩,
        rfl, (hmem_data i).1⟩
    · -- Every `ConstAddrOf A cA` is covered by `blk`
      intro x hx
      rcases hx with ⟨-, hst⟩ | ⟨ms', i, m, hms', hm, hxm⟩
      · exact (standalone_not_block hst ⟨rs', hA.muts⟩).elim
      · have hrs_eq : rs' = ms' := Ixon.ConstantInfo.muts.inj (hA.muts.symm.trans hms')
        subst hrs_eq
        have hi_lt : i < rs'.size := by
          by_contra hge; rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hm; cases hm
        obtain ⟨rc, hrc⟩ := hA.recrs m (List.mem_of_getElem? (by rwa [Array.getElem?_toList]))
        subst hrc
        rcases hxm with rfl | ⟨_, _, hc, -⟩
        · let ii : Fin rs'.size := ⟨i, hi_lt⟩
          refine ⟨.recInfo (mkD ii).cvW (mkD ii).mI (mkD ii).rP (mkD ii).rulesW, ?_,
            by rw [memberAddr_recr_eq]; rfl⟩
          rw [hds, List.map_map]
          exact List.mem_map.mpr ⟨ii, List.mem_finRange ii, rfl⟩
        · cases hc
  · -- `TwinPartsFacts`
    rw [← hws]
    refine
      { canonAt := fun w hw => by
          obtain ⟨i, rfl⟩ := hw_inv w hw
          have hd := hmem_data i
          obtain ⟨hform, -⟩ := hd.2.2.2.2.2.2.2.2.2.1 f ws rfl hws_name hpeers hmove
          obtain ⟨DW, DC, hDW, hDC, hfn, hargs⟩ := hd.2.2.2.2.2.2.2.2.1
          exact ⟨Core.rprjAddr rb i.val,
            Or.inr ⟨rs, i.val, .recr (hcanon i.val i.isLt).rc, hrb_muts,
              (hcanon i.val i.isLt).hmem, Or.inl (memberAddr_recr_eq rb i.val _).symm⟩,
            rfl,
            { major := ⟨DW, DC, hDW, hDC, hfn, fun _ => hargs⟩
              form := hform.elim Or.inl (fun hS => Or.inr (Or.inr hS)) }⟩
        front := fun w hw => by obtain ⟨i, rfl⟩ := hw_inv w hw; exact (hmem_data i).2.1
        letFree := fun w hw => by obtain ⟨i, rfl⟩ := hw_inv w hw; exact (hmem_data i).2.2.1
        canonical := fun w hw => by obtain ⟨i, rfl⟩ := hw_inv w hw; exact (hmem_data i).2.2.2.1
        lvls := fun w hw => by obtain ⟨i, rfl⟩ := hw_inv w hw; exact (hmem_data i).2.2.2.2.1
        rulesLen := fun w hw => by obtain ⟨i, rfl⟩ := hw_inv w hw; exact (hmem_data i).2.2.2.2.2.1
        rules := fun w hw => by
          obtain ⟨i, rfl⟩ := hw_inv w hw
          exact ((hmem_data i).2.2.2.2.2.2.2.2.2.1 f ws rfl hws_name hpeers hmove).2
        stored := fun w hw => by
          obtain ⟨i, rfl⟩ := hw_inv w hw
          exact ⟨(hmem_data i).2.2.2.2.2.2.1, (hmem_data i).2.2.2.2.2.2.2.1⟩ }
  · -- `TwinLoadFacts`
    rw [← hws]
    refine
      { usedStored := husedA
        noRole := fun w hw => by
          obtain ⟨i, rfl⟩ := hw_inv w hw
          exact (hmem_data i).2.2.2.2.2.2.2.2.2.2.2
        loaded := fun w hw ms' p rc hms' hp hm hname _ => by
          obtain ⟨i, rfl⟩ := hw_inv w hw
          have hrs_eq : rs' = ms' := Ixon.ConstantInfo.muts.inj (hA.muts.symm.trans hms')
          subst hrs_eq
          have hp_lt : p.idx.toNat < rs'.size := by
            by_contra hge; rw [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at hm; cases hm
          rw [memberAddr_recr_eq] at hname
          have ha_eq : Core.rprjAddr A i.val = Core.rprjAddr A p.idx.toNat := keyOf_inj hroles hname
          have hi_eq : i.val = p.idx.toNat :=
            rprjAddr_inj_of_members hA.members hA.recrs hrs'_lt_u64 i.isLt hp_lt ha_eq
          have hp_eq : p = ⟨i.val.toUInt64, A⟩ := by
            cases p with
            | mk idx blk =>
              simp only at hp hi_eq
              subst hp
              have hidx : idx = i.val.toUInt64 := by
                apply UInt64.ext
                change idx.toNat = (UInt64.ofNat i.val).toNat
                rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans i.isLt hrs'_lt_u64), hi_eq]
              subst hidx; rfl
          have hrc_eq : rc = (mA_of i).rc := by
            rw [← hi_eq] at hm
            exact Ixon.MutConst.recr.inj (Option.some.inj (hm.symm.trans (mA_of i).hmem))
          subst hp_eq hrc_eq
          exact (hmem_data i).2.2.2.2.2.2.2.2.2.2.1 }

/-! ## `FamilyTwinRowFam` producer -/

private theorem unitStepTwin_of_concl_rbS {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A rb : _root_.Address} {c crb : Ixon.Constant} (ht : t.check = .ok ())
    (hconcl : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env → X env →
      (∀ x, UsedRef E₀ A x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
      (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
      (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
      ∃ (blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
        TwinDeclReads t E₀ A c blk ∧
        DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
        (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) ∧
        (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
        Decl.CoreCompanions ⟨E, env₂, t, lim⟩ ∧
        (∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
          ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci))
    (hkeep : TwinStepKeeps.{u} X t envT E₀ E lim A c) :
    UnitStepTwin.{u} X t envT E₀ E lim A c rb crb := by
  intro env hext hnd hinv hX href hrbS hfresh
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨blk, env₂, hreads, hrun, hstored, hmodel, hcomp, hrel⟩ :=
    hconcl env hext hnd hinv hX href hrbS hfresh
  obtain ⟨hinv₂, hX₂⟩ :=
    hkeep env env₂ blk hext hnd hinv hX href hfresh hreads hrun hstored hmodel hcomp hrel
  obtain ⟨ws, henv, hnd₂, hfr₂, hnames, hrecs, hmods⟩ := twinRun_parts hrun
  subst henv
  have hrecName : ∀ ci ∈ twinRecs ws, ∃ ci₀ ∈ blk, ci₀.name = ci.name := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := by
      rw [← hnames]
      exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨ci₀, hci₀, he⟩ := List.mem_map.mp hm
    exact ⟨ci₀, hci₀, he⟩
  refine ⟨twinRecs ws ++ twinModels ws, hnd₂, hfr₂, hinv₂, hX₂, ?_, ?_⟩
  · intro x hx
    obtain ⟨ci₀, hci₀, hn₀⟩ := hreads.2.2 x hx
    obtain ⟨x', hx', hn', hrd⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := keyOf_inj hroles (hn'.symm.trans hn₀)
    rw [hxx] at hrd
    obtain ⟨c', hc', hsa⟩ := hstored ci₀ hci₀
    rcases find?_append_cases (twinRecs ws ++ twinModels ws) hc' with hm | hold
    · refine ⟨c', hm, ci₀, ?_, hrd, hsa⟩
      rw [Core.WhnfAux.name_of_find hc', hn₀]
    · rw [hn₀, hfresh x hx] at hold
      cases hold
  · intro ci hci
    rcases List.mem_append.mp hci with hr | hmo
    · obtain ⟨ci₀, hci₀, he⟩ := hrecName ci hr
      obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci₀ hci₀
      exact Or.inl ⟨x, hx, he.symm.trans hn⟩
    · obtain ⟨ci', -, hk, -⟩ := hmods ci hmo
      exact Or.inr ⟨ci'.name, .model, hk⟩

private theorem familyTwin_step_core
    (hFlat : TwinCallFlat) (hRecon : TwinCallRecon) (hStoredLvls : StoredRecLvlsOk)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    {E₀ : Ixon.Env} {lim : Option Nat} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {famOf : _root_.Address → Option _root_.Address}
    (hRF : StoredFamiliesRForm RFormS t R famOf)
    {A : _root_.Address} {c : Ixon.Constant} {B rb : _root_.Address} {crb : Ixon.Constant}
    (hW : Walked Top Inner A) (hc : recordOf E₀ A = some c) (hlog : InLogic c)
    (htw : twin A = some B)
    (hcase : (fam B = some rb ∧ recordOf E₀ rb = some crb ∧
        RecBlock E₀ rb ∧ (RFormS t E₀ B A → RFormS t E₀ B rb)) ∨
      (fam B = none ∧ StoredTwinCanon t R envT famOf B rb crb))
    (hClosed_at : ∀ rs, fam B = some rb → FamRecRecord E₀ rb crb rs →
      ∃ S : _root_.Address → Prop,
        (ReconView.ofStore t E₀).ClosedOn S ∧
        (FlatView.ofStore t E₀).ClosedOn S ∧
        S B ∧
        (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) :
    UnitStepTwin.{u}
      (fun env => FoldExtra.{u} FormerOpenTraceAt t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb := by
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hb : Bounded calls := (hctx.good envT lim).2
  have hRS : LoadedReads.RunStore calls E₀ := hWc.runStore
  have hH : LoadedReads.HashedRecordsStored calls E₀ := hWc.hashedStored
  have hL : LinkLaws FormerOpenTraceAt := linkLaws_formerOpenTrace
  -- Twin record `A`
  obtain ⟨c₀, rs', hA₀, hszA⟩ := hFR.graph.twinRecord A B htw
  have hA : FamRecRecord E₀ A c rs' := by
    have e : c₀ = c := Option.some.inj (hA₀.record.symm.trans hc)
    rw [← e]; exact hA₀
  have hkeep :=
    (twinStepKeeps_foldExtra (t := t) (envT := envT) (E₀ := E₀) (E := E) (lim := lim) (A := A) hL
      fun x hx => constAddr_hash_size_of_block hA.muts hx).and_familyRecsModeled (fam := fam)
  rcases hcase with ⟨hfam, hcrb, hrec_rb, hpref⟩ | ⟨hnone, hcanon⟩
  · -- **Graph arm** (`fam B = some rb`, `E_rec = E₀`)
    obtain ⟨-, cb₀, hcb₀, hlogB, -⟩ := hFR.graph.famUnit B rb hfam
    obtain ⟨cb, ms, hcb, hms, hind⟩ := hFR.famInd B rb hfam
    have ecb : cb = cb₀ := Option.some.inj (hcb.symm.trans hcb₀)
    have hlogB' : InLogic cb := by rw [ecb]; exact hlogB
    have hTB : Top B := hFR.graph.famBlock B rb hfam
    have hB : FamBlockRecord E₀ B cb ms :=
      { record := hcb
        muts := hms
        indcs := hind
        logic := hlogB'
        members := fun i m hm => (hG.members B cb ms hTB hcb hms i m hm).1
        ctors := fun i ind j hm hj =>
          (hG.members B cb ms hTB hcb hms i (.indc ind) hm).2 ind j rfl hj }
    obtain ⟨bAddr, hC, hrecAt⟩ := hFR.famRecAt
    obtain ⟨rs, cs_rb, hrb, hcall_rb⟩ := hrecAt B rb crb hfam hcrb
    obtain ⟨cs_A, hcall_A⟩ := hC.twinCall A B htw
    have hsz_rb : rs.size ≠ 0 := by
      obtain ⟨crb', rs_r, hcrb', hrs_r, hpos_r, -⟩ := hrec_rb
      have ec : crb' = crb := Option.some.inj (hcrb'.symm.trans hcrb)
      subst ec
      have er : rs_r = rs := Ixon.ConstantInfo.muts.inj (hrs_r.symm.trans hrb.muts)
      subst er
      exact Nat.ne_of_gt hpos_r
    have hlogicB : ∀ cb', recordOf E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      have e : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
      rw [e]; exact hlogB'
    -- Flattened family for `rb` and `A`
    obtain ⟨cb_rb, ms_rb, es, off, hFOB_rb, hRF_rb, hBD_rb, hlvls_rb⟩ :=
      hFlat calls bAddr t E₀ B rb crb rs lim cs_rb ht hb hRS hH hrb hsz_rb hlogicB hcall_rb
    obtain ⟨cb_A, ms_A, es_A, off_A, hFOB_A, hRF_A, hBD_A, hlvls_A⟩ :=
      hFlat calls bAddr t E₀ B A c rs' lim cs_A ht hb hRS hH hA hszA hlogicB hcall_A
    have hcb_rb_eq : cb_rb = cb := Option.some.inj (hFOB_rb.block.record.symm.trans hcb)
    subst cb_rb
    have hms_rb_eq : ms_rb = ms := Ixon.ConstantInfo.muts.inj (hFOB_rb.block.muts.symm.trans hms)
    subst ms_rb
    have hcb_A_eq : cb_A = cb := Option.some.inj (hFOB_A.block.record.symm.trans hcb)
    subst cb_A
    have hms_A_eq : ms_A = ms := Ixon.ConstantInfo.muts.inj (hFOB_A.block.muts.symm.trans hms)
    subst ms_A
    obtain ⟨hoff_eq, hes_eq⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
      (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A hBD_rb
    subst off_A es_A
    have hes_len_rb : es.length = rs.size := by
      simpa only [List.length_map] using hFOB_rb.covers
    have hes_len_A : es.length = rs'.size := by
      simpa only [List.length_map] using hFOB_A.covers
    have hrs_len : rs.size = rs'.size := hes_len_rb.symm.trans hes_len_A
    -- Extract members for `rb` and `A`
    obtain ⟨ind₀, hms0, hextract_rb⟩ := familyCall_extract_members ht hRS hH hctx.shape
      hctx.recordsFor hctx.toStepStore (limWithin_all t lim) hB hrb hcall_rb
    obtain ⟨ind₀', hms0', hextract_A⟩ := familyCall_extract_members ht hRS hH hctx.shape
      hctx.recordsFor hctx.toStepStore (limWithin_all t lim) hB hA hcall_A
    have hind0_eq : ind₀' = ind₀ :=
      Ixon.MutConst.indc.inj (Option.some.inj (hms0'.symm.trans hms0))
    subst ind₀'
    -- Reconstruction form for `rb` and `A`
    have hrec_form_rb := hRecon calls bAddr t E₀ B rb cb crb ms rs lim cs_rb ht hb hRS hH hB hrb
      hsz_rb hcall_rb
    have hrec_form_A := hRecon calls bAddr t E₀ B A cb c ms rs' lim cs_A ht hb hRS hH hB hA
      hszA hcall_A
    have hrefs_ok_A := recRefs_of_familyCall hRS hH hc hcall_A
    -- Align `fuel` across `rb` and `A`
    have hMR_pair : ∃ fuel : Nat,
        (∀ k rc, rs[k]? = some (.recr rc) →
          MemberRecon ExprLvEq t E₀ rb crb rs es off fuel k rc ∨
          (ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat ∧
            MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
              t E₀ rb crb rs es off fuel k rc)) ∧
        (∀ k rc, rs'[k]? = some (.recr rc) →
          MemberRecon ExprLvEq t E₀ A c rs' es off fuel k rc ∨
          MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
            t E₀ A c rs' es off fuel k rc) ∧
        ((∀ k rc, rs[k]? = some (.recr rc) →
            MemberRecon ExprLvEq t E₀ rb crb rs es off fuel k rc) ∨
          ((∀ k rc, rs[k]? = some (.recr rc) →
              ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat ∧
              MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
                t E₀ rb crb rs es off fuel k rc) ∧
            (∀ k rc, rs'[k]? = some (.recr rc) →
              MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
                t E₀ A c rs' es off fuel k rc))) := by
      -- Helper to unpack `RecordReconWith TyRel t E₀ B r` onto `(cr, rs_r, es, off)`
      have unpack_rr : ∀ {TyRel : KExpr → KExpr → Prop} {r : _root_.Address} {cr : Ixon.Constant}
          {rs_r : Array Ixon.MutConst},
          recordOf E₀ r = some cr → cr.info = .muts rs_r →
          RecordReconWith TyRel t E₀ B r →
          ∃ f_r, ∀ k rc, rs_r[k]? = some (.recr rc) →
            MemberRecon TyRel t E₀ r cr rs_r es off f_r k rc := by
        intro TyRel r cr rs_r hrec_r hmut_r hRR
        obtain ⟨cr', rs', es', off', f_r, hrec', hmut', -, hBD', hM'⟩ := hRR
        have ecr : cr' = cr := Option.some.inj (hrec'.symm.trans hrec_r)
        subst cr'
        have ers : rs' = rs_r := Ixon.ConstantInfo.muts.inj (hmut'.symm.trans hmut_r)
        subst rs'
        obtain ⟨ho', he'⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD' hBD_rb
        subst off' es'
        exact ⟨f_r, hM'⟩
      have unpack_wc : ∀ {r : _root_.Address} {cr : Ixon.Constant} {rs_r : Array Ixon.MutConst},
          recordOf E₀ r = some cr → cr.info = .muts rs_r →
          RecordWrapConsObs calls t E₀ B r →
          ∃ f_r, ∀ k rc, rs_r[k]? = some (.recr rc) →
            ctorsBefore (ReconView.ofStore t E₀) es es.length = some rc.minors.toNat ∧
            MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
              t E₀ r cr rs_r es off f_r k rc := by
        intro r cr rs_r hrec_r hmut_r hWC
        obtain ⟨cr', rs', es', off', f_r, hrec', hmut', -, hBD', hM'⟩ := hWC
        have ecr : cr' = cr := Option.some.inj (hrec'.symm.trans hrec_r)
        subst cr'
        have ers : rs' = rs_r := Ixon.ConstantInfo.muts.inj (hmut'.symm.trans hmut_r)
        subst rs'
        obtain ⟨ho', he'⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD' hBD_rb
        subst off' es'
        exact ⟨f_r, hM'⟩
      by_cases hRF_rb_eq : RFormS t E₀ B rb
      · obtain ⟨f_rb, hM_rb⟩ := unpack_rr hcrb hrb.muts hRF_rb_eq
        rcases hrec_form_A with hA_eq | hA_obs
        · obtain ⟨f_A, hM_A⟩ := unpack_rr hc hA.muts hA_eq
          refine ⟨max f_rb f_A,
            fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr)),
            fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr)),
            Or.inl fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr)⟩
        · obtain ⟨f_A, hM_A⟩ := unpack_wc hc hA.muts hA_obs
          refine ⟨max f_rb f_A,
            fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr)),
            fun k rc hr => Or.inr (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2),
            Or.inl fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr)⟩
      · have hrb_obs : RecordWrapConsObs calls t E₀ B rb := hrec_form_rb.resolve_left hRF_rb_eq
        have hA_obs : RecordWrapConsObs calls t E₀ B A :=
          hrec_form_A.resolve_left (fun h => hRF_rb_eq (hpref h))
        obtain ⟨f_rb, hM_rb⟩ := unpack_wc hcrb hrb.muts hrb_obs
        obtain ⟨f_A, hM_A⟩ := unpack_wc hc hA.muts hA_obs
        refine ⟨max f_rb f_A,
          fun k rc hr => Or.inr ⟨(hM_rb k rc hr).1,
            Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr).2⟩,
          fun k rc hr => Or.inr (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2),
          Or.inr ⟨fun k rc hr => ⟨(hM_rb k rc hr).1,
              Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr).2⟩,
            fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2⟩⟩
    obtain ⟨fuel, hMR_rb_all, hMR_A_all, hMR_mode⟩ := hMR_pair
    refine unitStepTwin_of_concl_rbS ht ?_ hkeep
    intro env hext hnd hinv hX href hrbS hfresh
    have hinst : FamilyInstalled t env rb crb := familyInstalled_of_clause hX.2 hfam hcrb hrbS
    have hstoredRb := familyRecsStored_of_clause hX.2 hfam hcrb hrbS
    have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
      intro x hx hst
      obtain ⟨ci, hci, hname⟩ := hst
      have hs := find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
      rw [hfresh x hx] at hs; simp at hs
    have hkeyA : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
      fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx)
    have husedA : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x := by
      intro i hi x hx
      have hux : UsedRef E₀ A x := ⟨c, i, hc, hi, by rwa [← Array.getElem?_toList]⟩
      rcases hrefs_ok_A x hux with hcov | hneed
      · obtain ⟨ci, hci, hn⟩ := coveredAt_stored hctx.shape htwf (fun _ _ => trivial) hcov
        exact Or.inl (find_isSome_of_storedAt ⟨ci, hext ci hci, hn⟩)
      · rcases href x hux with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd hneed h3
    -- Build `CanonMemberAt` for every `k < rs'.size`
    let mkC : ∀ k (hk : k < rs'.size), CanonMemberAt calls t E₀ env B rb crb rs es off fuel ind₀ k :=
      fun k hk =>
        let mC := Classical.choice (hextract_rb k (by omega))
        Classical.choice (canonMemberAt_of_extracted ht hctx.toStepStore hinv hrb hRF_rb mC
          (hlvls_rb ind₀ k mC.rc hms0 mC.hmem) hstoredRb
          (hMR_rb_all k mC.rc mC.hmem))
    have hpair_all :
        (∀ k (hk : k < rs'.size), ExprLvEq (mkC k hk).ty_ld (mkC k hk).R) ∨
        ((∀ k rc, rs'[k]? = some (.recr rc) →
            MemberRecon (fun ty R => WrapConsObs (wrapAt t E₀) (WrapperObserved calls t) R ty)
              t E₀ A c rs' es off fuel k rc) ∧
          ∃ S : _root_.Address → Prop,
            (ReconView.ofStore t E₀).ClosedOn S ∧
            (∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t E₀) S e) ∧
            (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) := by
      rcases hMR_mode with hrb_eq | ⟨-, hA_obs⟩
      · left
        intro k hk
        have hM_eq := hrb_eq k (mkC k hk).rc (mkC k hk).hmem
        obtain ⟨ty1, R1, _, _, hty1, hR1, hlv1, -, -, -⟩ := hM_eq
        have hty_e : ty1 = (mkC k hk).ty_ld := Option.some.inj (hty1.symm.trans (mkC k hk).hty_ld)
        have hR_e : R1 = (mkC k hk).R := Option.some.inj (hR1.symm.trans (mkC k hk).hR)
        rwa [hty_e, hR_e] at hlv1
      · right
        obtain ⟨S, hS_rec, hS_flat, hSB, hS_excl⟩ := hClosed_at rs hfam hrb
        have hS_ent : ∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t E₀) S e := by
          obtain ⟨_, n, hn⟩ := hBD_rb
          intro e he
          have hx := Binding.FamilyFlat.derivedFlatAt_entryAt hS_flat hSB hn e he
          exact ⟨hx.addr, hx.params⟩
        exact ⟨hA_obs, S, hS_rec, hS_ent, hS_excl⟩
    exact twinTargetConcl_of_parts ht hctx.toStepStore hA hszA hinv hX.1.1.2 hinst hfresh
      (twinParts_of_canon_extracted ht hctx.toStepStore hinv (fun _ _ h => h) (fun _ _ h => h)
        hrb.muts hrb.members hrb.recrs hA hszA hrs_len hes_len_A hRF_rb hRF_A
        mkC hextract_A (fun k rc hr => hlvls_A ind₀ k rc hms0 hr) hMR_A_all hpair_all
        husedA hfresh hkeyA)
  · -- **Stored arm** (`fam B = none`, `StoredTwinCanon`, `E_rec = E`)
    obtain ⟨cb, ms, rs, es, off, hFOB_R, hRF_R, hBD_R⟩ := hcanon.family
    have hE₀_rec : ∀ a c', recordOf E₀ a = some c' → recordOf E a = some c' :=
      fun a c' h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.runRecord a c' h)
    have hR_rec : ∀ a c', recordOf R a = some c' → recordOf E a = some c' :=
      fun a c' h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.recordsFor.2.1 a c' h)
    have hE₀_blob : ∀ y b, E₀.blobs.get? y = some b → E.blobs.get? y = some b := hctx.runBlob
    have hR_blob : ∀ y b, R.blobs.get? y = some b → E.blobs.get? y = some b := hctx.recordsFor.2.2.1
    have hlogicB : ∀ cb', recordOf E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      have e : cb' = cb := Option.some.inj
        ((hE₀_rec B cb' hcb').symm.trans (hR_rec B cb hFOB_R.block.record))
      rw [e]; exact hFOB_R.block.logic
    obtain ⟨bAddr, hC⟩ := hFR.checks
    obtain ⟨cs_A, hcall_A⟩ := hC.twinCall A B htw
    -- Flattened family for `A` over `E₀`, unified with `es, off` from `R` via `E`
    obtain ⟨cb_A, ms_A, es_A, off_A, hFOB_A, hRF_A, hBD_A, hlvls_A⟩ :=
      hFlat calls bAddr t E₀ B A c rs' lim cs_A ht hb hRS hH hA hszA hlogicB hcall_A
    have hcb_A_eq : cb_A = cb := Option.some.inj
      ((hE₀_rec B cb_A hFOB_A.block.record).symm.trans (hR_rec B cb hFOB_R.block.record))
    subst cb_A
    have hms_A_eq : ms_A = ms :=
      Ixon.ConstantInfo.muts.inj (hFOB_A.block.muts.symm.trans hFOB_R.block.muts)
    subst ms_A
    obtain ⟨hoff_eq, hes_eq⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
      (fun a c1 c2 h1 h2 => Option.some.inj ((hE₀_rec a c1 h1).symm.trans (hR_rec a c2 h2)))
      (fun y b1 b2 h1 h2 => Option.some.inj ((hE₀_blob y b1 h1).symm.trans (hR_blob y b2 h2)))
      hBD_A hBD_R
    subst off_A es_A
    have hes_len_rb : es.length = rs.size := by
      simpa only [List.length_map] using hFOB_R.covers
    have hes_len_A : es.length = rs'.size := by
      simpa only [List.length_map] using hFOB_A.covers
    have hrs_len : rs.size = rs'.size := hes_len_rb.symm.trans hes_len_A
    -- Extract members for `A`
    obtain ⟨ind₀, hms0, hextract_A⟩ := familyCall_extract_members ht hRS hH hctx.shape
      hctx.recordsFor hctx.toStepStore (limWithin_all t lim) hFOB_A.block hA hcall_A
    have hrefs_ok_A := recRefs_of_familyCall hRS hH hc hcall_A
    -- Grow `RFormS t R B rb` and `A`'s recon to common store `E`
    have hRF_rb_E : RFormS t E B rb := (hRF B rb hcanon.selected).grow hR_rec hR_blob
    have hBD_E : BlockDerivedFlat t E B off es :=
      Binding.FamilyFlat.blockDerivedFlat_grow hR_rec hR_blob hBD_R
    have hrec_form_A_E : RFormS t E B A ∨ RecordWrapConsObs calls t E B A := by
      rcases hRecon calls bAddr t E₀ B A cb c ms rs' lim cs_A ht hb hRS hH hFOB_A.block hA hszA
          hcall_A with h | h
      · exact Or.inl (h.grow hE₀_rec hE₀_blob)
      · exact Or.inr (recordWrapConsObs_grow hE₀_rec hE₀_blob h)
    have hcrb_E : recordOf E rb = some crb := hR_rec rb crb hFOB_R.record.record
    have hc_E : recordOf E A = some c := hE₀_rec A c hc
    have hRF_rb_E_flat : RecordFlat t E rb crb rs es := hRF_R.of_blobs hR_blob
    have hRF_A_E_flat : RecordFlat t E A c rs' es := hRF_A.of_blobs hE₀_blob
    -- Unpack `fuel` on `E`
    have hMR_stored : ∃ fuel : Nat,
        (∀ k rc, rs[k]? = some (.recr rc) →
          MemberRecon ExprLvEq t E rb crb rs es off fuel k rc) ∧
        (∀ k rc, rs'[k]? = some (.recr rc) →
          MemberRecon ExprLvEq t E A c rs' es off fuel k rc ∨
          MemberRecon (fun ty R => WrapConsObs (wrapAt t E) (WrapperObserved calls t) R ty)
            t E A c rs' es off fuel k rc) := by
      obtain ⟨crb', rs_r, es_r, off_r, f_rb, hrb', hrs_r, -, hBD_r, hM_rb⟩ := hRF_rb_E
      have ecrb : crb' = crb := Option.some.inj (hrb'.symm.trans hcrb_E)
      subst crb'
      have ers_r : rs_r = rs := Ixon.ConstantInfo.muts.inj (hrs_r.symm.trans hFOB_R.record.muts)
      subst rs_r
      obtain ⟨ho_r, he_r⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
        (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_r hBD_E
      subst off_r es_r
      rcases hrec_form_A_E with hA_eq | hA_obs
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_eq
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc_E)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_E
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inl (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr))⟩
      · obtain ⟨c', rsA', esA', offA', f_A, hc', hrsA', -, hBD_A', hM_A⟩ := hA_obs
        have ec' : c' = c := Option.some.inj (hc'.symm.trans hc_E)
        subst c'
        have ersA' : rsA' = rs' := Ixon.ConstantInfo.muts.inj (hrsA'.symm.trans hA.muts)
        subst rsA'
        obtain ⟨ho_A, he_A⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
          (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD_A' hBD_E
        subst offA' esA'
        exact ⟨max f_rb f_A,
          fun k rc hr => Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_left _ _) (hM_rb k rc hr),
          fun k rc hr => Or.inr (Binding.FamilyRecon.MemberRecon.fuel_mono (Nat.le_max_right _ _) (hM_A k rc hr).2)⟩
    obtain ⟨fuel, hM_rb_E, hMR_A_all⟩ := hMR_stored
    refine unitStepTwin_of_concl ht ?_ hkeep
    intro env hext hnd hinv hX href hfresh
    have hinst : FamilyInstalled t env rb crb := familyInstalled_of_ext hext hnd hcanon.installed
    have hrecs : StoredFamilyRecs t R env B cb rb crb :=
      (hcanon.recs cb hFOB_R.block.record).mono_env hext hnd
    have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
      intro x hx hst
      obtain ⟨ci, hci, hname⟩ := hst
      have hs := find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
      rw [hfresh x hx] at hs; simp at hs
    have hkeyA : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
      fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx)
    have husedA : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x := by
      intro i hi x hx
      have hux : UsedRef E₀ A x := ⟨c, i, hc, hi, by rwa [← Array.getElem?_toList]⟩
      rcases hrefs_ok_A x hux with hcov | hneed
      · obtain ⟨ci, hci, hn⟩ := coveredAt_stored hctx.shape htwf (fun _ _ => trivial) hcov
        exact Or.inl (find_isSome_of_storedAt ⟨ci, hext ci hci, hn⟩)
      · rcases href x hux with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · exact absurd hneed h3
    let mkC : ∀ k (hk : k < rs'.size), CanonMemberAt calls t E env B rb crb rs es off fuel ind₀ k :=
      fun k hk =>
        Classical.choice (canonMemberAt_of_stored ht hR_rec hR_blob hFOB_R hRF_rb_E_flat hms0 hrecs
          hBD_R hStoredLvls (by omega) (hM_rb_E k))
    have hpair_all :
        (∀ k (hk : k < rs'.size), ExprLvEq (mkC k hk).ty_ld (mkC k hk).R) ∨
        ((∀ k rc, rs'[k]? = some (.recr rc) →
            MemberRecon (fun ty R => WrapConsObs (wrapAt t E) (WrapperObserved calls t) R ty)
              t E A c rs' es off fuel k rc) ∧
          ∃ S : _root_.Address → Prop,
            (ReconView.ofStore t E).ClosedOn S ∧
            (∀ e ∈ es, Binding.FamilyRecon.REntryAt (ReconView.ofStore t E) S e) ∧
            (∀ j rc, rs[j]? = some (.recr rc) → ¬ S (memberAddr rb j (.recr rc)))) := by
      left
      intro k hk
      have hM_eq := hM_rb_E k (mkC k hk).rc (mkC k hk).hmem
      obtain ⟨ty1, R1, _, _, hty1, hR1, hlv1, -, -, -⟩ := hM_eq
      have hty_e : ty1 = (mkC k hk).ty_ld := Option.some.inj (hty1.symm.trans (mkC k hk).hty_ld)
      have hR_e : R1 = (mkC k hk).R := Option.some.inj (hR1.symm.trans (mkC k hk).hR)
      rwa [hty_e, hR_e] at hlv1
    exact twinTargetConcl_of_parts ht hctx.toStepStore hA hszA hinv hX.1.1.2 hinst hfresh
      (twinParts_of_canon_extracted ht hctx.toStepStore hinv hE₀_rec hE₀_blob
        hFOB_R.record.muts (fun i m hm => hR_rec _ _ (hFOB_R.record.members i m hm))
        hFOB_R.record.recrs hA hszA hrs_len hes_len_A hRF_rb_E_flat hRF_A_E_flat
        mkC hextract_A (fun k rc hr => hlvls_A ind₀ k rc hms0 hr) hMR_A_all hpair_all
        husedA hfresh hkeyA)

/-- **Typing-half twin row `FamilyTwinRowFam` from the isolated upstream interfaces.** -/
theorem familyTwin_of_premises
    (hFlat : TwinCallFlat) (hRecon : TwinCallRecon)
    (hStoredLvls : StoredRecLvlsOk) (hClosed : GraphStoreClosed.{u}) :
    FamilyTwinRowFam.{u} RFormS FormerOpenTraceAt :=
  fun calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx famOf hRF
    A c B rb crb hW hc hlog htw hcase =>
    familyTwin_step_core hFlat hRecon hStoredLvls hWalk hFR hctx hRF hW hc hlog htw hcase
      (fun rs hfam hrb => hClosed calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner
        hFR hctx B rb crb rs hfam hrb)

/-- **`FamilyTwinRowFam` with witness well-formedness (`EnvWF envT`) and block-wholeness
(`BoundaryFacts.whole`) threaded**, matching the hypotheses in scope in `FamilyStepsFamFull`. -/
def FamilyTwinRowFamWF (RFormS : Binding.StoredFormPred)
    (L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      Ix.Kernel.EnvWF envT →
      (∀ E', RecordsFor R E' →
        ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
          (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E' a = some c →
          Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E' B = some cb → cb.info = .muts ms →
          BlockStored t envT B ms) →
      ∀ famOf : _root_.Address → Option _root_.Address, StoredFamiliesRForm RFormS t R famOf →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        ((fam B = some rb ∧ recordOf E₀ rb = some crb ∧
            RecBlock E₀ rb ∧ (RFormS t E₀ B A → RFormS t E₀ B rb)) ∨
          (fam B = none ∧ StoredTwinCanon t R envT famOf B rb crb)) →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- **Typing-half twin row `FamilyTwinRowFamWF` from only `TwinCallFlat`, `TwinCallRecon`, and
`StoredRecLvlsOk`** (discharging `GraphStoreClosed` via `graphStoreClosed_of_envWF`). -/
theorem familyTwinWF_of_premises
    (hFlat : TwinCallFlat) (hRecon : TwinCallRecon) (hStoredLvls : StoredRecLvlsOk) :
    FamilyTwinRowFamWF.{u} RFormS FormerOpenTraceAt :=
  fun calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx hEnvWF hWhole
    famOf hRF A c B rb crb hW hc hlog htw hcase =>
    familyTwin_step_core hFlat hRecon hStoredLvls hWalk hFR hctx hRF hW hc hlog htw hcase
      (fun _ hfam hrb => graphStoreClosed_of_envWF hWalk hFR hctx hEnvWF hWhole hfam hrb)

end IxVM.Refinement.Typing.TwinFamily

