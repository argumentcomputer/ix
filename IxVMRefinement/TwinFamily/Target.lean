import IxVMRefinement.Decl.TwinRec
import IxVMRefinement.Decl.ModeledAux
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.FamilyGraph.Graph
import IxVMRefinement.Assembly.RecRhsPw
import IxCK.Kernel.Model.FoldLate
import IxCK.Kernel.Model.ThmLevels
import IxCK.Kernel.Model.StoreArKeep

/-! # The step of a second family record: its target at IxCK's twin record

A run may accept a second recursor record `rb'` for a mutual or nested block `B` whose family
record `rb` is installed (`FamilyGraph.twinBlock`). Its unit is stepped by IxCK's twin route:
the one statement that step has to produce from the circuit is `TwinStepTarget`, whose
conclusion is IxCK's own record `DeclRecTwinRunJ` at the positional package `twinPosRulesJ`
(derivations on the terms at positional level parameters, which is how the circuit types a
recursor whose level parameters are a permutation of the positions).

* `TwinStepTarget`: from the accepted family check of the block with the second record, at any
  limit of the role context, the prefix invariant at that limit, what the record uses stored,
  and the block's family record installed (each of its recursors stored with its model
  companion): the second record's declaration as read, IxCK's twin record for it, each member
  stored as a constant that stores its reading, and a model companion at each member.
* What the fold gets from the conclusion (`envModelN_twinStep`, `declStoreInv_twinStep`,
  `thmLevels_twinStep`, `twinStep_consts`): IxCK's fold invariant with a registry in every set
  theory, the store facts, the theorems' level parameters, and the constants the step adds (the
  twin recursors at the record's keys and model copies at derived keys).
* `FamilyRecsModeled`: the clause a fold carries so that the twin's step finds the block's
  family record installed with its companions; the family step establishes it
  (`modelSide_of_target`) and the twin step keeps it (the target's last conjunct).
* The generated terms. IxCK's record asks, of each recursor and each rule, one generated term
  related by `WrapRel` to the stored canonical one and to the twin's, which is the canonical
  term itself or is typed (`TwinTypeGen`, `TwinRuleGen`). Where the canonical term is above the
  twin's, no further fact is needed (`twinTypeGen_of_canonical_above`,
  `twinRuleGen_of_canonical_above`); where the twin's type is above the canonical one, the
  twin's own front door types it (`twinTypeGen_of_twin_above`), and a rule needs a typed common
  term (`twinRuleGen_of_typed`). -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KExpr KKey)
open IxVM.Refinement.Decl (twinPosRulesJ judgeFrames_twinPosRulesJ judgeSound_twinPosRulesJ_of
  DeclStoreInv)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (Judgements ConstantValCheckJ DeclRecTwinRunJ TwinRecPart twinModels
  twinRecs WrapRel SymWrapT TwinRuleMatch NativeFam)
open Ix.Kernel.Model (EnvModelN EnvModelM JudgeFrames JudgeSound HasModel StoreArR)

set_option linter.unusedVariables false

/-! ## The target -/

/-- **The second record's declaration, as read**: the block's constants are the readings of the
record's constant addresses, one for each, under distinct keys. -/
def TwinDeclReads (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (rb' : _root_.Address)
    (crb' : Ixon.Constant) (blk : List (ConstantInfo .anon)) : Prop :=
  (blk.map (·.name)).Nodup ∧
  (∀ ci ∈ blk, ∃ x, ConstAddrOf rb' crb' x ∧ ci.name = keyOf t x ∧ Reads t E₀ x ci) ∧
  (∀ x, ConstAddrOf rb' crb' x → ∃ ci ∈ blk, ci.name = keyOf t x)

/-- **The block's family record is installed**: each of its recursors is stored as a recursor,
with its model companion. -/
def FamilyInstalled (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (rb : _root_.Address)
    (crb : Ixon.Constant) : Prop :=
  ∀ x, ConstAddrOf rb crb x →
    (∃ cv mI rP rules, env.find? (keyOf t x) = some (.recInfo cv mI rP rules)) ∧
    HasModel env (keyOf t x)

/-- **The block's family record, as the run checked it**: `rb`'s record in the run's store is
a family record (`FamRecRecord`) that a family check of the block `B` in the run accepted, under
the binding `bAddr` and at the limit `lim` of the second record's own family check, so that the
two checks rebuild the block's recursors under one role context. The canonical recursor of each
part of a second record is the member of `rb` at the part's place in `B`'s family; this is what
ties the two. For a family record in the graph (`fam B = some rb`) the graph's producer gives
it; for a family the witness stores it is not available (the record may be only in the
witness's store), and the stored case is open. -/
def FamRecOfBlock (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (B rb : _root_.Address) (crb : Ixon.Constant) (lim : Option Nat) : Prop :=
  ∃ (rs : Array Ixon.MutConst) (cs : List (Call F)),
    FamRecRecord E₀ rb crb rs ∧ FamilyCallAtLim calls bAddr t B rb lim cs

/-- **A predicate on a family record's form, as a family check of its block accepts it**, of the
run's calls, the binding, the role table, the run's store, the block, the record and the limit.
The form rule (c) prefers (the reconstruction's at every member) is one; the circuit's
record-level form check fixes it. -/
abbrev RecordFormPred : Type :=
  List (Call F) → _root_.Address → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address →
    _root_.Address → Option Nat → Prop

/-- **The twin step's target**, at a record form `RForm`. The hypotheses are the accepted family
check of the block `B` with the second record `rb'` on the modeled route, at any limit, and the
family check of `B` with its family record `rb` under the same binding and limit; that the
family record is in the form `RForm` where the second record is (the graph's choice of the
family record); the prefix invariant at that limit, with every stored derived key's root stored
(`Decl.AuxRootSynced`, a part of the fold's clause); what the second record uses, stored; the
block's family record installed (wherever the record itself is: in the run's store, or, for a
stored family, in the witness's); freshness and key freedom of the second record's constant
addresses. The conclusion is the second record's declaration as read, IxCK's twin record for it
over the positional package, each member stored after the step as a constant that stores its
reading, a model companion at each member, the scoped core's role and record companions after
the step, and the reload of each new constant at the key of an address. -/
def TwinStepTarget (RForm : RecordFormPred) : Prop :=
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
    Decl.PrefixInv.{u} E t lim env → Decl.AuxRootSynced env →
    (∀ x, UsedRef E₀ rb' x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf rb' crb' x ∨ ¬ NeedOk E₀ x) →
    FamilyInstalled t env rb crb →
    (∀ x, ConstAddrOf rb crb x →
      ∃ ci ci₀, env.find? (keyOf t x) = some ci ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) →
    (∀ x, ConstAddrOf rb' crb' x → env.find? (keyOf t x) = none) →
    (∀ x, ConstAddrOf rb' crb' x → Decl.KeyFree (keyOf t x)) →
    ∃ (blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      TwinDeclReads t E₀ rb' crb' blk ∧
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name) ∧
      Decl.CoreCompanions ⟨E, env₂, t, lim⟩ ∧
      (∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) ∧
      NewRecNotNative t E env env₂

/-! ## What the fold gets from the conclusion -/

/-- **IxCK's fold invariant with a registry across the twin step**: the twin block extends the
model it is given (`declRecTwinJ`), and the registry is kept as it is. -/
theorem envModelN_twinStep {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {R : NativeFam .anon → Prop}
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      EnvModelN V .verified env R → EnvModelN V .verified env₂ R :=
  fun V _ hE =>
    EnvModelN.step V hE (fun mp _ hEE =>
      ⟨Ix.Kernel.Semantics.declRecTwinRunJ_etaClosed hEE hrun,
        Ix.Kernel.Model.declRecTwinJ judgeFrames_twinPosRulesJ
          (fun m => judgeSound_twinPosRulesJ_of m) mp hrun⟩)

/-- **The store facts across the twin step**: the store invariant, the typed theorems, the
recursor `K` facts, the eta towers, the table bodies and the recursor shapes. -/
theorem declStoreInv_twinStep {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)}
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂) (h : DeclStoreInv env) :
    DeclStoreInv env₂ :=
  h.step_twin_pos hrun

/-- **The theorems' level parameters across the twin step**: the step stores no theorem. -/
theorem thmLevels_twinStep {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)}
    (hrun : DeclRecTwinRunJ twinPosRulesJ env block env₂) (hT : Ix.Kernel.ThmLevels env) :
    Ix.Kernel.ThmLevels env₂ :=
  Ix.Kernel.Model.ThmLevels.step_noThm hT
    (Ix.Kernel.Model.twin_newSat (fun _ _ _ _ _ heq => nomatch heq)
      (fun _ _ _ _ _ _ heq => nomatch heq) hrun)

/-- **The constants the twin step adds**: the twin recursors, one for each member of the block
and under its name, then copies of model companions at derived keys. -/
theorem twinStep_consts {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} (hrun : DeclRecTwinRunJ J env block env₂) :
    ∃ ws : List (TwinRecPart .anon), env₂ = ⟨twinRecs ws ++ (twinModels ws ++ env.consts)⟩ ∧
      (twinRecs ws).map (·.name) = block.map (·.name) ∧
      ∀ c ∈ twinModels ws, ∃ k, c.name = Ix.Kernel.auxKey k .model := by
  obtain ⟨ws, f, -, hblk, henv, -, -, -, hall⟩ := hrun
  refine ⟨ws, henv, ?_, ?_⟩
  · rw [hblk]
    simp only [twinRecs, List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    exact (hall w hw).1.name_eq
  · intro c hc
    obtain ⟨w, -, hmi⟩ := List.mem_filterMap.mp hc
    unfold TwinRecPart.modelInfo? at hmi
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
    exact ⟨w.cvW.name, rfl⟩

/-- **The arity of the stored terms across the twin step** (a statement; not proved here): from
IxCK's twin record, the stored terms after the block are arity-correct and resolve when the
prefix's are. -/
def TwinKeepsStoreAr : Prop :=
  ∀ (env env₂ : Ix.Kernel.Env .anon) (block : List (ConstantInfo .anon)),
    DeclRecTwinRunJ twinPosRulesJ env block env₂ → StoreArR env → StoreArR env₂

/-! ## The clause that hands the twin its block's family record -/

/-- **A stored member of a block's family record is a recursor with a model companion.** For
every family record a block claims (`fam B = some rb`): where the environment stores a constant
at a constant address of the record, it is a recursor and has a model companion. The family step
establishes it for the recursors it stores; no other unit stores at such an address (a unit is
claimed by no block, so it shares no constant address with a family record), so every other step
keeps it; the witness's environment stores no constant address of a family record, so it holds
there. With it, the twin's step, which is handed its block's family record stored, finds it
installed (`familyInstalled_of_clause`). -/
def FamilyRecsModeled (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (fam : _root_.Address → Option _root_.Address) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (B rb x : _root_.Address) (crb : Ixon.Constant),
    fam B = some rb → recordOf E₀ rb = some crb → ConstAddrOf rb crb x →
    (env.find? (keyOf t x)).isSome = true →
    (∃ cv mI rP rules, env.find? (keyOf t x) = some (.recInfo cv mI rP rules) ∧
      ∃ ci₀, Reads t E₀ x ci₀ ∧ StoredAs (.recInfo cv mI rP rules) ci₀) ∧
      HasModel env (keyOf t x)

/-- The clause is kept by a step that keeps every stored constant and stores, at a constant
address of a claimed family record, only a recursor that stores its reading with a model
companion. -/
theorem FamilyRecsModeled.step {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {fam : _root_.Address → Option _root_.Address} {env env₂ : Ix.Kernel.Env .anon}
    (h : FamilyRecsModeled t E₀ fam env)
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env₂.find? k = some c)
    (hnew : ∀ (B rb x : _root_.Address) (crb : Ixon.Constant),
      fam B = some rb → recordOf E₀ rb = some crb → ConstAddrOf rb crb x →
      (env₂.find? (keyOf t x)).isSome = true → env.find? (keyOf t x) = none →
      (∃ cv mI rP rules, env₂.find? (keyOf t x) = some (.recInfo cv mI rP rules) ∧
        ∃ ci₀, Reads t E₀ x ci₀ ∧ StoredAs (.recInfo cv mI rP rules) ci₀) ∧
        HasModel env₂ (keyOf t x)) :
    FamilyRecsModeled t E₀ fam env₂ := by
  intro B rb x crb hrb hcrb hx hs
  cases hold : env.find? (keyOf t x) with
  | none => exact hnew B rb x crb hrb hcrb hx hs hold
  | some c =>
    obtain ⟨⟨cv, mI, rP, rules, hf, ci₀, hrd, hst⟩, hm⟩ :=
      h B rb x crb hrb hcrb hx (by rw [hold]; rfl)
    rw [hold] at hf
    refine ⟨⟨cv, mI, rP, rules, ?_, ci₀, hrd, hst⟩, hm.mono hfind⟩
    rw [← hf]
    exact hfind hold

/-- **The clause at an environment that stores no constant address of a claimed family
record**, the witness's environment in particular (`FamilyGraph.famFresh`). -/
theorem familyRecsModeled_of_fresh {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {fam : _root_.Address → Option _root_.Address} {env : Ix.Kernel.Env .anon}
    (hfr : ∀ B rb crb x, fam B = some rb → recordOf E₀ rb = some crb → ConstAddrOf rb crb x →
      ¬ StoredAt t env x) :
    FamilyRecsModeled t E₀ fam env := by
  intro B rb x crb hrb hcrb hx hs
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  exact (hfr B rb crb x hrb hcrb hx (storedAt_of_find hci)).elim

/-- **With the clause, a claimed family record whose constant addresses are stored is
installed.** -/
theorem familyInstalled_of_clause {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {fam : _root_.Address → Option _root_.Address} {env : Ix.Kernel.Env .anon}
    {B rb : _root_.Address} {crb : Ixon.Constant} (h : FamilyRecsModeled t E₀ fam env)
    (hrb : fam B = some rb) (hcrb : recordOf E₀ rb = some crb)
    (hstored : ∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) :
    FamilyInstalled t env rb crb := by
  intro x hx
  obtain ⟨⟨cv, mI, rP, rules, hf, -⟩, hm⟩ := h B rb x crb hrb hcrb hx (hstored x hx)
  exact ⟨⟨cv, mI, rP, rules, hf⟩, hm⟩

/-- **With the clause, each stored constant address of a claimed family record stores its
reading in `E₀`.** -/
theorem familyRecsStored_of_clause {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {fam : _root_.Address → Option _root_.Address} {env : Ix.Kernel.Env .anon}
    {B rb : _root_.Address} {crb : Ixon.Constant} (h : FamilyRecsModeled t E₀ fam env)
    (hrb : fam B = some rb) (hcrb : recordOf E₀ rb = some crb)
    (hstored : ∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) :
    ∀ x, ConstAddrOf rb crb x →
      ∃ ci ci₀, env.find? (keyOf t x) = some ci ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀ := by
  intro x hx
  obtain ⟨⟨cv, mI, rP, rules, hf, ci₀, hrd, hst⟩, -⟩ := h B rb x crb hrb hcrb hx (hstored x hx)
  exact ⟨.recInfo cv mI rP rules, ci₀, hf, hrd, hst⟩

/-! ## The generated terms of IxCK's twin record -/

section Generated

variable {J : Judgements .anon} {env : Ix.Kernel.Env .anon}

/-- **A term is typed as IxCK's twin record asks of a generated term**: closed, over the given
level parameters, resolved, bounded, and inferred at the environment. -/
def GenTyped (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (lps : List LevelParam)
    (g : KExpr) : Prop :=
  g.hasFvar = false ∧ g.allLevelParamsDefined lps = true ∧ g.constsResolve env = true ∧
    g.looseBVarsBounded 0 = true ∧ ∃ ty, J.infer env 0 g ty

/-- **The generated type of a twin recursor**, as `DeclRecTwinRunJ` asks it: one term related by
`WrapRel` to the canonical recursor's type and to the twin's checked type, which is the canonical
type, is typed, or sits over symmetrically wrapper-related types. -/
def TwinTypeGen (J : Judgements .anon) (env : Ix.Kernel.Env .anon)
    (cvC cvW' : ConstantVal .anon) : Prop :=
  ∃ tyG : KExpr, WrapRel env.find? tyG cvC.type ∧ WrapRel env.find? tyG cvW'.type ∧
    (tyG = cvC.type ∨ GenTyped J env cvC.levelParams tyG ∨ SymWrapT env.find? cvC.type cvW'.type)

/-- **The generated right-hand side of a twin rule**, as `TwinRuleJ` asks it. -/
def TwinRuleGen (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (lps : List LevelParam) (cvW' : ConstantVal .anon) (rC rW' : RecRule .anon) : Prop :=
  ∃ rhsG : KExpr, WrapRel env.find? rhsG rC.rhs ∧
    WrapRel env.find? (rhsG.renameConsts f) rW'.rhs ∧
    (rhsG = rC.rhs ∨ GenTyped J env lps rhsG ∨ TwinRuleMatch env.find? f cvW'.type rC.rhs rW'.rhs)

/-- Where the canonical type is above the twin's (the twin consumed at least the wrappers the
canonical record did; in particular where the two terms are equal), the canonical type is the
generated type: nothing is typed. -/
theorem twinTypeGen_of_canonical_above {cvC cvW' : ConstantVal .anon}
    (h : WrapRel env.find? cvC.type cvW'.type) : TwinTypeGen J env cvC cvW' :=
  ⟨cvC.type, WrapRel.refl _ _, h, Or.inl rfl⟩

/-- Where the twin's checked type is above the canonical type (the twin kept wrappers the
canonical record consumed), the twin's own type is the generated type: it is typed by the twin's
own front door. -/
theorem twinTypeGen_of_twin_above {cvC cvW cvW' : ConstantVal .anon}
    (hfr : JudgeFrames J env) (hcv : ConstantValCheckJ J env cvW cvW')
    (hlps : cvW.levelParams = cvC.levelParams)
    (h : WrapRel env.find? cvW'.type cvC.type) : TwinTypeGen J env cvC cvW' := by
  obtain ⟨-, -, -, -, hlb, hfv, type, stype, lv, hann, hlp, hres, hinf, -, hcv'⟩ := hcv.inv
  obtain ⟨hfv', hlb'⟩ := hfr.annot_syntax hann hfv hlb
  subst hcv'
  refine ⟨type, h, WrapRel.refl _ _, Or.inr (Or.inl ⟨hfv', ?_, hres, hlb', stype, hinf⟩)⟩
  rw [← hlps]
  exact hlp

/-- Where the two records consumed different wrappers, a common term above both that is typed
is the generated type. The circuit's reconstruction is above both; its typing is the fact to
supply. -/
theorem twinTypeGen_of_typed {cvC cvW' : ConstantVal .anon} {g : KExpr}
    (hC : WrapRel env.find? g cvC.type) (hW : WrapRel env.find? g cvW'.type)
    (ht : GenTyped J env cvC.levelParams g) : TwinTypeGen J env cvC cvW' :=
  ⟨g, hC, hW, Or.inr (Or.inl ht)⟩

/-- Where the canonical and twin types are symmetrically wrapper-related (`SymWrapT`) with a
common `WrapRel` ancestor `tyG`, nothing further is typed. -/
theorem twinTypeGen_of_symWrapT {cvC cvW' : ConstantVal .anon} {g : KExpr}
    (hC : WrapRel env.find? g cvC.type) (hW : WrapRel env.find? g cvW'.type)
    (hSym : SymWrapT env.find? cvC.type cvW'.type) : TwinTypeGen J env cvC cvW' :=
  ⟨g, hC, hW, Or.inr (Or.inr hSym)⟩

/-- Where the canonical rule, renamed to the twin's peers, is above the twin's rule, the
canonical right-hand side is the generated one: nothing is typed. -/
theorem twinRuleGen_of_canonical_above {f : KKey → KKey} {lps : List LevelParam}
    {cvW' : ConstantVal .anon} {rC rW' : RecRule .anon}
    (h : WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs) :
    TwinRuleGen J env f lps cvW' rC rW' :=
  ⟨rC.rhs, WrapRel.refl _ _, h, Or.inl rfl⟩

/-- A common right-hand side above both rules that is typed at the environment is the generated
one. No front door types a rule's right-hand side, so in every case but the one above this
typing has to be supplied. -/
theorem twinRuleGen_of_typed {f : KKey → KKey} {lps : List LevelParam}
    {cvW' : ConstantVal .anon} {rC rW' : RecRule .anon} {g : KExpr}
    (hC : WrapRel env.find? g rC.rhs)
    (hW : WrapRel env.find? (g.renameConsts f) rW'.rhs) (ht : GenTyped J env lps g) :
    TwinRuleGen J env f lps cvW' rC rW' :=
  ⟨g, hC, hW, Or.inr (Or.inl ht)⟩

/-- Where the twin rule matches the twin type's λ-prefix and the canonical rule's body under
`SymWrapT` (`TwinRuleMatch`), nothing further is typed. -/
theorem twinRuleGen_of_match {f : KKey → KKey} {lps : List LevelParam}
    {cvW' : ConstantVal .anon} {rC rW' : RecRule .anon} {g : KExpr}
    (hC : WrapRel env.find? g rC.rhs)
    (hW : WrapRel env.find? (g.renameConsts f) rW'.rhs)
    (hm : TwinRuleMatch env.find? f cvW'.type rC.rhs rW'.rhs) :
    TwinRuleGen J env f lps cvW' rC rW' :=
  ⟨g, hC, hW, Or.inr (Or.inr hm)⟩

/-- The generated type is the clause of `DeclRecTwinRunJ` for a twin recursor. -/
theorem twinTypeGen_iff_ty_gen {w : TwinRecPart .anon} :
    TwinTypeGen J env w.cvC w.cvW' ↔
      ∃ tyG : KExpr,
        WrapRel env.find? tyG w.cvC.type ∧
        WrapRel env.find? tyG w.cvW'.type ∧
        (tyG = w.cvC.type ∨
          (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
            tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
            ∃ sty, J.infer env 0 tyG sty) ∨
          SymWrapT env.find? w.cvC.type w.cvW'.type) :=
  Iff.rfl

end Generated

end IxVM.Refinement.Typing.TwinFamily
