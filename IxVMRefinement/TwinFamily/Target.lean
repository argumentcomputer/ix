import IxVMRefinement.Decl.TwinRec
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.FamilyGraph.Graph
import IxC.Kernel.Model.FoldLate
import IxC.Kernel.Model.ThmLevels
import IxC.Kernel.Model.StoreArKeep

/-! # The step of a second family record: its target at IxC's twin record

A run may accept a second recursor record `rb'` for a mutual or nested block `B` whose family
record `rb` is installed (`FamilyGraph.twinBlock`). Its unit is stepped by IxC's twin route:
the one statement that step has to produce from the circuit is `TwinStepTarget`, whose
conclusion is IxC's own record `DeclRecTwinRunJ` at the positional package `twinPosRulesJ`
(derivations on the terms at positional level parameters, which is how the circuit types a
recursor whose level parameters are a permutation of the positions).

* `TwinStepTarget`: from the accepted family check of the block with the second record, at any
  limit of the role context, the prefix invariant at that limit, what the record uses stored,
  and the block's family record installed (each of its recursors stored with its model
  companion): the second record's declaration as read, IxC's twin record for it, each member
  stored as a constant that stores its reading, and a model companion at each member.
* What the fold gets from the conclusion (`envModelN_twinStep`, `declStoreInv_twinStep`,
  `thmLevels_twinStep`, `twinStep_consts`): IxC's fold invariant with a registry in every set
  theory, the store facts, the theorems' level parameters, and the constants the step adds (the
  twin recursors at the record's keys and model copies at derived keys).
* `FamilyRecsModeled`: the clause a fold carries so that the twin's step finds the block's
  family record installed with its companions; the family step establishes it
  (`modelSide_of_target`) and the twin step keeps it (the target's last conjunct).
* The generated terms. IxC's record asks, of each recursor and each rule, one generated term
  related by `WrapRel` to the stored canonical one and to the twin's, which is the canonical
  term itself or is typed (`TwinTypeGen`, `TwinRuleGen`). Where one of the two records' terms is
  above the other, no further fact is needed (`twinTypeGen_of_canonical_above`,
  `twinTypeGen_of_twin_above`, `twinRuleGen_of_canonical_above`). Where the two records consumed
  different wrappers, the common term is the circuit's reconstruction, and its typing
  (`GenTyped`) is what has to be supplied (`twinTypeGen_of_typed`, `twinRuleGen_of_typed`). -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (twinPosRulesJ judgeFrames_twinPosRulesJ judgeSound_twinPosRulesJ_of
  DeclStoreInv)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (Judgements ConstantValCheckJ DeclRecTwinRunJ TwinRecPart twinModels
  twinRecs WrapRel NativeFam)
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

/-- **The twin step's target.** The hypotheses are the accepted family check of the block `B`
with the second record `rb'` on the modeled route, at any limit; the prefix invariant at that
limit; what the second record uses, stored; the block's family record `rb` installed; the inert
clause; freshness and key freedom of the second record's constant addresses. The conclusion is
the second record's declaration as read, IxC's twin record for it over the positional package,
each member stored after the step as a constant that stores its reading, and a model companion
at each member. -/
def TwinStepTarget : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb rb' : _root_.Address)
    (cb crb crb' : Ixon.Constant) (ms rs rs' : Array Ixon.MutConst) (lim : Option Nat)
    (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    FamBlockRecord E₀ B cb ms → FamRecRecord E₀ rb crb rs → FamRecRecord E₀ rb' crb' rs' →
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
    ∃ (blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      TwinDeclReads t E₀ rb' crb' blk ∧
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ ci ∈ blk, HasModel env₂ ci.name)

/-! ## What the fold gets from the conclusion -/

/-- **IxC's fold invariant with a registry across the twin step**: the twin block extends the
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
IxC's twin record, the stored terms after the block are arity-correct and resolve when the
prefix's are. -/
def TwinKeepsStoreAr : Prop :=
  ∀ (env env₂ : Ix.Kernel.Env .anon) (block : List (ConstantInfo .anon)),
    DeclRecTwinRunJ twinPosRulesJ env block env₂ → StoreArR env → StoreArR env₂

/-! ## The clause that hands the twin its block's family record -/

/-- **Every stored recursor at a member of a block of recursors has a model companion.** The
family step establishes it for the recursors it stores, the twin step for its own, and no other
step stores a recursor at such an address. With it, the twin's step finds the block's family
record installed (`familyInstalled_of_clause`). -/
def FamilyRecsModeled (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ (rb x : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon)),
    FamRecRecord E₀ rb crb rs → ConstAddrOf rb crb x →
    env.find? (keyOf t x) = some (.recInfo cv mI rP rules) → HasModel env (keyOf t x)

/-- The clause is kept by a step that stores no recursor at a member of a block of recursors
beside recursors with a model companion. -/
theorem FamilyRecsModeled.step {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} (h : FamilyRecsModeled t E₀ env)
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {c : ConstantInfo .anon},
      env.find? k = some c → env₂.find? k = some c)
    (hnew : ∀ (k : Ix.Kernel.Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
      (rules : List (RecRule .anon)), env₂.find? k = some (.recInfo cv mI rP rules) →
      env.find? k = some (.recInfo cv mI rP rules) ∨ HasModel env₂ k) :
    FamilyRecsModeled t E₀ env₂ := by
  intro rb x crb rs cv mI rP rules hR hx hf
  rcases hnew _ cv mI rP rules hf with hold | hm
  · exact (h rb x crb rs cv mI rP rules hR hx hold).mono hfind
  · exact hm

/-- **With the clause, a family record whose recursors are stored as recursors is installed.** -/
theorem familyInstalled_of_clause {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} (h : FamilyRecsModeled t E₀ env) (hR : FamRecRecord E₀ rb crb rs)
    (hstored : ∀ x, ConstAddrOf rb crb x →
      ∃ cv mI rP rules, env.find? (keyOf t x) = some (.recInfo cv mI rP rules)) :
    FamilyInstalled t env rb crb := by
  intro x hx
  obtain ⟨cv, mI, rP, rules, hf⟩ := hstored x hx
  exact ⟨⟨cv, mI, rP, rules, hf⟩, h rb x crb rs cv mI rP rules hR hx hf⟩

/-! ## The generated terms of IxC's twin record -/

section Generated

variable {J : Judgements .anon} {env : Ix.Kernel.Env .anon}

/-- **A term is typed as IxC's twin record asks of a generated term**: closed, over the given
level parameters, resolved, bounded, and inferred at the environment. -/
def GenTyped (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (lps : List LevelParam)
    (g : KExpr) : Prop :=
  g.hasFvar = false ∧ g.allLevelParamsDefined lps = true ∧ g.constsResolve env = true ∧
    g.looseBVarsBounded 0 = true ∧ ∃ ty, J.infer env 0 g ty

/-- **The generated type of a twin recursor**, as `DeclRecTwinRunJ` asks it: one term related by
`WrapRel` to the canonical recursor's type and to the twin's checked type, which is the canonical
type or is typed. -/
def TwinTypeGen (J : Judgements .anon) (env : Ix.Kernel.Env .anon)
    (cvC cvW' : ConstantVal .anon) : Prop :=
  ∃ tyG : KExpr, WrapRel env.find? tyG cvC.type ∧ WrapRel env.find? tyG cvW'.type ∧
    (tyG = cvC.type ∨ GenTyped J env cvC.levelParams tyG)

/-- **The generated right-hand side of a twin rule**, as `TwinRuleJ` asks it. -/
def TwinRuleGen (J : Judgements .anon) (env : Ix.Kernel.Env .anon) (f : KKey → KKey)
    (lps : List LevelParam) (rC rW' : RecRule .anon) : Prop :=
  ∃ rhsG : KExpr, WrapRel env.find? rhsG rC.rhs ∧
    WrapRel env.find? (rhsG.renameConsts f) rW'.rhs ∧
    (rhsG = rC.rhs ∨ GenTyped J env lps rhsG)

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
  refine ⟨type, h, WrapRel.refl _ _, Or.inr ⟨hfv', ?_, hres, hlb', stype, hinf⟩⟩
  rw [← hlps]
  exact hlp

/-- Where the two records consumed different wrappers, a common term above both that is typed
is the generated type. The circuit's reconstruction is above both; its typing is the fact to
supply. -/
theorem twinTypeGen_of_typed {cvC cvW' : ConstantVal .anon} {g : KExpr}
    (hC : WrapRel env.find? g cvC.type) (hW : WrapRel env.find? g cvW'.type)
    (ht : GenTyped J env cvC.levelParams g) : TwinTypeGen J env cvC cvW' :=
  ⟨g, hC, hW, Or.inr ht⟩

/-- Where the canonical rule, renamed to the twin's peers, is above the twin's rule, the
canonical right-hand side is the generated one: nothing is typed. -/
theorem twinRuleGen_of_canonical_above {f : KKey → KKey} {lps : List LevelParam}
    {rC rW' : RecRule .anon} (h : WrapRel env.find? (rC.rhs.renameConsts f) rW'.rhs) :
    TwinRuleGen J env f lps rC rW' :=
  ⟨rC.rhs, WrapRel.refl _ _, h, Or.inl rfl⟩

/-- A common right-hand side above both rules that is typed at the environment is the generated
one. No front door types a rule's right-hand side, so in every case but the one above this
typing has to be supplied. -/
theorem twinRuleGen_of_typed {f : KKey → KKey} {lps : List LevelParam}
    {rC rW' : RecRule .anon} {g : KExpr} (hC : WrapRel env.find? g rC.rhs)
    (hW : WrapRel env.find? (g.renameConsts f) rW'.rhs) (ht : GenTyped J env lps g) :
    TwinRuleGen J env f lps rC rW' :=
  ⟨g, hC, hW, Or.inr ht⟩

/-- The generated type is the clause of the circuit-facing contract of a modeled twin
(`ModeledTwinMemberOut.ty_gen`). -/
theorem twinTypeGen_iff_ty_gen {w : TwinRecPart .anon} :
    TwinTypeGen J env w.cvC w.cvW' ↔
      ∃ tyG : KExpr,
        WrapRel env.find? tyG w.cvC.type ∧
        WrapRel env.find? tyG w.cvW'.type ∧
        (tyG = w.cvC.type ∨
          (tyG.hasFvar = false ∧ tyG.allLevelParamsDefined w.cvC.levelParams = true ∧
            tyG.constsResolve env = true ∧ tyG.looseBVarsBounded 0 = true ∧
            ∃ sty, J.infer env 0 tyG sty)) :=
  Iff.rfl

end Generated

end IxVM.Refinement.Typing.TwinFamily
