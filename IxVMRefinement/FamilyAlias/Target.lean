import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Assembly.NativeBlockAux
import IxVMRefinement.Assembly.LateValueStep
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Decl.FamilyDeclInv
import IxVMRefinement.Decl.FamilyMentions
import IxVMRefinement.Assembly.FamilyArm
import IxVMRefinement.Assembly.FamilyFold
import IxVMRefinement.Assembly.FamilyAdviceWalk
import IxVMRefinement.Claim.TopBase
import IxVMRefinement.FamilyAlias.Package
import IxVMRefinement.FamilyAlias.Step
import IxVMRefinement.FamilyAlias.Install
import IxVMRefinement.FamilyAlias.Roots

/-! # The family step: its target at IxC's own record, with model aliases

The one statement the step of a mutual or nested family has to produce from the circuit
(`FamilyStepTarget`), and what the fold gets from it (`modelSide_of_target`).

The target is stated at IxC's renamed record `DeclIndRenRunJ` at the model keys, over the family
package `famJ h` in place of `rulesJ`, after an alias group at derived keys: the circuit's advice
records are stored at keys of their own, and each model key of the record is a definition by its
advice constant. It is stated at any limit of the role context (`lim : Option Nat`: validating at
a group limit, or assumed); the conclusion mentions no limit.

`modelSide_of_target` takes the conclusion's first four conjuncts and nothing else. It gives the
declaration layer's invariant after the block in every set theory, a model companion at every
recursor the block stores, and the constants the step adds: the block's members under their own
names, and the aliases. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (DeclIndRenRunJ)
open Ix.Kernel.Model (rulesJ)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ)

set_option linter.unusedVariables false

/-- **The family check of the block at `B` with the family record at `rb`, at any limit**:
`check_family [rc, B, rb]` observed with calls `cs` under a role context at `lim` (validating at
a group limit, or assumed), the call and its calls in the run. -/
def FamilyCallAtLim (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (B rb : _root_.Address) (lim : Option Nat) (cs : List (Call F)) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.BaseSeams.addr h xb B ∧ Core.BaseSeams.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- The family check at a group limit is the family check at that limit. -/
theorem FamilyCallAt.toLim {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {n : Nat} {cs : List (Call F)}
    (hc : FamilyCallAt calls bAddr t B rb n cs) :
    FamilyCallAtLim calls bAddr t B rb (some n) cs :=
  hc

/-- The family's declaration, as read: the block's constants are the readings of the block
record's and the recursor record's constant addresses, one for each, under distinct keys, and no
basis pin hits. -/
def FamDeclReads (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (blk : List (ConstantInfo .anon)) : Prop :=
  (blk.map (·.name)).Nodup ∧
  (∀ ci ∈ blk, ∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x ∧ Reads t E₀ x ci) ∧
  (∀ x, FamAddr B cb rb crb x → ∃ ci ∈ blk, ci.name = keyOf t x) ∧
  Ix.Kernel.basisPinHit blk = none

/-- **The family step's target.** The hypotheses are the accepted family call on the modeled
route at any limit, the prefix invariant at that limit, the needs of the two records, their inert
clauses, the stored advice and what an advice record uses, the pinned equality stored (every
environment a step is asked at extends a valid table's, `eqPin_of_shape`), freshness and key
freedom. The conclusion is an alias group at
derived keys over the prefix (each alias a definition whose value is a stored constant at the
alias's own level parameters), each alias rooted at a member of the block, the family's
declaration as read, IxC's renamed record at the model keys over `famJ h` (positional
derivations on the terms with the aliases renamed to their targets), and each member stored
after the block as a constant that stores its reading (`StoredAs`: what a unit step hands the
fold for each constant address of the two records). -/
def FamilyStepTarget : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ E : Ixon.Env) (env : Ix.Kernel.Env .anon) (B rb : _root_.Address)
    (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (lim : Option Nat)
    (cs : List (Call F)),
    t.check = .ok () → LoadedReads.RunStore calls E₀ → StepStore calls t E₀ E →
    FamBlockRecord E₀ B cb ms → FamRecRecord E₀ rb crb rs →
    FamilyCallAtLim calls bAddr t B rb lim cs →
    ModeledRouteAt calls B →
    Decl.PrefixInv.{u} E t lim env →
    (∀ x, UsedRef E₀ B x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    InertClause t cb → InertClause t crb →
    (∀ a, AdviceIn cs a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, AdviceIn cs a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA →
    (∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) →
    (∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x)) →
    ∃ (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      FamDeclReads t E₀ B cb rb crb blk ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci)

/-- **The model side of the record** (proved): from an alias group and the renamed record over
the family package, the fold invariant holds after the block in every set theory, and every
recursor the block stores has a model companion. -/
theorem famStep_of_record {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {aliases blk : List (ConstantInfo .anon)}
    (hg : AliasGroup env h aliases)
    (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂) :
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FoldInv V env → Decl.FoldInv V env₂) ∧
    (∀ (k : Ix.Kernel.Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
      (rules : List (Ix.Kernel.RecRule .anon)),
      env₂.find? k = some (.recInfo cv mI rP rules) →
      (⟨aliases ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = none →
      Ix.Kernel.Model.HasModel env₂ k) :=
  ⟨fun V _ hE =>
      Decl.FamilyAlias.foldInv_step_declIndRenJ (nP := 0)
        (Decl.FamilyAlias.judgeFrames_famJ h)
        (fun _ _ _ m => Decl.FamilyAlias.judgeSound_famJ_of m h) hpin hna hd V
        (Decl.FamilyAlias.foldInv_aliasGroup hg hE).1,
    fun _ _ _ _ _ hf hn => Decl.FamilyAlias.hasModel_declIndRenJ hd hf hn⟩

/-- **The constants the step adds**: the block's members under their own names, one for each,
then the aliases. -/
theorem famStep_consts {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {aliases blk : List (ConstantInfo .anon)}
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂) :
    ∃ new : List (ConstantInfo .anon), env₂ = ⟨(new ++ aliases) ++ env.consts⟩ ∧
      (∀ c ∈ new, ∃ ci ∈ blk, c.name = ci.name) ∧
      (∀ ci ∈ blk, ∃ c ∈ new, c.name = ci.name) := by
  obtain ⟨new, heq, hnew, hall⟩ := Decl.FamilyAlias.declIndRunJ_consts_eq hd.shape
  refine ⟨new, ?_, hnew, hall⟩
  rw [heq]
  simp [List.append_assoc]

/-- **What the fold gets from the target's conclusion** (proved): the declaration layer's
invariant after the block in every set theory, a model companion at every recursor the block
stores, and the constants the step adds. No hypothesis beyond the conclusion's four
conjuncts. -/
theorem modelSide_of_target {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address}
    {cb crb : Ixon.Constant} {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {aliases blk : List (ConstantInfo .anon)}
    (hg : AliasGroup env h aliases)
    (hroots : ∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂) :
    (∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FullDeclInv V env → Decl.FullDeclInv V env₂) ∧
    (∀ (k : Ix.Kernel.Key .anon) (cv : ConstantVal .anon) (mI rP : Nat)
      (rules : List (Ix.Kernel.RecRule .anon)),
      env₂.find? k = some (.recInfo cv mI rP rules) →
      (⟨aliases ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = none →
      Ix.Kernel.Model.HasModel env₂ k) ∧
    (∃ new : List (ConstantInfo .anon), env₂ = ⟨(new ++ aliases) ++ env.consts⟩ ∧
      (∀ c ∈ new, ∃ ci ∈ blk, c.name = ci.name) ∧
      (∀ ci ∈ blk, ∃ c ∈ new, c.name = ci.name)) :=
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)
  ⟨Decl.FamilyAlias.fullDeclInv_famStep hg hreads.2.2.2 hna hroots hd,
    fun _ _ _ _ _ hf hn => Decl.FamilyAlias.hasModel_declIndRenJ hd hf hn,
    famStep_consts hd⟩

end IxVM.Refinement.Typing.FamilyAlias
