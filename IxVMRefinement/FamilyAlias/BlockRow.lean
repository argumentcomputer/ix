import IxVMRefinement.FamilyAlias.StepKeeps
import IxVMRefinement.FamilyAlias.StepPins
import IxVMRefinement.FamilyGraph.Composition

/-! # The family row from the circuit side's facts

`familyBlockRow_of_circuit`: the residual theorem's row `familyBlock` (`FamilyBlockRow`) from
`unitStepFamily_of_facts` at the row's own hypotheses, with two named premises:

* `FamilyBlockCircuitRow`: what the circuit side hands the step of a block with its family
  record (`FamilyBlockCircuit`): the seam at each environment the step is handed (the family as
  read and the facts of its check), the block's record as a block of inductives, the route fact
  at each inductive the step stores, the companion facts of each recursor it stores, and the load
  facts that reach its new constants;
* `FamilyClaimRow`: a member of the block at the key of a claimed family record's constant
  address is a recursor (`hclaim`).

Everything else is proved: key freedom and the pinned equality from the step context's table
shape and the table's check (`familyKeyFree_of_shape`, `familyEqPin_of_shape`), the addresses'
length from the two block records (`constAddr_hash_size_of_block`), and the keeping of the fold's
clause (`famStepKeeps_foldExtra`). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ)
open IxVM.Refinement.Typing.TwinFamily (FamilyRecsModeled)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts isRecursor)

set_option linter.unusedVariables false

/-- **What the circuit side hands the step of the block at `A` with its family record at
`rb`** (module docstring). -/
structure FamilyBlockCircuit (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat)
    (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (adv : _root_.Address → Prop) (fam : _root_.Address → Option _root_.Address) : Prop where
  /-- The seam: the family as read and the facts of its check, at each environment the step is
  handed. -/
  seam : ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env →
    (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
    (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
    ∃ (blk : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr)
      (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      FamDeclReads t E₀ A c rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss
  /-- The block's record is a block of inductives. -/
  block : ∃ ms, FamBlockRecord E₀ A c ms
  /-- The route fact at each inductive the step stores. -/
  modeled : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
    Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block
  /-- The companion facts of each recursor the step stores. -/
  recs : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls
  /-- The load facts that reach the step's new constants. -/
  loads : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    NewLoads (appCtx ⟨E, env, t, lim⟩ new).stored new

/-- **The circuit side's facts at every block with a family record**, at the hypotheses of the
row `familyBlock`. -/
def FamilyBlockCircuitRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
        (rs : Array Ixon.MutConst), Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
        fam A = some rb → FamRecRecord E₀ rb crb rs →
        FamilyBlockCircuit.{u} L t envT E₀ E lim A c rb crb (adv A) fam

/-- **`hclaim` at every block with a family record**: a member of the block's declaration, at
the key of a constant address of a claimed family record, is a recursor. -/
def FamilyClaimRow : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
        (rs : Array Ixon.MutConst), Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
        fam A = some rb → FamRecRecord E₀ rb crb rs →
        ∀ blk : List (ConstantInfo .anon), FamDeclReads t E₀ A c rb crb blk →
          ∀ (B' rb' x : _root_.Address) (crb' : Ixon.Constant), fam B' = some rb' →
            recordOf E₀ rb' = some crb' → ConstAddrOf rb' crb' x →
            ∀ ci ∈ blk, ci.name = keyOf t x → isRecursor ci = true

/-- **The row `familyBlock` from the circuit side's facts and `hclaim`** (module docstring). -/
theorem familyBlockRow_of_circuit {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hcirc : FamilyBlockCircuitRow.{u} L) (hclaim : FamilyClaimRow.{u}) :
    FamilyBlockRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb
  have hC := hcirc calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb
    crb rs hTop hc hlog hkind hfam hrb
  have hcl := hclaim calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c
    rb crb rs hTop hc hlog hkind hfam hrb
  obtain ⟨bAddr, hW, -⟩ := hTW
  have ht : t.check = .ok () := hW.check_ok
  obtain ⟨ms, hB⟩ := hC.block
  have hsz : ∀ x, FamAddr A c rb crb x → x.hash.size = 32 := by
    intro x hx
    rcases hx with hx | hx
    · exact TwinFamily.constAddr_hash_size_of_block hB.muts hx
    · exact TwinFamily.constAddr_hash_size_of_block hrb.muts hx
  exact unitStepFamily_of_facts hC.seam (familyKeyFree_of_shape hctx.shape ht)
    (familyEqPin_of_shape hctx.shape) hcl
    (famStepKeeps_foldExtra hL hsz hC.modeled hC.recs hC.loads)

end IxVM.Refinement.Typing.FamilyAlias
