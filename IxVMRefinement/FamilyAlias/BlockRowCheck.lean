import IxVMRefinement.FamilyAlias.ClaimRow
import IxVMRefinement.FamilyAlias.BlockLoads
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.Assembly.TypingBasisProj

/-! # The family row from the facts of the family check

`familyBlockRow_of_check`: the residual theorem's row `familyBlock` (`FamilyBlockRow`) from the
circuit side's facts that read the family check (`FamilyBlockCheckRow`): the seam, the
companion facts of each recursor the step stores, and the six load facts at its new constants
that read the family check (`FamilyLoadsCheck`; the other eight are `FamLoadCtx.newLoads`, from
the store, the records and the route fact, `famLoadCtx_of_step`). The other two facts
`familyBlockRow_of_circuit` takes from the circuit side are proved at the row:

* `famBlockRecord_of_run`: the block's record is a block of inductives with its member and
  constructor projection records (`FamilyRun.famInd`, the walk's `TopGraph.members`);
* `famModeledAt_of_run`: the route fact at the block (`ModeledAt E A`), from the run-level
  modeled route of the family check (`FamilyChecksAt.famCall`), the walk's dispatch on the
  block's first member (`MemberCheckedLimAt.dispatch`), the dispatch's functionality and the
  run's coverage (`modeledAt_of_modeledRoute`);

and `hclaim` is `familyClaimRow`. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ)
open IxVM.Refinement.Typing.TwinFamily (FamilyRecsModeled)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts)

set_option linter.unusedVariables false

/-- **The block's record at the family row**: a block of inductives whose member and
constructor projection records the run's store holds. -/
theorem famBlockRecord_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {envT : Ix.Kernel.Env .anon}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hlog : InLogic c) (hfam : fam A = some rb) : ∃ ms, FamBlockRecord E₀ A c ms := by
  obtain ⟨-, -, hG⟩ := hTW
  obtain ⟨cb, ms, hcb, hmuts, hall⟩ := hrun.famInd A rb hfam
  have e : cb = c := Option.some.inj (hcb.symm.trans hc)
  rw [e] at hmuts
  exact ⟨ms,
    { record := hc
      muts := hmuts
      indcs := hall
      logic := hlog
      members := fun i m hm => (hG.members A c ms hTop hc hmuts i m hm).1
      ctors := fun i ind j hm hj => (hG.members A c ms hTop hc hmuts i _ hm).2 ind j rfl hj }⟩

/-- **The route fact at the block of the family row**: the family check runs on the modeled
route of the block (`FamilyChecksAt.famCall`), the walk's check of the block's first member
observed the dispatch on it, and the dispatch's answer is a function of the store's records, so
no good run answers `0` at the block. -/
theorem famModeledAt_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hTW : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hrun : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c : Ixon.Constant} (hTop : Top A) (hc : recordOf E₀ A = some c)
    (hfam : fam A = some rb) : ModeledAt E A := by
  obtain ⟨bAddr', hC⟩ := hrun.checks
  have hroute : ModeledRouteAt calls A := (hC.famCall A rb hfam).1
  obtain ⟨bAddr, hW, -⟩ := hTW
  obtain ⟨cb, ms, hcb, hmuts, hall⟩ := hrun.famInd A rb hfam
  have e : cb = c := Option.some.inj (hcb.symm.trans hc)
  rw [e] at hmuts
  obtain ⟨-, cb', hcb', -, x, hx, -⟩ := hrun.graph.famUnit A rb hfam
  have e' : cb' = c := Option.some.inj (hcb'.symm.trans hc)
  rw [e'] at hx
  have hpos : 0 < ms.size := by
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, -⟩
    · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
    · have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hmuts)
      rw [e2] at hm
      have hmem : m ∈ ms.toList := by simpa using Array.mem_of_getElem? hm
      simpa using List.length_pos_of_mem hmem
  have hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', h⟩ := hW.checked A hTop
    have e3 : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e3] at h
    exact h
  have hm0 : Claim.MemberCheckedLimAt calls bAddr t A ms 0 lim :=
    Claim.membersChecked_of_block hW.runStore hc hmuts hchk 0 hpos
  have hobs := Claim.MemberCheckedLimAt.dispatch hW.runStore hall hm0
  have hcanon₀ : L1.CanonicalHashCoverage E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hW.hashedStored bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage E calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hctx.recordsFor.1
      (fun a v h => hctx.runRecord a v ((hW.runStore.recordOf_eq_recordAt a).trans h))
  exact modeledAt_of_modeledRoute (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
    (hctx.good Ix.Kernel.Env.empty none) hcanon hroute hobs

/-- **What the family step gives the load facts** (`FamLoadCtx`), at each environment the step's
record is taken at: the store's records at the two records' addresses (the run's, decoded), the
route fact, and the new constants: the members at the keys of the two records' constant
addresses (`famStep_consts`, `FamDeclReads`), the aliases definitions at derived keys. -/
theorem famLoadCtx_of_step {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} (hctx : StepCtx.{u} calls t R envT E₀ E)
    {A rb : _root_.Address} {c crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs) (hroute : ModeledAt E A)
    {lim : Option Nat} {env : Ix.Kernel.Env .anon} {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {aliases blk new : List (ConstantInfo .anon)} (hinv : Decl.PrefixInv.{u} E t lim env)
    (hg : AliasGroup env h aliases) (hreads : FamDeclReads t E₀ A c rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩)
    (hst : ∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) :
    FamLoadCtx ⟨E, env, t, lim⟩ new A c ms rb crb rs := by
  have hdec : L1.EnvDecoded E := hctx.recordsFor.1
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hdec a).trans (hctx.runRecord a d hd')
  obtain ⟨new', henv, hnewN, -⟩ := famStep_consts hd
  have h2 : new ++ env.consts = (new' ++ aliases) ++ env.consts := congrArg Ix.Kernel.Env.consts henv
  have hnew : new = new' ++ aliases := List.append_cancel_right h2
  exact
    { wf := hinv.tableWf
      decoded := hdec
      held := hashedBlockProjectionsHeld_of_decoded hdec
      muts := hB.muts
      indcs := hB.indcs
      rmuts := hrb.muts
      recrs := hrb.recrs
      members := fun i m hm => hrec _ _ (hB.members i m hm)
      ctors := fun i ind j hm hj => hrec _ _ (hB.ctors i ind j hm hj)
      rmembers := fun i m hm => hrec _ _ (hrb.members i m hm)
      record := hrec _ _ hB.record
      route := hroute
      newName := by
        intro cn hcn
        rw [hnew] at hcn
        rcases List.mem_append.mp hcn with hm | hm
        · obtain ⟨ci, hci, hn⟩ := hnewN cn hm
          obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci hci
          exact Or.inl ⟨x, hx, hn.trans hk⟩
        · exact Or.inr ⟨(AliasGroup.defn_of_mem hg cn hm).1, AliasGroup.name_aux hg cn hm⟩
      found := by
        intro x hx
        obtain ⟨ci, hci, hk⟩ := hreads.2.2.1 x hx
        obtain ⟨c', hc', -⟩ := hst ci hci
        rw [hk] at hc'
        exact ⟨c', hc'⟩ }

/-- **What the circuit side's family check hands the step of the block at `A` with its family
record at `rb`**: the seam, the companion facts of each recursor the step stores, and the load
facts that reach its new constants (the fields of `FamilyBlockCircuit` that read the family
check). -/
structure FamilyBlockCheck (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
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
  /-- The load facts at the step's new constants that read the family check. -/
  loads : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    FamilyLoadsCheck (appCtx ⟨E, env, t, lim⟩ new).stored new

/-- **The facts of the family check at every block with a family record**, at the hypotheses of
the row `familyBlock`. -/
def FamilyBlockCheckRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
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
        FamilyBlockCheck.{u} L t envT E₀ E lim A c rb crb (adv A) fam

/-- **The circuit side's facts at the family row from those of the family check**: the block's
record and the route fact are proved at the row. -/
theorem familyBlockCircuitRow_of_check {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hchk : FamilyBlockCheckRow.{u} L) : FamilyBlockCircuitRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb
  have hK := hchk calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb
    crb rs hTop hc hlog hkind hfam hrb
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hroute : ModeledAt E A := famModeledAt_of_run hTW hrun hctx hTop hc hfam
  exact
    { seam := hK.seam
      block := ⟨ms, hB⟩
      route := hroute
      recs := hK.recs
      loads := fun env h aliases blk new hinv hg hreads hd hst =>
        (famLoadCtx_of_step hctx hB hrb hroute hinv hg hreads hd hst).newLoads
          (hK.loads env h aliases blk new hinv hg hreads hd hst) }

/-- **The row `familyBlock` from the facts of the family check** (module docstring). -/
theorem familyBlockRow_of_check {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) (hchk : FamilyBlockCheckRow.{u} L) : FamilyBlockRow.{u} L :=
  familyBlockRow_of_circuit hL (familyBlockCircuitRow_of_check hchk) familyClaimRow

end IxVM.Refinement.Typing.FamilyAlias
