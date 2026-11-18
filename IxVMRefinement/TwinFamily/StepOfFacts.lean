import IxVMRefinement.TwinFamily.Facts
import IxVMRefinement.TwinFamily.StepKeeps

/-! # The twin's unit step from the facts of the twin record

The twin's unit step at the fold's clause with the family recursors' companions beside it
(`FoldExtra L t E env ∧ FamilyRecsModeled t E₀ fam env`), from the run hypotheses of
`TwinStepTarget`, the block's family record installed and in the reconstruction's form at every
environment the step is handed (wherever those come from), and the facts the circuit side
hands: the second record's declaration as read with the facts of its parts (`TwinPartsFacts`),
and the reload of each new constant. It composes `twinStepTarget_of_facts`,
`twinStepKeeps_foldExtra` and `TwinStepKeeps.and_familyRecsModeled` into
`unitStepTwin_of_installed`. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart NativeFam)

set_option linter.unusedVariables false

/-- **The twin's unit step from the facts** (module docstring). -/
theorem unitStepTwin_of_facts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {recon : _root_.Address → Core.KExpr × List Core.KExpr}
    (hseam : TwinSeam.{u} recon)
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {fam : _root_.Address → Option _root_.Address} {A B rb : _root_.Address}
    {c cb crb : Ixon.Constant} {ms rs' : Array Ixon.MutConst} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hRS : LoadedReads.RunStore calls E₀)
    (hSS : StepStore calls t E₀ E) (hB : FamBlockRecord E₀ B cb ms)
    (hrbB : FamRecOfBlock calls t E₀ B rb crb)
    (hA : FamRecRecord E₀ A c rs') (hsz : rs'.size ≠ 0)
    (hne : A ≠ rb) (hcall : FamilyCallAtLim calls bAddr t B A lim cs)
    (hroute : ModeledRouteAt calls B) (hinert : InertClause t c)
    (hkey : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hinst : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env →
      (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
      (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
      FamilyInstalled t env rb crb)
    (hform : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env →
      (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
      (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
      CanonReconForm t env rb crb recon)
    (hreload : ∀ (env env₂ : Ix.Kernel.Env .anon) (blk : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → TwinDeclReads t E₀ A c blk →
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      ∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) :
    UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb :=
  unitStepTwin_of_installed (twinStepTarget_of_facts hseam) ht hRS hSS hB hrbB hA hsz hne
    hcall hroute hinert hkey hinst hform
    (twinStepKeeps_foldExtra hL (fun x hx => constAddr_hash_size_of_block hA.muts hx)
      hreload).and_familyRecsModeled

/-- **The twin's unit step for a block whose family record is in the graph** (`fam B = some rb`):
the clause `FamilyRecsModeled` gives the family record installed (`familyInstalled_of_clause`),
so the step takes, beside the circuit side and the run facts, only the canonical record in the
reconstruction's form and the reloads. -/
theorem unitStepTwin_of_facts_fam {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {recon : _root_.Address → Core.KExpr × List Core.KExpr}
    (hseam : TwinSeam.{u} recon)
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {fam : _root_.Address → Option _root_.Address} {A B rb : _root_.Address}
    {c cb crb : Ixon.Constant} {ms rs' : Array Ixon.MutConst} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hRS : LoadedReads.RunStore calls E₀)
    (hSS : StepStore calls t E₀ E) (hB : FamBlockRecord E₀ B cb ms)
    (hrbB : FamRecOfBlock calls t E₀ B rb crb) (hfam : fam B = some rb)
    (hA : FamRecRecord E₀ A c rs') (hsz : rs'.size ≠ 0)
    (hne : A ≠ rb) (hcall : FamilyCallAtLim calls bAddr t B A lim cs)
    (hroute : ModeledRouteAt calls B) (hinert : InertClause t c)
    (hkey : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hform : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env →
      (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
      (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
      CanonReconForm t env rb crb recon)
    (hreload : ∀ (env env₂ : Ix.Kernel.Env .anon) (blk : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → TwinDeclReads t E₀ A c blk →
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      ∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) :
    UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb := by
  have hcrb : recordOf E₀ rb = some crb := by
    obtain ⟨rs, -, -, -, hrb, -⟩ := hrbB
    exact hrb.record
  exact unitStepTwin_of_facts hL hseam ht hRS hSS hB hrbB hA hsz hne hcall hroute hinert hkey
    (fun env _ _ _ hXe hrbS => familyInstalled_of_clause hXe.2 hfam hcrb hrbS) hform
    hreload

end IxVM.Refinement.Typing.TwinFamily
