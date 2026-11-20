import IxVMRefinement.FamilyAlias.StepKeeps
import IxVMRefinement.FamilyAlias.StepPins
import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.TwinFamily.StepKeeps

/-! # The family row from the circuit side's facts

`familyBlockRow_of_circuit`: the residual theorem's row `familyBlock` (`FamilyBlockRow`) from
`unitStepFamily_of_facts` at the row's own hypotheses, with two named premises:

* `FamilyBlockCircuitRow`: what the circuit side hands the step of a block with its family
  record (`FamilyBlockCircuit`): the seam at each environment the step is handed (the family as
  read and the facts of its check), the block's record as a block of inductives, the route fact
  at the block (`ModeledAt E A`), the companion facts of each recursor the step stores, and the
  load facts that reach its new constants;
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

/-- **The route fact at each inductive the family step stores**, from the route fact at the
block, at a store that holds the run's records at the family's addresses: the record there is a
member's or a constructor's projection, so an inductive projection there names the block. -/
theorem famModeled_at {E₀ E : Ixon.Env} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs)
    (hrun : ∀ x, FamAddr A c rb crb x → ∀ d, recordOf E₀ x = some d →
      Ix.Cert.recordAt E x = some d)
    (hmod : ModeledAt E A) :
    ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block := by
  intro x hx cm ip hcm hinfo
  have key : ∀ {d : Ixon.Constant}, recordOf E₀ x = some d → cm = d := fun hd => by
    have h1 := hrun x hx _ hd
    rw [hcm] at h1
    exact Option.some.inj h1
  rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩ |
      ⟨⟨-, hs⟩ | ⟨rs', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩
  · exact (standalone_not_block hs ⟨ms, hB.muts⟩).elim
  · have hmm : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hB.muts)
    subst hmm
    obtain ⟨ind, rfl⟩ := hB.indcs m (by simpa using Array.mem_of_getElem? hget)
    have hc : cm = memberProjection A i (.indc ind) := key (by rw [hxm]; exact hB.members i _ hget)
    subst hc
    have hip : ip = ⟨i.toUInt64, A⟩ := (Ixon.ConstantInfo.iPrj.inj hinfo).symm
    rw [hip]
    exact hmod
  · have hmm : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hB.muts)
    subst hmm
    subst hind
    have hc : cm = constructorProjection A i j := key (by rw [hxc]; exact hB.ctors i ind j hget hj)
    subst hc
    simp [constructorProjection] at hinfo
  · exact (standalone_not_block hs ⟨rs, hrb.muts⟩).elim
  · have hmm : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hrb.muts)
    subst hmm
    obtain ⟨r, rfl⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hget)
    have hc : cm = memberProjection rb i (.recr r) :=
      key (by rw [hxm]; exact hrb.members i _ hget)
    subst hc
    simp [memberProjection] at hinfo
  · have hmm : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hrb.muts)
    subst hmm
    obtain ⟨r, hr⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hget)
    rw [hind] at hr
    exact nomatch hr

/-- **The route fact at each constructor the family step stores**, from the route fact at the
block, at a store that holds the run's records at the family's addresses. -/
theorem famModeled_ctor_at {E₀ E : Ixon.Env} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs)
    (hrun : ∀ x, FamAddr A c rb crb x → ∀ d, recordOf E₀ x = some d →
      Ix.Cert.recordAt E x = some d)
    (hmod : ModeledAt E A) :
    ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (cp : Ixon.ConstructorProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .cPrj cp → ¬ NativeAt E cp.block := by
  intro x hx cm cp hcm hinfo
  have key : ∀ {d : Ixon.Constant}, recordOf E₀ x = some d → cm = d := fun hd => by
    have h1 := hrun x hx _ hd
    rw [hcm] at h1
    exact Option.some.inj h1
  rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩ |
      ⟨⟨-, hs⟩ | ⟨rs', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩
  · exact (standalone_not_block hs ⟨ms, hB.muts⟩).elim
  · have hmm : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hB.muts)
    subst hmm
    obtain ⟨ind, rfl⟩ := hB.indcs m (by simpa using Array.mem_of_getElem? hget)
    have hc : cm = memberProjection A i (.indc ind) := key (by rw [hxm]; exact hB.members i _ hget)
    subst hc
    simp [memberProjection] at hinfo
  · have hmm : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hB.muts)
    subst hmm
    subst hind
    have hc : cm = constructorProjection A i j := key (by rw [hxc]; exact hB.ctors i ind j hget hj)
    subst hc
    have hcp : cp = ⟨i.toUInt64, j.toUInt64, A⟩ := (Ixon.ConstantInfo.cPrj.inj hinfo).symm
    rw [hcp]
    exact hmod
  · exact (standalone_not_block hs ⟨rs, hrb.muts⟩).elim
  · have hmm : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hrb.muts)
    subst hmm
    obtain ⟨r, rfl⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hget)
    have hc : cm = memberProjection rb i (.recr r) :=
      key (by rw [hxm]; exact hrb.members i _ hget)
    subst hc
    simp [memberProjection] at hinfo
  · have hmm : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hrb.muts)
    subst hmm
    obtain ⟨r, hr⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hget)
    rw [hind] at hr
    exact nomatch hr

/-- **The route fact at each inductive the family step stores**, at a store that holds the run's
records (`famModeled_at`). -/
theorem famModeled_of_route {E₀ E : Ixon.Env} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs)
    (hrun : ∀ a d, recordOf E₀ a = some d → Ix.Cert.recordAt E a = some d)
    (hmod : ModeledAt E A) :
    ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block :=
  famModeled_at hB hrb (fun x _ d hd => hrun x d hd) hmod

/-- **The route fact at each constructor the family step stores**, at a store that holds the run's
records (`famModeled_ctor_at`). -/
theorem famModeled_ctor_of_route {E₀ E : Ixon.Env} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ A c ms) (hrb : FamRecRecord E₀ rb crb rs)
    (hrun : ∀ a d, recordOf E₀ a = some d → Ix.Cert.recordAt E a = some d)
    (hmod : ModeledAt E A) :
    ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (cp : Ixon.ConstructorProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .cPrj cp → ¬ NativeAt E cp.block :=
  famModeled_ctor_at hB hrb (fun x _ d hd => hrun x d hd) hmod

/-- **What the circuit side hands the step of the block at `A` with its family record at
`rb`** (module docstring). The companion and load facts are asked at the record that installs the
family check's selected forms (`SelectedInstalled`) and modeled projection tables, with the check's
facts and what the check gives of those forms (`SelectedForms`). -/
structure FamilyBlockCircuit (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat)
    (A : _root_.Address) (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (adv : _root_.Address → Prop) (fam : _root_.Address → Option _root_.Address) : Prop where
  /-- The seam: the family as read, the facts of its check and what it gives of its selected
  forms, at each environment the step is handed. -/
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
      FamDeclReads t E₀ A c rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss ∧
        SelectedForms t E₀ E A c rb crb env blk adv'.ren tys rhsss
  /-- The block's record is a block of inductives. -/
  block : ∃ ms, FamBlockRecord E₀ A c ms
  /-- The route fact at the block. -/
  route : ModeledAt E A
  /-- The companion facts of each recursor the step stores. -/
  recs : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
    (aliases blk new : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
    (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr)),
    Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
    FamDeclReads t E₀ A c rb crb blk →
    FamilyCheckFacts env blk adv' tys rhsss →
    SelectedForms t E₀ E A c rb crb env blk adv'.ren tys rhsss →
    DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
    (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci) →
    SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
    ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls
  /-- The load facts that reach the step's new constants, at an environment that extends the
  witness's and is handed what the two records use. -/
  loads : ∀ (ms : Array Ixon.MutConst), c.info = .muts ms →
    ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop)
      (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk new : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr))
      (bpf : BlockProjFacts t E₀ E env A c ms blk tys adv'.ren)
      (pcs : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      AliasGroup env h aliases →
      FamDeclReads t E₀ A c rb crb blk →
      FamilyCheckFacts env blk adv' tys rhsss →
      SelectedForms t E₀ E A c rb crb env blk adv'.ren tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
      (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
        StoredAs c' ci) →
      SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
      BlockProjInstallResult.{u} t env ⟨new ++ env.consts⟩ Reg A ms bpf.elig pcs →
      NewLoads (appCtx ⟨E, env, t, lim⟩ (pcs ++ new)).stored (pcs ++ new)

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
theorem familyBlockRow_of_circuit
    (hL : LinkLaws FormerOpenTraceAt) (hcirc : FamilyBlockCircuitRow.{u} FormerOpenTraceAt)
    (hclaim : FamilyClaimRow.{u}) :
    FamilyBlockRow.{u} FormerOpenTraceAt := by
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
  exact unitStepFamily_of_facts
    (Sel := fun env blk adv' tys rhsss => SelectedForms t E₀ E A c rb crb env blk adv'.ren tys rhsss)
    hB hC.seam
    (familyKeyFree_of_shape hctx.shape ht) (familyEqPin_of_shape hctx.shape)
    (familyBasisPins_of_shape hctx.shape) hcl
    (fun _ _ _ _ _ hSel => hSel.2.2 ms hB.muts)
    (famStepKeeps_foldExtra
      (Sel := fun env blk adv' tys rhsss => SelectedForms t E₀ E A c rb crb env blk adv'.ren tys rhsss)
      (ms := ms) hL hsz
      (famModeled_of_route hB hrb hctx.runRecord hC.route)
      (famModeled_ctor_of_route hB hrb hctx.runRecord hC.route) hC.recs (hC.loads ms hB.muts))

end IxVM.Refinement.Typing.FamilyAlias
