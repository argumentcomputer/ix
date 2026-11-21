import IxVMRefinement.FamilyAlias.ClosureFamilyStep

/-! # What one family check gives, for both family rows

`KernelModeled::check_family` checks a block `cb` (members `ms`, at `B`) with its family record
`crb` (members `rs`, at `rb`): it loads the block's types, its constructors and the record's
recursors (`members_val`, three times), reads the payload's advice for each (`get_addrs`), builds
the renaming from the members to their models from those same lists (`src`, `dst`), checks every
member against its model (`member_val`), and every recursor and rule (`check_recs`,
`check_rules`, `check_iota_rule`), and the record's references (`family_refs_ok`).

`FamilyCallFacts` states, over the semantic model, what one such accepted check gives, for one
selection fixed by the check: the family as read `blk` (types, constructors, recursors), the
advice `advM` (each member's model, each rule's theorem; its renaming `advM.ren` is the one the
check builds from the lists, `FamilyCheckFacts.table`), the selected annotated types `tys` and the
selected annotated right-hand sides `rhsss`:

* `canon`: the selected forms are the check's loads (`FamilyTysCanon`; store-free);
* `majorRefs`: the major premise's head of each recursor at its selected type is a reference the
  family record uses;
* `recRefs`: each reference the family record uses is covered at the check's limit, or is one a
  step needs stored;
* at every environment a step of the block is handed (`FamilyStepEnv`): `reads`, the family as
  read (`FamDeclReads`); `checkFacts`, the facts of the check (`FamilyCheckFacts`, the one field
  with typing judgements); `companions`, the companion facts of each recursor at its selected
  type, over the check's own store (`FamRecsCompanion` at `E₀`).

`FamilyCallRow` asks it at every accepted family check. Both family rows follow from it:

* `familyBlockCheckRow_of_call`: the typing side's `FamilyBlockCheckRow`;
* `closureFamilyCheck_of_call`: the binding side's `ClosureFamilyCheck` at every group of every
  binding run.

Nothing a row needs at another store is asked of the check: the companion facts are carried from
the check's store to every store that holds the records the family record uses
(`famRecsCompanion_carry`), which a step's store does (`StepCtx.runRecord`) and every record store
for the closure's store does (the closure's store is closed under what its records use). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Core (KExpr)
open IxVM.Refinement.Decl.FamilyAlias (FamilyAdvice FamilyCheckFacts nonrecsOf recsOf)

set_option linter.unusedVariables false

/-! ## The interface -/

/-- **The major premise's head of each recursor of the family, at its selected annotated type, is
a reference the family record uses** (where the recursor has a rule). Producer:
`KernelModeled::check_rules`, whose `rec_major_pins` reads the head's address off the recursor's
type and loads it as an inductive (`Ingress::get_ci`), and the reader, which reads a constant of
the record's expression from the record's references. -/
def MajorRefs (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (rb : _root_.Address)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) : Prop :=
  ∀ (k : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules₀ : List (RecRule .anon))
    (tyA : KExpr) (p : _root_.Address) (us : List Core.KLevel),
    (recsOf blk)[k]? = some (.recInfo cv mI rP rules₀) →
    tys[(nonrecsOf blk).length + k]? = some tyA → rules₀ ≠ [] →
    (Core.piDomAt mI tyA).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
    UsedRef E₀ rb p

/-- **An environment a step of the block at `B` with its family record at `rb` is handed**, over
the store `E` at the limit `lim`: the calls are good for `E`, which holds the run's records; a
valid table's environment is below it; its names are distinct; it satisfies the prefix invariant
and the fold's extra clause; the block's references are no inert axiom's; what the two records and
the advice `adv` use is stored, or is one of the two records' constant addresses, or is no
reference a step needs; each advice record's constant addresses are stored; none of the two
records' constant addresses is; a reference covered at the limit is stored; and a reference the
block uses is stored or is one a step needs. -/
structure FamilyStepEnv (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (B : _root_.Address) (cb : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (adv : _root_.Address → Prop) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop where
  store : StepStore calls t E₀ E
  shape : ∃ (G : Nat → Prop) (R : Ixon.Env) (envT : Ix.Kernel.Env .anon),
    TableShape.{u} t G R envT ∧ ∀ ci ∈ envT.consts, ci ∈ env.consts
  nodup : (env.consts.map (·.name)).Nodup
  prefixInv : Decl.PrefixInv.{u} E t lim env
  extra : FoldExtra.{u} L t E env
  inert : InertClause t cb
  refs : ∀ x, UsedRef E₀ B x ∨ UsedRef E₀ rb x →
    (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x
  advStored : ∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
    (env.find? (keyOf t x)).isSome = true
  advRefs : ∀ a, adv a → ∀ x, UsedRef E₀ a x →
    (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x
  fresh : ∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none
  /-- A reference covered at the limit (its role walked, its group below the limit) is stored:
  the table's environment below `env` keeps it. -/
  covered : ∀ x, Claim.CoveredAt t lim x → (env.find? (keyOf t x)).isSome = true
  /-- A reference the block uses is stored or is one a step needs stored: the walk of the block
  reads the safety of each used reference it does not cover. -/
  blockRefs : ∀ x, UsedRef E₀ B x → (env.find? (keyOf t x)).isSome = true ∨ NeedOk E₀ x

/-- **What one accepted family check gives** (module docstring): the check of the block `cb` at
`B` (members `ms`) with the family record `crb` at `rb` (members `rs`), under a role context at
`lim`, whose advice records `adv` holds, with the selection the check fixes: the family as read
`blk`, the advice `advM`, the selected annotated types `tys` and right-hand sides `rhsss`. -/
structure FamilyCallFacts (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
    (adv : _root_.Address → Prop) (blk : List (ConstantInfo .anon)) (advM : FamilyAdvice)
    (tys : List KExpr) (rhsss : List (List KExpr)) : Prop where
  /-- The selected forms are the check's loads. Producer: `KernelModeled::member_val` at each
  member (`Ingress::get_ci_iprj`, `get_ci_cprj` at the member's root), `check_recs` (the K
  assertion, the type's scope check) and `check_iota_rule` (each right-hand side's scope check),
  with `Ingress::get_ci_rprj` at each recursor. -/
  canon : FamilyTysCanon t E₀ B cb ms rb crb rs blk tys rhsss
  /-- The major premise's heads are references of the family record (`MajorRefs`). -/
  majorRefs : MajorRefs t E₀ rb blk tys
  /-- Each reference the family record uses is covered at the limit, or is one a step needs
  stored. Producer: `family_refs_ok`'s `assert_inner_refs_safe` (`assert_used_not_block`, and
  `KernelClaim::assert_safe_used_refs`, which reads the safety of the record and its owner unless
  `KernelRoles::walk_covered` answers `1`, only at a reference covered at the limit). -/
  recRefs : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x
  /-- The family as read, at every environment a step is handed. Producer: the check's loads of
  the block and of the family record (`Ingress::load_verified_constant`,
  `Ingress::build_recur_addrs`, `block_ctor_addrs`, `family_recs`) and of each member
  (`Ingress::get_ci` in `member_val`); no member's key is a pinned basis key, which the
  environment stores and the members' keys are not. -/
  reads : ∀ E env, FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    FamDeclReads t E₀ B cb rb crb blk
  /-- The facts of the check at every environment a step is handed. Producer:
  `members_val` (three times), `check_recs`, `check_rules`, `check_iota_rule`, with their typing
  and conversion calls (`KernelInfer::k_infer`, `KernelDefEq::k_is_def_eq`,
  `KernelInfer::k_ensure_sort`) read at the environment. -/
  checkFacts : ∀ E env, FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    FamilyCheckFacts env blk advM tys rhsss
  /-- The companion facts of each recursor at its selected type, over the check's own store, at
  every environment a step is handed. Producer: `check_rules` (`rec_major_pins`,
  `assert_index_vars`, the rule count against the major's constructor count),
  `check_rules_go` (each rule's constructor projection at its position) and the canonical rule
  comparison, with the constructor's return type check at its block. -/
  companions : ∀ E env, FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    FamRecsCompanion E₀ t env blk tys
  /-- The projection check facts for every eligible member of the block, at every environment
  a step is handed. Producer: `KernelModeled::check_projs`. -/
  projs : ∀ E env, FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    Nonempty (BlockProjFacts t E₀ E env B cb ms blk tys advM.ren)

/-- **The facts of every accepted family check** (module docstring): at every family check of
the block at `B` with its family record at `rb` in a run, under a role context at `lim`, on the
modeled route, the records of the run's store, and every advice predicate `adv` that holds the
check's advice records (each advice record the check validates, or each record of the check's own
advice list with a constant address), what the check gives with one selection. -/
def FamilyCallRow (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (B rb : _root_.Address) (cb crb : Ixon.Constant)
    (ms rs : Array Ixon.MutConst) (lim : Option Nat) (cs : List (Call F))
    (adv : _root_.Address → Prop),
    LoadedReads.RunStore calls E₀ → LoadedReads.HashedRecordsStored calls E₀ →
    FamBlockRecord E₀ B cb ms → FamRecRecord E₀ rb crb rs →
    FamilyCallAtLim calls bAddr t B rb lim cs → ModeledRouteAt calls B →
    ((∀ a, AdviceIn cs a → adv a) ∨
      ∃ advAs : List Aiur.Library.Bytes.Address,
        FamilyCallOwn calls bAddr t B rb lim cs advAs ∧
        ∀ a, AdviceListedIn advAs a →
          adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) →
    ∃ (blk : List (ConstantInfo .anon)) (advM : FamilyAdvice) (tys : List KExpr)
      (rhsss : List (List KExpr)),
      FamilyCallFacts.{u} L calls t E₀ lim B cb ms rb crb rs adv blk advM tys rhsss

/-! ## The companion facts at another store -/

/-- **The companion facts carried from the check's store** to a store `E` that holds, at each
reference the family record uses, the check's store's record. Only the major premise's record and
the rules' constructors read the store; the major premise's head is such a reference
(`MajorRefs`). -/
theorem famRecsCompanion_carry {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {rb : _root_.Address} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr}
    (hS : ∀ a, recordOf E₀ a = Ix.Cert.recordAt E₀ a)
    (hE : ∀ p, UsedRef E₀ rb p → ∀ c, recordOf E₀ p = some c → Ix.Cert.recordAt E p = some c)
    (hmaj : MajorRefs t E₀ rb blk tys) (hc : FamRecsCompanion E₀ t env blk tys) :
    FamRecsCompanion E t env blk tys := by
  intro k cv mI rP rules₀ tyA hk htyA
  obtain ⟨h0, hnr⟩ := hc k cv mI rP rules₀ tyA hk htyA
  have hmove : rules₀ ≠ [] → ∀ (p : _root_.Address) (us : List Core.KLevel),
      (Core.piDomAt mI tyA).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
      ∃ cm, Ix.Cert.recordAt E₀ p = some cm ∧ Ix.Cert.recordAt E p = some cm := by
    intro hne p us hhead
    obtain ⟨cm, hcm⟩ := h0.major p us hne hhead
    exact ⟨cm, hcm,
      hE p (hmaj k cv mI rP rules₀ tyA p us hk htyA hne hhead) cm ((hS p).trans hcm)⟩
  refine ⟨⟨fun p us hne hhead => ?_, ⟨h0.rules.1, fun p cm ip us hhead hcm hip j rl hj => ?_⟩,
    h0.plain⟩, hnr⟩
  · obtain ⟨cm, -, h⟩ := hmove hne p us hhead
    exact ⟨cm, h⟩
  · have hne : rules₀ ≠ [] := by
      rintro rfl
      simp at hj
    obtain ⟨cm₀, h₀, h⟩ := hmove hne p us hhead
    have e : cm = cm₀ := Option.some.inj (hcm.symm.trans h)
    subst e
    exact h0.rules.2 p cm ip us hhead h₀ hip j rl hj

/-! ## The typing side's row -/

/-- **The typing side's family row from the facts of the family check**: at the row's block with
its family record, the family check of the run's family checks (`FamilyChecksAt.famCall`, with
its own advice list) gives the selection; the step's environment is one the check's facts are
asked at (the witness's table environment below it, the walk's inert clause at the block); the
companion facts are carried to the step's store, which holds the run's records. -/
theorem familyBlockCheckRow_of_call {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hcall : FamilyCallRow.{u} L) : FamilyBlockCheckRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hneed := Claim.TopWalk.need hTW hTop hc hkind hlog
  obtain ⟨bAddr, hW, -⟩ := hTW
  have hinert : InertClause t c := hW.inertClause hTop hc
  have hS : LoadedReads.RunStore calls E₀ := hW.runStore
  obtain ⟨bAddr', hC⟩ := hrun.checks
  obtain ⟨hroute, cs, advAs, hown, hlist⟩ := hC.famCall A rb hfam
  obtain ⟨blk, advM, tys, rhsss, hF⟩ := hcall calls bAddr' t E₀ A rb c crb ms rs lim cs (adv A)
    hS hW.hashedStored hB hrb hown.toLim hroute (Or.inr ⟨advAs, hown, hlist⟩)
  refine ⟨fun env hextT hnd hinv hX hrefs hadv1 hadv2 hfresh => ?_, hF.recRefs⟩
  have hSE : FamilyStepEnv.{u} L calls t E₀ lim A c rb crb (adv A) E env :=
    { store := hctx.toStepStore
      shape := ⟨fun _ => True, R, envT, hctx.shape, hextT⟩
      nodup := hnd
      prefixInv := hinv
      extra := hX.1
      inert := hinert
      refs := hrefs
      advStored := hadv1
      advRefs := hadv2
      fresh := hfresh
      covered := fun x hx => by
        obtain ⟨ci, hci, hname⟩ :=
          coveredAt_stored hctx.shape hinv.tableWf (fun _ _ => trivial) hx
        exact find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩
      blockRefs := fun x hu => by
        by_cases hcov : Covered t x
        · obtain ⟨ci, hci, hname⟩ := covered_stored hctx.shape hinv.tableWf hcov
          exact Or.inl (find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩)
        · obtain ⟨c', i, hc', hi, hx⟩ := hu
          have e : c' = c := Option.some.inj (hc'.symm.trans hc)
          rw [e] at hi hx
          have hx' : c.refs.toList[i]? = some x := by
            rw [Array.getElem?_toList]
            exact hx
          exact Or.inr (hneed i hi x hx' (hinert i hi x hx') hcov) }
  refine ⟨blk, advM, tys, rhsss, hF.reads E env hSE, hF.checkFacts E env hSE, ?_⟩
  unfold SelectedForms
  refine ⟨fun ms' rs' hms' hrs' => ?_, ?_, fun ms' hms' => ?_⟩
  · have e1 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
    have e2 : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hrb.muts)
    subst e1 e2
    exact hF.canon
  · exact famRecsCompanion_carry hS.recordOf_eq_recordAt
      (fun p _ c' hc' => hctx.runRecord p c' hc') hF.majorRefs (hF.companions E env hSE)
  · have e1 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
    subst e1
    exact hF.projs E env hSE

/-! ## The binding side's row -/

/-- **The binding side's family check at every group of every binding run, from the facts of the
family check**: at a new block with its selected family record, the group's family check
(`GroupFamilyChecks.famCall`, whose advice records the context's advice holds) gives the
selection; the step's environment is one the check's facts are asked at (the fold's table
environment below it, at the group's validation limit); the companion facts are carried to every
record store for the closure's store, which holds the records the family record uses (the
closure's store is closed under what its records use, and holds the family record). -/
theorem closureFamilyCheck_of_call {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hcall : FamilyCallRow.{u} L) :
    ∀ calls, Binding.AtGroups (Binding.BindingRun calls) (ClosureFamilyCheck.{u} L calls) := by
  intro calls t ρ Rs hrun hall ht g hg6 hg R R' R₁ env₀ envT famOf₀ famOf adv cont bAddr B rb cb
    crb hC hextT hndT hnB hcb hunc hfam hcrb hfrT
  have hS : LoadedReads.RunStore calls ρ.E₀ := hrun.runStore
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hcb₀ : recordOf ρ.E₀ B = some cb := Binding.recordOf_of_loaded hloaded hcb
  have hcrb₀ : recordOf ρ.E₀ rb = some crb := Binding.recordOf_of_loaded hloaded hcrb
  obtain ⟨-, hroute, cs, advAs, hown, hadvIn, -⟩ := hC.checks.famCall B rb hfam
  obtain ⟨cb', ms, crb', rs, flat, hFB⟩ := hC.checks.family B rb hfam
  have e1 : cb' = cb := Option.some.inj (hFB.block.record.symm.trans hcb₀)
  subst cb'
  have e2 : crb' = crb := Option.some.inj (hFB.record.record.symm.trans hcrb₀)
  subst crb'
  have hcb' : recordOf R' B = some cb := Binding.recordOf_of_loaded hC.store.le₂.1 hcb
  have hnB' : Binding.New R R' B := ⟨by rw [hcb']; rfl, hnB.2⟩
  obtain ⟨blk, advM, tys, rhsss, hF⟩ := hcall calls bAddr t ρ.E₀ B rb cb crb ms rs
    (some (Binding.valLimit g)) cs (adv B) hS hrun.hashedStored hFB.block hFB.record
    (Binding.FamilyCallOwn.toCall hown)
    hroute (Or.inr ⟨advAs, hown, fun a ha => Or.inl (hadvIn a ha)⟩)
  refine ⟨fun Ec hRc hst env hext hnd hinv hX hinert hrefs hadv1 hadv2 hfresh => ?_, hF.recRefs⟩
  have hSE : FamilyStepEnv.{u} L calls t ρ.E₀ (some (Binding.valLimit g)) B cb rb crb (adv B)
      Ec env :=
    { store := hst
      shape := ⟨(· < g), R, env₀, hC.bnd.shape, fun ci hci => hext ci (hextT ci hci)⟩
      nodup := hnd
      prefixInv := hinv
      extra := hX
      inert := hinert
      refs := hrefs
      advStored := hadv1
      advRefs := hadv2
      fresh := hfresh
      covered := fun x hx => by
        obtain ⟨ci, hci, hname⟩ := coveredAt_stored hC.bnd.shape hinv.tableWf
          (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g)) hx
        exact find_isSome_of_storedAt ⟨ci, hext ci (hextT ci hci), hname⟩
      blockRefs := fun x hu => Or.inr (hC.run.famNeedOk B rb x hfam hnB' hu) }
  refine ⟨blk, advM, tys, rhsss, hF.reads Ec env hSE, hF.checkFacts Ec env hSE,
    fun ms' rs' hms' hrs' => ?_, fun E hE => ?_, fun ms' hms' => ?_⟩
  · have e3 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hFB.block.muts)
    have e4 : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hFB.record.muts)
    subst e3 e4
    exact hF.canon
  · -- a reference the family record uses has the run's record in the closure's store
    refine famRecsCompanion_carry hS.recordOf_eq_recordAt (fun p hp c' hc' => ?_) hF.majorRefs
      (hF.companions Ec env hSE)
    obtain ⟨c₁, i, hc₁, hi, hx⟩ := hp
    have e5 : c₁ = crb := Option.some.inj (hc₁.symm.trans hcrb₀)
    subst e5
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp ((hC.closed.1 rb c₁ hcrb).2 i hi p hx)
    have e6 : P = c' := Option.some.inj ((Binding.recordOf_of_loaded hloaded hP).symm.trans hc')
    subst e6
    exact hE.2.1 p P hP
  · have e3 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hFB.block.muts)
    subst e3
    exact hF.projs Ec env hSE

end IxVM.Refinement.Typing.FamilyAlias
