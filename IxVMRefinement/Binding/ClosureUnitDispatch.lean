import IxVMRefinement.Binding.ClosureFamilyRun
import IxVMRefinement.Binding.ClauseValueSteps
import IxVMRefinement.Binding.ClauseRecursor
import IxVMRefinement.Binding.ReadsLocal
import IxVMRefinement.Binding.RootSafety
import IxVMRefinement.Assembly.NativeBlockStepOver
import IxVMRefinement.Assembly.BlockRouteFunctional
import IxVMRefinement.Assembly.NativeFormerLength
import IxVMRefinement.Assembly.TypingRecBasisFresh
import IxVMRefinement.Assembly.RawQueryCoverage
import IxVMRefinement.Claim.TopCheckFacts
import IxVMRefinement.FamilyGraph.CheckedKinds

/-! # The plain step of a new unit of a group's closure, by the kind of its record

`ClosureUnitSteps` (`Binding/ClosureFold.lean`) is the closure fold's step of a new unit with no
selected family record, claimed by no block and of no twin's shape. This module proves it at
every group of every binding run (`closureUnitSteps_bindingRun`), by a case split over the
record's kind onto the proved steps of the kinds:

* a definition, theorem or opaque record: `overUnitStep_value`;
* a block of definitions: `overUnitStep_defnBlock`;
* a standalone recursor: `overUnitStep_recLate_of_arm`;
* a block of one inductive type, which the run's dispatch puts on the native route: whose former
  is declared at its telescope (`overUnitStep_nativeBlockTele_closed`), at a definition
  (`overUnitStep_nativeBlockAlias`), or reads as a telescope of another length, which the circuit
  refuses (`overUnitStep_formerTeleOther`).

The other forms do not arise. An empty block has no constant address. A block's member-kind
check, run by the check of its first member, refuses a block of mixed kinds
(`Claim.MemberCheckedLimAt.block_kinds`, `Claim.check_block_member_kinds_uniform`). A non-empty
block of recursors is a twin's shape. A block of inductive types the dispatch answers as modeled
has a selected family record (`ClosureRunFacts.routeNew`): for one inductive type the dispatch's
observation agrees with the route computed from the step's store (`Route.block_is_modeled_agrees`)
and, the closure's store being closed under what its records use, with the route over that store
(`blockRoute_congr`); a block of two or more inductive types is modeled (`modeledRouteAt_of_multi`).

What each step reads of the run about the unit, from the context the fold hands it and from the
run predicate:

* the check at the group's validation limit (`FamilyAdmits.checked`, the family alternative being
  excluded for an unclaimed unit, read at the observed check by `BindingRun.checked_iff`);
* a record store for the closure's store that the run's calls are good for
  (`BindingRun.stepStores`), with the run's hashed records (`BindingRun.hashedStored`);
* key freedom of the record's constant addresses (`plain_keyFree`): a prelude role's key is stored
  before group 6, and an operation's address in the group is the group's role unit, which the
  closure's store lacks;
* the inert and cover clauses, from the run facts `ClosureRunFacts.notInert` and `.needOk`, and
  that the record uses none of its own constant addresses (`plain_notConstAddr`, by rank);
* for a recursor, that the closure's store holds the record heading its major premise
  (`recMajorTie_held`: its key is the key of a reference the record uses, `read_keys`);
* for a block declared at a definition, that its member's key is no literal function's key
  (`ClosureRunFacts.literals`). -/

universe u

set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## Keys in a term and in its annotations -/

/-- A key of a lifted term is a key of the term. -/
theorem keyIn_of_liftLooseBVars {k : Ix.Kernel.Key .anon} (amt : Nat) :
    ∀ (e : Ix.Kernel.Expr .anon) (c : Nat),
      KeyIn k (Ix.Kernel.Expr.liftLooseBVars amt c e) → KeyIn k e
  | .bvar i, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    split at h <;> cases h
  | .fvar i ty, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    exact h
  | .sort u, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h
  | .const n us, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    exact h
  | .lit l, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h
  | .app f a, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h with
    | appFn h => exact .appFn (keyIn_of_liftLooseBVars amt f c h)
    | appArg h => exact .appArg (keyIn_of_liftLooseBVars amt a c h)
  | .lam ty b m, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h with
    | lamTy h => exact .lamTy (keyIn_of_liftLooseBVars amt ty c h)
    | lamBody h => exact .lamBody (keyIn_of_liftLooseBVars amt b (c + 1) h)
  | .forallE ty b m, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h with
    | allTy h => exact .allTy (keyIn_of_liftLooseBVars amt ty c h)
    | allBody h => exact .allBody (keyIn_of_liftLooseBVars amt b (c + 1) h)
  | .letE ty v b l, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h with
    | letTy h => exact .letTy (keyIn_of_liftLooseBVars amt ty c h)
    | letVal h => exact .letVal (keyIn_of_liftLooseBVars amt v c h)
    | letBody h => exact .letBody (keyIn_of_liftLooseBVars amt b (c + 1) h)
  | .proj s i e, c, h => by
    rw [Ix.Kernel.Expr.liftLooseBVars] at h
    cases h with
    | proj => exact .proj _ _
    | projBody h => exact .projBody (keyIn_of_liftLooseBVars amt e c h)

/-- A key of a term with a value substituted is a key of the term or of the value. -/
theorem keyIn_of_instantiate1Lift {k : Ix.Kernel.Key .anon} {v : Ix.Kernel.Expr .anon} :
    ∀ (e : Ix.Kernel.Expr .anon) (d : Nat),
      KeyIn k (Ix.Kernel.Expr.instantiate1Lift e v d) → KeyIn k e ∨ KeyIn k v
  | .bvar i, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    split at h
    · exact Or.inr (keyIn_of_liftLooseBVars d v 0 h)
    · split at h <;> cases h
  | .fvar i ty, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    exact Or.inl h
  | .sort u, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h
  | .const n us, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    exact Or.inl h
  | .lit l, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h
  | .app f a, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h with
    | appFn h => exact (keyIn_of_instantiate1Lift f d h).imp (fun h => .appFn h) id
    | appArg h => exact (keyIn_of_instantiate1Lift a d h).imp (fun h => .appArg h) id
  | .lam ty b m, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h with
    | lamTy h => exact (keyIn_of_instantiate1Lift ty d h).imp (fun h => .lamTy h) id
    | lamBody h => exact (keyIn_of_instantiate1Lift b (d + 1) h).imp (fun h => .lamBody h) id
  | .forallE ty b m, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h with
    | allTy h => exact (keyIn_of_instantiate1Lift ty d h).imp (fun h => .allTy h) id
    | allBody h => exact (keyIn_of_instantiate1Lift b (d + 1) h).imp (fun h => .allBody h) id
  | .letE ty val b l, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h with
    | letTy h => exact (keyIn_of_instantiate1Lift ty d h).imp (fun h => .letTy h) id
    | letVal h => exact (keyIn_of_instantiate1Lift val d h).imp (fun h => .letVal h) id
    | letBody h => exact (keyIn_of_instantiate1Lift b (d + 1) h).imp (fun h => .letBody h) id
  | .proj s i e, d, h => by
    rw [Ix.Kernel.Expr.instantiate1Lift] at h
    cases h with
    | proj => exact Or.inl (.proj _ _)
    | projBody h => exact (keyIn_of_instantiate1Lift e d h).imp (fun h => .projBody h) id

/-- **A key of an annotation of a term is a key of the term.** -/
theorem keyIn_of_annotates {k : Ix.Kernel.Key .anon} {e' e : Ix.Kernel.Expr .anon}
    (h : Annotates e' e) : KeyIn k e' → KeyIn k e := by
  induction h with
  | bvar => intro h; cases h
  | fvar _ ih =>
    intro h
    cases h with
    | fvarTy h => exact .fvarTy (ih h)
  | sort => intro h; cases h
  | const => intro h; exact h
  | lit => intro h; cases h
  | app _ _ ihf iha =>
    intro h
    cases h with
    | appFn h => exact .appFn (ihf h)
    | appArg h => exact .appArg (iha h)
  | lam _ _ iht ihb =>
    intro h
    cases h with
    | lamTy h => exact .lamTy (iht h)
    | lamBody h => exact .lamBody (ihb h)
  | forallE _ _ iht ihb =>
    intro h
    cases h with
    | allTy h => exact .allTy (iht h)
    | allBody h => exact .allBody (ihb h)
  | proj _ ih =>
    intro h
    cases h with
    | proj => exact .proj _ _
    | projBody h => exact .projBody (ih h)
  | letE _ ih =>
    intro h
    rcases keyIn_of_instantiate1Lift _ 0 (ih h) with hb | hv
    · exact .letBody hb
    · exact .letVal hv

/-- **A store closed under what its records use holds the record heading a recursor's major
premise**: the key heading it is a key of the reading of the recursor's type, so the key of a
reference the record uses or the record's own key (`read_keys`), and keys are injective. -/
theorem recMajorTie_held {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) (hwf : t.wf = true)
    {S E₀ : Ixon.Env} (hcl : UsedClosed S) {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (hc : recordOf S A = some c) (hinfo : c.info = .recr rc)
    {P : _root_.Address} (htie : RecMajorTie t E₀ A c rc P) : (recordOf S P).isSome = true := by
  obtain ⟨tyP, E', hread, hann, hmaj⟩ := htie
  have hk : KeyIn (keyOf t P) tyP := keyIn_of_annotates hann (keyIn_of_majorKey hmaj)
  have hkeys := read_keys ht
    (P := fun k => ∃ y, (recordOf S y).isSome = true ∧ k = keyOf t y)
    (fun i hi a ha => ⟨a, (hcl.1 A c hc).2 i hi a ha, rfl⟩)
    (fun i k hs => by
      unfold soloSelf at hs
      split at hs
      · cases Except.ok.inj (Option.some.inj hs)
        exact ⟨A, by rw [hc]; rfl, rfl⟩
      · cases hs)
    (fun i hi => by simp [usedRefIdxs, hinfo, hi]) hread
  obtain ⟨y, hy, hky⟩ := hkeys _ hk
  have e : P = y := Core.keyOf_inj hwf hky
  rw [e]
  exact hy

/-! ## The route of a block of inductive types -/

/-- **The dispatch on a block of inductive types whose first member the run checked**: the route
over the step's store is modeled, or the run observed a native answer. -/
theorem route_or_nativeObs {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ Ec)
    (hcov : L1.CanonicalHashCoverage Ec calls) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {lim : Option Nat}
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B ms 0 lim) :
    Route.blockRoute Ec B = some true ∨ Claim.NativeObsAt calls B := by
  obtain ⟨bp, r, h, h', cs, b, ev, hsub, hb, hB⟩ := Claim.MemberCheckedLimAt.dispatch hS hall hchk
  have g₁ := (hst.good Ix.Kernel.Env.empty lim).sub hsub
  have ha := Route.block_is_modeled_agrees (E := Ec) g₁.1 g₁.2 hb ev
  obtain ⟨v, hv⟩ := ha.known (canonicalHashCoverage_sub hsub hcov)
  have hr := ha.value v hv
  rw [hB] at hv
  cases v with
  | true => exact Or.inl hv
  | false =>
    rw [Route.bit_false] at hr
    subst hr
    exact Or.inr ⟨bp, h, h', cs, b, ev, hsub, hb, hB⟩

/-! ## The block whose former reads as a telescope of another length -/

/-- **The binding fold's step of a one-type native block whose former reads as a telescope of
another length**: no environment the step is asked at exists, the circuit refusing the block
(`formerTeleOther_false`). -/
theorem overUnitStep_formerTeleOther {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat}
    (ht : t.check = .ok ()) (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hcn : Carried lim) (hln : LimWithin G t lim)
    (hnat : NativeRouteAt calls B) (hother : FormerTeleOther t E₀ B cb ind)
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    OverUnitStep.{u} L t G R envT E₀ B cb := by
  intro env Reg hext hnd hcl href hfresh
  exfalso
  have hC₀ := hcl Ec hRc lim hcn hln
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  exact formerTeleOther_false.{u} ht hst hC₀.prefixInv hrec hchk hnat hstored hfreshT hother

/-! ## The keys of a unit's constant addresses -/

set_option maxRecDepth 100000 in
/-- A reserved basis name is the key of a prelude role of the basis groups (decided). -/
theorem reservedBasis_role (r : Ix.Kernel.Role) :
    (Ix.Kernel.reservedBasisNames : List (Ix.Kernel.Key .anon)).contains (.role r) = true →
      r ∈ preludeRoles ∧ Ix.SpecDigest.groupOf r < 6 := by
  cases r <;> decide +kernel

/-- An operation's key is the key of an operation role. -/
theorem opRole_of_key {r : Ix.Kernel.Role}
    (h : (Ix.Kernel.Key.role r : Ix.Kernel.Key .anon) ∈ RoleOps.opNames) : r ∈ RoleOps.opRoles := by
  rw [RoleOps.opNames_eq_map] at h
  obtain ⟨r', hr', he⟩ := List.mem_map.mp h
  cases he
  exact hr'

private theorem bool_false_of_not_true {b : Bool} (h : b = true → False) : b = false := by
  cases b
  · rfl
  · exact (h rfl).elim

section Plain

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {calls : List (Call F)}
  {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R' R₁ : Ixon.Env}
  {env : Ix.Kernel.Env .anon} {famOf₀ famOf : _root_.Address → Option _root_.Address}
  {adv cont : _root_.Address → _root_.Address → Prop} {bAddr : _root_.Address}

/-- **A constant address of a record new in the closure's store is held there and new in the
group**: the record's own address, or a projection record whose block is the record. -/
theorem constAddr_new
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} {c : Ixon.Constant} (hnA : New R R' A)
    (hc₁ : recordOf R₁ A = some c) (hx : ConstAddrOf A c x) :
    (recordOf R₁ x).isSome = true ∧ New R R' x := by
  rcases constAddr_record hC.closed hc₁ hx with ⟨he, -⟩ | ⟨-, P, hP, -, hPo⟩
  · subst he
    exact ⟨by rw [hc₁]; rfl, hnA⟩
  · refine ⟨by rw [hP]; rfl, ⟨by rw [recordOf_of_loaded hC.store.le₂.1 hP]; rfl, ?_⟩⟩
    cases hR : recordOf R x with
    | none => rfl
    | some p =>
      exfalso
      have e : p = P := Option.some.inj ((recordOf_of_loaded hC.store.le₁.1 hR).symm.trans hP)
      subst e
      obtain ⟨hown, -⟩ := hC.bnd.shape.usedClosed.1 x p hR
      rw [hPo, hnA.2] at hown
      simp at hown

/-- A record the closure's store holds is no new role unit's. -/
theorem not_roleUnit_of_held
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {x : _root_.Address} (hx : (recordOf R₁ x).isSome = true) (hnx : New R R' x) :
    ¬ RoleUnitAt t g x := by
  intro hu
  have hnone := hC.noUnit x hu hnx
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨lc, hl, -⟩ := recordOf_some hc
  rw [hnone] at hl
  cases hl

/-- **The key of a constant address of a new unit is free** (module docstring): an address key is
free; a reserved basis name is a prelude role's key, stored before group 6 and so at the step's
environment, against freshness; an operation's address new in the group is the group's role
unit, which the closure's store lacks. -/
theorem plain_keyFree
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (ht : t.check = .ok ()) (hg6 : 6 ≤ g) {envT : Ix.Kernel.Env .anon}
    (hext : ∀ ci ∈ env.consts, ci ∈ envT.consts) {A x : _root_.Address} {c : Ixon.Constant}
    (hnA : New R R' A) (hc₁ : recordOf R₁ A = some c) (hx : ConstAddrOf A c x)
    (hfr : ¬ StoredAt t envT x) : Decl.KeyFree (keyOf t x) := by
  rcases keyOf_cases t x with ⟨hk, -⟩ | ⟨r, hr, hk⟩
  · rw [hk]
    exact keyFree_id x
  · have haddr : t.addressOf? r = some x := Claim.addressOf_eq_some_of_mem_bound ht hr
    obtain ⟨hheld, hnx⟩ := constAddr_new hC hnA hc₁ hx
    have hop : r ∉ RoleOps.opRoles := by
      intro hop
      have hrg := hC.admits.opsOwn x r hnx haddr hop
      exact not_roleUnit_of_held hC hheld hnx ⟨r, hrg, haddr, Or.inl hop⟩
    rw [hk]
    refine ⟨bool_false_of_not_true fun hres => ?_, bool_false_of_not_true fun hnat => ?_,
      bool_false_of_not_true fun hdm => ?_⟩
    · obtain ⟨hpre, hlt⟩ := reservedBasis_role r hres
      obtain ⟨ci, hci, -⟩ := hC.bnd.shape.preludeKept (Ix.SpecDigest.groupOf r) r x
        (Nat.lt_of_lt_of_le hlt hg6) (role_mem_roleGroup r) hpre haddr
      rw [← hk] at hci
      obtain ⟨ci', hmem, hname⟩ := storedAt_of_find hci
      exact hfr ⟨ci', hext ci' hmem, hname⟩
    · exact hop (opRole_of_key (RoleOps.mem_opNames.mpr (Or.inl (List.contains_iff_mem.mp hnat))))
    · exact hop (opRole_of_key (RoleOps.mem_opNames.mpr (Or.inr (List.contains_iff_mem.mp hdm))))

/-- **A new unit uses none of its own constant addresses**: a used reference is new and ranked
below the unit, or held before the group, and a constant address is the unit's own address or a
projection record of it, ranked above it. -/
theorem plain_notConstAddr
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} {c : Ixon.Constant} (hnA : New R R' A)
    (hc' : recordOf R' A = some c) (hc₁ : recordOf R₁ A = some c) (hused : UsedRef ρ.E₀ A x) :
    ¬ ConstAddrOf A c x := by
  intro hx
  rcases hC.admits.rankUsed A x hnA (usedRef₂ hC.admits hc' hused) with ⟨hnx, hrk⟩ | hold
  · rcases constAddr_record hC.closed hc₁ hx with ⟨he, -⟩ | ⟨-, P, hP, hPp, hPo⟩
    · subst he
      exact Nat.lt_irrefl _ hrk
    · have hP' : recordOf R' x = some P := recordOf_of_loaded hC.store.le₂.1 hP
      rcases hC.admits.rankOwner x P hnx hP' hPp with ⟨-, hrk'⟩ | hheld
      · rw [hPo] at hrk'
        exact Nat.lt_asymm hrk hrk'
      · rw [hPo, hnA.2] at hheld
        simp at hheld
  · rcases constAddr_record hC.closed hc₁ hx with ⟨he, -⟩ | ⟨-, P, hP, -, hPo⟩
    · subst he
      rw [hnA.2] at hold
      simp at hold
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hold
      have e : p = P := Option.some.inj ((recordOf_of_loaded hC.store.le₁.1 hp).symm.trans hP)
      subst e
      obtain ⟨hown, -⟩ := hC.bnd.shape.usedClosed.1 x p hp
      rw [hPo, hnA.2] at hown
      simp at hown

end Plain

/-! ## The dispatcher -/

/-- **The plain step of every new unit of the closure of a group of a binding run** (module
docstring): the step of the unit's kind, with what each kind's step reads of the run from the
context and the run predicate. -/
theorem closureUnitSteps_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (ht : t.check = .ok ()) {g : Nat}
    (hg6 : 6 ≤ g) : ClosureUnitSteps.{u} FormerOpenTraceAt calls ρ t g := by
  intro R R' R₁ env envT famOf₀ famOf adv cont bAddr A c hC hext hnd hnA hc hk hca hfa hunc hntw
    hfr
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hS : LoadedReads.RunStore calls ρ.E₀ := hrun.runStore
  have hcov : LoadedReads.HashedRecordsStored calls ρ.E₀ := hrun.hashedStored
  -- the closure's store: within the run's records, and every blob the run loaded
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hblobs : ∀ x b, ρ.E₀.blobs.get? x = some b → R₁.blobs.get? x = some b :=
    fun x b h => hC.store.blobs x b (hC.reads.blobs x b h)
  have hc' : recordOf R' A = some c := recordOf_of_loaded hC.store.le₂.1 hc
  have hc₀ : recordOf ρ.E₀ A = some c := recordOf_of_loaded hloaded hc
  have hnA' : New R R' A := ⟨by rw [hc']; rfl, hnA.2⟩
  have hlogic : InLogic c := hC.admits.logic A c hnA' hc'
  -- a record store for the closure's store
  have hzc : R₁.consts.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := hC.store.le₂.1 _ lc h
      rw [hC.admits.zeroFree.1] at h'
      cases h'
  have hzb : R₁.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some b =>
      have h' := hC.store.le₂.2 _ b h
      rw [hC.admits.zeroFree.2] at h'
      cases h'
  obtain ⟨Ec, hRc, hst⟩ := hrun.stepStores R₁ hloaded
    (fun a b h => hC.admits.loadedBlobs a b (hC.store.le₂.2 a b h))
    (fun p hp lc h => hC.admits.committed p hp lc (hC.store.le₂.1 _ lc h)) ⟨hzc, hzb⟩
  have hcanon₀ : L1.CanonicalHashCoverage ρ.E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hcov bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage Ec calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hst.decoded
      (fun a v h => hst.runRecord a v ((hS.recordOf_eq_recordAt a).trans h))
  -- the unit is a plain unit of the group
  have hplain : PlainUnitAt t g R R' famOf A c :=
    ⟨hnA', hc', hk, not_roleUnit_of_held hC (by rw [hc]; rfl) hnA', hfa, hunc, hntw⟩
  -- the check at the group's validation limit
  have hchkA : ρ.checked A (valLimit g) := by
    rcases hC.famAdmits.checked A c hnA' hc' hk hntw with h | ⟨B, hB, -⟩
    · exact h
    · exact (hunc B hB).elim
  obtain ⟨bAddr', hiff⟩ := hrun.checked_iff
  have hU : UnitCheckedAt calls bAddr' t ρ.E₀ A (some (valLimit g)) := (hiff A _).mp hchkA
  have hcn : Carried (some (valLimit g)) := carried_valLimit g
  have hln : LimWithin (· < g) t (some (valLimit g)) := limWithin_below t g
  -- what every kind's step reads
  have hkeys : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x) :=
    fun x hx => plain_keyFree hC ht hg6 hext hnA' hc hx (hfr x hx)
  have hinert : InertClause t c := fun i hi x hx =>
    Claim.inertKey_keyOf_false ht (hC.run.notInert A c x hplain (usedRef_of_idx hc₀ hi hx))
  have hcover : ∀ env', HandedRefs t envT ρ.E₀ A c env' → CoverAt t env' c :=
    coverAt_of_needOk hc₀ fun i hi x hx _ =>
      ⟨hC.run.needOk A c x hplain (usedRef_of_idx hc₀ hi hx),
        plain_notConstAddr hC hnA' hc' hc (usedRef_of_idx hc₀ hi hx)⟩
  -- the check of a record that declares one constant
  have hdirect : (∀ ms, c.info ≠ .muts ms) →
      Claim.CheckedLimAt calls bAddr' t A (some (valLimit g)) := by
    intro hnm
    rcases hU with h | ⟨c', ms', hc'', hms', -⟩
    · exact h
    · rw [Option.some.inj (hc''.symm.trans hc₀)] at hms'
      exact (hnm ms' hms').elim
  rcases hk with ⟨d, hinfo⟩ | ⟨rc, hinfo⟩ | ⟨ms, hms⟩
  · -- a definition, theorem or opaque record
    exact overUnitStep_value linkLaws_formerOpenTrace ht hS hRc hst hc hloaded hblobs hinfo hlogic
      (hdirect fun ms h => by rw [hinfo] at h; cases h) hcn hln hkeys hinert hcover
  · -- a standalone recursor
    have hchk := hdirect fun ms h => by rw [hinfo] at h; cases h
    have hkey : Decl.KeyFree (keyOf t A) := hkeys A (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩)
    have harm : RecArmRun calls t A (some (valLimit g)) :=
      recArmRun_of_limArm (recArmLimAt_of_checked hS hc₀ hinfo hchk)
    exact overUnitStep_recLate_of_arm ht hS hcov hRc hst hc hloaded hblobs hinfo hlogic harm hcn
      hln hkey hinert hcover
      (recMajorFreshNotBasis_of_arm ht hS hst hc₀ hinfo harm hinert hcover hrun.preludePinned hRc
        hkey)
      (fun P htie => recMajorTie_held ht htwf hC.closed hc hinfo htie)
  · -- a block: every member checked at the group's limit
    have hmem : ∀ k, k < ms.size →
        Claim.MemberCheckedLimAt calls bAddr' t A ms k (some (valLimit g)) := by
      rcases hU with h | ⟨c', ms', hc'', hms', hk'⟩
      · exact (Claim.checked_not_block hS hc₀ hms h).elim
      · rw [Option.some.inj (hc''.symm.trans hc₀), hms] at hms'
        have e : ms' = ms := (Ixon.ConstantInfo.muts.inj hms').symm
        rw [e] at hk'
        exact hk'
    have hpos : 0 < ms.size := by
      obtain ⟨x, hx⟩ := hca
      rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms', hm, -⟩
      · exact (standalone_not_block hs ⟨ms, hms⟩).elim
      · rw [hms] at hms'
        have e : ms = ms' := Ixon.ConstantInfo.muts.inj hms'
        subst e
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (Array.getElem?_eq_some_iff.mp hm).1
    -- the member-kind check: members of one kind
    obtain ⟨xk, rk, h₁, h₂, cs₁, hak, evk, hsubk⟩ :=
      Claim.MemberCheckedLimAt.block_kinds hS (hmem 0 hpos)
    have hkinds := Claim.check_block_member_kinds_uniform hS
      ((hS.recordOf_eq_recordAt A).symm.trans hc₀) hms hak evk hsubk
    -- a modeled route at the step's store gives a family record
    have hnoModel : Route.blockRoute Ec A ≠ some true := by
      intro hroute
      have e : Route.blockRoute Ec A = Route.blockRoute R₁ A := by
        refine blockRoute_congr hc (recordOf_of_recordsFor hRc hc) (fun a ha => ?_)
        have hRa : (recordOf R₁ a).isSome = true := by
          rcases ha with ⟨i, hi, hx⟩ | ⟨ms', i, m, hms', hm, hx⟩
          · exact (hC.closed.1 A c hc).2 i hi a hx
          · rw [hx]
            exact Option.isSome_iff_exists.mpr ⟨_, (hC.closed.2 A c ms' hc hms' i m hm).1⟩
        obtain ⟨ca, hca'⟩ := Option.isSome_iff_exists.mp hRa
        unfold Route.isIndAt
        rw [recordOf_of_recordsFor hRc hca', hca']
      rw [e] at hroute
      obtain ⟨rb, hrb⟩ := hC.run.routeNew R₁ A hC.store hnA' hroute
      rw [hfa] at hrb
      cases hrb
    have hgood := hst.good Ix.Kernel.Env.empty (some (valLimit g))
    rcases hkinds with hdefs | hinds | hrecs
    · -- a block of definitions
      have hdb : DefnBlock ms := fun i m hm =>
        hdefs m (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm))
      exact overUnitStep_defnBlock linkLaws_formerOpenTrace ht hS hcov hRc hst hc
        (fun i mi h => by rw [(hC.closed.2 A c ms hc hms i mi h).1]; rfl) hloaded hblobs hms
        hlogic hdb hmem hcn hln hkeys hinert hcover
    · -- a block of inductive types
      rcases route_or_nativeObs hS hst hcanon hinds (hmem 0 hpos) with hroute | hobs
      · exact (hnoModel hroute).elim
      · by_cases h2 : 2 ≤ ms.size
        · exfalso
          obtain ⟨-, hmod⟩ := modeledRouteAt_of_multi ht hst hc₀ hms h2 hinds
          exact hmod (hobs.nativeAt hgood)
        · obtain ⟨m, rfl⟩ := Claim.array_of_size_one ms (by omega)
          obtain ⟨ind, rfl⟩ := hinds m (by simp)
          have hnat : NativeRouteAt calls A := nativeRouteAt_of_nativeObs hgood hcanon hobs
          have hm0 := hmem 0 (by simp)
          have hmp := hC.closed.2 A c #[.indc ind] hc hms 0 (.indc ind) rfl
          have hRformer : recordOf R₁ (Core.iprjAddr A 0) =
              some (memberProjection A 0 (.indc ind)) := hmp.1
          have hRctors : ∀ j < ind.ctors.size,
              recordOf R₁ (ctorAddr A 0 j) = some (constructorProjection A 0 j) :=
            fun j hj => hmp.2 ind rfl j hj
          have hrec : BlockUnitRecord ρ.E₀ A c ind :=
            ⟨hc₀, hms, hlogic, recordOf_of_loaded hloaded hmp.1,
              fun j hj => recordOf_of_loaded hloaded (hRctors j hj)⟩
          rcases formerAt_cases t ρ.E₀ A c ind with htele | halias | hother
          · exact overUnitStep_nativeBlockTele_closed linkLaws_formerOpenTrace ht hS hcov hRc hst
              hrec (fun a ca h => recordOf_of_loaded hloaded h) hC.closed hc hRformer hRctors
              hblobs hm0 hcn hln hnat htele hkeys hinert hcover hcanon Core.projGuardRunReading
          · exact overUnitStep_nativeBlockAlias ht hS hRc hst hrec hc hRformer hRctors hblobs hm0
              hcn hln hnat halias (hC.run.literals A c ind hplain hms) hkeys hinert hcover hcanon
          · exact overUnitStep_formerTeleOther ht hRc hst hrec hm0 hcn hln hnat hother hinert
              hcover
    · -- a non-empty block of recursors is a twin's shape
      exact (hntw ⟨ms, hms, hpos, hrecs⟩).elim

/-- **The closure's plain unit step at every group of every binding run**, from the run alone:
the residual's `ClosureUnitSteps` hypothesis, discharged. The facts it reads beyond the closure's
context are fields of the run's facts at the group (`ClosureRunFacts`). -/
theorem closureUnitSteps_bindingRun :
    ∀ calls, AtGroups (BindingRun calls) (ClosureUnitSteps.{u} FormerOpenTraceAt calls) :=
  fun _ _ _ _ hrun _ ht _ hg6 _ => closureUnitSteps_of_run hrun ht hg6

end IxVM.Refinement.Binding
