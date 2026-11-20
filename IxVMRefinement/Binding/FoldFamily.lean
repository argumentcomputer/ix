import IxVMRefinement.Binding.WalkedStored
import IxVMRefinement.Binding.ClosureFoldProof
import IxVMRefinement.Binding.ClauseFold
import IxVMRefinement.Binding.StrEqns

/-! # The binding fold with its modeled blocks' families: the invariant, the group step, the fold

The binding fold over the fold's clause (`IxVMRefinement.Binding.ClauseFold`) carries `BndOver`
from group to group. Its family form carries two facts beside it, which the closure fold reads
and concludes (`ClosureStepOverFamilyW`) and which the typing half imports:

* `WalkedStored ρ t G R env`: every non-block record of `R` in Lean's logic with its block that the
  run checked is stored at its key, and so is the record of every walked role of a group of `G`.
  It reads the run record `ρ`, so it is no field of `BoundaryFacts`, which reads no run;
* `StoredFamilies t R env famOf`: one selected family record per stored modeled block.

Here:

* `BndOverW L ρ t G R env`: the invariant
  `BndOver ∧ WalkedStored ρ ∧ RecordsStored ∧ ∃ famOf, StoredFamilies`; `RecordsStored` (every
  non-block record of the store is stored) passes through a group: the closure stores what it adds
  (`ClosureStepOverFamilyW`), a role unit's record is at a kept role's key, which the invariant
  before the raise stores (`recordsStored_roleUnit`), and a group with no role unit keeps the
  closure's entries;
* `RoleUnitStepOverW P L ρ t g`: the step of a group whose one role is a role unit, handed beside
  `RoleUnitStepOver`'s premises the store before the group within the closure's store
  (`StoreLe R R₁`), the walked records stored at the closure's store and one stored family map
  there; it concludes, beside the invariant before the raise, the walked records stored on the
  groups up to `g` and the same family map stored at the grown store and environment;
* `GroupStepOverW L Fam ρ t g`: the step of a group, from the invariant below `g`, the admission
  of `g` with its reading clause, the run's family checks of the group (`Fam`) and their store
  side (`FamilyAdmits`);
* `groupStepOverW_of_parts`: the step from the closure in the family form, the stored shapes
  where the group has no role unit, and the two role units. At a group with no role unit the
  walked records of the group are kept roles, which the closure stores (`GroupKept`), and the
  closure's store has the group's store's entries, so the families pass by store congruence;
* `fold_groups_overW`, `overWFam_of_bndOverW`: the fold over the groups from 6 to 77 and the
  witness of the internal part with its stored families (`OverWFam`);
* `FamiliesChain Run Fam`: the run gives, at each group, a family selection with the run's family
  checks and their store side. At the binding run predicate and `ClosureFam` it is the type of the
  run predicate's field of the families (its producer is the claim's export);
* `BasisOverW L Run`: the invariant with its family form at the six basis groups;
* `binding_skeleton_overW`: **the binding half for the internal part with its stored families**,
  `BindingSpecOn (OverWFam L)`, from named hypotheses each about a run.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The invariant and the steps' interfaces -/

/-- **The binding fold's invariant with its family form** (module docstring). -/
structure BndOverW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop where
  bnd : BndOver.{u} L t G R env
  walked : WalkedStored ρ t G R env
  stored : RecordsStored t R env
  fams : ∃ famOf, StoredFamilies t R env famOf

/-- **The step of a group whose one role is a role unit, with the family form** (module
docstring); `P` is membership in the operations or in the standard axioms. -/
def RoleUnitStepOverW (P : Ix.Kernel.Role → Prop)
    (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun) (t : Ix.Kernel.RoleTable)
    (g : Nat) : Prop :=
  ∀ (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env) (env₁ : Ix.Kernel.Env .anon)
    (famOf₁ : _root_.Address → Option _root_.Address),
    roleGroup g = [r] → P r → t.addressOf? r = some a → Admits ρ t g R R' →
    AdmitsReads ρ t R R' → BndOver.{u} L t (· < g) R₁ env₁ → AddsAt R₁ R' a → StoreLe R R₁ →
    WalkedStored ρ t (· < g) R₁ env₁ → StoredFamilies t R₁ env₁ famOf₁ →
    StoreLevelsParams t R' →
    ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env₁.consts, ci ∈ env'.consts) ∧
      BeforeRaise.{u} L t g R' env' ∧ WalkedStored ρ t (· < g + 1) R' env' ∧
      StoredFamilies t R' env' famOf₁

/-- **The step of group `g` with the family form** (module docstring). `Fam` is what the run's
family checks give at the group (`ClosureFam` at a binding run). -/
def GroupStepOverW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (Fam : Ixon.Env → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → _root_.Address → Prop) → (_root_.Address → _root_.Address → Prop) →
      Prop)
    (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop),
    BndOverW.{u} L ρ t (· < g) R env → Admits ρ t g R R' → AdmitsReads ρ t R R' →
    Fam R R' famOf adv cont → FamilyAdmits ρ t g R R' famOf adv cont →
    ∃ env' : Ix.Kernel.Env .anon, (∀ ci ∈ env.consts, ci ∈ env'.consts) ∧
      BndOverW.{u} L ρ t (· < g + 1) R' env'

/-! ## The two facts along a store with the same entries and along a grown store -/

/-- **The walked records stored depend on the store only through its records.** -/
theorem walkedStored_storeCongr {ρ : BRun} {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R R' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a) (h : WalkedStored ρ t G R env) :
    WalkedStored ρ t G R' env := by
  refine ⟨fun x c n hx hnb hlog hlogB hchk => ?_, h.2⟩
  rw [← recordOf_storeCongr hc] at hx
  exact h.1 x c n hx hnb hlog
    (fun cb hcb => hlogB cb (by rw [← recordOf_storeCongr hc]; exact hcb)) hchk

/-- **The non-block records stored depend on the store only through its records.** -/
theorem recordsStored_storeCongr {t : Ix.Kernel.RoleTable} {R R' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (h : RecordsStored t R env) : RecordsStored t R' env := by
  intro x c hx hnb
  rw [← recordOf_storeCongr hc] at hx
  exact h x c hx hnb

set_option maxRecDepth 100000 in
private theorem opRoles_walked : RoleOps.opRoles.all (fun r => walkedRole r) = true := by
  decide +kernel

/-- **The non-block records stored after a role unit's step**: a record held at the closure's
store was stored there, and the environment grows; the role unit's record is at the key of a kept
role of the group (an operation is a walked role, a standard axiom a kept role), which the
invariant before the raise past the group stores. -/
theorem recordsStored_roleUnit {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role} {a : _root_.Address}
    {R₁ R' : Ixon.Env} {env₁ env' : Ix.Kernel.Env .anon} (htwf : t.wf = true)
    (hr : r ∈ roleGroup g) (hk : r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms)
    (ha : t.addressOf? r = some a) (hadds : AddsAt R₁ R' a)
    (hext : ∀ ci ∈ env₁.consts, ci ∈ env'.consts) (hB : BeforeRaise.{u} L t g R' env')
    (h : RecordsStored t R₁ env₁) : RecordsStored t R' env' := by
  intro x c hx hnb
  cases h' : R'.consts.get? x with
  | none =>
    unfold recordOf at hx
    rw [h'] at hx
    cases hx
  | some lc =>
    rcases hadds.2.1 x lc h' with h₁ | hxa
    · have hx₁ : recordOf R₁ x = some c := by
        unfold recordOf at hx ⊢
        rw [h₁]
        rw [h'] at hx
        exact hx
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (h x c hx₁ hnb)
      exact Option.isSome_iff_exists.mpr ⟨ci, find_of_ext hext hB.shape.reading.nodup hci⟩
    · have hkr : keptRole r := by
        rcases hk with hop | hs
        · exact Or.inl (Or.inl (List.all_eq_true.mp opRoles_walked r hop))
        · exact Or.inr hs
      obtain ⟨ci, hci, -⟩ := hB.shape.kept g r a (Nat.lt_succ_self g) hr hkr ha
      have hkey : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
      rw [hxa, hkey]
      exact Option.isSome_iff_exists.mpr ⟨ci, hci⟩

/-- **The route of a block depends on the store only through its records.** -/
theorem blockRoute_storeCongr {R R' : Ixon.Env}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a) (B : _root_.Address) :
    Route.blockRoute R' B = Route.blockRoute R B := by
  cases hB : recordOf R B with
  | none =>
    have hB' : recordOf R' B = none := by
      rw [← recordOf_storeCongr hc]
      exact hB
    simp [Route.blockRoute, hB, hB']
  | some cb =>
    refine blockRoute_congr hB (by rw [← recordOf_storeCongr hc]; exact hB) (fun a _ => ?_)
    unfold Route.isIndAt
    rw [recordOf_storeCongr hc]

/-- **The stored families pass to a store closed under what its records use that holds the
records and blobs of the first**, and to an environment that keeps what the first stores and the
family records installed, provided the blocks the new store routes as modeled and the new
environment stores were already so at the first. -/
theorem storedFamilies_grow {t : Ix.Kernel.RoleTable} {R₁ R' : Ixon.Env}
    {env₁ env' : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    (hle : ∀ a c, recordOf R₁ a = some c → recordOf R' a = some c)
    (hblob : ∀ x b, R₁.blobs.get? x = some b → R'.blobs.get? x = some b) (hclosed : UsedClosed R')
    (hblocks : ∀ B cb, recordOf R' B = some cb → Route.blockRoute R' B = some true →
      (∀ x, ConstAddrOf B cb x → StoredAt t env' x) →
      recordOf R₁ B = some cb ∧ Route.blockRoute R₁ B = some true ∧
        ∀ x, ConstAddrOf B cb x → StoredAt t env₁ x)
    (hst : ∀ x, StoredAt t env₁ x → StoredAt t env' x)
    (hinst : ∀ rb crb, FamilyInstalled t env₁ rb crb → FamilyInstalled t env' rb crb)
    (hfind : ∀ {k : Ix.Kernel.Key .anon} {ci : Ix.Kernel.ConstantInfo .anon},
      env₁.find? k = some ci → env'.find? k = some ci)
    (hlp : StoreLevelsParams t R')
    (h : StoredFamilies t R₁ env₁ famOf) : StoredFamilies t R' env' famOf where
  selected := fun B cb hB hroute hstored => by
    obtain ⟨hB₁, hroute₁, hst₁⟩ := hblocks B cb hB hroute hstored
    exact h.selected B cb hB₁ hroute₁ hst₁
  family := fun B rb hrb => by
    obtain ⟨cb, ms, crb, rs, flat, hF⟩ := h.family B rb hrb
    exact ⟨cb, ms, crb, rs, flat,
      familyOfBlock_of_closed hclosed (hle _ _ hF.block.record) (hle _ _ hF.record.record) hF⟩
  blockStored := fun B rb cb hrb hcb x hx => by
    obtain ⟨cb₁, ms, crb, rs, flat, hF⟩ := h.family B rb hrb
    have e : cb₁ = cb := rec_eq (hle _ _ hF.block.record) hcb
    have hB₁ := hF.block.record
    rw [e] at hB₁
    exact hst x (h.blockStored B rb cb hrb hB₁ x hx)
  installed := fun B rb crb hrb hcrb => by
    obtain ⟨cb, ms, crb₁, rs, flat, hF⟩ := h.family B rb hrb
    have e : crb₁ = crb := rec_eq (hle _ _ hF.record.record) hcrb
    have hrb₁ := hF.record.record
    rw [e] at hrb₁
    obtain ⟨hs, hi⟩ := h.installed B rb crb hrb hrb₁
    exact ⟨fun x hx => hst x (hs x hx), hinst rb crb hi⟩
  flat := storedFamiliesFlat_grow hle hblob hclosed h.flat
  form := storedFamiliesForm_grow hle hblob h.form
  recs := fun B rb cb crb hrb hcb hcrb => by
    obtain ⟨cb₁, ms, crb₁, rs, flat, hF⟩ := h.family B rb hrb
    have e1 : cb₁ = cb := rec_eq (hle _ _ hF.block.record) hcb
    have e2 : crb₁ = crb := rec_eq (hle _ _ hF.record.record) hcrb
    subst e1 e2
    exact (h.recs B rb cb₁ crb₁ hrb hF.block.record hF.record.record).mono hle hblob hfind
  levelsParams := hlp

/-- **The stored families depend on the store only through its records and blobs**, at a store
closed under what its records use. -/
theorem storedFamilies_storeCongr {t : Ix.Kernel.RoleTable} {R R' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a) (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a)
    (hclosed : UsedClosed R')
    (h : StoredFamilies t R env famOf) : StoredFamilies t R' env famOf :=
  storedFamilies_grow (fun a c hac => by rw [← recordOf_storeCongr hc]; exact hac)
    (fun x b hx => by rw [← hb x]; exact hx) hclosed
    (fun B cb hB hroute hst => by
      rw [← recordOf_storeCongr hc] at hB
      rw [blockRoute_storeCongr hc] at hroute
      exact ⟨hB, hroute, hst⟩)
    (fun _ h => h) (fun _ _ h => h) (fun h => h) (h.levelsParams.of_storeCongr hc) h

/-- **The walked records of a group with no role unit are stored once its kept roles are**: the
walked roles of the group are kept roles. -/
theorem walkedStored_succ_of_kept {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (htwf : t.wf = true) (hW : WalkedStored ρ t (· < g) R env)
    (hkept : ∀ r ∈ roleGroup g, keptRole r → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci) :
    WalkedStored ρ t (· < g + 1) R env := by
  refine ⟨hW.1, fun r x hw hgr ha => ?_⟩
  by_cases hlt : Ix.SpecDigest.groupOf r < g
  · exact hW.2 r x hw hlt ha
  · have hgr' : Ix.SpecDigest.groupOf r < g + 1 := hgr
    have e : Ix.SpecDigest.groupOf r = g := by omega
    have hr : r ∈ roleGroup g := by
      rw [← e]
      exact role_mem_roleGroup r
    obtain ⟨ci, hci⟩ := hkept r hr (Or.inl (Or.inl hw)) x ha
    have hkey : keyOf t x = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
    rw [hkey]
    exact Option.isSome_iff_exists.mpr ⟨ci, hci⟩

/-! ## The step of a group from its parts -/

private theorem literalRoles_anchors : ∀ r ∈ literalRoles, r ∈ shapeAnchors := by decide

set_option maxRecDepth 100000 in
private theorem literalRoles_groups_le : ∀ r ∈ literalRoles, Ix.SpecDigest.groupOf r ≤ 45 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem natRoles_below :
    Ix.SpecDigest.groupOf .nat < 41 ∧ Ix.SpecDigest.groupOf .natZero < 41 ∧
      Ix.SpecDigest.groupOf .natSucc < 41 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

private theorem valLimit_literalGroup : valLimit 45 = 41 := by decide

/-- **The invariant below `g + 1` at a group with no role unit**, from the closure's invariant
below `g`, the group's kept and prelude roles stored, and the stored shapes below `g + 1`: the
raise past `g` (the fabricated roles' keys and, at group 45, the literal support are derived
here). The store is the closure's. -/
theorem bndOver_succ_of_noUnit {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R₁ : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hall : AllBound t) (htwf : t.wf = true) (hg6 : 6 ≤ g) (hg : g < 77)
    (hnu : ∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms))
    (hb₁ : BndOver.{u} L t (· < g) R₁ env₁) (hkept : GroupKept t g R₁ env₁)
    (hshapes : Shapes (· < g + 1) env₁) :
    BndOver.{u} L t (· < g + 1) R₁ env₁ := by
  have hfab := fabKeys_of_groupKept htwf hg6 hnu hkept
  have hlit : g = 45 → Ix.Kernel.strLitSupported env₁ = true ∧
      ∀ r ∈ literalRoles, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
        ∃ ci, env₁.find? (Core.keyOf t a) = some ci := by
    intro h45
    refine ⟨?_, fun r hrl hf a ha => ?_⟩
    · obtain ⟨E, hE⟩ := OpInstall.recordsFor_exists hb₁.shape.committed
      obtain ⟨Reg, hR⟩ := hb₁.clause
      have hC := hR E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)
      obtain ⟨h1, h2, h3⟩ := natRoles_below
      have hlim : ∀ n, some (valLimit g) = some n → n = 41 := by
        intro n hn
        rw [h45, valLimit_literalGroup] at hn
        exact (Option.some.inj hn).symm
      have hnat : Ix.Kernel.natLitSupported env₁ = true :=
        hC.companions.natLit ⟨hall .nat, fun n hn => by rw [hlim n hn]; exact h1⟩
          ⟨hall .natZero, fun n hn => by rw [hlim n hn]; exact h2⟩
          ⟨hall .natSucc, fun n hn => by rw [hlim n hn]; exact h3⟩
      refine strLitSupported_of_shapes hnat hshapes (fun r hr => ?_)
      have hle := literalRoles_groups_le r hr
      show Ix.SpecDigest.groupOf r < g + 1
      omega
    · by_cases hlt : Ix.SpecDigest.groupOf r < g
      · obtain ⟨ci, hci, -⟩ := hb₁.shape.kept _ r a hlt (role_mem_roleGroup r)
          (Or.inl (Or.inr (literalRoles_anchors r hrl))) ha
        rw [Core.keyOf_of_addressOf htwf ha]
        exact ⟨ci, hci⟩
      · have hle : Ix.SpecDigest.groupOf r ≤ 45 := literalRoles_groups_le r hrl
        have hgr : Ix.SpecDigest.groupOf r = g := by omega
        have hmem : r ∈ roleGroup g := by
          rw [← hgr]
          exact role_mem_roleGroup r
        exact hfab r hmem hf a ha
  have htail : g = 76 → Core.PrimEqnEnv env₁ := fun h76 => by
    subst h76
    exact primEqnEnv_of_bndOver hall hb₁ hshapes
  have hraise : RaiseAt t env₁ g :=
    raiseAt_of_noOps hg6 (fun r hr hop' => hnu r hr (Or.inl hop')) hfab hlit htail
  have hB : BeforeRaise.{u} L t g R₁ env₁ :=
    beforeRaise_of_kept hall hb₁ (fun r hr hkr a ha => hkept.1 r hr hkr (hnu r hr) a ha)
      hkept.2 hshapes hraise
  exact bndOver_of_beforeRaise hall hg hB

/-- **The step of group `g` with the family form, from its parts** (module docstring). -/
theorem groupStepOverW_of_parts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {ρ : BRun}
    {t : Ix.Kernel.RoleTable} {g : Nat}
    {Fam : Ixon.Env → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → _root_.Address → Prop) → (_root_.Address → _root_.Address → Prop) →
      Prop}
    (hall : AllBound t) (htwf : t.wf = true) (hg6 : 6 ≤ g) (hg : g < 77)
    (hcl : ClosureStepOverFamilyW.{u} L ρ t g Fam) (hnone : RoleFreeShapes.{u} L ρ t g)
    (hop : RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L ρ t g)
    (hax : RoleUnitStepOverW.{u} (· ∈ standardAxioms) L ρ t g) :
    GroupStepOverW.{u} L Fam ρ t g := by
  intro R R' env famOf adv cont hW hadm hrd hFam hFA
  obtain ⟨hb, hws, hrs, famOf₀, hsf⟩ := hW
  obtain ⟨R₁, env₁, famOf₁, hRR₁, hR₁R', hblobs, hunit, hext, hb₁, hkept, hsf₁, -, -, hws₁,
    hrs₁⟩ := hcl R R' env famOf₀ famOf adv cont hb hws hrs hsf hadm hrd hFam hFA
  by_cases hu : ∃ r ∈ roleGroup g, r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms
  · obtain ⟨r, hr, hk⟩ := hu
    have hsingle : roleGroup g = [r] := roleGroup_unit hr hk
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall r)
    have hadds : AddsAt R₁ R' a := by
      refine ⟨hR₁R'.1, fun x lc hx => ?_, fun x b => ⟨hblobs x b, hR₁R'.2 x b⟩⟩
      cases h₁ : R₁.consts.get? x with
      | some lc' =>
        have e : some lc' = some lc := (hR₁R'.1 x lc' h₁).symm.trans hx
        exact Or.inl e
      | none =>
        obtain ⟨r', hr', ha', -⟩ := hunit x (by rw [hx]; rfl) h₁
        rw [hsingle] at hr'
        have er : r' = r := List.mem_singleton.mp hr'
        rw [er, ha] at ha'
        exact Or.inr (Option.some.inj ha').symm
    rcases hk with hk' | hk'
    · obtain ⟨env', hext', hB', hws', hsf'⟩ :=
        hop r a R R₁ R' env₁ famOf₁ hsingle hk' ha hadm hrd hb₁ hadds hRR₁ hws₁ hsf₁ hFA.levelsParams
      exact ⟨env', fun ci h => hext' ci (hext ci h),
        ⟨bndOver_of_beforeRaise hall hg hB', hws',
          recordsStored_roleUnit htwf hr (Or.inl hk') ha hadds hext' hB' hrs₁, famOf₁, hsf'⟩⟩
    · obtain ⟨env', hext', hB', hws', hsf'⟩ :=
        hax r a R R₁ R' env₁ famOf₁ hsingle hk' ha hadm hrd hb₁ hadds hRR₁ hws₁ hsf₁ hFA.levelsParams
      exact ⟨env', fun ci h => hext' ci (hext ci h),
        ⟨bndOver_of_beforeRaise hall hg hB', hws',
          recordsStored_roleUnit htwf hr (Or.inr hk') ha hadds hext' hB' hrs₁, famOf₁, hsf'⟩⟩
  · have hnu : ∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) :=
      fun r hr hk => hu ⟨r, hr, hk⟩
    have hsame : ∀ x, R₁.consts.get? x = R'.consts.get? x := by
      intro x
      cases h₁ : R₁.consts.get? x with
      | some lc => exact (hR₁R'.1 x lc h₁).symm
      | none =>
        cases h' : R'.consts.get? x with
        | none => rfl
        | some lc =>
          obtain ⟨r', hr', -, hk'⟩ := hunit x (by rw [h']; rfl) h₁
          exact absurd hk' (hnu r' hr')
    have hrec' : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
        (env₁.find? (keyOf t x)).isSome = true := by
      intro x c hrc hnm
      rw [← recordOf_storeCongr hsame] at hrc
      exact hrs₁ x c hrc hnm
    have hshapes : Shapes (· < g + 1) env₁ := hnone hnu R R₁ R' env₁ hadm hrd hR₁R' hb₁ hkept hrec'
    have hb₂ : BndOver.{u} L t (· < g + 1) R₁ env₁ :=
      bndOver_succ_of_noUnit hall htwf hg6 hg hnu hb₁ hkept hshapes
    have hws₂ : WalkedStored ρ t (· < g + 1) R₁ env₁ :=
      walkedStored_succ_of_kept htwf hws₁ (fun r hr hkr a ha => by
        obtain ⟨ci, hci, -⟩ := hkept.1 r hr hkr (hnu r hr) a ha
        exact ⟨ci, hci⟩)
    have hsameB : ∀ x, R₁.blobs.get? x = R'.blobs.get? x := by
      intro x
      cases h₁ : R₁.blobs.get? x with
      | some b => exact (hR₁R'.2 x b h₁).symm
      | none =>
        cases h' : R'.blobs.get? x with
        | none => rfl
        | some b =>
          have := hblobs x b h'
          rw [h₁] at this
          cases this
    exact ⟨env₁, hext, ⟨bndOver_storeCongr hsame hsameB hb₂, walkedStored_storeCongr hsame hws₂,
      recordsStored_storeCongr hsame hrs₁, famOf₁,
      storedFamilies_storeCongr hsame hsameB hadm.usedClosed hsf₁⟩⟩

/-! ## The fold and the witness -/

/-- **The invariant with its family form below every group from 6 to 77**, from the invariant at
the basis groups, the admission of each group, its reading clause, a family selection with the
run's family checks and their store side at each group, and the step of each group. -/
theorem fold_groups_overW {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {ρ : BRun}
    {t : Ix.Kernel.RoleTable} {Rs : Nat → Ixon.Env} {env₆ : Ix.Kernel.Env .anon}
    {Fam : Nat → Ixon.Env → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → _root_.Address → Prop) → (_root_.Address → _root_.Address → Prop) →
      Prop}
    (hbase : BndOverW.{u} L ρ t (· < 6) (Rs 6) env₆)
    (hadm : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1)))
    (hrd : ∀ g, 6 ≤ g → g < 77 → AdmitsReads ρ t (Rs g) (Rs (g + 1)))
    (hfam : ∀ g, 6 ≤ g → g < 77 → ∃ (famOf : _root_.Address → Option _root_.Address)
      (adv cont : _root_.Address → _root_.Address → Prop),
      Fam g (Rs g) (Rs (g + 1)) famOf adv cont ∧
        FamilyAdmits ρ t g (Rs g) (Rs (g + 1)) famOf adv cont)
    (hstep : ∀ g, 6 ≤ g → g < 77 → GroupStepOverW.{u} L (Fam g) ρ t g) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∃ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ env₆.consts, ci ∈ env.consts) ∧ BndOverW.{u} L ρ t (· < g) (Rs g) env := by
  intro g hg
  induction g, hg using Nat.le_induction with
  | base => exact fun _ => ⟨env₆, fun _ h => h, hbase⟩
  | succ g hg ih =>
    intro hg77
    obtain ⟨env, hext, hb⟩ := ih (by omega)
    obtain ⟨famOf, adv, cont, hF, hFA⟩ := hfam g hg (by omega)
    obtain ⟨env', hext', hb'⟩ := hstep g hg (by omega) (Rs g) (Rs (g + 1)) env famOf adv cont hb
      (hadm g hg (by omega)) (hrd g hg (by omega)) hF hFA
    exact ⟨env', fun ci h => hext' ci (hext ci h), hb'⟩

/-- **The invariant on the 77 groups gives a table witness on every group**, for the internal
part with its stored families `OverWFam L`. -/
theorem overWFam_of_bndOverW {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {ρ : BRun}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : BndOverW.{u} L ρ t (· < 77) R env) :
    TableWitness.{u} (OverWFam.{u} L) t (fun _ => True) R env :=
  let hw := overW_of_bndOver h.bnd
  ⟨hw.shape, hw.facts, h.fams⟩

/-! ## The named hypotheses -/

/-- **A family selection at each group, with the run's family checks and their store side**:
for every run, at each group from 6 to 76, a selection `famOf` with advice `adv` and container
recursors `cont` such that `Fam` (the run's family checks at the group, `ClosureFam` at a binding
run) and `FamilyAdmits` hold from the store before the group to the store after it. At
`BindingRun calls` and `ClosureFam calls` it is the type of the run predicate's field of the
families. -/
def FamiliesChain (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop)
    (Fam : BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → ∀ g, 6 ≤ g → g < 77 →
    ∃ (famOf : _root_.Address → Option _root_.Address)
      (adv cont : _root_.Address → _root_.Address → Prop),
      Fam ρ t g (Rs g) (Rs (g + 1)) famOf adv cont ∧
        FamilyAdmits ρ t g (Rs g) (Rs (g + 1)) famOf adv cont

/-- **The six basis groups with the family form**: the invariant below group 6 at the store
`Rs 6`, with the walked records stored and a stored family map. -/
def BasisOverW (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop) : Prop :=
  ∀ t ρ Rs, Run t ρ Rs → AllBound t → t.check = .ok () →
    ∃ env, BndOverW.{u} L ρ t (· < 6) (Rs 6) env

/-! ## The binding half -/

/-- **The binding half for the internal part with its stored families** (module docstring). Its
hypotheses: the claim's export with the observed run record; the six basis groups with the family
form; the admission of each group, its reading clause and the group's families; and for each group
from 6 to 76 of a run, the closure in the family form with the walked records stored, the stored
shapes where the group has no role unit, and the steps of an operation and of a standard axiom
with the family form. -/
theorem binding_skeleton_overW {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {calls : List (Call F)} {d : Digest}
    (bindingClaimExport : BindingClaimExportObs Run calls d)
    (basisGroups : BasisOverW.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupFamilies : FamiliesChain Run Fam)
    (groupClosure : AtGroups Run fun ρ t g => ClosureStepOverFamilyW.{u} L ρ t g (Fam ρ t g))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L)) :
    BindingSpecOn.{u} (OverWFam.{u} L) calls d := by
  intro bytes spec a hde hdig V
  rcases bindingClaimExport bytes spec a hde hdig V with
    hcol | ⟨tb, t, htb, hadmt, hall, E₀, rank, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadmt).wellFormed
    have htwf : t.wf = true := wf_of_check ht
    obtain ⟨env₆, hb6⟩ := basisGroups t _ Rs hrun hall ht
    obtain ⟨env, -, hb⟩ :=
      fold_groups_overW (Fam := fun g => Fam (observedRun calls a t E₀ rank) t g) hb6
      (groupAdmissions t _ Rs hrun) (groupAdmissionReads t _ Rs hrun)
      (groupFamilies t _ Rs hrun)
      (fun g hg6 hg => groupStepOverW_of_parts hall htwf hg6 hg
        (groupClosure t _ Rs hrun hall ht g hg6 hg)
        (groupWithoutRoleUnit t _ Rs hrun hall ht g hg6 hg)
        (operationRoleUnit t _ Rs hrun hall ht g hg6 hg)
        (standardAxiomRoleUnit t _ Rs hrun hall ht g hg6 hg)) 77 (by omega) (Nat.le_refl 77)
    have hlast := groupAdmissions t _ Rs hrun 76 (by omega) (by omega)
    exact Or.inr ⟨tb, t, Rs 77, env, htb, hadmt, hall,
      loadedBy_sub hload hlast.loaded hlast.loadedBlobs, overWFam_of_bndOverW hb⟩

end IxVM.Refinement.Binding
