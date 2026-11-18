import IxVMRefinement.Binding.FamilyStep
import IxVMRefinement.Binding.FamilyAdmits
import IxVMRefinement.Binding.Glue
import IxVMRefinement.Callees.RouteDispatch

/-! # What the binding fold's family form gives the witness, and what the typing half imports

The two halves share one witness `(R, env)` of the table's shape and its internal part
(`OverW L`). The typing half's family fold imports two facts about the modeled blocks the
witness already stores; they cannot come from the table's shape alone (a witness of the shape
may store a modeled block without any recursor), so they come from the binding fold's family
form, through the internal part:

* `StoredFamilies t R env famOf`: one selected family record per stored modeled block, indexed
  by the block (`famOf B`): its record in the witness's store `R`, the block's family member by
  member (`FamilyOfBlock`: one recursor per type at least, so non-empty for a non-empty block,
  with each type's recursor at the type's position), stored whole, each recursor with its model
  companion (`FamilyInstalled`);
* `OverWFam L`: the internal part with the stored families beside it, one map for the witness;
* `storedFamily_of_clause`, `StoredFamiliesImport`, `storedFamiliesImport_overWFam`: the first
  import of the typing half, as a consequence of the internal part: at a stored modeled block,
  the selected family and its facts;
* `StoredFamiliesRForm RForm famOf`: the second import (the stored-twin premise): the selected
  family record of every stored modeled block is in the reconstruction's form at every member
  (`RForm B rb`, a placeholder for the twin step's record-level predicate);
* `ClosureStepOverFamily`: the closure of a group with its modeled blocks' families, keeping the
  selected map: `ClosureStepOver` with the run's family checks and `FamilyAdmits` as premises. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The stored families, block-indexed -/

/-- **The family the witness installed for each stored modeled block** (module docstring). -/
structure StoredFamilies (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf : _root_.Address → Option _root_.Address) : Prop where
  /-- A block of `R` the store routes as modeled, whose constant addresses `env` stores, has a
  selected family record. -/
  selected : ∀ B cb, recordOf R B = some cb → Route.blockRoute R B = some true →
    (∀ x, ConstAddrOf B cb x → StoredAt t env x) → ∃ rb, famOf B = some rb
  /-- The selected record is the block's family, member by member, in `R`. -/
  family : ∀ B rb, famOf B = some rb → ∃ cb ms crb rs, FamilyOfBlock R B cb ms rb crb rs
  /-- A block with a selected family is stored. -/
  blockStored : ∀ B rb cb, famOf B = some rb → recordOf R B = some cb →
    ∀ x, ConstAddrOf B cb x → StoredAt t env x
  /-- The selected record is stored whole, each recursor with its model companion. -/
  installed : ∀ B rb crb, famOf B = some rb → recordOf R rb = some crb →
    (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb

/-- **The witness's internal part with its stored families**: `OverW L` and one selected family
map. -/
abbrev OverWFam (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  OverW.{u} L t G R env ∧ ∃ famOf, StoredFamilies t R env famOf

/-- **At a stored modeled block, the selected family and its facts.** -/
theorem storedFamily_of_clause {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {famOf : _root_.Address → Option _root_.Address}
    (h : StoredFamilies t R env famOf) {B : _root_.Address} {cb : Ixon.Constant}
    (hB : recordOf R B = some cb) (hroute : Route.blockRoute R B = some true)
    (hst : ∀ x, ConstAddrOf B cb x → StoredAt t env x) :
    ∃ rb ms crb rs, famOf B = some rb ∧ FamilyOfBlock R B cb ms rb crb rs ∧
      (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb := by
  obtain ⟨rb, hrb⟩ := h.selected B cb hB hroute hst
  obtain ⟨cb', ms, crb, rs, hf⟩ := h.family B rb hrb
  have e : cb' = cb := Option.some.inj (hf.block.record.symm.trans hB)
  subst e
  obtain ⟨hstored, hinst⟩ := h.installed B rb crb hrb hf.record.record
  exact ⟨rb, ms, crb, rs, hrb, hf, hstored, hinst⟩

/-- **The typing half's first import** at the witnesses of the internal part `W`: one selected
family map, and at every stored modeled block its family, member by member, stored whole with its
companions. -/
def StoredFamiliesImport
    (W : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon),
    W t (fun _ => True) R env →
    ∃ famOf : _root_.Address → Option _root_.Address,
      ∀ B cb, recordOf R B = some cb → Route.blockRoute R B = some true →
        (∀ x, ConstAddrOf B cb x → StoredAt t env x) →
        ∃ rb ms crb rs, famOf B = some rb ∧ FamilyOfBlock R B cb ms rb crb rs ∧
          (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb

/-- **The first import holds at the internal part with its stored families.** -/
theorem storedFamiliesImport_overWFam (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) :
    StoredFamiliesImport (OverWFam.{u} L) := by
  intro t R env hW
  obtain ⟨famOf, hF⟩ := hW.2
  exact ⟨famOf, fun B cb hB hroute hst => storedFamily_of_clause hF hB hroute hst⟩

/-- **The second import, the stored-twin premise**: the selected family record of every stored
modeled block is in the reconstruction's form at every member. `RForm B rb` is a placeholder for
the record-level form predicate the twin step's producer uses (the reconstruction's own type at
every member of the record `rb` of block `B`); the predicate's text is the twin step's. -/
def StoredFamiliesRForm (RForm : _root_.Address → _root_.Address → Prop)
    (famOf : _root_.Address → Option _root_.Address) : Prop :=
  ∀ B rb, famOf B = some rb → RForm B rb

/-! ## The closure of a group with its families -/

/-- **The closure of group `g` with its modeled blocks' families** (module docstring). `Fam`
is what the run's family checks give at the group (instantiated with `GroupFamilyChecks` at a
binding run's calls). The stored families before the group are kept and extended. -/
def ClosureStepOverFamily (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) (g : Nat)
    (Fam : Ixon.Env → Ixon.Env → (_root_.Address → Option _root_.Address) →
      (_root_.Address → _root_.Address → Prop) → (_root_.Address → _root_.Address → Prop) →
      Prop) : Prop :=
  ∀ (R R' : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop),
    BndOver.{u} L t (· < g) R env → StoredFamilies t R env famOf₀ →
    Admits ρ t g R R' → AdmitsReads ρ t R R' →
    Fam R R' famOf adv cont → FamilyAdmits ρ t g R R' famOf adv cont →
    ∃ (R₁ : Ixon.Env) (env₁ : Ix.Kernel.Env .anon)
      (famOf₁ : _root_.Address → Option _root_.Address),
      StoreLe R R₁ ∧ StoreLe R₁ R' ∧
      (∀ x b, R'.blobs.get? x = some b → R₁.blobs.get? x = some b) ∧
      (∀ a, (R'.consts.get? a).isSome = true → R₁.consts.get? a = none → RoleUnitAt t g a) ∧
      (∀ ci ∈ env.consts, ci ∈ env₁.consts) ∧
      BndOver.{u} L t (· < g) R₁ env₁ ∧ GroupKept t g R₁ env₁ ∧
      StoredFamilies t R₁ env₁ famOf₁ ∧
      (∀ B rb, famOf₀ B = some rb → famOf₁ B = some rb) ∧
      (∀ B rb, famOf B = some rb → famOf₁ B = some rb)

end IxVM.Refinement.Binding
