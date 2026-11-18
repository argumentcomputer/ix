import IxVMRefinement.Binding.FamilyOf
import IxVMRefinement.Binding.Defs
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.Binding.FamilyFlat

/-! # A group's admission with modeled blocks: the family checks and the store

The run's admission of group `g` (`Admits`) describes the records the group adds by reference:
the walk of the group's roots, used references and projection blocks. A block the circuit
routes as modeled is checked together with records that no reference reaches: the family record
the claim's payload names, the advice records, and the container recursors its witnesses name
(`KernelModeled::check_family`, under the group's validation context). This module states what
the binding fold's family form needs of a group beside `Admits`:

* `ContainerRecIn cs x`: a check of the container recursor at `x` among the calls `cs`;
* `GroupFamilyChecks calls bAddr t E₀ g R R' famOf adv cont`: what the run's family checks give at
  group `g`: every new block of inductive types in Lean's logic that the run routes as modeled,
  where a member's check at the group's limit ran the dispatch, has a selected family record
  `famOf B`,
  the one its family check accepted at the group's validation limit, with that check's advice
  `adv B` and container recursors `cont B`; the selected record is the block's family, position by
  position over the flattened family (`FamilyOfBlock`: complete, so the binding's family check must
  refuse an empty record under a group's validation, batch candidate B1″); and a new non-empty
  block of recursors is a selected family record or was checked as a second family record of a
  block (a twin);
* `FamilyAdmits ρ t g R R' famOf adv cont`: what the group's store holds and in what order: the
  family record of a new block is new, ranked after its block (the block's unit owns it); the
  advice records and container recursors are in the store, and those new in the group are ranked
  before the block (their own units come first); and a new unit is checked by the run's check
  of a unit at the group's limit, or is a selected family record (checked by its block's family
  check, which is no check of a unit). This is the only check clause of a group's admission:
  `Admits` has none, since a check of every new unit as a unit is false of a selected family
  record. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

/-- **A container recursor's check of the record at `x`**: a call of
`KernelModeled::check_container_rec` at `x` among the calls `cs`. -/
def ContainerRecIn (cs : List (Call F)) (x : _root_.Address) : Prop :=
  ∃ (rc xa ib : SourceValue F) (h : Heap F),
    (⟨"KernelModeled::check_container_rec", [rc, xa, ib], h⟩ : Call F) ∈ cs ∧
    Core.S0.addr h xa x

/-- **What a binding run's family checks give at group `g`** (module docstring). -/
structure GroupFamilyChecks (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) : Prop where
  /-- Every block of inductive types in Lean's logic, new in the group, that the run routes as
  modeled has a selected family record, where a member's check at the group's validation limit
  shows the dispatch ran on it. (`ModeledRouteAt` reads the run's observations of the dispatch,
  so it holds of a record the dispatch never saw: the field is asked of blocks of inductive
  types in Lean's logic, the records the modeled arm of `check_const` reaches, and only where
  the check of a member at the group's limit ran that arm's dispatch.) -/
  modeled : ∀ B cb (ms : Array Ixon.MutConst), New R R' B → recordOf E₀ B = some cb →
    InLogic cb → cb.info = .muts ms → (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) →
    ModeledRouteAt calls B →
    (∃ k, k < ms.size ∧ Claim.MemberCheckedLimAt calls bAddr t B ms k (some (valLimit g))) →
    ∃ rb, famOf B = some rb
  /-- The selected record is the one the family check of the new block accepted, under the
  group's validation context; `adv B` and `cont B` hold the check's advice records and
  container recursors. -/
  famCall : ∀ B rb, famOf B = some rb → New R R' B ∧ ModeledRouteAt calls B ∧
    ∃ cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧
      (∀ a, AdviceIn cs a → adv B a) ∧ (∀ x, ContainerRecIn cs x → cont B x)
  /-- The selected record is the block's family, position by position over the flattened family,
  in the run's store. -/
  family : ∀ B rb, famOf B = some rb →
    ∃ cb ms crb rs flat, FamilyOfBlock E₀ B cb ms rb crb rs flat
  /-- The selected record's flattened family, entry by entry: derived from the block's
  constructors and read off the record. `check_family`'s `check_nested_aux` with the changed
  `aux_all_in` (the record's entries, `build_flat_block`, are the derived ones, `nested_walk`,
  in order) and `check_recs` (entry `k` at recursor `k`), at the offset `block_elim` computes. -/
  familyFlat : ∀ B rb, famOf B = some rb → ∃ (cb crb : Ixon.Constant)
      (ms rs : Array Ixon.MutConst) (es : List FamilyFlat.FlatEntry) (off : Nat),
    FamilyOfBlock E₀ B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) ∧
    FamilyFlat.RecordFlat t E₀ rb crb rs es ∧ FamilyFlat.BlockDerivedFlat t E₀ B off es
  /-- A new non-empty block of recursors is a selected family record, or was checked as a
  second family record of a block (a twin). -/
  claimed : ∀ (A : _root_.Address) (c : Ixon.Constant) (rs' : Array Ixon.MutConst),
    New R R' A → recordOf E₀ A = some c → c.info = .muts rs' → 0 < rs'.size →
    (∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ B, famOf B = some A) ∨ ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs

/-- **What the group's store holds for its modeled blocks, and in what order** (module
docstring). -/
structure FamilyAdmits (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) : Prop where
  /-- The family record of a block new in the group is new, after the block. -/
  famNew : ∀ B rb, famOf B = some rb → New R R' B → New R R' rb ∧ ρ.rank g B < ρ.rank g rb
  /-- The advice of a new block's family check is in the store; a new advice record comes
  before the block. -/
  advice : ∀ B rb a, famOf B = some rb → New R R' B → adv B a →
    (recordOf R' a).isSome = true ∧ (New R R' a → ρ.rank g a < ρ.rank g B)
  /-- The container recursors of a new block's family check are in the store; a new one comes
  before the block. -/
  container : ∀ B rb x, famOf B = some rb → New R R' B → cont B x →
    (recordOf R' x).isSome = true ∧ (New R R' x → ρ.rank g x < ρ.rank g B)
  /-- A new unit was checked at the group's limit by a check of a unit, or is the selected family
  record of a block new in the group: installed with that block by its step, checked by the
  block's family check (`GroupFamilyChecks.famCall`), which is no check of a unit. -/
  checked : ∀ a c, New R R' a → recordOf R' a = some c → UnitKind c →
    ρ.checked a (valLimit g) ∨ ∃ B, famOf B = some a ∧ New R R' B

/-- **The family record of a new block is held by the group's store, with its member
projections**: from `famNew` and the store's closure under block members. -/
theorem FamilyAdmits.famRecord_held {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat}
    {R R' : Ixon.Env} {famOf : _root_.Address → Option _root_.Address}
    {adv cont : _root_.Address → _root_.Address → Prop}
    (h : FamilyAdmits ρ t g R R' famOf adv cont) (hc : UsedClosed R')
    {B rb : _root_.Address} (hrb : famOf B = some rb) (hB : New R R' B) :
    ∃ crb, recordOf R' rb = some crb ∧ ∀ rs, crb.info = .muts rs → ∀ i m, rs[i]? = some m →
      recordOf R' (memberAddr rb i m) = some (memberProjection rb i m) := by
  obtain ⟨⟨hsome, -⟩, -⟩ := h.famNew B rb hrb hB
  cases hr : recordOf R' rb with
  | none => simp [hr] at hsome
  | some crb => exact ⟨crb, rfl, fun rs hmuts i m hm => (hc.2 rb crb rs hr hmuts i m hm).1⟩

end IxVM.Refinement.Binding
