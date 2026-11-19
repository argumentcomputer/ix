import IxVMRefinement.Binding.FamilyStep
import IxVMRefinement.Binding.FamilyAdmits
import IxVMRefinement.Binding.Glue
import IxVMRefinement.Callees.RouteDispatch
import IxVMRefinement.Binding.FamilyFlatLocal

/-! # What the binding fold's family form gives the witness, and what the typing half imports

The two halves share one witness `(R, env)` of the table's shape and its internal part
(`OverW L`). The typing half's family fold imports two facts about the modeled blocks the
witness already stores; they cannot come from the table's shape alone (a witness of the shape
may store a modeled block without any recursor), so they come from the binding fold's family
form, through the internal part:

* `StoredFamilies t R env famOf`: one selected family record per stored modeled block, indexed
  by the block (`famOf B`): its record in the witness's store `R`, the block's family position by
  position over the flattened family (`FamilyOfBlock`: one recursor per entry, the block's types
  first, so non-empty for a non-empty block; each recursor eliminating its position's entry,
  auxiliary positions included), stored whole, each recursor with its model companion
  (`FamilyInstalled`), its flattened family entry by entry, derived from the block and read
  off the record (`StoredFamiliesFlat`), and its reconstruction form (`StoredFamiliesRForm` at
  `FamilyRecon.RFormS`: each recursor the block's reconstruction at its position). Only a
  complete record is selected: an empty family record is no canonical source, and the binding
  never stores a modeled block with one alone;
* `storedFamiliesFlat_grow`, `storedFamiliesFlat_of_sub`, `storedFamiliesFlat_join`,
  `storedFamiliesFlat_none`: the flattened families across the fold's stores (a larger store, a
  used-closed sub-store of the run's store, a joined map, no selection);
* `OverWFam L`: the internal part with the stored families beside it, one map for the witness;
* `storedFamily_of_clause`, `StoredFamiliesImport`, `storedFamiliesImport_overWFam`: the first
  import of the typing half, as a consequence of the internal part: at a stored modeled block,
  the selected family and its facts;
* `StoredFormPred`, `StoredFamiliesRForm RFormS t R famOf`: the second import (the stored-twin
  premise): the selected family record of every stored modeled block is in the reconstruction's
  form at every member (`RFormS t R B rb`, the twin step's record-level predicate over the
  witness's store); `StoredFamilies.form` is it at `FamilyRecon.RFormS`, carried across the fold's
  stores by `FamilyWitnessForm`;
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

/-- **The selected records' flattened families, entry by entry**: the selected record of a block
is the block's family over the flattened family `es` (by the entries' addresses), reads `es`
position by position with its parameters and levels (`FamilyFlat.RecordFlat`), and `es` is the
flattened family derived from the block's constructors (`FamilyFlat.BlockDerivedFlat`, at the
block's elimination offset). Producer: the binding run's family check of the block, whose
`check_nested_aux` asserts with the changed `aux_all_in` that the record's entries are the derived
ones in order (`GroupFamilyChecks.familyFlat`), carried to the witness's store
(`storedFamiliesFlat_of_sub`, `storedFamiliesFlat_grow`). -/
def StoredFamiliesFlat (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address) : Prop :=
  ∀ B rb, famOf B = some rb → ∃ (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst)
    (es : List FamilyFlat.FlatEntry) (off : Nat),
    FamilyOfBlock R B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) ∧
    FamilyFlat.RecordFlat t R rb crb rs es ∧ FamilyFlat.BlockDerivedFlat t R B off es

/-- **A predicate on a stored family record's form**, of the role table, the store that holds the
record and its block, the block and the record: the form reads the record and the block, which
only a store gives. -/
abbrev StoredFormPred : Type :=
  Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → _root_.Address → Prop

/-- **The second import, the stored-twin premise**: the selected family record of every stored
modeled block, in the witness's store `R`, is in the reconstruction's form at every member
(`RFormS t R B rb`, the record-level form predicate the twin step's producer uses: the
reconstruction's own type at every member of the record `rb` of block `B`). -/
def StoredFamiliesRForm (RFormS : StoredFormPred) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address) : Prop :=
  ∀ B rb, famOf B = some rb → RFormS t R B rb

/-- **The family the witness installed for each stored modeled block** (module docstring). -/
structure StoredFamilies (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (famOf : _root_.Address → Option _root_.Address) : Prop where
  /-- A block of `R` the store routes as modeled, whose constant addresses `env` stores, has a
  selected family record. -/
  selected : ∀ B cb, recordOf R B = some cb → Route.blockRoute R B = some true →
    (∀ x, ConstAddrOf B cb x → StoredAt t env x) → ∃ rb, famOf B = some rb
  /-- The selected record is the block's family, position by position over the flattened family,
  in `R`. -/
  family : ∀ B rb, famOf B = some rb → ∃ cb ms crb rs flat, FamilyOfBlock R B cb ms rb crb rs flat
  /-- A block with a selected family is stored. -/
  blockStored : ∀ B rb cb, famOf B = some rb → recordOf R B = some cb →
    ∀ x, ConstAddrOf B cb x → StoredAt t env x
  /-- The selected record is stored whole, each recursor with its model companion. -/
  installed : ∀ B rb crb, famOf B = some rb → recordOf R rb = some crb →
    (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb
  /-- The selected records' flattened families, entry by entry, derived from the block and read
  off the record, in `R`. -/
  flat : StoredFamiliesFlat t R famOf
  /-- The selected records' reconstruction form in `R`: each record is the block's family over
  the flattened family derived from the block, and each of its recursors is the block's
  reconstruction at its position (`FamilyRecon.RFormS`). -/
  form : StoredFamiliesRForm FamilyRecon.RFormS t R famOf
  /-- Each recursor member of a selected family record is stored with its canonical loaded form
  (`TwinFamily.TwinMemberLoaded`), mentions no recursor key of the record, and carries the four
  header-count facts of `KernelModeled::check_recs`. -/
  recs : ∀ B rb cb crb, famOf B = some rb → recordOf R B = some cb → recordOf R rb = some crb →
    StoredFamilyRecs t R env B cb rb crb

/-! ## The flattened families across stores -/

/-- **No selection, no flattened family to carry.** -/
theorem storedFamiliesFlat_none {t : Ix.Kernel.RoleTable} {R : Ixon.Env} :
    StoredFamiliesFlat t R (fun _ => none) :=
  fun B rb h => nomatch h

/-- **The flattened families pass to a store closed under what its records use that holds the
records and blobs of the first.** -/
theorem storedFamiliesFlat_grow {t : Ix.Kernel.RoleTable} {R R' : Ixon.Env}
    {famOf : _root_.Address → Option _root_.Address}
    (hle : ∀ a c, recordOf R a = some c → recordOf R' a = some c)
    (hblob : ∀ x b, R.blobs.get? x = some b → R'.blobs.get? x = some b)
    (hclosed : UsedClosed R') (h : StoredFamiliesFlat t R famOf) :
    StoredFamiliesFlat t R' famOf := by
  intro B rb hrb
  obtain ⟨cb, crb, ms, rs, es, off, hF, hR, hD⟩ := h B rb hrb
  exact ⟨cb, crb, ms, rs, es, off,
    familyOfBlock_of_closed hclosed (hle _ _ hF.block.record) (hle _ _ hF.record.record) hF,
    hR.of_blobs hblob, FamilyFlat.blockDerivedFlat_grow hle hblob hD⟩

/-- **The flattened families checked over the run's store `E₀` pass to a sub-store closed under
used references and owners that holds the selected blocks and records and `E₀`'s blobs**: the
derivation reads only the block and what it reaches (`FamilyFlat.blockDerivedFlat_of_closed_sub`),
the record's reading only the record and the blobs. -/
theorem storedFamiliesFlat_of_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {famOf : _root_.Address → Option _root_.Address}
    (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    (hheld : ∀ B rb, famOf B = some rb →
      (recordOf R B).isSome = true ∧ (recordOf R rb).isSome = true)
    (h : StoredFamiliesFlat t E₀ famOf) : StoredFamiliesFlat t R famOf := by
  intro B rb hrb
  obtain ⟨cb, crb, ms, rs, es, off, hF, hR, hD⟩ := h B rb hrb
  obtain ⟨hB, hrbH⟩ := hheld B rb hrb
  have hcb : recordOf R B = some cb :=
    (FamilyFlat.recordOf_eq_of_held hsub hB).trans hF.block.record
  have hcrb : recordOf R rb = some crb :=
    (FamilyFlat.recordOf_eq_of_held hsub hrbH).trans hF.record.record
  exact ⟨cb, crb, ms, rs, es, off, familyOfBlock_of_closed hcl hcb hcrb hF, hR.of_blobs hblob,
    FamilyFlat.blockDerivedFlat_of_closed_sub checked hwf hsub hcl hblob hB hD⟩

/-- **The flattened families of a map selecting from two maps.** -/
theorem storedFamiliesFlat_join {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {famOf famOf₀ fam : _root_.Address → Option _root_.Address}
    (h : StoredFamiliesFlat t R famOf) (h₀ : StoredFamiliesFlat t R famOf₀)
    (hj : ∀ B rb, fam B = some rb → famOf B = some rb ∨ famOf₀ B = some rb) :
    StoredFamiliesFlat t R fam := by
  intro B rb hrb
  rcases hj B rb hrb with h1 | h1
  · exact h B rb h1
  · exact h₀ B rb h1

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
    ∃ rb ms crb rs flat, famOf B = some rb ∧ FamilyOfBlock R B cb ms rb crb rs flat ∧
      (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb := by
  obtain ⟨rb, hrb⟩ := h.selected B cb hB hroute hst
  obtain ⟨cb', ms, crb, rs, flat, hf⟩ := h.family B rb hrb
  have e : cb' = cb := Option.some.inj (hf.block.record.symm.trans hB)
  subst e
  obtain ⟨hstored, hinst⟩ := h.installed B rb crb hrb hf.record.record
  exact ⟨rb, ms, crb, rs, flat, hrb, hf, hstored, hinst⟩

/-- **The typing half's first import** at the witnesses of the internal part `W`: one selected
family map, and at every stored modeled block its family, position by position over the flattened
family, stored whole with its
companions. -/
def StoredFamiliesImport
    (W : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (R : Ixon.Env) (env : Ix.Kernel.Env .anon),
    W t (fun _ => True) R env →
    ∃ famOf : _root_.Address → Option _root_.Address,
      ∀ B cb, recordOf R B = some cb → Route.blockRoute R B = some true →
        (∀ x, ConstAddrOf B cb x → StoredAt t env x) →
        ∃ rb ms crb rs flat, famOf B = some rb ∧ FamilyOfBlock R B cb ms rb crb rs flat ∧
          (∀ x, ConstAddrOf rb crb x → StoredAt t env x) ∧ FamilyInstalled t env rb crb

/-- **The first import holds at the internal part with its stored families.** -/
theorem storedFamiliesImport_overWFam (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) :
    StoredFamiliesImport (OverWFam.{u} L) := by
  intro t R env hW
  obtain ⟨famOf, hF⟩ := hW.2
  exact ⟨famOf, fun B cb hB hroute hst => storedFamily_of_clause hF hB hroute hst⟩

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
