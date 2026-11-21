import IxVMRefinement.Binding.StoreClausesWalk
import IxVMRefinement.Binding.FamilyAdmits

/-! # The rank of a group's new records, over its walk and its payload

The admission of group `g` orders the records it adds: a record after what it uses and after its
block (`Admits.rankUsed`, `Admits.rankOwner`), and for a modeled block `B` with the selected
family record `rb`: the advice records and container recursors of `B`'s family check before `B`,
`B` before `rb`, and what `rb` uses before `B` unless it is a constant address of `B` or `rb`
(`FamilyAdmits.famNew`, `.advice`, `.container`; `ClosureRunFacts.famRefs`).

* `GroupRanked t E₀ Pay g famOf adv cont rank`: `rank` orders the new records of group `g` in
  the store sequence `groupStore t E₀ Pay` as those clauses ask, for the family selection
  `famOf` with its advice `adv` and container recursors `cont`.
* `groupRanked_walk`: at a group without payload whose family selection names only payload
  blocks (so none), the rank of the group's walk (`walkRank`) is such a rank.

At a group with a payload the rank is not the walk's: a witness the advice uses may be walked
after the block. Such a rank exists where the order above has no cycle among the group's new
records; that is a premise of the run (`RemainingFamilyClauses.payloadRanked`). -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **A rank of the new records of group `g`** (module docstring). -/
structure GroupRanked (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (rank : _root_.Address → Nat) :
    Prop where
  used : ∀ a x, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
    UsedRef (groupStore t E₀ Pay (g + 1)) a x →
    (New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x ∧ rank x < rank a) ∨
      (recordOf (groupStore t E₀ Pay g) x).isSome = true
  owner : ∀ a c, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
    recordOf (groupStore t E₀ Pay (g + 1)) a = some c → IsProj c →
    (New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) (Ix.Cert.ownerOf a c) ∧
        rank (Ix.Cert.ownerOf a c) < rank a) ∨
      (recordOf (groupStore t E₀ Pay g) (Ix.Cert.ownerOf a c)).isSome = true
  fam : ∀ B rb, famOf B = some rb →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) B → rank B < rank rb
  advice : ∀ B rb a, famOf B = some rb →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) B → adv B a →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a → rank a < rank B
  container : ∀ B rb x, famOf B = some rb →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) B → cont B x →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x → rank x < rank B
  famRefs : ∀ B rb x, famOf B = some rb → UsedRef E₀ rb x → NeedOk E₀ x →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x →
    (∃ cb crb, recordOf (groupStore t E₀ Pay (g + 1)) B = some cb ∧
        recordOf (groupStore t E₀ Pay (g + 1)) rb = some crb ∧ FamAddr B cb rb crb x) ∨
      rank x < rank B

section Walk

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {Pay : PayloadRel}

/-- **At a group without payload the walk's rank orders the new records**: the family selection
names only blocks with a payload, so there is none, and the clauses on it hold vacuously. -/
theorem groupRanked_walk (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) (hnp : ∀ B a, ¬ Pay g B a)
    {famOf : _root_.Address → Option _root_.Address}
    {adv cont : _root_.Address → _root_.Address → Prop}
    (hfam : ∀ B rb, famOf B = some rb → Pay g B rb) :
    GroupRanked t E₀ Pay g famOf adv cont (walkRank recs) where
  used := groupStore_rankUsed hC hb hbr hax hP hws hg hw hnp
  owner := groupStore_rankOwner hC hb hax hg hw hnp
  fam := fun B rb h _ => (hnp B rb (hfam B rb h)).elim
  advice := fun B rb _ h _ _ _ => (hnp B rb (hfam B rb h)).elim
  container := fun B rb _ h _ _ _ => (hnp B rb (hfam B rb h)).elim
  famRefs := fun B rb _ h _ _ _ => (hnp B rb (hfam B rb h)).elim

end Walk

end IxVM.Refinement.Binding
