import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Core.Rep

/-! # The advice records a family check lists, at its own context

`check_family` walks the advice addresses its payload lists with
`check_advice_records(rc, advice, Nil, wset)` under its own role context `rc`. `AdviceListedIn`
names an address of such a walk among the calls `cs`, observed under a role context at the limit
`lim` with the table at the binding `bAddr`: the walk's own call or one of its recursive calls on
a suffix of the list. Each listed record's `check_advice_record` runs under the same role context
(`Decl.check_advice_records_obs`), so a listed record is checked at that limit; an advice-record
check nested deeper under another context (a covered role's validation walk at a group limit) is
not a listed address of a walk at `lim`. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

/-- **An advice record listed to an advice walk among the calls `cs`** under a role context at
`lim` with the table at the binding `bAddr`: an address of the list a `check_advice_records`
call observed among `cs` walks. -/
def AdviceListedIn (cs : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) (a : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xadv seen wset r : SourceValue F) (advAs : List Bytes.Address)
    (cs₁ : List (Call F)),
    Claim.RCLimRep t bAddr lim h rc ∧
    RepList addrListEnum (Bytes.RepAddressRef addrTy) h advAs xadv ∧
    ObsFn Obs.W "KernelModeled::check_advice_records" [rc, xadv, seen, wset] h r h' cs₁ ∧
    (∀ cl ∈ cs₁, cl ∈ cs) ∧ ∃ b ∈ advAs, ixAddr b = a

end IxVM.Refinement.Typing
