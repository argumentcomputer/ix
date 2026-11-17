import IxVMRefinement.Binding.Glue
import IxVMRefinement.Binding.StoreCongr

/-! # The store congruence the group step asks, for a store-relative extra clause

`stepCoreR_of_parts` takes `BndCongr X`. For the binding fold's form of a store-relative clause,
`StoreX X` (the clause at every record store for the fold's store), it holds outright: a record
store for a store is one for any store with the same entries (`recordsFor_storeCongr`), and the
rest is `bnd_storeCongr`.
-/

universe u

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

/-- **`BndCongr` for a store-relative extra clause.** -/
theorem bndCongr_storeX (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop) :
    BndCongr.{u} (StoreX X) := by
  intro t G R R' env hc hb h
  refine bnd_storeCongr hc hb (fun hX E hE => hX E ?_) h
  exact recordsFor_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm) hE

end IxVM.Refinement.Binding
