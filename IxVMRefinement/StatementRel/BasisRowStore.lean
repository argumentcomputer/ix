import IxVMRefinement.StatementRel.RowReader

/-! # The basis store as a store of rows

`basisRowStore` presents `StoreInhabit.basisStore`, the 24 committed records of the basis
blocks and the quotient package, to the row reader of `RowReader`.
-/

namespace IxVM.Refinement.BasisReads

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.StoreInhabit
open IxVM.Refinement.RowReader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Every projection record of a block of the basis rows is one of the rows (by evaluation:
the row found is the projection record, term for term). -/
theorem basis_projs_found :
    (expectedProjsOf basisRows).map (fun p => (findProjOf basisRows p).map (·.2)) =
      (expectedProjsOf basisRows).map some :=
  rfl

/-- **The basis store, as a store of rows.** -/
def basisRowStore : RowStore committedDefaultRoleTable where
  rows := basisRows
  store := recordOf basisStore
  blob := fun x => basisStore.blobs.get? x
  checked := committedDefaultRoleTable_check
  holds := fun e he => store_record_of_mem (a := e.1) (c := e.2) he
  only := fun _ _ h => store_record_inv h
  hashed := fun e he =>
    committedRows_hashed (e.1, Ixon.serConstant e.2)
      (committedPrelude_rows e (basisRows_sub e he)).1
  projs := map_eq_pointwise basis_projs_found

/-- What each row of the basis store declares, where it declares something. -/
def basisReadings : List (_root_.Address × Option (ConstantInfo .anon)) :=
  basisRowStore.rows.attach.map fun x =>
    (x.1.1, (readRow basisRowStore x.1.1 x.1.2 x.2).map (·.1))

end IxVM.Refinement.BasisReads
