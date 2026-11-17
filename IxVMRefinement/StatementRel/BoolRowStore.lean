import IxVMRefinement.StatementRel.RowsStore

/-! # The store of the basis rows and the `Bool` rows

`boolStore` holds the 24 committed prelude records of the basis blocks and the quotient
package and the five committed records of the `Bool` block (the block, the projection records
of `Bool`, `Bool.false` and `Bool.true`, and the recursor record of `Bool.rec`).
`boolRowStore` presents it to the row reader, and `boolBlock` is the inductive block as the
reader reads it from the four rows that declare constants.
-/

namespace IxVM.Refinement.BoolInhabit

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.StoreInhabit (basisRows)
open IxVM.Refinement.RowReader
open IxVM.Refinement.RowsStore

/-- **The rows**: the 24 basis and quotient rows and the five rows of the `Bool` block (the
last five of the 33 committed prelude records). -/
def boolRows : List Row := basisRows ++ committedPreludeList.drop 28

/-- The rows are at distinct addresses (decided). -/
theorem boolEntries_distinct :
    (entriesOf boolRows).Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide +kernel

theorem boolRows_committed : Committed boolRows :=
  ⟨boolEntries_distinct, fun e he => by
    rcases List.mem_append.mp he with h | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop h⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Every projection record of a block among the rows is one of the rows (by evaluation: the
row found is the projection record, term for term). -/
theorem bool_projs_found :
    (expectedProjsOf boolRows).map (fun p => (findProjOf boolRows p).map (·.2)) =
      (expectedProjsOf boolRows).map some :=
  rfl

/-- **The store.** -/
def boolStore : Ixon.Env := rowsEnv boolRows

/-- **The store, as a store of rows.** -/
def boolRowStore : RowStore committedDefaultRoleTable :=
  rowStoreOf boolRows boolRows_committed bool_projs_found

/-- What the row at position `i` declares, if it declares something. -/
def readingAt (i : Nat) : Option (ConstantInfo .anon) :=
  (boolRowStore.rows.attach[i]?).bind fun x => (readRow boolRowStore x.1.1 x.1.2 x.2).map (·.1)

/-- **The `Bool` block, as read from its rows**: the type, the two constructors and the
recursor (rows 25 to 28; row 24 is the block record, which declares nothing). -/
def boolBlock : List (ConstantInfo .anon) := [25, 26, 27, 28].filterMap readingAt

end IxVM.Refinement.BoolInhabit
