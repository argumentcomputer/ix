import IxVMRefinement.StatementRel.BasisRowStore

/-! # What the basis records declare, and that the pins store it

`basis_reads_stored`: every address of the basis store with a reading has a reading that
the kernel's pinned constant at its key stores. The readings are computed by the row reader
(`RowReader.readRow`), and `StoredAs` is checked by evaluation, row by row
(`basis_rowsOk`).

This is the pin relation for the 19 role records of the basis blocks and the quotient
package (inductive types, constructors, recursors with their rules, the four quotient
records and `Quot.sound`): the record a run walks reads as a constant the stored pin is
`StoredAs`.
-/

namespace IxVM.Refinement.BasisReads

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.TableInhabit
open IxVM.Refinement.StoreInhabit
open IxVM.Refinement.RowReader

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Every row of the basis store that is not a block has a reading that the pin at its key
stores (decided: the reading is computed and `StoredAs` checked, row by row). -/
theorem basis_rowsOk :
    basisRowStore.rows.attach.all
      (fun x => isMutsInfo x.1.2.info || rowOk basisRowStore basisEnv x.1.1 x.1.2 x.2) =
        true := by
  decide +kernel

/-- **Every record of the basis store with a reading reads as a constant its pin stores**:
at the key of its address the environment of pins holds a pinned basis constant, and the
record has a reading that this pin is `StoredAs`. -/
theorem basis_reads_stored :
    ∀ a, (∃ ci₀, Reads committedDefaultRoleTable basisStore a ci₀) →
      ∃ pin ci₀, basisEnv.find? (keyOf committedDefaultRoleTable a) = some pin ∧
        PinnedBasis pin ∧ Reads committedDefaultRoleTable basisStore a ci₀ ∧
        StoredAs pin ci₀ := by
  intro a hr
  obtain ⟨pin, ci₀, hfind, hread, hst⟩ :=
    reads_stored basisRowStore basisEnv basis_rowsOk a hr
  exact ⟨pin, ci₀, hfind, basisEnv_pinned pin (List.mem_of_find?_eq_some hfind), hread, hst⟩

end IxVM.Refinement.BasisReads
