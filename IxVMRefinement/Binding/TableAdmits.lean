import IxVMRefinement.RoleVal.BasisPinLoop
import IxVMRefinement.Binding.ClaimExport
import IxVMRefinement.StatementRel.StoreInhabit

/-! # The loaded role table: the prelude pins

`LoadedTablePinsPrelude` (`Binding/ClaimExport.lean`) asks that a table the load's value
represents, binding every role, pins the prelude. The load's own loop `assert_basis_pinned` pins
every prelude role the table it built binds (`RoleVal.assert_basis_pinned_loop`, on the bindings
the load read, `RoleVal.load_role_table_bindings`); a representation `Claim.TableFullRep t` of
the same value has its address index complete for `t`'s pairs, and that index is the one the load
built (its entries are determined by the tree, `RoleVal.rbtreeEntries_det`), so `t`'s pairs are
the pairs the load read.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- **A loaded table that binds every role pins the prelude**, for every observed load. -/
theorem loadedTablePinsPrelude : LoadedTablePinsPrelude := by
  intro a x_a x_tbl h h₁ cs₁ t ev htf hall
  obtain ⟨hP, lb, v, cs', hpb, evpin⟩ := RoleVal.load_role_table_bindings ev
  have hpin := RoleVal.assert_basis_pinned_loop hpb 37 0 rfl (Heap.Extends.refl _)
    (by rw [Nat.cast_zero]; exact evpin)
  have hext : Heap.Extends hP h₁ := evpin.heap_extends
  obtain ⟨-, bp, byRole, byAddr, evm, hl, -, -, ⟨est, hbstt, -, hcov⟩, -⟩ := htf
  obtain ⟨-, bp', byRole', byAddr', evm', ents, es, hl', -, -, hbst, hidx⟩ := hpb.mono hext
  rw [hl] at hl'
  injection hl' with hv
  injection hv with _ _ hxs
  simp only [List.cons.injEq, and_true] at hxs
  obtain ⟨-, -, rfl, -⟩ := hxs
  have hes : est = es := RoleVal.rbtreeEntries_det hbstt.1 hbst.1
  subst hes
  obtain ⟨b₀, t₀, hdef, hadm, hdef_eq⟩ := StoreInhabit.preludePinned_default
  refine ⟨b₀, t₀, hdef, hadm, fun ro hro => ?_⟩
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hall ro)
  obtain ⟨b, hb, hmem⟩ := hcov ro a' (Claim.mem_bound_of_addressOf_eq_some ha')
  rcases (hidx b _).mp hmem with h0 | ⟨ro', hm', hw⟩
  · cases h0
  · obtain rfl := RolesAux.roleNum_add_one_inj (Value.field.inj hw)
    rw [ha', ← hdef_eq ro hro, hpin ro hro (Nat.zero_le _) b hm', hb]

end IxVM.Refinement.Binding
