import IxCC.Own.Rc.Heap
import IxCC.Own.Rc.Proof.Allocation
import IxCC.Own.Rc.Proof.LeakFreedom
import IxCC.Own.Rc.Proof.ReleaseValue
import IxCC.Own.Rc.Proof.Shape
import IxCC.Own.Rc.Proof.Transfer
import IxCC.Own.Rc.Release

/-! Exact axiom fences for the checked plain-RC foundation. -/

/-- info: 'IxCC.Own.Rc.alloc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.alloc_sound

/-- info: 'IxCC.Own.Rc.balance_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_alloc

/-- info: 'IxCC.Own.Rc.balance_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_free

/-- info: 'IxCC.Own.Rc.balance_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_hold

/-- info: 'IxCC.Own.Rc.balance_inc_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_inc_cell

/-- info: 'IxCC.Own.Rc.balance_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_shared

/-- info: 'IxCC.Own.Rc.balance_unhold' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.balance_unhold

/-- info: 'IxCC.Own.Rc.bodyOk_of_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.bodyOk_of_den

/-- info: 'IxCC.Own.Rc.canDup_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.canDup_field

/-- info: 'IxCC.Own.Rc.canDup_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.canDup_owned

/-- info: 'IxCC.Own.Rc.changeCount_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.changeCount_sameBodies

/-- info: 'IxCC.Own.Rc.counts_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.counts_set

/-- info: 'IxCC.Own.Rc.decShared_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.decShared_counts

/-- info: 'IxCC.Own.Rc.decShared_dyn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.decShared_dyn

/-- info: 'IxCC.Own.Rc.decShared_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.decShared_readback

/-- info: 'IxCC.Own.Rc.dropAll_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_balance

/-- info: 'IxCC.Own.Rc.dropAll_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_heapOk

/-- info: 'IxCC.Own.Rc.dropAll_reclaims' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_reclaims

/-- info: 'IxCC.Own.Rc.dropAll_retaining' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_retaining

/-- info: 'IxCC.Own.Rc.dropAll_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_sound

/-- info: 'IxCC.Own.Rc.dropAll_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_value

/-- info: 'IxCC.Own.Rc.dup_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dup_owned

/-- info: 'IxCC.Own.Rc.dup_projection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dup_projection

/-- info: 'IxCC.Own.Rc.dynCount_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dynCount_alloc

/-- info: 'IxCC.Own.Rc.dynCount_fresh' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dynCount_fresh

/-- info: 'IxCC.Own.Rc.edgeCount_alloc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.edgeCount_alloc

/-- info: 'IxCC.Own.Rc.edgeCount_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.edgeCount_free

/-- info: 'IxCC.Own.Rc.edgeCount_set_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.edgeCount_set_count

/-- info: 'IxCC.Own.Rc.external_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.external_hold

/-- info: 'IxCC.Own.Rc.fields_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.fields_avoid

/-- info: 'IxCC.Own.Rc.free_external_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.free_external_ne

/-- info: 'IxCC.Own.Rc.free_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.free_readback

/-- info: 'IxCC.Own.Rc.free_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.free_value

/-- info: 'IxCC.Own.Rc.heapOk_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_alloc

/-- info: 'IxCC.Own.Rc.heapOk_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_empty

/-- info: 'IxCC.Own.Rc.heapOk_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_free

/-- info: 'IxCC.Own.Rc.heapOk_set_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_set_count

/-- info: 'IxCC.Own.Rc.heapOk_zero_all_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_zero_all_dead

/-- info: 'IxCC.Own.Rc.heapOk_zero_no_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.heapOk_zero_no_live

/-- info: 'IxCC.Own.Rc.held_external' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.held_external

/-- info: 'IxCC.Own.Rc.inc_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.inc_counts

/-- info: 'IxCC.Own.Rc.inc_dyn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.inc_dyn

/-- info: 'IxCC.Own.Rc.inc_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.inc_readback

/-- info: 'IxCC.Own.Rc.inc_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.inc_root

/-- info: 'IxCC.Own.Rc.mass_dec_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.mass_dec_lt

/-- info: 'IxCC.Own.Rc.mass_free_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.mass_free_lt

/-- info: 'IxCC.Own.Rc.mass_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.mass_set

/-- info: 'IxCC.Own.Rc.readback_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.readback_sameBodies

/-- info: 'IxCC.Own.Rc.refsIn_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.refsIn_append

/-- info: 'IxCC.Own.Rc.refsIn_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.refsIn_pos

/-- info: 'IxCC.Own.Rc.refsIn_zero_of_absent' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.refsIn_zero_of_absent

/-- info: 'IxCC.Own.Rc.releaseOne_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_balance

/-- info: 'IxCC.Own.Rc.releaseOne_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_decreases

/-- info: 'IxCC.Own.Rc.releaseOne_final' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_final

/-- info: 'IxCC.Own.Rc.releaseOne_final_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_final_balance

/-- info: 'IxCC.Own.Rc.releaseOne_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_heapOk

/-- info: 'IxCC.Own.Rc.releaseOne_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_readback

/-- info: 'IxCC.Own.Rc.releaseOne_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_value

/-- info: 'IxCC.Own.Rc.sameBodies_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.sameBodies_set

/-- info: 'IxCC.Own.Rc.setCell_cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.setCell_cell

/-- info: 'IxCC.Own.Rc.setCell_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.setCell_size

/-- info: 'IxCC.Own.Rc.toFir_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.toFir_free

/-- info: 'IxCC.Own.Rc.toFir_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.toFir_sameBodies

/-- info: 'IxCC.Own.Rc.total_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.total_append

/-- info: 'IxCC.Own.Rc.total_mem_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.total_mem_le

/-- info: 'IxCC.Own.Rc.total_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.total_set

/-- info: 'IxCC.Own.Rc.total_zero_of_entries' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.total_zero_of_entries

/-- info: 'IxCC.Own.Rc.value_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.value_sameBodies

/-- info: 'IxCC.Own.Rc.SameBodies.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Rc.SameBodies.refl
