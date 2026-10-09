import Compilatrix.Own.Rc.Heap
import Compilatrix.Own.Rc.Proof.Allocation
import Compilatrix.Own.Rc.Proof.LeakFreedom
import Compilatrix.Own.Rc.Proof.ReleaseValue
import Compilatrix.Own.Rc.Proof.Shape
import Compilatrix.Own.Rc.Proof.Transfer
import Compilatrix.Own.Rc.Release

/-! Exact axiom fences for the checked plain-RC foundation. -/

/-- info: 'Compilatrix.Own.Rc.alloc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.alloc_sound

/-- info: 'Compilatrix.Own.Rc.balance_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_alloc

/-- info: 'Compilatrix.Own.Rc.balance_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_free

/-- info: 'Compilatrix.Own.Rc.balance_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_hold

/-- info: 'Compilatrix.Own.Rc.balance_inc_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_inc_cell

/-- info: 'Compilatrix.Own.Rc.balance_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_shared

/-- info: 'Compilatrix.Own.Rc.balance_unhold' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.balance_unhold

/-- info: 'Compilatrix.Own.Rc.bodyOk_of_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.bodyOk_of_den

/-- info: 'Compilatrix.Own.Rc.canDup_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.canDup_field

/-- info: 'Compilatrix.Own.Rc.canDup_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.canDup_owned

/-- info: 'Compilatrix.Own.Rc.changeCount_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.changeCount_sameBodies

/-- info: 'Compilatrix.Own.Rc.counts_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.counts_set

/-- info: 'Compilatrix.Own.Rc.decShared_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.decShared_counts

/-- info: 'Compilatrix.Own.Rc.decShared_dyn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.decShared_dyn

/-- info: 'Compilatrix.Own.Rc.decShared_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.decShared_readback

/-- info: 'Compilatrix.Own.Rc.dropAll_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_balance

/-- info: 'Compilatrix.Own.Rc.dropAll_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_heapOk

/-- info: 'Compilatrix.Own.Rc.dropAll_reclaims' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_reclaims

/-- info: 'Compilatrix.Own.Rc.dropAll_retaining' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_retaining

/-- info: 'Compilatrix.Own.Rc.dropAll_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_sound

/-- info: 'Compilatrix.Own.Rc.dropAll_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_value

/-- info: 'Compilatrix.Own.Rc.dup_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dup_owned

/-- info: 'Compilatrix.Own.Rc.dup_projection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dup_projection

/-- info: 'Compilatrix.Own.Rc.dynCount_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dynCount_alloc

/-- info: 'Compilatrix.Own.Rc.dynCount_fresh' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dynCount_fresh

/-- info: 'Compilatrix.Own.Rc.edgeCount_alloc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.edgeCount_alloc

/-- info: 'Compilatrix.Own.Rc.edgeCount_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.edgeCount_free

/-- info: 'Compilatrix.Own.Rc.edgeCount_set_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.edgeCount_set_count

/-- info: 'Compilatrix.Own.Rc.external_hold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.external_hold

/-- info: 'Compilatrix.Own.Rc.fields_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.fields_avoid

/-- info: 'Compilatrix.Own.Rc.free_external_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.free_external_ne

/-- info: 'Compilatrix.Own.Rc.free_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.free_readback

/-- info: 'Compilatrix.Own.Rc.free_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.free_value

/-- info: 'Compilatrix.Own.Rc.heapOk_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_alloc

/-- info: 'Compilatrix.Own.Rc.heapOk_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_empty

/-- info: 'Compilatrix.Own.Rc.heapOk_free' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_free

/-- info: 'Compilatrix.Own.Rc.heapOk_set_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_set_count

/-- info: 'Compilatrix.Own.Rc.heapOk_zero_all_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_zero_all_dead

/-- info: 'Compilatrix.Own.Rc.heapOk_zero_no_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.heapOk_zero_no_live

/-- info: 'Compilatrix.Own.Rc.held_external' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.held_external

/-- info: 'Compilatrix.Own.Rc.inc_counts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.inc_counts

/-- info: 'Compilatrix.Own.Rc.inc_dyn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.inc_dyn

/-- info: 'Compilatrix.Own.Rc.inc_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.inc_readback

/-- info: 'Compilatrix.Own.Rc.inc_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.inc_root

/-- info: 'Compilatrix.Own.Rc.mass_dec_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.mass_dec_lt

/-- info: 'Compilatrix.Own.Rc.mass_free_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.mass_free_lt

/-- info: 'Compilatrix.Own.Rc.mass_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.mass_set

/-- info: 'Compilatrix.Own.Rc.readback_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.readback_sameBodies

/-- info: 'Compilatrix.Own.Rc.refsIn_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.refsIn_append

/-- info: 'Compilatrix.Own.Rc.refsIn_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.refsIn_pos

/-- info: 'Compilatrix.Own.Rc.refsIn_zero_of_absent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.refsIn_zero_of_absent

/-- info: 'Compilatrix.Own.Rc.releaseOne_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_balance

/-- info: 'Compilatrix.Own.Rc.releaseOne_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_decreases

/-- info: 'Compilatrix.Own.Rc.releaseOne_final' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_final

/-- info: 'Compilatrix.Own.Rc.releaseOne_final_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_final_balance

/-- info: 'Compilatrix.Own.Rc.releaseOne_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_heapOk

/-- info: 'Compilatrix.Own.Rc.releaseOne_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_readback

/-- info: 'Compilatrix.Own.Rc.releaseOne_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_value

/-- info: 'Compilatrix.Own.Rc.sameBodies_set' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.sameBodies_set

/-- info: 'Compilatrix.Own.Rc.setCell_cell' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.setCell_cell

/-- info: 'Compilatrix.Own.Rc.setCell_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.setCell_size

/-- info: 'Compilatrix.Own.Rc.toFir_free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.toFir_free

/-- info: 'Compilatrix.Own.Rc.toFir_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.toFir_sameBodies

/-- info: 'Compilatrix.Own.Rc.total_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.total_append

/-- info: 'Compilatrix.Own.Rc.total_mem_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.total_mem_le

/-- info: 'Compilatrix.Own.Rc.total_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.total_set

/-- info: 'Compilatrix.Own.Rc.total_zero_of_entries' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.total_zero_of_entries

/-- info: 'Compilatrix.Own.Rc.value_sameBodies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.value_sameBodies

/-- info: 'Compilatrix.Own.Rc.SameBodies.refl' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.SameBodies.refl
