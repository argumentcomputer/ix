import IxCC.Rt.Rc.Array.Layout
import IxCC.Rt.Rc.Array.Invariant
import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Rc.Array.Proof.Classes
import IxCC.Rt.Rc.Array.Proof.BasicOps
import IxCC.Rt.Rc.Array.Proof.MutOps
import IxCC.Rt.Rc.Array.Proof.Release
import IxCC.Rt.Rc.Array.Proof.Alloc
import IxCC.Rt.Proof.ArrayWire
import IxCC.Rt.Rc.Array.Proof.OpsCopying

/-! Exact axiom fences for DR3 native contiguous array runtime (`Layout`,
`Invariant`, `Procs`, `Proof.{Classes,BasicOps,MutOps,Release,Alloc}`).
Every theorem depends strictly on subsets of
`[propext, Classical.choice, Quot.sound]`. -/

/-! ### Layout & Invariant -/

/-- info: 'IxCC.Rt.Rc.Array.classWordsFast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.classWordsFast_eq

/-- info: 'IxCC.Rt.Rc.Array.classForFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.classForFast_eq

/-- info: 'IxCC.Rt.Rc.Array.scanTagFixed_or_cls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.scanTagFixed_or_cls

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.dec_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.dec_shared

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.inc_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.inc_ref

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.setWord_boxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.setWord_boxed

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.setWord_limbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.setWord_limbs

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.setByte_inPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.setByte_inPlace

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.pushWord_boxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.pushWord_boxed

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.pushWord_limbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.pushWord_limbs

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.pushByte_inPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.pushByte_inPlace

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.pop_inPlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.pop_inPlace

/-- info: 'IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataByteArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataByteArray

/-- info: 'IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataLimbArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataLimbArray

/-- info: 'IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataBoxedArray' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.StaticArrayCell.ofRodataBoxedArray

/-- info: 'IxCC.Rt.Rc.Array.allocatorReady_toArrayAllocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.allocatorReady_toArrayAllocator

/-! ### Operational Lir Proofs -/

/-- info: 'IxCC.Rt.Rc.Array.arrClassFor_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrClassFor_eval

/-- info: 'IxCC.Rt.Rc.Array.arrClassFor_zero_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrClassFor_zero_fail

/-- info: 'IxCC.Rt.Rc.Array.arrClassFor_overflow_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrClassFor_overflow_fail

/-- info: 'IxCC.Rt.Rc.Array.arrClassWords_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrClassWords_eval

/-- info: 'IxCC.Rt.Rc.Array.arrSize_live_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrSize_live_eval

/-- info: 'IxCC.Rt.Rc.Array.arrSize_static_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrSize_static_eval

/-- info: 'IxCC.Rt.Rc.Array.arrCap_live_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrCap_live_eval

/-- info: 'IxCC.Rt.Rc.Array.arrCap_static_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrCap_static_eval

/-- info: 'IxCC.Rt.Rc.Array.arrGet_limbs_live_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrGet_limbs_live_eval

/-- info: 'IxCC.Rt.Rc.Array.arrGet_boxed_live_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrGet_boxed_live_eval

/-- info: 'IxCC.Rt.Rc.Array.arrGet_limbs_static_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrGet_limbs_static_eval

/-- info: 'IxCC.Rt.Rc.Array.arrGet_oob_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrGet_oob_trap

/-- info: 'IxCC.Rt.Rc.Array.byteArrGet_live_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrGet_live_eval

/-- info: 'IxCC.Rt.Rc.Array.byteArrGet_static_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrGet_static_eval

/-- info: 'IxCC.Rt.Rc.Array.arrPopLimbs_unique_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrPopLimbs_unique_eval

/-- info: 'IxCC.Rt.Rc.Array.byteArrPop_unique_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrPop_unique_eval

/-- info: 'IxCC.Rt.Rc.Array.arrSetLimbs_unique_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrSetLimbs_unique_eval

/-- info: 'IxCC.Rt.Rc.Array.arrPushBoxed_unique_room_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrPushBoxed_unique_room_eval

/-- info: 'IxCC.Rt.Rc.Array.arrPushLimbs_unique_room_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrPushLimbs_unique_room_eval

/-- info: 'IxCC.Rt.Rc.Array.byteArrSet_unique_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrSet_unique_eval

/-- info: 'IxCC.Rt.Rc.Array.byteArrPush_unique_room_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrPush_unique_room_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_immediate_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_immediate_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_static_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_static_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_shared_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_shared_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_unboxed_free_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_unboxed_free_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_boxed_empty_free_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_boxed_empty_free_eval

/-- info: 'IxCC.Rt.Rc.Array.arrDec_boxed_immediates_free_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrDec_boxed_immediates_free_eval

/-- info: 'IxCC.Rt.Rc.Array.arrAllocCell_oom_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrAllocCell_oom_eval

/-- info: 'IxCC.Rt.Rc.Array.arrEmptyCapBoxed_free_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrEmptyCapBoxed_free_eval

/-- info: 'IxCC.Rt.Rc.Array.arrEmptyCapBoxed_bump_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrEmptyCapBoxed_bump_eval

/-- info: 'IxCC.Rt.Rc.Array.arrEmptyCapLimbs_free_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrEmptyCapLimbs_free_eval

/-- info: 'IxCC.Rt.Rc.Array.arrEmptyCapLimbs_bump_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.arrEmptyCapLimbs_bump_eval

/-- info: 'IxCC.Rt.Rc.Array.byteArrEmptyCap_bump_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.byteArrEmptyCap_bump_eval

/-! ### DR1 / DR3 / DR4 Array & Static String Wiring (`Rt.Proof.ArrayWire`) -/

/-- info: 'IxCC.Rt.Proof.buildStringRodata_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.buildStringRodata_spec

/-- info: 'IxCC.Rt.Proof.buildStringRodata_staticCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.buildStringRodata_staticCell

/-- info: 'IxCC.Rt.Proof.buildStringRodata_readbackString' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.buildStringRodata_readbackString

/-- info: 'IxCC.Rt.Proof.buildStringRodata_linkedRodata_readbackString' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.buildStringRodata_linkedRodata_readbackString

/-- info: 'IxCC.Rt.Proof.rodataStrProc_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.rodataStrProc_eval

/-- info: 'IxCC.Rt.Proof.bytesToWords64_byte_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.bytesToWords64_byte_eq

/-- info: 'IxCC.Rt.Proof.storeWords_wordAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.storeWords_wordAt

/-- info: 'IxCC.Rt.Proof.strLitProc_staticCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.strLitProc_staticCell

/-- info: 'IxCC.Rt.Proof.strLitProc_readbackString' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.strLitProc_readbackString

/-- info: 'IxCC.Rt.Proof.relocateFunc_meta' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.relocateFunc_meta

/-- info: 'IxCC.Rt.Proof.extendedArrayRuntimeFuncs_len' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Proof.extendedArrayRuntimeFuncs_len

/-! ### Certified-route array runtime (rt-array-procs): kinds by width, the cell invariant, the one
release on array cells, the procedures' paths -/

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.template_or_cls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.template_or_cls

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.header_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.header_fields

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.capOfClass_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.capOfClass_spec

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.payload_eq_classBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.payload_eq_classBytes

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.cellWords_le_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.cellWords_le_max

/-- info: 'IxCC.Rt.Rc.Array.ElemKind.tag_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ElemKind.tag_injective

/-- info: 'IxCC.Rt.Rc.Array.ArrayKind.elem_header' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrayKind.elem_header

/-- info: 'IxCC.Rt.Rc.Array.ArrayKind.elem_staticHeader' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrayKind.elem_staticHeader

/-- info: 'IxCC.Rt.Rc.Array.ValAt.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ValAt.read

/-- info: 'IxCC.Rt.Rc.Array.ValAt.load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ValAt.load

/-- info: 'IxCC.Rt.Rc.Array.valAt_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.valAt_write

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.count_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.count_load

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.scan_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.scan_load

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.class_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.class_load

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.elem_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.elem_load

/-- info: 'IxCC.Rt.Rc.Array.MemFrame.arrCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.MemFrame.arrCell

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.setElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.setElem

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.pushElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.pushElem

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.truncate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.truncate

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.withCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.withCount

/-- info: 'IxCC.Rt.Rc.Array.LiveArrayCell.toArrCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.LiveArrayCell.toArrCell

/-- info: 'IxCC.Rt.Rc.Array.StaticArrayCell.toStatic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.StaticArrayCell.toStatic

/-- info: 'IxCC.Rt.Rc.Array.MemFrame.liveArrayCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.MemFrame.liveArrayCell

/-- info: 'IxCC.Rt.Rc.Array.MemFrame.freeChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.MemFrame.freeChain

/-- info: 'IxCC.Rt.Rc.Array.star_call0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.star_call0

/-- info: 'IxCC.Rt.Rc.Array.star_call1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.star_call1

/-- info: 'IxCC.Rt.Rc.Array.inc_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.inc_returns

/-- info: 'IxCC.Rt.Rc.Array.IncAll.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.IncAll.frame

/-- info: 'IxCC.Rt.Rc.Array.classFor_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.classFor_returns

/-- info: 'IxCC.Rt.Rc.Array.classWords_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.classWords_returns

/-- info: 'IxCC.Rt.Rc.Array.ArrayAllocator.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrayAllocator.frame

/-- info: 'IxCC.Rt.Rc.Array.ArrayAllocator.push_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrayAllocator.push_free

/-- info: 'IxCC.Rt.Rc.Array.Allocated.not_allocBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.Allocated.not_allocBytes

/-- info: 'IxCC.Rt.Rc.Array.decArr_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_entry

/-- info: 'IxCC.Rt.Rc.Array.decArr_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_ret

/-- info: 'IxCC.Rt.Rc.Array.decArr_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_done

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_immediate

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_static

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_shared

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_leaf

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_array_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_array_empty

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_array_detach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_array_detach

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_ctor_detach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_ctor_detach

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_finish

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_recycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_recycle

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_array_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_array_next

/-- info: 'IxCC.Rt.Rc.Array.decArr_step_ctor_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_step_ctor_next

/-- info: 'IxCC.Rt.Rc.Array.decArr_returns_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_returns_immediate

/-- info: 'IxCC.Rt.Rc.Array.decArr_returns_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.decArr_returns_static

/-- info: 'IxCC.Rt.Rc.Array.StaticArrCell.decArr_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.StaticArrCell.decArr_returns

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.decArr_returns_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.decArr_returns_shared

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.decArr_returns_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.decArr_returns_packed

/-- info: 'IxCC.Rt.Rc.Array.ArrShell.decArr_returns_boxed_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrShell.decArr_returns_boxed_empty

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.decArr_returns_immediates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.decArr_returns_immediates

/-- info: 'IxCC.Rt.Rc.Array.allocClass_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.allocClass_spec

/-- info: 'IxCC.Rt.Rc.Array.alloc_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.alloc_returns

/-- info: 'IxCC.Rt.Rc.Array.copy_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.copy_returns

/-- info: 'IxCC.Rt.Rc.Array.size_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.size_returns

/-- info: 'IxCC.Rt.Rc.Array.get_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.get_returns

/-- info: 'IxCC.Rt.Rc.Array.get_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.get_traps

/-- info: 'IxCC.Rt.Rc.Array.set_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.set_traps

/-- info: 'IxCC.Rt.Rc.Array.set_unique_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.set_unique_packed

/-- info: 'IxCC.Rt.Rc.Array.set_unique_boxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.set_unique_boxed

/-- info: 'IxCC.Rt.Rc.Array.push_unique_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.push_unique_room

/-- info: 'IxCC.Rt.Rc.Array.pop_empty_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.pop_empty_packed

/-- info: 'IxCC.Rt.Rc.Array.pop_empty_boxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.pop_empty_boxed

/-- info: 'IxCC.Rt.Rc.Array.pop_unique_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.pop_unique_packed

/-- info: 'IxCC.Rt.Rc.Array.pop_unique_boxed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.pop_unique_boxed

/-- info: 'IxCC.Rt.Rc.Array.AllocDone.arrCell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.AllocDone.arrCell

/-- info: 'IxCC.Rt.Rc.Array.fresh_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.fresh_copy

/-- info: 'IxCC.Rt.Rc.Array.set_shared_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.set_shared_packed

/-- info: 'IxCC.Rt.Rc.Array.ArrCell.push_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.ArrCell.push_writes

/-- info: 'IxCC.Rt.Rc.Array.growCap_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.growCap_spec

/-- info: 'IxCC.Rt.Rc.Array.push_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.push_grow

/-- info: 'IxCC.Rt.Rc.Array.push_shared_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.push_shared_packed

/-- info: 'IxCC.Rt.Rc.Array.pop_shared_packed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Rt.Rc.Array.pop_shared_packed
