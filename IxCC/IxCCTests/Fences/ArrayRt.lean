import IxCC.Rt.Rc.Array.Layout
import IxCC.Rt.Rc.Array.Invariant
import IxCC.Rt.Rc.Array.Procs
import IxCC.Rt.Rc.Array.Proof.Classes
import IxCC.Rt.Rc.Array.Proof.BasicOps
import IxCC.Rt.Rc.Array.Proof.MutOps
import IxCC.Rt.Rc.Array.Proof.Release
import IxCC.Rt.Rc.Array.Proof.Alloc
import IxCC.Rt.Proof.ArrayWire

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
