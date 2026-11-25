import IxCC.Shape.Src.Tree

/-! Required axiom fences for the source-level shape discipline in production
(`IxCC.Shape.Progress`, `IxCC.Shape.Src.*`): the progress statements' discharge lemmas (moved
from `IxCCCorrect.Progress`, whose fence they were in), the judgment's soundness, the
decision's soundness, the range and word lemmas, and the hooks' theorems with no "source goes wrong"
case. Each is within
`propext`, `Classical.choice`, `Quot.sound`. Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Progress.NeverWrong.neverStuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.NeverWrong.neverStuck

/-- info: 'IxCC.Progress.viewed_stuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.viewed_stuck_iff

/-- info: 'IxCC.Progress.neverStuck_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.neverStuck_iff

/-- info: 'IxCC.Progress.neverWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.neverWrong_iff

/-- info: 'IxCC.Progress.not_goesWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.not_goesWrong_iff

/-- info: 'IxCC.Progress.rc_not_goesWrong_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_not_goesWrong_iff

/-- info: 'IxCC.Progress.not_stuck_of_refinesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.not_stuck_of_refinesOn

/-- info: 'IxCC.Progress.recheck_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.recheck_sound_of_neverWrong

/-- info: 'IxCC.Progress.recheck_not_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.recheck_not_stuck

/-- info: 'IxCC.Progress.recheck_not_stuck_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.recheck_not_stuck_at

/-- info: 'IxCC.Progress.rc_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_sound_of_neverWrong

/-- info: 'IxCC.Progress.rc_not_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_not_stuck

/-- info: 'IxCC.Progress.rc_not_stuck_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_not_stuck_at

/-- info: 'IxCC.Progress.plainExeOutcome_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Progress.plainExeOutcome_mono

/-- info: 'IxCC.Progress.plain_exe_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.plain_exe_sound_of_neverWrong

/-- info: 'IxCC.Progress.rc_plain_exe_sound_of_neverWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_plain_exe_sound_of_neverWrong

/-- info: 'IxCC.Progress.plain_exe_specified_of_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.plain_exe_specified_of_neverStuck

/-- info: 'IxCC.Progress.rc_plain_exe_specified_of_neverStuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Progress.rc_plain_exe_specified_of_neverStuck

/-- info: 'IxCC.SrcShape.allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.allOk

/-- info: 'IxCC.SrcShape.run_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.run_ok

/-- info: 'IxCC.SrcShape.run_ok_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.run_ok_vals

/-- info: 'IxCC.SrcShape.neverWrong_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_shape

/-- info: 'IxCC.SrcShape.recheck_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.recheck_sound_of_shape

/-- info: 'IxCC.SrcShape.view_nat_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.view_nat_ok

/-- info: 'IxCC.SrcShape.view_enum_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.view_enum_ok

/-- info: 'IxCC.SrcShape.wordValue_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.wordValue_ok

/-- info: 'IxCC.SrcShape.asWord_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.SrcShape.asWord_lt

/-- info: 'IxCC.SrcShape.selectRule_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.selectRule_ok

/-- info: 'IxCC.SrcShape.synth_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.synth_sound

/-- info: 'IxCC.SrcShape.chkWith_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.chkWith_sound

/-- info: 'IxCC.SrcShape.entryOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.entryOk_sound

/-- info: 'IxCC.SrcShape.sigOk_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.sigOk_of_cert

/-- info: 'IxCC.SrcShape.dataCtorOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.dataCtorOk_sound

/-- info: 'IxCC.SrcShape.wordEntryOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.wordEntryOk_sound

/-- info: 'IxCC.SrcShape.neverWrong_of_cert_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_cert_nat

/-- info: 'IxCC.SrcShape.neverWrong_of_cert_enum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_cert_enum

/-- info: 'IxCC.SrcShape.neverWrong_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_check

/-- info: 'IxCC.SrcShape.neverWrong_of_enumRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_enumRoot

/-- info: 'IxCC.SrcShape.neverStuck_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverStuck_checked

/-- info: 'IxCC.SrcShape.runShaped_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.runShaped_ok

/-- info: 'IxCC.SrcShape.runShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.runShaped_sound

/-- info: 'IxCC.SrcShape.checkShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.checkShaped_sound

/-- info: 'IxCC.SrcShape.neverWrong_of_shape_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.neverWrong_of_shape_view

/-- info: 'IxCC.SrcShape.rc_neverWrong_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rc_neverWrong_of_check

/-- info: 'IxCC.SrcShape.rc_sound_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rc_sound_of_shape

/-- info: 'IxCC.SrcShape.rcRunShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rcRunShaped_sound

/-- info: 'IxCC.SrcShape.reads_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.reads_val

/-- info: 'IxCC.SrcShape.rc_view_tree_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rc_view_tree_ok

/-- info: 'IxCC.SrcShape.rc_neverWrong_of_treeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rc_neverWrong_of_treeRoot

/-- info: 'IxCC.SrcShape.view_enum_ok_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.view_enum_ok_any

/-- info: 'IxCC.SrcShape.rc_neverWrong_of_enumRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rc_neverWrong_of_enumRoot

/-- info: 'IxCC.SrcShape.rcCheckShaped_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rcCheckShaped_sound

/-- info: 'IxCC.SrcShape.rcRunShapedTree_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.rcRunShapedTree_sound

/-- info: 'IxCC.SrcShape.wordEntryOk_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.wordEntryOk_range

/-- info: 'IxCC.SrcShape.wordCtorOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.SrcShape.wordCtorOk_sound

/-- info: 'IxCC.SrcShape.arrows_data_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.SrcShape.arrows_data_inj

/-- info: 'IxCC.SrcShape.valOk_single' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.SrcShape.valOk_single

/-- info: 'IxCC.SrcShape.ValOk.natLt_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.SrcShape.ValOk.natLt_inv
