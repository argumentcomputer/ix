import IxCC.Recheck.Proof.Compile
import IxCC.Compiler.Proof
import IxCC.CompileClaim.Proof
import IxCC.Ring0.Proof
import IxCC.Src.Proof.Lazify

/-! The actual compiler statements expose the existing native BLAKE3 dependency
through ingress and production. The separate replay fences retain their exact
standard-axiom sets. This file adds no assumption to `Recheck.run` or `sound`. -/

/-- info: 'IxCC.Recheck.compileInput_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compileInput_parts

/-- info: 'IxCC.Recheck.compile_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compile_parts

/-- info: 'IxCC.Recheck.compileInput_object_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compileInput_object_refines

/-- info: 'IxCC.Recheck.compile_object_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compile_object_refines

/-- info: 'IxCC.Recheck.compile_driver_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compile_driver_exists

/-- info: 'IxCC.Recheck.compiled_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compiled_sound

/-- info: 'IxCC.Recheck.compile_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compile_bytes

/-- info: 'IxCC.Recheck.sound_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.sound_of_eval

/-- info: 'IxCC.Recheck.recheckWithContracts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.recheckWithContracts_sound

/-- info: 'IxCC.Recheck.compileWithContracts_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.compileWithContracts_sound

/-- info: 'IxCC.Compiler.recheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compiler.recheck_sound

/-- info: 'IxCC.Compiler.compileInput_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.compileInput_sound

/-- info: 'IxCC.Compiler.compile_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.compile_sound

/-- info: 'IxCC.Compiler.produceAuto_zeroRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.produceAuto_zeroRc_sound

/-- info: 'IxCC.Compiler.produceAuto_plainRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.produceAuto_plainRc_sound

/-- info: 'IxCC.Compiler.compileAuto_zeroRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.compileAuto_zeroRc_sound

/-- info: 'IxCC.Compiler.compileAuto_plainRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.compileAuto_plainRc_sound

/-- info: 'IxCC.Compiler.produceAuto_immortal_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.produceAuto_immortal_sound

/-- info: 'IxCC.Compiler.compileAuto_immortal_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Compiler.compileAuto_immortal_sound

/-- info: 'IxCC.CompileClaim.ofPayloadBytes_toPayloadBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.ofPayloadBytes_toPayloadBytes

/-- info: 'IxCC.CompileClaim.ofClaimBytes_toClaimBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.ofClaimBytes_toClaimBytes

/-- info: 'IxCC.CompileClaim.checkClaim_ok_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.checkClaim_ok_iff

/-- info: 'IxCC.CompileClaim.verifyProgram_immortal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_immortal_sound

/-- info: 'IxCC.CompileClaim.verifyProgram_zeroRc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_zeroRc_sound

/-- info: 'IxCC.CompileClaim.verifyProgram_plainRc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_plainRc_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_immortal_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_immortal_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_zeroRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_zeroRc_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_plainRc_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_plainRc_sound

/-- info: 'IxCC.X86.Mnemonic.all_unprivileged' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.X86.Mnemonic.all_unprivileged

/-- info: 'IxCC.Ring0.op_rows_no_privileged_opcode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.op_rows_no_privileged_opcode

/-- info: 'IxCC.Ring0.op_rows_direct_control_and_unprivileged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.op_rows_direct_control_and_unprivileged

/-- info: 'IxCC.Ring0.op_row_no_indirect_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.op_row_no_indirect_branch

/-- info: 'IxCC.Ring0.table_index_direct_control_and_unprivileged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.table_index_direct_control_and_unprivileged

/-- info: 'IxCC.Ring0.stream_check_cfi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.stream_check_cfi

/-- info: 'IxCC.Ring0.stream_run_framePreserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.stream_run_framePreserved

/-- info: 'IxCC.Ring0.byteEval_run_framePreserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.byteEval_run_framePreserved

/-- info: 'IxCC.Ring0.session_runCalls_preserves_unmapped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.session_runCalls_preserves_unmapped

/-- info: 'IxCC.Ring0.text_preserved_of_canonicalOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.text_preserved_of_canonicalOk

/-- info: 'IxCC.Ring0.external_realizes_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.external_realizes_preserved

/-- info: 'IxCC.Ring0.kernelTablesPreserved_of_session_runCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.kernelTablesPreserved_of_session_runCalls

/-- info: 'IxCC.Ring0.verifyRing0Sip_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.verifyRing0Sip_sound

/-- info: 'IxCC.Ring0.verifyBytesRing0Sip_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Ring0.verifyBytesRing0Sip_sound

/-- info: 'IxCC.Ring0.admittedRing0Sip_call_not_goesWrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.admittedRing0Sip_call_not_goesWrong

/-- info: 'IxCC.Ring0.multi_sip_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.multi_sip_frame

/-- info: 'IxCC.Ring0.multi_sip_wordRegion_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.multi_sip_wordRegion_preserved

/-- info: 'IxCC.Ring0.pairwiseDisjointSips_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.pairwiseDisjointSips_frame

/-- info: 'IxCC.X86.Encode.encodeK_csimp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.encodeK_csimp

/-- info: 'IxCC.X86.Driver.checkOk_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Driver.checkOk_iff

/-- info: 'IxCC.X86.Driver.checkCanonical_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.Driver.checkCanonical_iff

/-- info: 'IxCC.X86.Driver.exists_canonicalOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Driver.exists_canonicalOk

/-- info: 'IxCC.X86.Driver.CanonicalOk.text_disjoint_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Driver.CanonicalOk.text_disjoint_mapped

/-- info: 'IxCC.X86.Driver.CanonicalOk.mapped_below47' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Driver.CanonicalOk.mapped_below47

/-- info: 'IxCC.X86.Driver.CanonicalOk.text_below47' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Driver.CanonicalOk.text_below47

/-- info: 'IxCC.Recheck.sound_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.sound_nat

/-- info: 'IxCC.Recheck.sound_ctor0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.sound_ctor0

/-- info: 'IxCC.Recheck.compile_sound_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.compile_sound_of_eval

/-- info: 'IxCC.Own.Plain.Certificate.admitWithContracts_lower_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitWithContracts_lower_refines

/-- info: 'IxCC.Recheck.Rc.contract_source_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Rc.contract_source_refines

/-- info: 'IxCC.Ring0.objectEval_exec_framePreserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.objectEval_exec_framePreserved

/-- info: 'IxCC.Ring0.session_run_preserves_unmapped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.session_run_preserves_unmapped

/-- info: 'IxCC.Ring0.external_wordAt_preserved' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Ring0.external_wordAt_preserved

/-- info: 'IxCC.Ring0.kernelTablesPreserved_of_session_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.kernelTablesPreserved_of_session_run

/-- info: 'IxCC.Recheck.checkCanonicalRelevance_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.Recheck.checkCanonicalRelevance_iff

/-- info: 'IxCC.Recheck.front_wellAnnotated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.front_wellAnnotated

/-- info: 'IxCC.Src.Table.checkAxiomClosure_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkAxiomClosure_sound

/-- info: 'IxCC.Src.Table.checkAxiomClosure_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkAxiomClosure_roots

/-- info: 'IxCC.Src.Table.checkAxiomWalk_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkAxiomWalk_closed

/-- info: 'IxCC.Src.Term.constsBudget_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Term.constsBudget_sound

/-! Statement pin: this fails to elaborate if `checkAxiomClosure_sound` loses its
closure conclusion. -/

example {p : IxCC.Src.Program} {thm c : IxCC.Src.CId}
    (h : IxCC.Src.Table.checkAxiomClosure p thm = .ok ())
    (hr : IxCC.Src.Table.AxiomReach p thm c) (hc : c < p.size) :
    IxCC.Src.Table.AxiomDeclOk p c :=
  (IxCC.Src.Table.checkAxiomClosure_sound h).2 c hr hc

/-- info: 'IxCC.Src.Table.ofCert_ok_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.ofCert_ok_props

/-- info: 'IxCC.Src.Table.buildResolve_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.buildResolve_sound

/-- info: 'IxCC.Src.Lazify.lazifyTerm_eqv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.lazifyTerm_eqv

/-- info: 'IxCC.Src.Lazify.term_modeEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.term_modeEq

/-- info: 'IxCC.Src.Lazify.spine_modeEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.spine_modeEq

/-- info: 'IxCC.Src.Lazify.ihs_modeEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.ihs_modeEq

/-- info: 'IxCC.Src.Lazify.setTerm_modeEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.setTerm_modeEq

/-- info: 'IxCC.Src.Lazify.step_modeEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.step_modeEq

/-- info: 'IxCC.Src.Lazify.run_modeEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.run_modeEq

/-- info: 'IxCC.Src.Lazify.run_termOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Lazify.run_termOf

/-- info: 'IxCC.Src.Program.ModeEq.termOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Program.ModeEq.termOf

/-! Statement pin: `Lazify.run` is `Program.ModeEq` to its input for every key list. -/

example (p : IxCC.Src.Program) (keys : List IxCC.Src.TermKey) :
    IxCC.Src.Program.ModeEq p (IxCC.Src.Lazify.run p keys) :=
  IxCC.Src.Lazify.run_modeEq p keys

/-- info: 'IxCC.CompileClaim.toPayloadBytes_ofPayloadBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.toPayloadBytes_ofPayloadBytes

/-- info: 'IxCC.CompileClaim.toClaimBytes_ofClaimBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.toClaimBytes_ofClaimBytes

/-- info: 'IxCC.Ring0.admittedRing0Sip_step_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.admittedRing0Sip_step_frame

/-- info: 'IxCC.Ring0.admittedRing0Sip_multi_sip_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.admittedRing0Sip_multi_sip_frame

/-- info: 'IxCC.Ring0.admittedRing0Sip_call_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.admittedRing0Sip_call_frame

/-- info: 'IxCC.Ring0.callRunsInFrame_of_ne_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.callRunsInFrame_of_ne_stuck

/-- info: 'IxCC.Ring0.linked_call_ne_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.linked_call_ne_stuck

/-- info: 'IxCC.Ring0.linked_run_call_ne_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.linked_run_call_ne_stuck

/-! Result shapes at the roots a claim names (`IxCC.Recheck.Proof.RootShape`), with the
readback-discovery facts they rest on (`IxCC.Recheck.Readback`). -/

/-- info: 'IxCC.Recheck.Readback.Shape.eq_of_beq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.Shape.eq_of_beq

/-- info: 'IxCC.Recheck.Readback.Shape.eq_of_beqList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.Shape.eq_of_beqList

/-- info: 'IxCC.Recheck.Readback.Shape.beq_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.Shape.beq_refl

/-- info: 'IxCC.Recheck.Readback.Shape.beqList_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.Shape.beqList_refl

/-- info: 'IxCC.Recheck.Readback.forIn_none_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.forIn_none_all

/-- info: 'IxCC.Recheck.Readback.shape?_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.shape?_head

/-- info: 'IxCC.Recheck.Readback.forIn_all_of_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.forIn_all_of_none

/-- info: 'IxCC.Recheck.Readback.forIn_some_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.forIn_some_false

/-- info: 'IxCC.Recheck.Readback.rowMatches_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.rowMatches_spec

/-- info: 'IxCC.Recheck.Readback.discoverRaw_root' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.discoverRaw_root

/-- info: 'IxCC.Recheck.resultShape?_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.resultShape?_iff

/-- info: 'IxCC.Recheck.toNat_shiftRight_one_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.toNat_shiftRight_one_lt

/-- info: 'IxCC.Recheck.readback_iff_viewShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.readback_iff_viewShape

/-- info: 'IxCC.Recheck.resultType?_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.resultType?_some

/-- info: 'IxCC.Recheck.some_beq_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.some_beq_false

/-- info: 'IxCC.Recheck.tagify_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.tagify_bool

/-- info: 'IxCC.Recheck.discover_enum_tagify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.discover_enum_tagify

/-- info: 'IxCC.Recheck.tagify_resultShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.tagify_resultShape

/-- info: 'IxCC.Recheck.erase_known' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.erase_known

/-- info: 'IxCC.Recheck.step_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.step_known

/-- info: 'IxCC.Recheck.steps_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.steps_known

/-- info: 'IxCC.Recheck.pipeline_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.pipeline_known

/-- info: 'IxCC.Recheck.runLir_boolKnown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.runLir_boolKnown

/-- info: 'IxCC.Recheck.Front.tys_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.tys_root

/-- info: 'IxCC.Recheck.Front.view_resultShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.view_resultShape

/-- info: 'IxCC.Recheck.Front.goesWrong_resultShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.goesWrong_resultShape

/-- info: 'IxCC.Recheck.Front.view_none_iff_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.view_none_iff_nat

/-- info: 'IxCC.Recheck.rootsOf_get_const' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.rootsOf_get_const

/-- info: 'IxCC.Recheck.Artifact.goesWrong_immortalRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Artifact.goesWrong_immortalRoot

/-- info: 'IxCC.CompileClaim.verifyProgram_immortal_rootShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_immortal_rootShape

/-- info: 'IxCC.CompileClaim.verifyProgram_zeroRc_rootShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_zeroRc_rootShape

/-- info: 'IxCC.CompileClaim.verifyBytes_immortal_rootShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_immortal_rootShape

/-- info: 'IxCC.CompileClaim.verifyBytes_zeroRc_rootShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_zeroRc_rootShape

/-- info: 'IxCC.Ring0.verifyRing0Sip_rootShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Ring0.verifyRing0Sip_rootShape

/-! The rows of a root's result type (erasure registers them; the middle and back
ends keep the table), the shape view at immortal roots, and constructor trees at
plain-RC roots (`IxCC.Recheck.Rc.Proof.RootTree`). -/

/-- info: 'IxCC.Recheck.Readback.rowMatches_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Readback.rowMatches_fields

/-- info: 'IxCC.Recheck.step_ctors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.step_ctors

/-- info: 'IxCC.Recheck.steps_ctors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.steps_ctors

/-- info: 'IxCC.Recheck.pipeline_ctors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.pipeline_ctors

/-- info: 'IxCC.Recheck.ofKey_of_tabOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.ofKey_of_tabOf

/-- info: 'IxCC.Recheck.mem_resultCtors_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.mem_resultCtors_bool

/-- info: 'IxCC.Recheck.erase_boolRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.erase_boolRow

/-- info: 'IxCC.Recheck.Front.boolRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.boolRows

/-- info: 'IxCC.Recheck.Front.shapeView_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.shapeView_some

/-- info: 'IxCC.Recheck.Front.shapeView_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.shapeView_of_shape

/-- info: 'IxCC.Recheck.Front.shapeView_off_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.shapeView_off_shape

/-- info: 'IxCC.Recheck.Front.goesWrong_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.goesWrong_shape

/-- info: 'IxCC.Recheck.Front.shapeView_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.shapeView_none_iff

/-- info: 'IxCC.Recheck.Front.shapeGoesWrong_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.shapeGoesWrong_iff

/-- info: 'IxCC.Recheck.Front.sound_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.sound_shape

/-- info: 'IxCC.Recheck.Front.safe_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Front.safe_shape

/-- info: 'IxCC.Recheck.Artifact.immortalRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Artifact.immortalRoot

/-- info: 'IxCC.Recheck.Artifact.shapeClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Artifact.shapeClaim

/-- info: 'IxCC.Recheck.treeShape_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.treeShape_view

/-- info: 'IxCC.Recheck.treeShapes_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.treeShapes_view

/-- info: 'IxCC.Recheck.discover_treeView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.discover_treeView

/-- info: 'IxCC.Recheck.RcReplay.runFront_ctors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_ctors

/-- info: 'IxCC.Recheck.RcReplay.runFront_boolKnown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_boolKnown

/-- info: 'IxCC.Recheck.RcReplay.Front.boolRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.boolRows

/-- info: 'IxCC.Recheck.RcReplay.isImmortalViewType_boolSig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.isImmortalViewType_boolSig

/-- info: 'IxCC.Recheck.RcReplay.treeView_flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.treeView_flat

/-- info: 'IxCC.Recheck.RcReplay.Front.view_plainShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.view_plainShape

/-- info: 'IxCC.Recheck.RcReplay.Front.goesWrong_plainShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Front.goesWrong_plainShape

/-- info: 'IxCC.Recheck.RcReplay.Artifact.goesWrong_plainRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Artifact.goesWrong_plainRoot

/-- info: 'IxCC.CompileClaim.verifyProgram_immortal_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_immortal_shape

/-- info: 'IxCC.CompileClaim.verifyProgram_zeroRc_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_zeroRc_shape

/-- info: 'IxCC.CompileClaim.verifyBytes_immortal_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_immortal_shape

/-- info: 'IxCC.CompileClaim.verifyBytes_zeroRc_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_zeroRc_shape

/-- info: 'IxCC.CompileClaim.verifyProgram_plainRc_rootShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgram_plainRc_rootShape

/-- info: 'IxCC.CompileClaim.verifyBytes_plainRc_rootShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝]
-/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_plainRc_rootShape
