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
