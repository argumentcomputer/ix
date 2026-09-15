import Compilatrix.IxIR1.HPT
import Compilatrix.IxIR1.HPTCache
import Compilatrix.IxIR1.HPTCasePrune
import Compilatrix.IxIR1.HPTCasePruneProgram
import Compilatrix.IxIR1.HPTDestroy
import Compilatrix.IxIR1.HPTFetchForward
import Compilatrix.IxIR1.HPTPAPFuse
import Compilatrix.IxIR1.HPTPAPFuseProgram
import Compilatrix.IxIR1.HPTProduce
import Compilatrix.IxIR1.HPTSound

/-! Required axiom fences for HPT; expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.IxIR1.HPT.postFixpoint_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.postFixpoint_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.semanticAudit_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.semanticAudit_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.postFixpoint_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.postFixpoint_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.semanticAudit_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.semanticAudit_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.FieldShape.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldShape.holds_of_le

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.holds_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.holds_of_le

/-- info: 'Compilatrix.IxIR1.HPT.FieldFactsHold.holds_of_listLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFactsHold.holds_of_listLe

/-- info: 'Compilatrix.IxIR1.HPT.HeapShape.toFieldShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.HeapShape.toFieldShape_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldShape.toHeapShape_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldShape.toHeapShape_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.ofFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.ofFact_holds

/-- info: 'Compilatrix.IxIR1.HPT.FieldFact.toFact_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FieldFact.toFact_holds

/-- info: 'Compilatrix.IxIR1.HPT.Fact.exactConstructor?_eq_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.exactConstructor?_eq_some

/-- info: 'Compilatrix.IxIR1.HPT.Fact.exactConstructor?_holds_loc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.exactConstructor?_holds_loc

/-- info: 'Compilatrix.IxIR1.HPT.Fact.caseFields_ctor_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.caseFields_ctor_holds

/-- info: 'Compilatrix.IxIR1.HPT.Fact.caseFields_natSucc_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Fact.caseFields_natSucc_holds

/-- info: 'Compilatrix.IxIR1.HPT.analyzeOp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.analyzeOp_sound

/-- info: 'Compilatrix.IxIR1.HPT.invoke_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.invoke_sound

/-- info: 'Compilatrix.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.functionSummary_sound_of_run_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.functionSummary_sound_of_run_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.postFixpoint

/-- info: 'Compilatrix.IxIR1.HPT.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.semanticAudit

/-- info: 'Compilatrix.IxIR1.HPT.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Production.functionSummary_sound

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.postFixpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.postFixpoint

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.semanticAudit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.semanticAudit

/-- info: 'Compilatrix.IxIR1.HPT.Cache.Production.functionSummary_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Cache.Production.functionSummary_sound

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runWithFacts_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_rewriteCurrentAt_body_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_rewriteProgram_eq

/-- info: 'Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.CasePrune.runMain_rebuild_rewriteProgram

/-- info: 'Compilatrix.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FetchForward.runCode_forwardHead?_eq

/-- info: 'Compilatrix.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.FetchForward.runCode_runWithFacts_eq_ownerCompatible

/-- info: 'Compilatrix.IxIR1.HPT.Destroy.runOp_specialize?_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Destroy.runOp_specialize?_success

/-- info: 'Compilatrix.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.Destroy.runCode_runWithFacts_success_ownerCompatible

/-- info: 'Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.PAPFuse.fusePair?_refines

/-- info: 'Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.IxIR1.HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok_defaultOracle
