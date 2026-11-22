import IxCC.Own.Plain.Proof.Certificate
import IxCC.Recheck.Rc.Proof.Replay
import IxCC.Compiler.Proof

/-! Exact axiom inventory of the parameter total (`Anf.maxParamTotal`): its check, admission's
monotonicity in it and the bound it gives every run of the source-domain check, on the plain-RC
route (`runFront_paramTotal`) and the zero-RC route (`runWithContracts_paramTotal`); and the
zero-RC route's check of the canonical map, which is the domain and the pins alone
(`checkContractPlainMap_canonical`). -/

/-- info: 'IxCC.Own.Plain.Certificate.checkParamTotal_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.checkParamTotal_ok

/-- info: 'IxCC.Own.Plain.Certificate.admit_params_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_params_mono

/-- info: 'IxCC.Own.Plain.Certificate.admit_paramTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_paramTotal

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_params_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_params_mono

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_paramTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_paramTotal

/-- info: 'IxCC.Recheck.RcReplay.runFront_paramTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_paramTotal

/-- info: 'IxCC.Own.Plain.checkContractPlainMap_canonical' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractPlainMap_canonical

/-- info: 'IxCC.Recheck.Artifact.checkContractOwn_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Artifact.checkContractOwn_iff

/-- info: 'IxCC.Recheck.runWithContracts_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.runWithContracts_ok

/-- info: 'IxCC.Recheck.runWithContracts_paramTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.runWithContracts_paramTotal
