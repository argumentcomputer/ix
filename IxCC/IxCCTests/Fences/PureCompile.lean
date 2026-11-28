import IxCC.Compile.Proof

/-! Exact axiom fences for the pure compiler's structural theorems (`IxCC.Compile.Proof`):
what `Compile.compile`, `check` and `build` computed, in terms of the ingress, the certificate
checker's acceptance and the executable writers. The semantic theorem over them is fenced with
the target statements (`IxCCCorrect/Fence.lean`). -/

/-- info: 'IxCC.Compile.bind_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.bind_ok

/-- info: 'IxCC.Compile.mapError_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.mapError_ok

/-- info: 'IxCC.Compile.require_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.require_ok

/-- info: 'IxCC.Compile.orRefuse_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.orRefuse_ok

/-- info: 'IxCC.Compile.withRetry_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.withRetry_ok

/-- info: 'IxCC.Compile.ingressRoots_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.ingressRoots_parts

/-- info: 'IxCC.Compile.ingress_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.ingress_parts

/-- info: 'IxCC.Compile.checkZero_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.checkZero_ok

/-- info: 'IxCC.Compile.checkPlain_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.checkPlain_ok

/-- info: 'IxCC.Compile.certifyZero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.certifyZero_sound

/-- info: 'IxCC.Compile.certifyPlain_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.certifyPlain_sound

/-- info: 'IxCC.Compile.certifyOn_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.certifyOn_sound

/-- info: 'IxCC.Compile.certifyAuto_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.certifyAuto_sound

/-- info: 'IxCC.Compile.certify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.certify_sound

/-- info: 'IxCC.Compile.targetIsRoot_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.targetIsRoot_ok

/-- info: 'IxCC.Compile.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.check_sound

/-- info: 'IxCC.Compile.executable_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.executable_plain

/-- info: 'IxCC.Compile.executable_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.executable_machine

/-- info: 'IxCC.Compile.build_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.build_spec

/-- info: 'IxCC.Compile.compile_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.compile_parts

/-- info: 'IxCC.Compile.compile_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.compile_deterministic

/-- info: 'IxCC.Compile.seedClosureOf_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Compile.seedClosureOf_ok

/-- info: 'IxCC.Compile.seedClosure_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.seedClosure_ok

/-- info: 'IxCC.Compile.check_seedClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.check_seedClosure

/-- info: 'IxCC.Compile.ingressAs_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.ingressAs_parts

/-- info: 'IxCC.Compile.zeroPolicy_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.zeroPolicy_ok

/-- info: 'IxCC.Compile.zeroPolicy_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Compile.zeroPolicy_refuses
