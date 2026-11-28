import IxCC.CompileClaim.Proof

/-! Exact axiom fences for `KF-4` / `SP-0` / `N5` seed-closure claim
verification and `FE-4` kernel-gated `verifyProgramChecked`. -/

/-- info: 'IxCC.CompileClaim.verifyBytes_kf4_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_kf4_closure

/-- info: 'IxCC.CompileClaim.verifyBytes_iff_kernelAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_iff_kernelAccepted

/-- info: 'IxCC.CompileClaim.verifyProgramChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyProgramChecked_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_kf4_immortal_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_kf4_immortal_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_kf4_zeroRc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_kf4_zeroRc_sound

/-- info: 'IxCC.CompileClaim.verifyBytes_kf4_plainRc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.CompileClaim.verifyBytes_kf4_plainRc_sound
