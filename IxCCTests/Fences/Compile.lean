import IxCC.Recheck.Proof.Compile

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
