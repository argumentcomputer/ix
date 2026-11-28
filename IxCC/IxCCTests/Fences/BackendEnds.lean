import IxCC.Backend.Proof.Ends

/-! Required axiom fences for the backend for `main`'s export:
the backend's conclusion for an emitted object under the entry invariant
(`Backend.emitted_ends`: the stacking simulation transported through
layout), and Lir to the object with no premise on the emitted code
(`compile_sim_main`, `compile_refines_main`, `compile_tsim_main`).
Generated from the module's public theorems; expected messages are
preserved verbatim. -/

/-- info: 'IxCC.Backend.statusOf_code' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Backend.statusOf_code

/-- info: 'IxCC.Backend.emitted_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.emitted_ends

/-- info: 'IxCC.Backend.compile_sim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compile_sim_main

/-- info: 'IxCC.Backend.compile_refines_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compile_refines_main

/-- info: 'IxCC.Backend.compile_tsim_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Backend.compile_tsim_main
