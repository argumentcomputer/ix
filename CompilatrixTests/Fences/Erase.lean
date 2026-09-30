import Compilatrix.Src.Proof.Mono
import Compilatrix.Lam.Proof.Mono

/-! Required axiom fences for the source-to-Lam theorems (M2.2): clock
monotonicity of SrcEval and Lam. Expected messages are preserved verbatim. -/

/-- info: 'Compilatrix.Src.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.eval_mono

/-- info: 'Compilatrix.Src.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.apply_mono

/-- info: 'Compilatrix.Src.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.applyAll_mono

/-- info: 'Compilatrix.Src.fire_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.fire_mono

/-- info: 'Compilatrix.Src.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.force_mono

/-- info: 'Compilatrix.Src.forceAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.forceAll_mono

/-- info: 'Compilatrix.Src.evalConst_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.evalConst_mono

/-- info: 'Compilatrix.Src.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Src.run_mono

/-- info: 'Compilatrix.Lam.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.eval_mono

/-- info: 'Compilatrix.Lam.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.apply_mono

/-- info: 'Compilatrix.Lam.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.force_mono

/-- info: 'Compilatrix.Lam.evalList_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.evalList_mono

/-- info: 'Compilatrix.Lam.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.applyAll_mono

/-- info: 'Compilatrix.Lam.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Lam.run_mono
