import Compilatrix.Anf.Proof.Mono

/-! Required axiom fences for the Anf proofs (M2.3): clock monotonicity of
Anf evaluation; ANF conversion (P1, Lam → Anf); the Anf-to-Anf relation, its
fundamental lemma and adequacy; the rewriting passes P2 shrink, P3 inline,
P4 specialise and pruning; the pipeline's correctness for every certificate
its replay accepts; and their traced restatements (decision D-1). Generated
by `plans/x86-phase1/m2-3/GenFences.lean`; expected messages are preserved
verbatim. -/

/-! Clock monotonicity of Anf evaluation (`Anf.Proof.Mono`). -/

/-- info: 'Compilatrix.Anf.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.eval_mono

/-- info: 'Compilatrix.Anf.evalBind_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.evalBind_mono

/-- info: 'Compilatrix.Anf.applyN_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.applyN_mono

/-- info: 'Compilatrix.Anf.evalAlts_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.evalAlts_mono

/-- info: 'Compilatrix.Anf.globVal_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.globVal_mono

/-- info: 'Compilatrix.Anf.callVal_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.callVal_mono

/-- info: 'Compilatrix.Anf.jumpTo_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.jumpTo_mono

/-- info: 'Compilatrix.Anf.enter_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.enter_mono

/-- info: 'Compilatrix.Anf.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Anf.run_mono
