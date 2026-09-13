import Compilatrix.Ixby.SourceSound
import Compilatrix.Ixby.WireSound
import Compilatrix.Ixby.SymbolicWire

/-! Keep the new target proofs on the ordinary logical basis; the checked
Ixon prefix retains the repository's existing, explicitly ledgered hash boundary. -/

/-- info: 'Compilatrix.Ixby.Data.eq_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Data.eq_of_equal

/-- info: 'Compilatrix.Ixby.RunCertificate.refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.RunCertificate.refinement

/-- info: 'Compilatrix.Ixby.ByteCertificate.execution_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.ByteCertificate.execution_refines

/-- info: 'Compilatrix.Ixby.SymbolicSource.eval_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.SymbolicSource.eval_sound

/-- info: 'Compilatrix.Ixby.SymbolicTarget.run_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.SymbolicTarget.run_sound

/-- info: 'Compilatrix.Ixby.DataExpr.eq_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.DataExpr.eq_of_equal

/-- info: 'Compilatrix.Ixby.WireEquality.array_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.WireEquality.array_eq

/-- info: 'Compilatrix.Ixby.SymbolicCertificate.refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.SymbolicCertificate.refinement

/-- info: 'Compilatrix.Ixby.SymbolicCertificate.byte_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.SymbolicCertificate.byte_refinement

/-- info: 'Ix.Ixby.evaluates_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Ixby.evaluates_deterministic

/-- info: 'Ix.Ixby.Blake3.hash_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Ixby.Blake3.hash_size

/-- info: 'Compilatrix.Pipeline.ValidatedErasure.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedErasure.sourcePreservation
