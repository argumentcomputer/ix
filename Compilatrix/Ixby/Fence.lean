import Compilatrix.Ixby.SourceSound
import Compilatrix.Ixby.WireSound

/-! Keep the new target proofs on the ordinary logical basis; the checked
Ixon prefix retains the repository's existing, explicitly ledgered hash boundary. -/

/-- info: 'Compilatrix.Ixby.Data.eq_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Data.eq_of_equal

/-- info: 'Compilatrix.Ixby.RunCertificate.refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.RunCertificate.refinement

/-- info: 'Compilatrix.Ixby.ByteCertificate.execution_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.ByteCertificate.execution_refines

/-- info: 'Ix.Ixby.evaluates_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Ix.Ixby.evaluates_deterministic

/-- info: 'Ix.Ixby.Blake3.hash_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Ix.Ixby.Blake3.hash_size

/-- info: 'Compilatrix.Pipeline.ValidatedErasure.sourcePreservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Blake3.HasherOps.hash._native.native_decide.ax_1✝] -/
#guard_msgs in #print axioms Compilatrix.Pipeline.ValidatedErasure.sourcePreservation
