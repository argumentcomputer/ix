import Compilatrix.Ixby.SourceSound
import Compilatrix.Ixby.WireSound
import Compilatrix.Ixby.SymbolicWire
import Compilatrix.Ixby.LeanSound

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

/-! The typed runtime representation slice adds no native reflection or hash axiom. -/

/-- info: 'Compilatrix.Ixby.Runtime.Representation.natOfBytesLE_bytesLE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.natOfBytesLE_bytesLE

/-- info: 'Compilatrix.Ixby.Runtime.Representation.bytesLE_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.bytesLE_extract

/-- info: 'Compilatrix.Ixby.Runtime.Representation.field_natural_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.field_natural_words

/-- info: 'Compilatrix.Ixby.Runtime.Representation.field_from_natural_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.field_from_natural_words

/-- info: 'Compilatrix.Ixby.Runtime.Representation.cached_sub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.cached_sub

/-- info: 'Compilatrix.Ixby.Runtime.Representation.toWord_nibble' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.toWord_nibble

/-- info: 'Compilatrix.Ixby.Runtime.Representation.fromWord_nibble' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.fromWord_nibble

/-- info: 'Compilatrix.Ixby.Runtime.Representation.claimResult_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.claimResult_injective

/-- info: 'Compilatrix.Ixby.Runtime.Representation.eval_field_from_natural_words' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.eval_field_from_natural_words

/-- info: 'Compilatrix.Ixby.Runtime.Representation.eval_field_bytes_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.eval_field_bytes_roundtrip

/-- info: 'Compilatrix.Ixby.Runtime.Representation.eval_bytesToField_noncanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Representation.eval_bytesToField_noncanonical

/-- info: 'Compilatrix.Ixby.Runtime.ScalarFunction.Checked.binary_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarFunction.Checked.binary_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.ScalarFunction.Checked.project_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarFunction.Checked.project_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extMul

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extInverse

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extFst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extFst

/-- info: 'Compilatrix.Ixby.LeanFrontend.Image.decodeNumber_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.LeanFrontend.Image.decodeNumber_represents

/-- info: 'Compilatrix.Ixby.LeanFrontend.Image.number_decode_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.LeanFrontend.Image.number_decode_roundtrip

/-- info: 'Compilatrix.Ixby.LeanFrontend.Image.decodeNumber_rejects_bad_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.LeanFrontend.Image.decodeNumber_rejects_bad_cache

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extMul_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extMul_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extInverse_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extInverse_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.ScalarCertificate.extFst_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.ScalarCertificate.extFst_evaluates

/-! Complete numeric conversion paths preserve the actual caller continuation. -/

/-- info: 'Compilatrix.Ixby.Runtime.Execution.Reaches.halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Execution.Reaches.halts

/-- info: 'Compilatrix.Ixby.Runtime.Execution.Reaches.evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Execution.Reaches.evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Execution.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Execution.resume

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.nibbleWord_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.nibbleWord_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.nibbleNat_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.nibbleNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.toWord_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.toWord_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.fromWordLoop_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.fromWordLoop_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fromRaw_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fromRaw_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fieldNatural_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fieldNatural_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fieldFromNatural_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fieldFromNatural_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.natural_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.natural_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.asField_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.asField_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.lowWord_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.lowWord_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_represents

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.natural_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.natural_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.asField_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.asField_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.lowWord_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.lowWord_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.fromWord_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.toWord_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.toWord_evaluates
