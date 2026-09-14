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

/-! Complete Nat add/sub/mul paths, including conversions and caller restoration. -/

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.call_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.call_natural

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.read_naturals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.read_naturals

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.binary_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.binary_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.add_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.add_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.sub_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.sub_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mul_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mul_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.add_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.add_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.sub_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.sub_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mul_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mul_evaluates

/-! Complete Nat division, remainder, and comparison paths. -/

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.quotientRemainder_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.quotientRemainder_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.div_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.div_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mod_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mod_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.lt_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.lt_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.le_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.le_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_field_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_field_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.div_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.div_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mod_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.mod_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.eq_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.lt_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.lt_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.le_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.le_evaluates

/-! Complete base-field and extension-packing paths, including conversion calls. -/

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.call_asField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.call_asField

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.read_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.read_fields

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.binary_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.binary_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.reduce_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.reduce_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.add_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.add_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.sub_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.sub_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.mul_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.mul_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.neg_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.neg_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.inverse_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.inverse_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.pack_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.pack_returns

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.reduce_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.reduce_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.add_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.add_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.sub_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.sub_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.mul_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.mul_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.neg_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.neg_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.inverse_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.inverse_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.pack_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.FieldArithmetic.Certificate.pack_evaluates

/-! Complete Nat shift, logarithm, and power loops with caller preservation. -/

/-- info: 'Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.call_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatArithmetic.Certificate.call_mul

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_halving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_halving

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_even

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_odd

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_half_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_half_le

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_square_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_square_le

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.pow_accumulator_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.pow_accumulator_le

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRightLoop_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRightLoop_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2Loop_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2Loop_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.powLoop_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.powLoop_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRight_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRight_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.pow_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.pow_returns

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRightLoop_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRightLoop_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2Loop_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2Loop_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.powLoop_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.powLoop_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRight_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.shiftRight_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.log2_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.NatLoops.Certificate.pow_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.NatLoops.Certificate.pow_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8Add_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8Add_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Add_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Add_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Mul_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Mul_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeAdd_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeAdd_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Sub_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Sub_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeSub_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeSub_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32And_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32And_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Or_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Or_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Xor_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Xor_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftLeft_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftLeft_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftRight_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftRight_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftLeft_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftLeft_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftRight_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftRight_returns

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.call_lowWord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.call_lowWord

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.read_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.read_parts

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.read_lowWords' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.read_lowWords

/-- info: 'Compilatrix.Ixby.Runtime.Conversion.Certificate.read_binary_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Conversion.Certificate.read_binary_parts

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8Equal_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8Equal_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Equal_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Equal_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Less_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Less_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeEqual_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeEqual_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeLess_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeLess_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ToNat_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ToNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ToU32_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ToU32_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ToNat_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ToNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeToNat_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeToNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8OfNat_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8OfNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNat_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeOfNat_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeOfNat_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ToU8_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ToU8_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNatLT_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNatLT_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.lowWord_mod' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.lowWord_mod

/-- info: 'Compilatrix.Ixby.Runtime.Words.lowWord_mask8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.lowWord_mask8

/-- info: 'Compilatrix.Ixby.Runtime.Words.lowWord_subtract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.lowWord_subtract

/-- info: 'Compilatrix.Ixby.Runtime.Words.subtract_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.subtract_nat

/-- info: 'Compilatrix.Ixby.Runtime.Words.masked_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.masked_count

/-- info: 'Compilatrix.Ixby.Runtime.Words.masked_count_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.masked_count_lt

/-- info: 'Compilatrix.Ixby.Runtime.Words.modular_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.modular_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.subtract_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.subtract_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.u8_lowWord' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.u8_lowWord

/-- info: 'Compilatrix.Ixby.Runtime.Words.u8_shiftLeft_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.u8_shiftLeft_nat

/-- info: 'Compilatrix.Ixby.Runtime.Words.u8_shiftRight_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.u8_shiftRight_nat

/-- info: 'Compilatrix.Ixby.Runtime.Words.u32_shiftLeft_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.u32_shiftLeft_nat

/-- info: 'Compilatrix.Ixby.Runtime.Words.u32_shiftRight_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.u32_shiftRight_nat

/-- info: 'Compilatrix.Ixby.Runtime.Words.identity_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.identity_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.compare_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.compare_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.logical_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.logical_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.shift_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.shift_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.truncate_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.truncate_returns

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ToNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ToNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ToU32_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ToU32_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ToNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ToNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeToNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeToNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8OfNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8OfNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeOfNat_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeOfNat_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ToU8_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ToU8_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNatLT_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32OfNatLT_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8Equal_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8Equal_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Equal_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Equal_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Less_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Less_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeEqual_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeEqual_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeLess_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeLess_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8Add_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8Add_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Add_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Add_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Mul_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Mul_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeAdd_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeAdd_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Sub_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Sub_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.usizeSub_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.usizeSub_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32And_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32And_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Or_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Or_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32Xor_evaluates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32Xor_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftLeft_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftLeft_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftRight_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u8ShiftRight_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftLeft_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftLeft_evaluates

/-- info: 'Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftRight_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Words.Certificate.u32ShiftRight_evaluates
