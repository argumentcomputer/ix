import Compilatrix.Ixby.Runtime.Native.WireNat

/-! Exact axiom fences for the fixed-width integer writer and its range helper. -/

/-- info: 'Compilatrix.Ixby.Runtime.Native.fixed_width_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.fixed_width_bounds

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.wireNatRange_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.wireNatRange_rejects

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.wireNatRange_encodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.wireNatRange_encodes

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_fixed_reaches_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_fixed_reaches_range

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_general_reaches_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_general_reaches_range

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_reaches_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_reaches_range

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_encodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_encodes

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.writeNat_rejects
