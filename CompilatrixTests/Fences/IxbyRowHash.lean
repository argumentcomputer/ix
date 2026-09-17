import Compilatrix.Ixby.Runtime.Native.RowHash

/-! Exact axiom fences for the certified MMCS row-hash helpers. -/

/-- info: 'Compilatrix.Ixby.Runtime.Native.hashRow_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.hashRow_bytes

/-- info: 'Compilatrix.Ixby.Runtime.Native.rowBytes_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.rowBytes_append

/-- info: 'Compilatrix.Ixby.Runtime.Native.rowBytes_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.rowBytes_singleton

/-- info: 'Compilatrix.Ixby.Runtime.Native.rowBytes_extract_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.rowBytes_extract_cons

/-- info: 'Compilatrix.Ixby.Runtime.Native.rowBytes_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.rowBytes_size

/-- info: 'Compilatrix.Ixby.Runtime.Native.eval_blake3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.eval_blake3

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.rowBytesLoop_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.rowBytesLoop_returns

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_returns

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_packed_traps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_packed_traps

/-- info: 'Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_writer_traps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.WireCertificate.hashRow_writer_traps
