import Compilatrix.Ixby.Runtime.Native.ArrayBasic
import Compilatrix.Ixby.Runtime.Native.ArrayRead

/-! The strengthened single-dispatch read contracts use ordinary Lean logic. -/

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.arrayGet_withoutStack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.arrayGet_withoutStack

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.packedGet_withoutStack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.packedGet_withoutStack

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_returns

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.arrayGet_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.arrayGet_outside

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.packedGet_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.packedGet_outside

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_outside

/-- info: 'Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_rejects_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Ixby.Runtime.Native.Certificate.writerGet_rejects_length
