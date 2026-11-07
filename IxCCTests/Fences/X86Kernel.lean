import IxCC.X86.CheckK
import IxCC.X86.StreamK
import IxCC.X86.ELFWriteK

/-! Required axiom fences for the kernel-evaluable twins of the backend's
last steps (M1.K1): each twin on `Recheck.run`'s path equals the original
it replaces there, so the recheck path's object and its `Stream.Valid` and
`ELF.Valid` certificates are the originals' (M2.8 composes through these).
Expected messages are preserved verbatim. -/

/-- info: 'IxCC.X86.Program.wellFormedK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Program.wellFormedK_eq

/-- info: 'IxCC.X86.Program.checkK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Program.checkK_eq

/-- info: 'IxCC.X86.Encode.encodeK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Encode.encodeK_eq

/-- info: 'IxCC.X86.Stream.checkK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.checkK_eq

/-- info: 'IxCC.X86.Stream.encodeK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.Stream.encodeK_eq

/-- info: 'IxCC.X86.ELFRead.parseK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRead.parseK_eq

/-- info: 'IxCC.X86.ELF.checkK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.checkK_eq

/-- info: 'IxCC.X86.ELF.writeK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.writeK_eq

/-- info: 'IxCC.X86.ELF.writeCheckedK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.writeCheckedK_eq
