import IxCC.X86.ELF
import IxCC.X86.ELFValidate
import IxCC.X86.ELFCheckK
import IxCC.X86.ELFWriteK
import IxCC.X86.ELFRodata
import IxCC.X86.ObjectRun
import IxCC.X86.ObjectCall
import IxCC.X86.Linked

/-! Exact axiom fences for DR1 `.rodata` immortal static ELF64 extensions
(`ELFValidate`, `ELFCheckK`, `ELFWriteK`, `ELFRodata`, `ObjectRun`,
`ObjectCall`, `Linked`). Every theorem depends strictly on subsets of
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'IxCC.X86.ELF.Valid.rodata' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.rodata

/-- info: 'IxCC.X86.ELF.Valid.rodata_readonly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.rodata_readonly

/-- info: 'IxCC.X86.ELF.Valid.rodataExported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.Valid.rodataExported

/-- info: 'IxCC.X86.ELF.sectionShapeK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.sectionShapeK_eq

/-- info: 'IxCC.X86.ELF.rodataExportsOkK_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELF.rodataExportsOkK_eq

/-- info: 'IxCC.X86.ELF.rodataObjectSymbol_mk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.X86.ELF.rodataObjectSymbol_mk

/-- info: 'IxCC.X86.ELFRodata.staticHeader_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.staticHeader_scan

/-- info: 'IxCC.X86.ELFRodata.staticHeader_cls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.staticHeader_cls

/-- info: 'IxCC.X86.ELFRodata.staticHeader_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.staticHeader_tag

/-- info: 'IxCC.X86.ELFRodata.staticHeader_rc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.staticHeader_rc

/-- info: 'IxCC.X86.ELFRodata.staticHeader_rc_signed_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.staticHeader_rc_signed_neg

/-- info: 'IxCC.X86.ELFRodata.encodeWords_getElem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.encodeWords_getElem

/-- info: 'IxCC.X86.ELFRodata.mapRodata_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ELFRodata.mapRodata_mapped

/-- info: 'IxCC.X86.ObjectEval.runTo_readOnlyFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.runTo_readOnlyFrame

/-- info: 'IxCC.X86.ObjectEval.call_readOnlyFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.call_readOnlyFrame

/-- info: 'IxCC.X86.ObjectEval.call_preserves_rodata' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.ObjectEval.call_preserves_rodata

/-- info: 'IxCC.X86.LinkedRodata.initCall_preserves_rodata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.LinkedRodata.initCall_preserves_rodata

/-- info: 'IxCC.X86.LinkedRodata.rootCall_preserves_rodata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.LinkedRodata.rootCall_preserves_rodata

/-- info: 'IxCC.X86.LinkedRodata.rodata_none_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.X86.LinkedRodata.rodata_none_eq
