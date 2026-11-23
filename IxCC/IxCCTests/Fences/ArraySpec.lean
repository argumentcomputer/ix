import IxCC.Src.ArraySpec
import IxCC.Src.Table.Array

/-! Exact axiom fences for DR3/DR4 `Src.ArraySpec` & `Src.Table.Array`
conservativity specifications (`Array`, `ByteArray`, `String`). Every theorem
depends strictly on subsets of `[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'IxCC.Src.ArraySpec.emptyWithCapacity_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.emptyWithCapacity_eq

/-- info: 'IxCC.Src.ArraySpec.size_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.size_eq

/-- info: 'IxCC.Src.ArraySpec.getInternal_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.getInternal_eq

/-- info: 'IxCC.Src.ArraySpec.set_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.set_eq

/-- info: 'IxCC.Src.ArraySpec.push_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.push_eq

/-- info: 'IxCC.Src.ArraySpec.pop_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.pop_eq

/-- info: 'IxCC.Src.ArraySpec.extract_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.extract_eq

/-- info: 'IxCC.Src.ArraySpec.copySlice_model_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.copySlice_model_eq

/-- info: 'IxCC.Src.ArraySpec.swap_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ArraySpec.swap_eq

/-- info: 'IxCC.Src.ByteArraySpec.size_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.size_eq

/-- info: 'IxCC.Src.ByteArraySpec.get_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.get_eq

/-- info: 'IxCC.Src.ByteArraySpec.set_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.set_eq

/-- info: 'IxCC.Src.ByteArraySpec.push_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.push_eq

/-- info: 'IxCC.Src.ByteArraySpec.copySlice_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.copySlice_eq

/-- info: 'IxCC.Src.ByteArraySpec.extract_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.extract_eq

/-- info: 'IxCC.Src.ByteArraySpec.append_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.ByteArraySpec.append_eq

/-- info: 'IxCC.Src.StringSpec.utf8ByteSize_eq' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.utf8ByteSize_eq

/-- info: 'IxCC.Src.StringSpec.toBytes_eq_toUTF8' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.toBytes_eq_toUTF8

/-- info: 'IxCC.Src.StringSpec.ofByteArray_toByteArray' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.ofByteArray_toByteArray

/-- info: 'IxCC.Src.StringSpec.fromUTF8?_toByteArray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.fromUTF8?_toByteArray

/-- info: 'IxCC.Src.StringSpec.append_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.append_toBytes

/-- info: 'IxCC.Src.StringSpec.eq_iff_toBytes_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.StringSpec.eq_iff_toBytes_eq

/-- info: 'IxCC.Src.Table.checkArrayOp_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkArrayOp_sound

/-- info: 'IxCC.Src.Table.checkByteArrayOp_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkByteArrayOp_sound

/-- info: 'IxCC.Src.Table.checkStringOp_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Table.checkStringOp_sound
