import IxVM.Mirrors.TagN

/-! The mirrors of the UInt64 and IxonDeserialize primitives and their callees, with their
lemmas (`Aiur.Generic.Derive.Mirrors`), derived from `IxVM.source`. -/

namespace IxVM.Refinement.Mirrors

/-- The UInt64 and IxonDeserialize primitives. -/
def deserializeRoots : List String := [
  "UInt64::from_bytes", "UInt64::to_bytes", "UInt64::from_fields",
  "UInt64::is_zero", "UInt64::eq", "UInt64::wrapping_succ",
  "UInt64::saturating_pred", "UInt64::to_field", "UInt64::sub_with_borrow",
  "UInt64::and", "UInt64::or", "UInt64::xor",
  "IxonDeserialize::read_byte",
  "IxonDeserialize::unpack_def_kind_safety",
  "IxonDeserialize::assert_wire_bool",
  "IxonDeserialize::get_quot_kind",
  "IxonDeserialize::get_u64_list",
  "IxonDeserialize::build_succ_chain",
  "IxonDeserialize::get_constant",
  "UInt32::less_than_fields"]

end IxVM.Refinement.Mirrors

#ixvm_mirrors IxVM.Refinement.Mirrors.deserializeRoots IxVM.Refinement.Mirrors.tagNRoots
