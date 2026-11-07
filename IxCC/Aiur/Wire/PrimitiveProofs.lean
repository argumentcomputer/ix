import IxCC.Aiur.Wire.Primitives

namespace IxCC.Aiur.Wire

open _root_.IxCC.Vendor.Aiur (G gSize)
open IxCC.Ixon
open IxCC.IxIR

theorem fieldWord_roundtrip (word : UInt64) :
    u64OfLEBytes (u64LEBytes word 8) = word := u64OfLEBytes_eight word

theorem getField_spec (value : G) : GetSpec getField (fieldBytes value) value := by
  let next : ByteArray → GetM G := fun bytes =>
    let word := u64OfLEBytes bytes
    if bounded : word < gSize then pure ⟨word, bounded⟩
    else throw "Aiur field: noncanonical representative"
  have tail : GetSpec (next (fieldBytes value)) ByteArray.empty value := by
    simp only [next, fieldBytes, fieldWord_roundtrip, dif_pos value.property]
    exact GetSpec.pure value
  have bytes := getBytes_spec (fieldBytes value)
  have size : (fieldBytes value).size = 8 := u64LEBytes_size 8 value.val
  rw [size] at bytes
  simpa [getField, next] using GetSpec.bind (next := next) bytes tail

theorem getOption_spec (read : GetM α) (encode : α → ByteArray) (fits : α → Bool)
    (spec : ∀ value, fits value = true → GetSpec read (encode value) value)
    (value : Option α) (admitted : optionFits fits value = true) :
    GetSpec (getOption read) (optionBytes encode value) value := by
  cases value with
  | none =>
    have total := GetSpec.bind (next := getOptionTag read)
      (Decode.getU8_tag_spec 0) (GetSpec.pure (none : Option α))
    simpa only [getOption, optionBytes, ByteArray.append_empty] using total
  | some value =>
    have total := GetSpec.bind (next := getOptionTag read)
      (Decode.getU8_tag_spec 1) (Decode.getSpecMap (spec value admitted) some)
    simpa only [getOption, optionBytes] using total

theorem getNatArray_spec (limits : Bounded.Limits) (values : Array Nat)
    (admitted : natArrayFits limits values = true) :
    GetSpec (getNatArray limits) (natArrayBytes values) values :=
  Bounded.getArray_spec limits (Bounded.getNat limits) Encoding.nat
    (Bounded.natFits limits) (Bounded.getNat_spec limits) values admitted

end IxCC.Aiur.Wire
