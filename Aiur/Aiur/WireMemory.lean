import Aiur.WireBoundary
import Aiur.TypecheckFacts

namespace Aiur

/-- Decode the prover's table once for the whole derivation. Unused malformed cells are omitted. -/
def WireROM.decode [NatCast F] [Zero F] [DecidableEq F] (decls : Declarations)
    (rom : WireROM F) : ROM F :=
  ⟨rom.entries.filterMap (fun cell => (cell.2.decode decls).map (fun value => (cell.1, value)))⟩

theorem WireROM.mem_decode [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {rom : WireROM F} {address : F} {value : Value F} :
    (address, value) ∈ (rom.decode decls).entries ↔ ∃ wire,
      (address, wire) ∈ rom.entries ∧ wire.decode decls = some value := by
  simp only [WireROM.decode, List.mem_filterMap]
  constructor
  · rintro ⟨⟨location, wire⟩, member, decoded⟩
    obtain ⟨result, run, same⟩ := Option.map_eq_some_iff.mp decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨wire, member, run⟩
  · rintro ⟨wire, member, decoded⟩
    exact ⟨(address, wire), member, by simp [decoded]⟩

theorem WireROM.decode_wellFormed [NatCast F] [Zero F] [DecidableEq F]
    (decls : Declarations) (rom : WireROM F) : (rom.decode decls).WellFormed decls := by
  rintro ⟨address, value⟩ member
  obtain ⟨wire, _, decoded⟩ := WireROM.mem_decode.mp member
  exact (WireValue.decode_spec decoded).2.1

theorem WireROM.decode_valid [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {rom : WireROM F} (valid : rom.Valid) : (rom.decode decls).Valid := by
  intro a ha b hb address types
  obtain ⟨left, leftMem, leftDecode⟩ := WireROM.mem_decode.mp ha
  obtain ⟨right, rightMem, rightDecode⟩ := WireROM.mem_decode.mp hb
  have typed : left.type = right.type :=
    (WireValue.decode_spec leftDecode).1.symm.trans
      (types.trans (WireValue.decode_spec rightDecode).1)
  have same : left = right := valid _ leftMem _ rightMem address typed
  rw [same, rightDecode] at leftDecode
  exact (Option.some.inj leftDecode).symm

end Aiur
