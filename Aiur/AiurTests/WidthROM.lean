import Aiur.Memory.WidthCorrectness
import Aiur.Memory.WireProvenance
import Mathlib.Algebra.Field.Rat

namespace AiurWidthROMTests
open Aiur

private def raw : WidthROM Rat := ⟨[(0, [7]), (0, [7, 8])]⟩
private def types : List Ty := [.field, .tuple [.field], .tuple [.field, .field]]
private def views : WireROM Rat := raw.toWireROM [] types

-- Widths can reuse the same numeric address, and equal-width types can share
-- identical physical words. Neither operation changes the canonical value.
example : raw.Valid := by unfold WidthROM.Valid raw; decide +kernel
example : views.Valid := raw.toWireROM_valid (by unfold WidthROM.Valid raw; decide +kernel) [] types
example : (0, WireValue.field 7) ∈ views.entries := by
  unfold views
  rw [WidthROM.mem_toWireROM]
  simp only [raw, types, List.mem_cons, List.not_mem_nil]
  decide +kernel
example : (0, WireValue.mk (.tuple [.field]) [7]) ∈ views.entries := by
  unfold views
  rw [WidthROM.mem_toWireROM]
  simp only [raw, types, List.mem_cons, List.not_mem_nil]
  decide +kernel
example : (0, WireValue.mk (.tuple [.field, .field]) [7, 8]) ∈ views.entries := by
  unfold views
  rw [WidthROM.mem_toWireROM]
  simp only [raw, types, List.mem_cons, List.not_mem_nil]
  decide +kernel
example : (0, WireValue.mk (.tuple [.field, .field]) [7]) ∉ views.entries := by
  unfold views
  rw [WidthROM.mem_toWireROM]
  simp only [raw, types, List.mem_cons, List.not_mem_nil]
  decide +kernel

-- Different words at the same address and width cannot pass the raw model.
example : ¬(WidthROM.mk [(0, [7]), (0, [8])] : WidthROM Rat).Valid := by unfold WidthROM.Valid; decide +kernel

-- Unrelated invalid interpretations are permitted. The load theorem derives
-- canonicality from the typed store, rather than validating every raw view.
private def flag : EnumDecl := ⟨"Flag", [⟨"Off", []⟩, ⟨"On", []⟩]⟩
private def flagViews : WireROM Rat :=
  (WidthROM.mk [(0, [7])]).toWireROM [flag] [.field, .enum "Flag"]
example : flagViews.Valid := (WidthROM.mk [(0, [7])]).toWireROM_valid (by unfold WidthROM.Valid; decide +kernel) [flag] _
example : (WireValue.mk (.enum "Flag") ([7] : List Rat)).decode [flag] = none := by decide +kernel
example : (0, Value.field 7) ∈ (flagViews.decode [flag]).entries := by
  apply WireROM.mem_decode.mpr
  refine ⟨WireValue.field 7, ?_, by decide +kernel⟩
  unfold flagViews
  rw [WidthROM.mem_toWireROM]
  simp only [List.mem_cons, List.not_mem_nil]
  decide +kernel

end AiurWidthROMTests
