import Aiur.Wire
import Mathlib.Data.List.FinRange

namespace Aiur

/-- Physical ROM words have no nominal tag. The payload length is its chip's
static width; addresses are local to that width. Only active rows occur here.
The STARK's lookup balance and field-capacity bounds remain adapter obligations. -/
structure WidthROM (F : Type) where
  entries : List (F × List F)

namespace WidthROM

/-- The same width and address must always supply the same words. -/
def Valid (rom : WidthROM F) : Prop :=
  ∀ a ∈ rom.entries, ∀ b ∈ rom.entries,
    a.1 = b.1 → a.2.length = b.2.length → a.2 = b.2

/-- Expand raw words into their static typed views for the existing compiler
model. This is a proof construction, not witness data or runtime validation.
Unused views may have invalid tags; the provenance theorem needs only the view
originating from the corresponding well-typed store. -/
def toWireROM (rom : WidthROM F) (decls : Declarations) (types : List Ty) : WireROM F :=
  ⟨rom.entries.flatMap fun (address, words) =>
    (types.filter fun type => (decls.layout type).toOption.map Layout.width == some words.length).map
      (fun type => (address, ⟨type, words⟩))⟩

theorem mem_toWireROM {rom : WidthROM F} {decls : Declarations} {types : List Ty}
    {address : F} {wire : WireValue F} :
    (address, wire) ∈ (rom.toWireROM decls types).entries ↔
      (address, wire.words) ∈ rom.entries ∧ wire.type ∈ types ∧
      (decls.layout wire.type).toOption.map Layout.width = some wire.words.length := by
  rcases wire with ⟨type, words⟩
  simp only [toWireROM, List.mem_flatMap, List.mem_map, List.mem_filter,
    beq_iff_eq, Prod.exists, Prod.mk.injEq, WireValue.mk.injEq]
  constructor
  · rintro ⟨a, w, member, t, ⟨typed, size⟩, rfl, rfl, rfl⟩
    exact ⟨member, typed, size⟩
  · rintro ⟨member, typed, size⟩
    exact ⟨address, words, member, type, ⟨typed, size⟩, rfl, rfl, rfl⟩

/-- Width-local functionality suffices for the type-directed ROM model. No
address directory, global uniqueness, or nominal tag column is assumed. -/
theorem toWireROM_valid {rom : WidthROM F} (valid : rom.Valid)
    (decls : Declarations) (types : List Ty) : (rom.toWireROM decls types).Valid := by
  rintro ⟨a, left⟩ ha ⟨b, right⟩ hb address typed
  obtain ⟨lm, _, ls⟩ := mem_toWireROM.mp ha
  obtain ⟨rm, _, rs⟩ := mem_toWireROM.mp hb
  have size : left.words.length = right.words.length := by
    rw [typed, rs] at ls
    exact (Option.some.inj ls).symm
  have words : left.words = right.words := valid _ lm _ rm address size
  cases left; cases right
  simp_all

/-- Reference construction: each width enumerates its own addresses. -/
def ofBuckets (widths : List Nat) (rows : Nat → List (List F)) (encode : Nat → F) : WidthROM F :=
  ⟨widths.flatMap fun width =>
    List.ofFn (fun i : Fin (rows width).length => (encode i, (rows width)[i]))⟩

/-- The injection bound is per bucket; numeric addresses can be reused freely
in other widths. The AIR enforces this with its local consecutive-address rows. -/
theorem ofBuckets_valid (widths : List Nat) (rows : Nat → List (List F)) (encode : Nat → F)
    (sized : ∀ w ∈ widths, ∀ words ∈ rows w, words.length = w)
    (distinct : ∀ w ∈ widths, ∀ i j, i < (rows w).length → j < (rows w).length →
      encode i = encode j → i = j) : (ofBuckets widths rows encode).Valid := by
  intro a ha b hb address size
  obtain ⟨w, wm, hm⟩ := List.mem_flatMap.mp ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  obtain ⟨v, vm, hn⟩ := List.mem_flatMap.mp hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hn
  have sameWidth : w = v :=
    (sized w wm _ (List.getElem_mem i.isLt)).symm.trans
      (size.trans (sized v vm _ (List.getElem_mem j.isLt)))
  subst v
  have same : i = j := Fin.ext (distinct w wm i j i.isLt j.isLt address)
  subst j
  rfl

end WidthROM
end Aiur
