import Aiur.Tiling.Copy

/-! Facts about the enumeration of physical rows and copy keys. -/

namespace Aiur.Tiling

variable {F : Type}

theorem nodup_flatMap_pairs {α β : Type} (l : List α) (g : α → List β) (hl : l.Nodup)
    (hg : ∀ a ∈ l, (g a).Nodup) : (l.flatMap fun a => (g a).map fun b => (a, b)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun a ha => (hg a ha).map (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
  apply hl.imp
  intro a a' ne
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨b, _, rfl⟩ ⟨b', _, h⟩
  exact ne (Prod.mk.inj h).1.symm

namespace System

variable (sys : System F)

theorem mem_enumerate {count : Nat → Nat} {f i x : Nat} :
    (f, i, x) ∈ sys.enumerate count ↔ f < sys.templates.length ∧ i < sys.cap f ∧ x < count f := by
  simp only [enumerate, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨f', hf, _, ⟨i', hi, x', hx, rfl⟩, rfl, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨hf, hi, hx⟩
  · rintro ⟨hf, hi, hx⟩
    exact ⟨f, hf, (i, x), ⟨i, hi, x, hx, rfl⟩, rfl, rfl⟩

theorem enumerate_nodup (count : Nat → Nat) : (sys.enumerate count).Nodup := by
  apply nodup_flatMap_pairs _ _ List.nodup_range
  intro f _
  exact nodup_flatMap_pairs _ _ List.nodup_range fun _ _ => List.nodup_range

theorem places_nodup : sys.places.Nodup := sys.enumerate_nodup _
theorem keys_nodup : sys.keys.Nodup := sys.enumerate_nodup _

theorem mem_places {f i r : Nat} :
    (f, i, r) ∈ sys.places ↔ f < sys.templates.length ∧ i < sys.cap f ∧ r < sys.rowCount f :=
  sys.mem_enumerate

theorem mem_keys {f i s : Nat} :
    (f, i, s) ∈ sys.keys ↔ f < sys.templates.length ∧ i < sys.cap f ∧ s < sys.slotCount f :=
  sys.mem_enumerate

theorem row_lt {f i r : Nat} (h : (f, i, r) ∈ sys.places) : sys.row f i r < sys.places.length :=
  List.idxOf_lt_length_of_mem h

theorem places_row {f i r : Nat} (h : (f, i, r) ∈ sys.places) :
    sys.places[sys.row f i r]'(sys.row_lt h) = (f, i, r) :=
  List.getElem_idxOf _

theorem row_places {p : Nat} (h : p < sys.places.length) :
    sys.row sys.places[p].1 sys.places[p].2.1 sys.places[p].2.2 = p :=
  sys.places_nodup.idxOf_getElem p h

theorem label_inj {k k' : Nat × Nat × Nat} (hk : k ∈ sys.keys) (hk' : k' ∈ sys.keys)
    (h : sys.keys.idxOf k = sys.keys.idxOf k') : k = k' := by
  have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem hk)
  have b := List.getElem_idxOf (List.idxOf_lt_length_of_mem hk')
  simp only [h] at a
  exact a.symm.trans b

theorem label_lt {f i s : Nat} (h : (f, i, s) ∈ sys.keys) : sys.label f i s < sys.keys.length + 1 := by
  have := List.idxOf_lt_length_of_mem h
  simp only [label]; omega

end System

end Aiur.Tiling
