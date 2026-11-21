import Aiur.Semantics
import Aiur.ROMSemantics
import Aiur.Semantics.CallTypes
import Mathlib.Data.List.Nodup

namespace Aiur

/-- A source location and a field address correspond through the values they contain.
    Distinct allocations may correspond to the same ROM address. -/
inductive Represents (rom : ROM F) (heap : Heap F) : SourceValue F → Value F → Prop where
  | field : Represents rom heap (.field value) (.field value)
  | tuple (items : List.Forall₂ (Represents rom heap) sources targets) :
      Represents rom heap (.tuple sources) (.tuple targets)
  | construct (items : List.Forall₂ (Represents rom heap) sources targets) :
      Represents rom heap (.construct name ctor sources) (.construct name ctor targets)
  | ptr (source : heap[location]? = some stored)
      (cell : (address, encoded) ∈ rom.entries)
      (contents : Represents rom heap stored encoded) :
      Represents rom heap (.ptr stored.type location) (.ptr encoded.type address)

variable {F : Type} {rom : ROM F} {heap larger : Heap F}

/-- Extending immutable memory preserves every earlier cell. -/
theorem heap_get_of_prefix (grows : heap <+: larger) {i : Nat} {v : SourceValue F}
    (found : heap[i]? = some v) : larger[i]? = some v := by
  obtain ⟨rest, rfl⟩ := grows
  rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).1)]
  exact found

theorem Represents.type {source : SourceValue F} {target : Value F}
    (related : Represents rom heap source target) : source.type = target.type := by
  induction related using Represents.rec
    (motive_2 := fun sources targets _ => sources.map Value.type = targets.map Value.type) with
  | field | construct => simp [Value.type]
  | tuple _ ih => simp only [Value.type, ih]
  | ptr _ _ _ ih => simp only [Value.type, ih]
  | nil => rfl
  | cons _ _ h t => simp only [List.map_cons, h, t]

theorem Represents.wellFormed (decls : Declarations) {source : SourceValue F} {target : Value F}
    (related : Represents rom heap source target) :
    source.wellFormed decls = target.wellFormed decls := by
  induction related using Represents.rec
    (motive_2 := fun sources targets _ =>
      sources.map Value.type = targets.map Value.type ∧
        sources.map (Value.wellFormed decls) = targets.map (Value.wellFormed decls)) with
  | field => simp [Value.wellFormed]
  | tuple _ ih => simp [Value.wellFormed, ih.2]
  | construct _ ih => simp [Value.wellFormed, ih.1, ih.2]
  | ptr _ _ related ih => simp [Value.wellFormed, related.type]
  | nil => exact ⟨rfl, rfl⟩
  | cons head _ h t => exact ⟨by simp [head.type, t.1], by simp [h, t.2]⟩

theorem Represents.mono {source : SourceValue F} {target : Value F}
    (related : Represents rom heap source target) (grows : heap <+: larger) :
    Represents rom larger source target := by
  induction related using Represents.rec
    (motive_2 := fun sources targets _ => List.Forall₂ (Represents rom larger) sources targets) with
  | field => exact .field
  | tuple _ ih => exact .tuple ih
  | construct _ ih => exact .construct ih
  | ptr source cell _ ih => exact .ptr (heap_get_of_prefix grows source) cell ih
  | nil => exact .nil
  | cons _ _ h t => exact .cons h t

abbrev RepresentsArgs (rom : ROM F) (heap : Heap F) := List.Forall₂ (Represents rom heap)
abbrev RepresentsEnv (rom : ROM F) (heap : Heap F) :=
  List.Forall₂ (fun (s : String × SourceValue F) (t : String × Value F) =>
    s.1 = t.1 ∧ Represents rom heap s.2 t.2)

theorem RepresentsArgs.mono {sources : List (SourceValue F)} {targets : List (Value F)}
    (related : RepresentsArgs rom heap sources targets) (grows : heap <+: larger) :
    RepresentsArgs rom larger sources targets := related.imp (fun _ _ h => h.mono grows)

theorem RepresentsEnv.mono {sources : Environment F Nat} {targets : Environment F}
    (related : RepresentsEnv rom heap sources targets) (grows : heap <+: larger) :
    RepresentsEnv rom larger sources targets := related.imp (fun _ _ h => ⟨h.1, h.2.mono grows⟩)

theorem ROM.functional (valid : rom.Valid) {address : F} {left right : Value F}
    (a : (address, left) ∈ rom.entries) (b : (address, right) ∈ rom.entries)
    (typed : left.type = right.type) : left = right :=
  valid _ a _ b rfl typed

/-- The pointer-free public interface can be represented in every ROM and heap. -/
theorem Represents.of_pointerFree (source : SourceValue F) (free : source.pointerFree = true)
    (encode : Nat → F) : Represents rom heap source (source.mapAddress encode) := by
  cases source with
  | field => simpa only [Value.mapAddress] using Represents.field
  | ptr => simp [Value.pointerFree, Value.type, Ty.pointerFree] at free
  | tuple items | construct _ _ items =>
      simp only [Value.mapAddress]
      first | apply Represents.tuple | apply Represents.construct
      have freeItems : ∀ item ∈ items, item.pointerFree = true := by
        simpa [Value.pointerFree, Value.type, Ty.pointerFree] using free
      apply List.forall₂_map_right_iff.mpr
      exact List.forall₂_same.mpr (fun item member => of_pointerFree item (freeItems item member) encode)
termination_by sizeOf source


/-- A pointer-free result is equal as data, without any address correspondence. -/
theorem Represents.pointerFree_eq {source : SourceValue F} {target : Value F}
    (related : Represents rom heap source target) : target.pointerFree = true →
    source = target.mapAddress (fun _ => 0) := by
  induction related using Represents.rec
    (motive_2 := fun sources targets _ =>
      (∀ value ∈ targets, value.pointerFree = true) →
        sources = targets.map (Value.mapAddress (fun _ => 0))) with
  | field => intro _; simp [Value.mapAddress]
  | tuple _ ih | construct _ ih =>
      intro free
      simp only [Value.mapAddress, Value.tuple.injEq, Value.construct.injEq, true_and]
      apply ih
      simpa [Value.pointerFree, Value.type, Ty.pointerFree] using free
  | ptr => simp [Value.pointerFree, Value.type, Ty.pointerFree]
  | nil => rfl
  | cons _ _ h t =>
      rename_i free
      simp only [List.map_cons]
      exact congrArg₂ List.cons (h (free _ (by simp))) (t (fun v mem => free v (by simp [mem])))

end Aiur
