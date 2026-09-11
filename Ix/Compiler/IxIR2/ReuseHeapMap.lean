import Ix.Compiler.IxIR2.ReservationHeap

/-!
# Allocation history for suspended reuse

The map retains every baseline allocation, including dead registers in saved
callers. Physical reuse may give a dead allocation and a later allocation the
same image. Injectivity is required only for currently live baseline nodes.
This keeps saved registers stable while reserving and later refilling a slot.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.IxIR1.Sim (NodeBoxIso RValIso RValsIso)

def MapRel (mapping : Array Nat) (left right : Nat) : Prop := mapping[left]? = some right

theorem MapRel.functional {mapping : Array Nat} {left first second : Nat}
    (one : MapRel mapping left first) (two : MapRel mapping left second) : first = second :=
  Option.some.inj (one.symm.trans two)

theorem MapRel.bound {mapping : Array Nat} {left right : Nat}
    (related : MapRel mapping left right) : left < mapping.size :=
  (Array.getElem?_eq_some_iff.mp related).1

theorem MapRel.push {mapping : Array Nat} {left right : Nat}
    (related : MapRel mapping left right) (location : Nat) :
    MapRel (mapping.push location) left right := by
  simpa only [MapRel, Array.getElem?_push_lt related.bound,
    Array.getElem?_eq_getElem related.bound] using related

theorem MapRel.fresh (mapping : Array Nat) (location : Nat) :
    MapRel (mapping.push location) mapping.size location := Array.getElem?_push_size

structure HeapMap (left right : Store) (mapping : Array Nat) : Prop where
  size : mapping.size = left.heap.nodes.size
  imageBound : ∀ {l r}, MapRel mapping l r → r < right.heap.nodes.size
  forward : ∀ {l r box}, MapRel mapping l r → left.get? l = some box →
    ∃ targetBox, right.get? r = some targetBox ∧ NodeBoxIso (MapRel mapping) box targetBox
  injectiveLive : ∀ {first second target firstBox secondBox},
    MapRel mapping first target → MapRel mapping second target →
    left.get? first = some firstBox → left.get? second = some secondBox → first = second
  backward : ∀ {r box}, right.get? r = some box →
    ∃ l sourceBox, MapRel mapping l r ∧ left.get? l = some sourceBox

namespace HeapMap

theorem empty : HeapMap ({} : Store) ({} : Store) #[] := by
  constructor
  · rfl
  · intro l r related; simp [MapRel] at related
  · intro l r box related; simp [MapRel] at related
  · intro l k r box other related; simp [MapRel] at related
  · intro r box found; simp [Store.get?, IxIR1.Store.get?] at found

theorem left_total {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {location : Nat} {box : NodeBox}
    (found : left.get? location = some box) : ∃ target, MapRel mapping location target := by
  have bound := (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? found)).1
  rw [← heap.size] at bound
  exact ⟨mapping[location], Array.getElem?_eq_getElem bound⟩

theorem get {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {location : Nat} {box : NodeBox}
    (found : left.get? location = some box) :
    ∃ target targetBox, MapRel mapping location target ∧ right.get? target = some targetBox ∧
      NodeBoxIso (MapRel mapping) box targetBox := by
  obtain ⟨target, mapped⟩ := heap.left_total found
  obtain ⟨targetBox, targetAt, boxes⟩ := heap.forward mapped found
  exact ⟨target, targetBox, mapped, targetAt, boxes⟩

theorem different_images {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {first second x y : Nat} {a b : NodeBox}
    (one : MapRel mapping first x) (two : MapRel mapping second y)
    (firstAt : left.get? first = some a) (secondAt : left.get? second = some b)
    (different : first ≠ second) : x ≠ y := by
  intro same
  exact different (heap.injectiveLive one (same ▸ two) firstAt secondAt)

theorem congr {left right left' right' : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping)
    (leftNodes : left'.heap.nodes = left.heap.nodes)
    (rightNodes : right'.heap.nodes = right.heap.nodes) : HeapMap left' right' mapping := by
  have leftGet : ∀ location, left'.get? location = left.get? location := by
    intro location; simp only [Store.get?, IxIR1.Store.get?, leftNodes]
  have rightGet : ∀ location, right'.get? location = right.get? location := by
    intro location; simp only [Store.get?, IxIR1.Store.get?, rightNodes]
  exact {
    size := by simpa only [leftNodes] using heap.size
    imageBound := fun related => by simpa only [rightNodes] using heap.imageBound related
    forward := fun related found => by
      rw [leftGet] at found
      simpa only [rightGet] using heap.forward related found
    injectiveLive := fun one two firstAt secondAt => by
      rw [leftGet] at firstAt secondAt
      exact heap.injectiveLive one two firstAt secondAt
    backward := fun found => by
      rw [rightGet] at found
      simpa only [leftGet] using heap.backward found }

end HeapMap

inductive SlotIso (mapping : Array Nat) : Option NodeBox → Option NodeBox → Prop where
  | absent : SlotIso mapping none none
  | present {left right : NodeBox} (boxes : NodeBoxIso (MapRel mapping) left right) :
      SlotIso mapping (some left) (some right)

theorem SlotIso.left {mapping : Array Nat} {left right : Option NodeBox} {box : NodeBox}
    (related : SlotIso mapping left right) (found : left = some box) :
    ∃ target, right = some target ∧ NodeBoxIso (MapRel mapping) box target := by
  cases related with
  | absent => cases found
  | present boxes => cases found; exact ⟨_, rfl, boxes⟩

theorem SlotIso.right {mapping : Array Nat} {left right : Option NodeBox} {box : NodeBox}
    (related : SlotIso mapping left right) (found : right = some box) :
    ∃ source, left = some source ∧ NodeBoxIso (MapRel mapping) source box := by
  cases related with
  | absent => cases found
  | present boxes => cases found; exact ⟨_, rfl, boxes⟩

/-- Change corresponding live slots, or remove both. The history array stays
unchanged, so all saved registers keep their original correspondence. -/
theorem HeapMap.replace {left right left' right' : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {oldLeft : NodeBox}
    {newLeft newRight : Option NodeBox} (mapped : MapRel mapping l r)
    (leftAt : left.get? l = some oldLeft)
    (slots : SlotIso mapping newLeft newRight)
    (leftSize : left'.heap.nodes.size = left.heap.nodes.size)
    (rightSize : right'.heap.nodes.size = right.heap.nodes.size)
    (leftGet : ∀ location, left'.get? location =
      if location = l then newLeft else left.get? location)
    (rightGet : ∀ location, right'.get? location =
      if location = r then newRight else right.get? location) :
    HeapMap left' right' mapping := by
  have oldLive {location : Nat} {box : NodeBox} (found : left'.get? location = some box) :
      ∃ old, left.get? location = some old := by
    by_cases same : location = l
    · exact ⟨oldLeft, same ▸ leftAt⟩
    · exact ⟨box, by simpa only [leftGet, same, ↓reduceIte] using found⟩
  refine {
    size := heap.size.trans leftSize.symm
    imageBound := fun related => by rw [rightSize]; exact heap.imageBound related
    forward := ?_
    injectiveLive := ?_
    backward := ?_ }
  · intro source target box related found
    by_cases same : source = l
    · subst source
      have targetEq := related.functional mapped
      subst target
      have newAt : newLeft = some box := by simpa only [leftGet, ↓reduceIte] using found
      obtain ⟨targetBox, targetAt, boxes⟩ := slots.left newAt
      exact ⟨targetBox, by simpa only [rightGet, ↓reduceIte] using targetAt, boxes⟩
    · have oldAt : left.get? source = some box := by
        simpa only [leftGet, same, ↓reduceIte] using found
      obtain ⟨targetBox, targetAt, boxes⟩ := heap.forward related oldAt
      have different := heap.different_images related mapped oldAt leftAt same
      exact ⟨targetBox, by simpa only [rightGet, different, ↓reduceIte] using targetAt, boxes⟩
  · intro first second target a b one two firstAt secondAt
    obtain ⟨oldA, oldFirst⟩ := oldLive firstAt
    obtain ⟨oldB, oldSecond⟩ := oldLive secondAt
    exact heap.injectiveLive one two oldFirst oldSecond
  · intro target box found
    by_cases same : target = r
    · subst target
      have newAt : newRight = some box := by simpa only [rightGet, ↓reduceIte] using found
      obtain ⟨sourceBox, sourceAt, _⟩ := slots.right newAt
      exact ⟨l, sourceBox, mapped, by simpa only [leftGet, ↓reduceIte] using sourceAt⟩
    · have oldAt : right.get? target = some box := by
        simpa only [rightGet, same, ↓reduceIte] using found
      obtain ⟨source, sourceBox, related, sourceAt⟩ := heap.backward oldAt
      have different : source ≠ l := by
        intro equal
        subst source
        exact same (related.functional mapped)
      exact ⟨source, sourceBox, related,
        by simpa only [leftGet, different, ↓reduceIte] using sourceAt⟩

/-- Append a new baseline allocation and map it to either a fresh or a
reserved physical slot. Old history entries are retained, even when dead
entries already name this physical location. Live injectivity follows from
the physical slot's exclusion from the live heap before it is filled. -/
theorem HeapMap.extend {left right left' right' : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {target : Nat} {newLeft newRight : NodeBox}
    (empty : right.get? target = none)
    (boxes : NodeBoxIso (MapRel mapping) newLeft newRight)
    (leftSize : left'.heap.nodes.size = left.heap.nodes.size + 1)
    (rightSize : right.heap.nodes.size ≤ right'.heap.nodes.size)
    (targetBound : target < right'.heap.nodes.size)
    (leftGet : ∀ location, left'.get? location =
      if location = left.heap.nodes.size then some newLeft else left.get? location)
    (rightGet : ∀ location, right'.get? location =
      if location = target then some newRight else right.get? location) :
    HeapMap left' right' (mapping.push target) := by
  have oldMap {l r : Nat} (related : MapRel (mapping.push target) l r)
      (old : l ≠ mapping.size) : MapRel mapping l r := by
    simpa only [MapRel, Array.getElem?_push, old, ↓reduceIte] using related
  have freshMap {r : Nat} (related : MapRel (mapping.push target) mapping.size r) :
      r = target := (related.functional (MapRel.fresh mapping target))
  have oldLive {l : Nat} {box : NodeBox} (found : left.get? l = some box) :
      l ≠ left.heap.nodes.size :=
    Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? found)).1
  have oldImage {l r : Nat} {box : NodeBox} (mapped : MapRel mapping l r)
      (found : left.get? l = some box) : r ≠ target := by
    obtain ⟨rightBox, rightAt, _⟩ := heap.forward mapped found
    intro same
    subst r
    rw [empty] at rightAt
    cases rightAt
  have lift : ∀ {l r}, MapRel mapping l r → MapRel (mapping.push target) l r :=
    fun related => related.push target
  refine {
    size := by simp only [Array.size_push, heap.size, leftSize]
    imageBound := ?_
    forward := ?_
    injectiveLive := ?_
    backward := ?_ }
  · intro l r related
    by_cases fresh : l = mapping.size
    · subst l
      rw [freshMap related]
      exact targetBound
    · exact Nat.lt_of_lt_of_le (heap.imageBound (oldMap related fresh)) rightSize
  · intro l r box related found
    by_cases fresh : l = mapping.size
    · subst l
      have boxEq : box = newLeft := by
        simpa only [leftGet, heap.size, ↓reduceIte, Option.some.injEq] using found.symm
      subst box
      have targetEq := freshMap related
      subst r
      exact ⟨newRight, by simp only [rightGet, ↓reduceIte], boxes.mono lift⟩
    · have leftOld : l ≠ left.heap.nodes.size := by simpa only [heap.size] using fresh
      have before : left.get? l = some box := by
        simpa only [leftGet, leftOld, ↓reduceIte] using found
      have mapped := oldMap related fresh
      obtain ⟨rightBox, rightAt, boxes⟩ := heap.forward mapped before
      have different := oldImage mapped before
      exact ⟨rightBox, by simpa only [rightGet, different, ↓reduceIte] using rightAt,
        boxes.mono lift⟩
  · intro first second r a b one two firstAt secondAt
    by_cases firstFresh : first = mapping.size
    · by_cases secondFresh : second = mapping.size
      · exact firstFresh.trans secondFresh.symm
      · have oldSecond : left.get? second = some b := by
          simpa only [leftGet, ← heap.size, secondFresh, ↓reduceIte] using secondAt
        have impossible := oldImage (oldMap two secondFresh) oldSecond
        subst first
        exact False.elim (impossible (freshMap one))
    · by_cases secondFresh : second = mapping.size
      · have oldFirst : left.get? first = some a := by
          simpa only [leftGet, ← heap.size, firstFresh, ↓reduceIte] using firstAt
        have impossible := oldImage (oldMap one firstFresh) oldFirst
        subst second
        exact False.elim (impossible (freshMap two))
      · have oldFirst : left.get? first = some a := by
          simpa only [leftGet, ← heap.size, firstFresh, ↓reduceIte] using firstAt
        have oldSecond : left.get? second = some b := by
          simpa only [leftGet, ← heap.size, secondFresh, ↓reduceIte] using secondAt
        exact heap.injectiveLive (oldMap one firstFresh) (oldMap two secondFresh) oldFirst oldSecond
  · intro r box found
    by_cases fresh : r = target
    · subst r
      exact ⟨mapping.size, newLeft, MapRel.fresh mapping target,
        by simp only [leftGet, heap.size, ↓reduceIte]⟩
    · have before : right.get? r = some box := by
        simpa only [rightGet, fresh, ↓reduceIte] using found
      obtain ⟨l, leftBox, related, leftAt⟩ := heap.backward before
      exact ⟨l, leftBox, related.push target,
        by simpa only [leftGet, oldLive leftAt, ↓reduceIte] using leftAt⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
