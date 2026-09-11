import Ix.Compiler.IxIR2.CallReuseOrder

/-!
# Runtime constructor shapes from baseline allocation

Reference-count changes and destruction preserve every surviving node's
world and payload. Constructor allocation obtains its payload length from
the evaluator's successful field check.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (RValsIso)

structure NodeProperty (property : Owned → Node → Prop) (store : Store) : Prop where
  holds : ∀ {location box}, store.get? location = some box → property box.world box.node

namespace NodeProperty

theorem empty (property : Owned → Node → Prop) : NodeProperty property ({} : Store) := by
  constructor
  intro location box found
  simp [Store.get?, IxIR1.Store.get?] at found

theorem congr {property : Owned → Node → Prop} {left right : Store}
    (valid : NodeProperty property left) (nodes : right.heap.nodes = left.heap.nodes) :
    NodeProperty property right := by
  constructor
  intro location box found
  exact valid.holds (by simpa only [Store.get?, IxIR1.Store.get?, nodes] using found)

theorem rcTick {property : Owned → Node → Prop} {store : Store}
    (valid : NodeProperty property store) : NodeProperty property store.rcTick := ⟨valid.holds⟩

theorem setRc {property : Owned → Node → Prop} {store : Store} {location rc : Nat}
    {box : NodeBox} (valid : NodeProperty property store) (found : store.get? location = some box) :
    NodeProperty property (store.setBox location { box with rc }) := by
  constructor
  intro other otherBox after
  by_cases same : location = other
  · subst other
    have updated := IxIR1.Sim.get?_setBox_same (new := { box with rc }) found
    have equal : otherBox = { box with rc } := Option.some.inj (after.symm.trans updated)
    subst otherBox
    exact valid.holds (box := box) found
  · exact valid.holds (IxIR1.Sim.get?_of_setBox_other same found after)

theorem kill {property : Owned → Node → Prop} {store : Store} {location : Nat} {box : NodeBox}
    (valid : NodeProperty property store) (found : store.get? location = some box) :
    NodeProperty property (store.kill location) := by
  constructor
  intro other otherBox after
  by_cases same : location = other
  · subst other
    have missing := IxIR1.Sim.get?_kill_same found
    change (store.heap.kill location).get? location = some otherBox at after
    rw [missing] at after
    cases after
  · exact valid.holds (IxIR1.Sim.get?_of_kill_other same found after)

theorem alloc {property : Owned → Node → Prop} {store : Store} {world : Owned} {node : Node}
    (valid : NodeProperty property store) (new : property world node) :
    NodeProperty property (store.allocNode world node).1 := by
  constructor
  intro location box found
  by_cases fresh : location = store.heap.nodes.size
  · subst location
    have atNew := IxIR1.Sim.HeapIso.get?_allocNode_new store.heap world node
    have same : box = ⟨world, 1, node⟩ := Option.some.inj (found.symm.trans atNew)
    subst box
    exact new
  · exact valid.holds (IxIR1.Sim.HeapIso.get?_of_allocNode_old fresh found)

theorem retain {property : Owned → Node → Prop} {store output : Store} {value : RVal}
    (valid : NodeProperty property store) (run : retainShared store value = .ok output) :
    NodeProperty property output := by
  cases value with
  | lit => cases run; exact valid
  | erased => cases run; exact valid
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp only [retainShared, found, shared, bne_self_eq_false, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at run
            subst output
            simpa only [shared] using (valid.setRc (rc := box.rc + 1) found).rcTick
          · simp [retainShared, found, shared] at run

theorem retainMany {property : Owned → Node → Prop} {store output : Store} {values : Array RVal}
    (valid : NodeProperty property store) (run : RetainSharedMany store values output) :
    NodeProperty property output := by
  have loop : ∀ (values : List RVal) {store output : Store}, NodeProperty property store →
      values.foldlM retainShared store = .ok output → NodeProperty property output := by
    intro values
    induction values with
    | nil => intro store output valid run; cases run; exact valid
    | cons head tail ih =>
        intro store output valid run
        rw [List.foldlM_cons] at run
        cases first : retainShared store head with
        | error error => simp [first, bind, Except.bind] at run
        | ok middle =>
            simp only [first, bind, Except.bind] at run
            exact ih (valid.retain first) run
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  exact loop values.toList valid run

theorem releaseWork {property : Owned → Node → Prop} {fuel remaining : Nat}
    {store output : Store} {values : List RVal} (valid : NodeProperty property store)
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    NodeProperty property output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact valid
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact valid
      | cons value rest =>
          cases value with
          | lit => exact ih valid run
          | erased => exact ih valid run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true] at run
                        exact ih (valid.rcTick.kill found) run
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        exact ih (valid.rcTick.setRc (rc := box.rc - 1) found)
                          (by simpa only [shared] using run)
                  · simp [releaseSharedWork, found, shared] at run

theorem dropWork {property : Owned → Node → Prop} {fuel remaining : Nat}
    {store output : Store} {values : List RVal} (valid : NodeProperty property store)
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    NodeProperty property output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact valid
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact valid
      | cons value rest =>
          cases value with
          | lit => exact ih valid run
          | erased => exact ih valid run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN address arity arguments => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        exact ih (valid.kill found) run
                  · simp [dropUniqueWork, found, unique] at run

end NodeProperty

def ShapedNode (context : Context) (world : Owned) : Node → Prop
  | .ctorN cid fields => ∃ schema, context.schemas world cid = some schema ∧
      fields.size = schema.fields.size
  | .papN .. => True

abbrev Shaped (context : Context) (store : Store) : Prop :=
  NodeProperty (ShapedNode context) store

theorem Shaped.fields {context : Context} {store : Store} {location : Nat}
    {box : NodeBox} {world : Owned} {cid : CtorId} {fields : Array RVal} {schema : CtorSchema}
    (shaped : Shaped context store) (view : ConstructorView store location world cid box fields)
    (schemaAt : context.schemas world cid = some schema) : fields.size = schema.fields.size := by
  obtain ⟨found, boxWorld, node⟩ := view.parts
  have shape := shaped.holds found
  rw [boxWorld, node] at shape
  obtain ⟨actualSchema, actualAt, sizes⟩ := shape
  have equal := Option.some.inj (actualAt.symm.trans schemaAt)
  subst actualSchema
  exact sizes

theorem HeapMap.fieldWorlds {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {leftValues rightValues : Array RVal} {schema : CtorSchema}
    (related : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (checked : FieldWorlds left schema leftValues) : FieldWorlds right schema rightValues := by
  have forward : ∀ {lefts rights : List RVal}, RValsIso (MapRel mapping) lefts rights →
      FieldValuesWorldForward left right lefts rights := by
    intro lefts rights related
    induction related with
    | nil => exact .nil
    | cons head tail ih => exact .cons (fun _ valid => heap.hasWorld head valid) ih
  exact checked.forward (forward related)

end Ix.Compiler.IxIR2.CallReuse.Sim
