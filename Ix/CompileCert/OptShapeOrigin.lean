import Ix.CompileCert.OptDispatchOrigin

/-! # The actual shape insertion's source, image and recognizer calls

The repaired ExactName map identifies the actual loop key structurally.
Skipped attempts preserve existing origins; overwrites carry their own
successful calls. No source-fidelity or current-view-build law is assumed.
-/

namespace Ix.CompileCert.OptShapeOrigin

open Ix (Name RecursorVal)
open Ix.Compile.Pass Ix.Compile.Pass.Opt
open Ix.Compile.ExactKey (ExactName)

/-- Calls from this exact input/view and the actual traversal. -/
def ShapeOrigin (inp : ViewInput) (view : BlockView) (r : Name) (s : RecShape) : Prop :=
  r ∈ (imageKinds inp.const? view.all).toList ∧
  ∃ (rv : RecursorVal) (img : Ix.Compile.Image.Image),
    inp.const? r = some (.recInfo rv) ∧ view.image inp r = .ok img ∧
    readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (ImageShape.viewRecInfo view) = some s ∧
    s.leanRec = r ∧ s.levelParams = img.levelParams

def Origins (inp : ViewInput) (view : BlockView) (table : Std.HashMap ExactName RecShape) : Prop :=
  ∀ (r : ExactName) s, table.get? r = some s → ShapeOrigin inp view r s

/-- ExactName identifies an overwritten key; every other hit keeps its origin. -/
theorem Origins.insert {inp : ViewInput} {view : BlockView} {table : Std.HashMap ExactName RecShape}
    (held : Origins inp view table) {r : ExactName} {s : RecShape} (origin : ShapeOrigin inp view r s) :
    Origins inp view (table.insert r s) := by
  intro q t hit
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hit
  split at hit
  · rename_i same
    have eq : r = q := eq_of_beq same
    subst q
    cases hit
    exact origin
  · rw [← Std.HashMap.get?_eq_getElem?] at hit
    exact held q t hit

/-- The ACTUAL insertion loop establishes every hit's own successful calls. -/
theorem optBlockOf_origins (inp : ViewInput) (view : BlockView) :
    Origins inp view (optBlockOf inp view).shapes := by
  unfold optBlockOf
  simp only [Id.run, Loop.idBind, Loop.idPure]
  rw [Loop.forIn_id_array _ (by
    intro r table
    repeat' first | rfl | split)]
  rw [← Array.foldl_toList]
  apply List.foldlRecOn
  · intro r s impossible
    simp at impossible
  · intro table held r member
    split <;> try exact held
    next rv source =>
      split <;> try exact held
      next img generated =>
        split <;> try exact held
        next s recognized =>
          apply Origins.insert held
          have result := ImageShape.readShape_result recognized
          exact ⟨member, rv, img, source, generated, recognized, result.1, result.2.1⟩

/-- Only the real shape hit is an input. In particular the source/image/
recognizer calls and exact leanRec/levelParams are not caller premises. -/
theorem optBlockOf_shape_origin {inp : ViewInput} {view : BlockView} {r : Name} {s : RecShape}
    (hit : (optBlockOf inp view).shapes.get? r = some s) : ShapeOrigin inp view r s :=
  optBlockOf_origins inp view r s hit

end Ix.CompileCert.OptShapeOrigin
