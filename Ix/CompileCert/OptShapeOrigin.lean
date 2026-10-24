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

open Ix (Expr ConstantInfo)
open Ix.CompileM OptDispatchOrigin

/-- One common O6 witness tuple, enriched with its OWN actual image calls.
Neither a fresh buildView nor occurrence-universe/source/reader fidelity is asserted. -/
def O6Images (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (sourceAll : Ix.Set Name) (o : Occ) (out : Expr) : Prop :=
  O6.apply (driverEnv cenv views sourceAll) o = some out ∧
  ∃ (k : AuxKind) (r key : Name) (view : BlockView) (block : OptBlock) (s : RecShape)
    (count : Nat) (levels : Array Ix.Level) (rv : RecursorVal) (img : Ix.Compile.Image.Image),
    classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧
    cenv.p3Heads.get? o.head = some key ∧ views.get? key = some view ∧
    (optBlocks cenv views).get? key = some block ∧ block = optBlockOf (viewInput cenv) view ∧
    (driverEnv cenv views sourceAll).blockOf o.head = some block ∧ block.shapes.get? r = some s ∧
    s.isSelection = true ∧ standardTelescope (driverEnv cenv views sourceAll) s k o.head = some count ∧
    count ≤ o.args.size ∧ O5.levels s o.us = some levels ∧
    r ∈ (imageKinds (viewInput cenv).const? view.all).toList ∧
    (viewInput cenv).const? r = some (.recInfo rv) ∧ view.image (viewInput cenv) r = .ok img ∧
    readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors rv.numIndices
      img.value (ImageShape.viewRecInfo view) = some s ∧
    s.leanRec = r ∧ s.levelParams = img.levelParams

/-- The actual computed-block equation identifies the insertion producer.
Every returned rv/img belongs to the SAME view/r/s as the existing O6 calls. -/
theorem o6_calls_images {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {o : Occ} {out : Expr} (calls : O6Calls cenv views sourceAll o out) :
    O6Images cenv views sourceAll o out := by
  obtain ⟨pass, k, r, key, view, block, s, count, levels, kind, kinds, owner, storedView,
      storedBlock, blockEq, blockHit, shapeHit, selection, telescope, enough, levelRun⟩ := calls
  have inserted : (optBlockOf (viewInput cenv) view).shapes.get? r = some s := by
    simpa only [blockEq] using shapeHit
  obtain ⟨member, rv, img, source, generated, recognized, name, params⟩ := optBlockOf_shape_origin inserted
  exact ⟨pass, k, r, key, view, block, s, count, levels, rv, img, kind, kinds, owner,
    storedView, storedBlock, blockEq, blockHit, shapeHit, selection, telescope, enough,
    levelRun, member, source, generated, recognized, name, params⟩

/-- Forgetting only the added image facts recovers the original calls. -/
theorem O6Images.calls {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {o : Occ} {out : Expr} (images : O6Images cenv views sourceAll o out) :
    O6Calls cenv views sourceAll o out := by
  obtain ⟨pass, k, r, key, view, block, s, count, levels, _, _, kind, kinds, owner, storedView,
      storedBlock, blockEq, blockHit, shapeHit, selection, telescope, enough, levelRun, _⟩ := images
  exact ⟨pass, k, r, key, view, block, s, count, levels, kind, kinds, owner, storedView,
    storedBlock, blockEq, blockHit, shapeHit, selection, telescope, enough, levelRun⟩

/-- Only the ACTUAL hook success is supplied. Its recovered O6 branch now
produces the real source/image/recognizer calls; every Branch remains explicit. -/
theorem passConfig_with_images {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {site : Option Name} {n : Name} {us : Array Ix.Level} {args : Array Expr}
    {out : Expr} {constants : Array ConstantInfo} {proofTag : Option String} {reports : Array String}
    (hit : (passConfig cenv views sourceAll).opt? site n us args = some (out, constants, proofTag, reports)) :
    Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env n = true ∧ constants = #[] ∧ proofTag = none ∧
    ∃ tag, engine (driverEnv cenv views sourceAll) { head := n, us, args, site } = some (tag, out, reports) ∧
      Branch 63 (driverEnv cenv views sourceAll) { head := n, us, args, site } tag out reports ∧
      (tag = "O6" → O6Images cenv views sourceAll { head := n, us, args, site } out) := by
  obtain ⟨permitted, empty, noProof, tag, ran, branch, origin⟩ := passConfig_with_o6_origin hit
  exact ⟨permitted, empty, noProof, tag, ran, branch, fun selected => o6_calls_images (origin selected)⟩

end Ix.CompileCert.OptShapeOrigin
