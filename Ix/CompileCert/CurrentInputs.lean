import Ix.CompileCert.RewriteCalls
import Ix.CompileCert.SemanticPresence
import Ix.Compile.Pass.Driver

open private Ix.CompileCert.DevelopmentFrames.instantiateWith_run from Ix.CompileCert.DevelopmentFrames
open private Traced pureT bindT getT readT modifyT withReaderT arrayForInT from Ix.CompileCert.RewriteCalls

/-! Actual current-input receipts and wrapper cache safety. A selected current
declaration's validity remains conditional on its actual writer proof. -/
namespace Ix.CompileCert.CurrentInputs
open Ix (Name Expr ConstantInfo)
open Ix.CompileM Ix.Compile.Pass Ix.Compile.Image
open Ix.Compile.ExactKey (ExactName)
open SemanticFrames SemanticPresence DevelopmentFrames RewriteCalls

theorem instantiateWith_frames (f : Expr) (args : Array Expr)
    {before after : DevState} {out : Expr} (good : InstFrames before)
    (hf : Frames f) (ha : ∀ a ∈ args, Frames a)
    (run : instantiateWith before f args = .ok (out, after)) : Frames out ∧ InstFrames after :=
  (Ix.CompileCert.DevelopmentFrames.instantiateWith_run f args hf ha good run).symm

theorem rewriteConstM_state (expansion? : Name → Except String (Option Expansion))
    (ci : ConstantInfo) (cfg : RwConfig) (before after : RwState) (out : ConstantInfo × Bool)
    (good : InstFrames before.dev)
    (run : ((rewriteConstM expansion? ci) cfg).run before = .ok (out, after)) : InstFrames after.dev := by
  have go : ∀ record e, Traced (Ix.Compile.Pass.rw expansion? rewriteFuel record e) :=
    fun record e cfg before out after run => rw_calls expansion? rewriteFuel record e cfg before after out run
  have traced : Traced (rewriteConstM expansion? ci) := by
    unfold rewriteConstM
    cases ci <;> dsimp only
    all_goals with_reducible repeat' first
      | exact pureT _
      | exact getT
      | exact readT
      | exact go _ _
      | apply modifyT; intro state; rfl
      | apply withReaderT
      | apply arrayForInT; intro value member acc
      | refine bindT ?_ (fun _ => ?_)
      | split
  obtain ⟨_, chain⟩ := traced cfg before out after run
  exact chain.preserves good

/-- The three actual suppliers of imageDecl's value, retaining their states. -/
inductive ImageValue (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (name : Name) (x : Expansion) (before : RwState) : Expr → RwState → Prop where
  | cached (entry : Expansion) (hit : before.exps.get? name = some entry) :
      ImageValue cenv views name x before entry.value before
  | original (miss : before.exps.get? name = none) (plain : x.needsRewrite = false) :
      ImageValue cenv views name x before x.value before
  | rewritten {value : Expr} {middle : RwState} (changed : Bool)
      (miss : before.exps.get? name = none) (needed : x.needsRewrite = true)
      (actual : ((Ix.Compile.Pass.rw (expansionLookup cenv views) rewriteFuel false x.value) {}).run before =
        .ok ((value, changed), middle)) : ImageValue cenv views name x before value middle

def ImageDeclReceipt (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (name : Name) (x : Expansion) (ty : Expr) (before : RwState)
    (dv : Ix.DefinitionVal) (after : RwState) : Prop :=
  ∃ middle changed, ImageValue cenv views name x before dv.value middle ∧
    ((Ix.Compile.Pass.rw (expansionLookup cenv views) rewriteFuel false ty) {}).run middle =
      .ok ((dv.cnst.type, changed), after) ∧ dv.cnst.name = name ∧ dv.cnst.levelParams = x.levelParams

theorem imageDecl_receipt (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (name : Name) (x : Expansion) (ty : Expr) (before : RwState)
    {dv : Ix.DefinitionVal} {after : RwState}
    (run : imageDecl cenv views name x ty before = .ok (dv, after)) :
    ImageDeclReceipt cenv views name x ty before dv after := by
  unfold imageDecl at run
  obtain ⟨⟨⟨value, type⟩, final⟩, rewritten, returned⟩ := Loop.except_bind_ok.mp run
  cases Except.ok.inj returned
  rw [← bind_pure_comp] at rewritten
  simp only [bind_assoc, pure_bind] at rewritten
  dsimp only [ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, pure, ReaderT.pure, StateT.pure, Except.pure,
    _root_.liftM, monadLift, MonadLift.monadLift, StateT.lift, Except.bind] at rewritten
  cases hit : before.exps.get? name with
  | some entry =>
    simp only [hit] at rewritten
    obtain ⟨⟨⟨type', changed⟩, after⟩, actual, same⟩ := Loop.except_bind_ok.mp rewritten
    cases Except.ok.inj same
    exact ⟨before, changed, .cached entry hit, actual, rfl, rfl⟩
  | none =>
    simp only [hit] at rewritten
    cases needed : x.needsRewrite with
    | false =>
      simp only [needed, Bool.false_eq_true, ↓reduceIte] at rewritten
      obtain ⟨⟨⟨type', changed⟩, after⟩, actual, same⟩ := Loop.except_bind_ok.mp rewritten
      cases Except.ok.inj same
      exact ⟨before, changed, .original hit needed, actual, rfl, rfl⟩
    | true =>
      simp only [needed, ↓reduceIte] at rewritten
      obtain ⟨⟨⟨value', valueChanged⟩, middle⟩, valueRun, rest⟩ := Loop.except_bind_ok.mp rewritten
      obtain ⟨⟨⟨type', changed⟩, after⟩, typeRun, same⟩ := Loop.except_bind_ok.mp rest
      cases Except.ok.inj same
      exact ⟨middle, changed, .rewritten valueChanged hit needed valueRun, typeRun, rfl, rfl⟩

private theorem ImageValue.state {cenv views name x before value middle}
    (origin : ImageValue cenv views name x before value middle) (good : InstFrames before.dev) :
    InstFrames middle.dev := by
  cases origin with
  | cached => exact good
  | original => exact good
  | rewritten changed miss needed actual => exact rw_state _ _ _ _ _ _ _ _ good actual

theorem imageDecl_state (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (name : Name) (x : Expansion) (ty : Expr) (before : RwState)
    {dv : Ix.DefinitionVal} {after : RwState} (good : InstFrames before.dev)
    (run : imageDecl cenv views name x ty before = .ok (dv, after)) : InstFrames after.dev := by
  obtain ⟨middle, changed, origin, typeRun, _, _⟩ := imageDecl_receipt cenv views name x ty before run
  exact rw_state _ _ _ _ _ _ _ _ (origin.state good) typeRun

theorem expansion_defn_current (cenv : CompileEnv) (view : BlockView) (name : Name)
    (d : Ix.DefinitionVal) (x : Expansion) (ty : Expr)
    (selected : cenv.env.get? name = some (.defnInfo d))
    (run : view.expansion (viewInput cenv) name = .ok (x, ty)) :
    x = { levelParams := d.cnst.levelParams, value := d.value, arity := lamArity d.value, needsRewrite := true } ∧
    ty = d.cnst.type := by
  simp only [BlockView.expansion, ViewInput.const?, viewInput, selected, pure, Except.pure] at run
  cases Except.ok.inj run; exact ⟨rfl, rfl⟩

theorem expansion_thm_current (cenv : CompileEnv) (view : BlockView) (name : Name)
    (d : Ix.TheoremVal) (x : Expansion) (ty : Expr)
    (selected : cenv.env.get? name = some (.thmInfo d))
    (run : view.expansion (viewInput cenv) name = .ok (x, ty)) :
    x = { levelParams := d.cnst.levelParams, value := d.value, arity := lamArity d.value, needsRewrite := true } ∧
    ty = d.cnst.type := by
  simp only [BlockView.expansion, ViewInput.const?, viewInput, selected, pure, Except.pure] at run
  cases Except.ok.inj run; exact ⟨rfl, rfl⟩

/-- The selected CURRENT declaration's validity is explicit, not inferred
from the original-source guard or from exact cache keys. -/
theorem expansion_defn_frames (cenv : CompileEnv) (view : BlockView) (name : Name)
    (d : Ix.DefinitionVal) (x : Expansion) (ty : Expr)
    (selected : cenv.env.get? name = some (.defnInfo d))
    (run : view.expansion (viewInput cenv) name = .ok (x, ty)) (valid : ConstFrames (.defnInfo d)) :
    Frames x.value ∧ Frames ty := by
  obtain ⟨rfl, rfl⟩ := expansion_defn_current cenv view name d x ty selected run
  exact ⟨valid.2, valid.1⟩

theorem expansion_thm_frames (cenv : CompileEnv) (view : BlockView) (name : Name)
    (d : Ix.TheoremVal) (x : Expansion) (ty : Expr)
    (selected : cenv.env.get? name = some (.thmInfo d))
    (run : view.expansion (viewInput cenv) name = .ok (x, ty)) (valid : ConstFrames (.thmInfo d)) :
    Frames x.value ∧ Frames ty := by
  obtain ⟨rfl, rfl⟩ := expansion_thm_current cenv view name d x ty selected run
  exact ⟨valid.2, valid.1⟩

end Ix.CompileCert.CurrentInputs
