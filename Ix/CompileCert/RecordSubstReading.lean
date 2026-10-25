import Ix.CompileCert.RecordSubst
import Ix.CompileCert.RecordRead

/-! Conditional expression-reader equivalence for the actual record walk.
Actual rewrite outputs still need their own ContractArity producer. -/
namespace Ix.CompileCert.RecordSubst
open Ix (Expr)
open Ix.CompileM Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.CompileCert.RecordSourceShape
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

theorem Frames.symm {e e' : Expr} (h : Frames e e') : Frames e' e := by
  induction h with
  | refl => exact .refl _
  | app _ _ ihf iha => exact .app ihf iha
  | lam n bi _ _ iht ihb => exact .lam n bi iht ihb
  | all n bi _ _ iht ihb => exact .all n bi iht ihb
  | letE n nd _ _ _ iht ihv ihb => exact .letE n nd iht ihv ihb
  | proj n i _ ih => exact .proj n i ih
  | mdata data _ ih => exact .mdata data ih
  | plain data data' plain plain' _ ih => exact .plain data' data plain' plain ih

private theorem lower {md : Ix.Kernel.Mode} {e e' : Expr} (h : Frames e e')
    (c : Ix.SemanticContract.Contract) (target : CExpr md) :
    withContract c e target = withContract c e' target := by
  cases c with
  | mk kind binder result letKind =>
    cases h <;> cases kind <;> try rfl
    all_goals cases target <;> rfl

theorem Frames.related_forward {md : Ix.Kernel.Mode} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} {e e' : Expr} (h : Frames e e') :
    ∀ {target}, Related names levels e target → Related names levels e' target := by
  induction h with
  | refl => intro target related; exact related
  | app _ _ ihf iha =>
    intro target related
    cases related with | app _ hf ha => exact .app _ (ihf hf) (iha ha)
  | lam n bi _ _ iht ihb =>
    intro target related
    cases related with | lam _ _ _ ht hb => exact .lam n bi _ (iht ht) (ihb hb)
  | all n bi _ _ iht ihb =>
    intro target related
    cases related with | all _ _ _ ht hb => exact .all n bi _ (iht ht) (ihb hb)
  | letE n nd _ _ _ iht ihv ihb =>
    intro target related
    cases related with | letE _ _ _ ht hv hb => exact .letE n nd _ (iht ht) (ihv hv) (ihb hb)
  | proj n i _ ih =>
    intro target related
    cases related with | proj _ _ mapped body => exact .proj i _ mapped (ih body)
  | mdata data child ih =>
    intro target related
    cases related with
    | mdata _ _ plain body => exact .mdata data _ plain (ih body)
    | contract _ _ c frame read body applied =>
      exact .contract data _ c frame read (ih body) (by rw [← lower child c _]; exact applied)
  | plain data data' plain plain' child ih =>
    intro target related
    cases related with
    | mdata _ _ _ body => exact .mdata data' _ plain' (ih body)
    | contract _ _ _ frame _ _ _ => rw [plain] at frame; contradiction

theorem Frames.related_iff {md : Ix.Kernel.Mode} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} {e e' : Expr} (h : Frames e e') (target) :
    Related names levels e' target ↔ Related names levels e target :=
  ⟨h.symm.related_forward, h.related_forward⟩

/-- Both directions for the SAME arity-guarded input and actual empty memo.
No metadata-slot faithfulness or whole-state/byte equality is asserted. -/
theorem substRecords_related {md : Ix.Kernel.Mode} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Ix.Kernel.Level → Prop} (records : Std.HashMap Nat (Nat × UInt64))
    (e : Expr) (arity : ContractArity e) (target) :
    Related names levels (substRecords records e) target ↔ Related names levels e target :=
  ((produced records e).2 arity).related_iff target

/-- Keep the actual record/subrun/final-reader witness, now related to its
input expression. Arity for a live rewritten input remains a producer obligation. -/
theorem withRecords_read {md : Ix.Kernel.Mode} (cx : Ctx md) (param : Nat → Ix.Kernel.LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → Ix.Kernel.LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ a, cx.blob a = context.1.blobs.get? a)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (e : Expr) (arity : ContractArity e) (before : BlockState)
    (good : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprWithRecords e) context before = (.ok value, after)) :
    ∃ lowered middle target, RecordRead.RecordInput e context before lowered middle ∧
      rawRun (compileExprNoSurgery lowered) context middle = (.ok value, after) ∧
      Related names (LevelMeaning context.2.univCtx σ param) e target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target := by
  obtain ⟨lowered, middle, target, input, ordinary, rel, read⟩ :=
    RecordRead.withRecords_read cx param self names σ bindings context aligned external selfSound e before good ran
  have original : Related names (LevelMeaning context.2.univCtx σ param) e target := by
    cases input with
    | plain => exact rel
    | recorded _ records _ _ _ => exact (substRecords_related records e arity target).mp rel
  exact ⟨lowered, middle, target, input, ordinary, original, read⟩

end Ix.CompileCert.RecordSubst
