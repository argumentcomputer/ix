import IxVMRefinement.Decl.NativeNormalizationFrame
import IxVMRefinement.Decl.NativeConstructorOrigin
import IxC.Kernel.Model.Inductives.NativeJudge

/-! # Actual normalized field readings in the original checked constructor frame -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame Graded)

universe u

/-- Every returned field carries its actual normalization call on its original opener's domain. -/
theorem normFieldDoms_calls {md : Mode} {env : Env md} {fuel : Nat} {T : Key md} :
    ∀ {count depth : Nat} {e residual : Expr md} {binders : List (Expr md × BinderMeta)},
      normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (binders, residual) →
      ∃ fvars, openPisAtFvars count e depth = some (fvars, residual) ∧
        fvars.length = count ∧
        ∀ j original output, fvars[j]? = some original → binders[j]? = some output →
          normPosDom (fueledOps .verified fuel) env T (depth + j) 1024 original.fvarTypeD = .ok output.1
  | 0, _, _, _, _, run => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨[], rfl, rfl, fun j _ _ absent _ => by cases j <;> cases absent⟩
  | count + 1, depth, e, _, _, run => by
    cases e with
    | forallE dom body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨dom', normalized, rest⟩ := exceptBind_ok run
      obtain ⟨⟨tailBinders, tailResidual⟩, recursive, result⟩ := exceptBind_ok rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
      obtain ⟨fvars, opened, countEq, calls⟩ := normFieldDoms_calls recursive
      refine ⟨.fvar depth dom :: fvars, ?_, ?_, ?_⟩
      · simp only [openPisAtFvars, opened]
      · simp only [List.length_cons, countEq]
      · intro j original output originalAt outputAt
        cases j with
        | zero =>
          obtain rfl := Option.some.inj originalAt
          obtain rfl := Option.some.inj outputAt
          simpa only [Nat.add_zero, Expr.fvarTypeD] using normalized
        | succ j =>
          simpa only [Nat.add_succ, Nat.succ_add] using calls j original output originalAt outputAt
    | _ => cases run

/-- The first actual constant check constructs a readable, graded type at every valuation. -/
theorem checked_type_reading {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel : Nat} {raw checked : ConstantVal md}
    (run : checkConstantVal (fueledOps .verified fuel) env raw = .ok checked) (φ : LevelParam → Nat) :
    ∃ reading, denoteMeta model.base2.acval env φ 0 checked.type = some reading ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ reading := by
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF run
  have scope : Expr.WScoped 0 checked.type := Expr.WScoped.of_not_hasFvar closed
  have leaves := Expr.LeavesBounded.of_not_hasFvar closed
  have aligned := CtxOk.nil (m := model.base2) (φ := φ) (Expr.fvarLeaves_eq_nil_of_not_hasFvar closed)
  obtain ⟨type, header, equal⟩ := constantValCheckJ_of_run run
  obtain ⟨_, _, _, _, _, _, _, _, _, st, _, inferred, _⟩ := header
  have checkedInfer : inferTypeCore .verified env fuel 0 checked.type = .ok st := by
    simpa only [equal] using inferred
  have judge := judgeSound_runJ rfl model fuel
  obtain ⟨reading, read⟩ := judge.accepted φ checkedInfer scope bounded leaves
  obtain ⟨_, _, graded, _, _⟩ := inferRowJ judge checkedInfer scope bounded leaves aligned read
  exact ⟨reading, read, fun ρ => graded ρ (Sat_nil V ρ)⟩

/-- Actual checks and normalization produce each normalized domain's reading in the ORIGINAL
parameter/field frame. Reannotation has not yet been identified with these readings. -/
theorem normCtorVal_field_frames {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel nP nF : Nat} {T : Key md}
    {raw initial checked : ConstantVal md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (φ : LevelParam → Nat) :
    ∃ parameterVars openedResidual fieldVars fields residual context bodyReading,
      openPisAtFvars nP initial.type 0 = some (parameterVars, openedResidual) ∧
      normFieldDoms (fueledOps .verified fuel) env T nP nF openedResidual = .ok (fields, residual) ∧
      openPisAtFvars nF openedResidual nP = some (fieldVars, residual) ∧
      parameterVars.length = nP ∧ fieldVars.length = nF ∧
      Opened model.base2 φ (nP + nF) initial.type (parameterVars ++ fieldVars) residual context bodyReading ∧
      ∀ j, j < nF → ∀ original output, fieldVars[j]? = some original → fields[j]? = some output →
        ∃ reading, denoteMeta model.base2.acval env φ (nP + j) output.1 = some reading ∧
          Graded V (context.drop (nP + nF - (nP + j))) reading ∧
          ∀ ρ : Nat → V, Sat V (context.drop (nP + nF - (nP + j))) ρ →
            interp V ρ (context.getD (nP + nF - 1 - (nP + j)) default) = interp V ρ reading := by
  obtain ⟨_, _, parameterVars, openedResidual, fields, residual, fieldVars,
      _, opened, fieldsRun, fieldsOpen, parameterCount, fieldCount, _, _, _⟩ :=
    normCtorVal_origin model.base2.wf first normalized
  obtain ⟨callVars, callOpen, _, calls⟩ := normFieldDoms_calls fieldsRun
  have sameVars : callVars = fieldVars := congrArg Prod.fst (Option.some.inj (callOpen.symm.trans fieldsOpen))
  rw [sameVars] at calls
  have wholeOpen : openPisAtFvars (nP + nF) initial.type 0 = some (parameterVars ++ fieldVars, residual) :=
    openPisAtFvars_add nP opened (by rw [Nat.zero_add]; exact fieldsOpen)
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF first
  obtain ⟨reading, read, graded⟩ := checked_type_reading model first φ
  obtain ⟨context, bodyReading, _, oldFrame⟩ := opened_of wholeOpen closed bounded read graded
  refine ⟨parameterVars, openedResidual, fieldVars, fields, residual, context, bodyReading,
    opened, fieldsRun, fieldsOpen, parameterCount, fieldCount, oldFrame, ?_⟩
  intro j inFields original output originalAt outputAt
  have wholeAt : (parameterVars ++ fieldVars)[nP + j]? = some original := by
    rw [List.getElem?_append_right (by omega), parameterCount, Nat.add_sub_cancel_left]
    exact originalAt
  have variable := oldFrame.var (nP + j) original wholeAt
  have inputFrame : Frame (nP + j) original.fvarTypeD :=
    ⟨variable.2.1, variable.2.2.1, variable.2.2.2.1⟩
  have aligned := oldFrame.ctx (by omega) variable.2.1 variable.2.2.2.2
  exact normPosDom_semantics model (calls j original output originalAt outputAt) inputFrame aligned
    (oldFrame.doms (nP + j) original wholeAt) (oldFrame.okΓ (nP + j) (by omega))

end IxVM.Refinement.Decl
