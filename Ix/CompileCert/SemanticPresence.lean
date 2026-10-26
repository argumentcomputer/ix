import Ix.Compile.SourceContract.SemanticPresence
import Ix.CompileCert.SemanticFrames
import Ix.Cert.Canon
import Ix.CompileDriver

namespace Ix.CompileCert.SemanticPresence
open Ix.Compile.SemanticPresence (spec)
open Ix.Cert.Canon
open SemanticFrames

theorem metadata_absent (data : Lean.MData)
    (absent : (!(Ix.SemanticContract.leanFields data).isEmpty) = false) :
    Ix.SemanticContract.hasMetadata (mdataS data) = false := by
  rw [hasMetadata_mdataS]
  simpa [hasContractLean, Ix.SemanticContract.leanFields, List.isEmpty_iff] using absent

/-- Absence in the structural source specification supplies actual canonical
frame validity. The production presence equation is a separate obligation. -/
theorem spec_false_canonical (e : Lean.Expr) (absent : spec e = false) : Frames (exprS e) := by
  induction e
  all_goals simp only [spec, Bool.or_eq_false_iff] at absent
  case mdata data inner ih =>
    change (Ix.SemanticContract.hasMetadata (mdataS data) = true → _) ∧ _
    refine ⟨?_, ih absent.2⟩
    intro present
    rw [metadata_absent data absent.1] at present
    cases present
  all_goals try cases ‹Lean.Literal›
  all_goals simp_all only [exprS, Frames, Ix.Expr.mkBVar, Ix.Expr.mkFVar, Ix.Expr.mkMVar,
    Ix.Expr.mkSort, Ix.Expr.mkConst, Ix.Expr.mkApp, Ix.Expr.mkLam, Ix.Expr.mkForallE,
    Ix.Expr.mkLetE, Ix.Expr.mkLit, Ix.Expr.mkProj, Id.run, idBind, true_and]

theorem production_absent (e : Lean.Expr) (absent : Ix.Compile.exprHasSemanticContracts e = false) :
    Frames (exprS e) := spec_false_canonical e (by
  simpa only [Ix.Compile.exprHasSemanticContracts, Ix.Compile.SemanticPresence.run_eq_spec] using absent)

def ConstFrames (ci : Ix.ConstantInfo) : Prop := Frames ci.getCnst.type ∧ match ci with
  | .defnInfo v => Frames v.value
  | .thmInfo v => Frames v.value
  | .opaqueInfo v => Frames v.value
  | .recInfo v => ∀ rule ∈ v.rules, Frames rule.rhs
  | _ => True

theorem source_absent (source : Lean.ConstantInfo)
    (absent : Ix.Compile.sourceHasSemanticContracts source = false) : ConstFrames (constS source) := by
  cases source <;> simp [Ix.Compile.sourceHasSemanticContracts, Ix.Compile.sourceBody?] at absent
  all_goals simp only [ConstFrames, constS, constValS, Ix.ConstantInfo.getCnst, and_true]
  case recInfo info =>
    refine ⟨production_absent _ absent.1, ?_⟩
    simpa using (fun (rule : Lean.RecursorRule) (member : rule ∈ info.rules) =>
      production_absent rule.rhs (absent.2 rule member))
  all_goals first
    | exact production_absent _ absent
    | exact ⟨production_absent _ absent.1, production_absent _ absent.2⟩

theorem guard_frames (source : Lean.ConstantInfo)
    (accepted : Ix.CompileM.inspectSemanticSource source = .ok ()) : ConstFrames (constS source) := by
  cases present : Ix.Compile.sourceHasSemanticContracts source with
  | false => exact source_absent source present
  | true =>
    unfold Ix.CompileM.inspectSemanticSource at accepted
    simp only [present, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
    rcases compiled : (Ix.CanonM.canonConst source).run {} with ⟨canonical, state⟩
    have correct : canonical = constS source := by
      simpa only [compiled, Id.run] using canonConst_run source {}
    simp only [compiled, correct] at accepted
    cases source <;> simp only [constS, constValS, Ix.ConstantInfo.getCnst, ConstFrames] at accepted ⊢
    all_goals obtain ⟨_, typeRun, rest⟩ := Loop.except_bind_ok.mp accepted
    all_goals have typeGood := (inspect_frames_iff _).mp ⟨_, typeRun⟩
    case quotInfo | inductInfo | ctorInfo | recInfo =>
      simp only [throw, throwThe, MonadExceptOf.throw] at rest
      cases rest
    all_goals first
      | exact ⟨typeGood, True.intro⟩
      | (obtain ⟨_, valueRun, _⟩ := Loop.except_bind_ok.mp rest
         exact ⟨typeGood, (inspect_frames_iff _).mp ⟨_, valueRun⟩⟩)

/-- An actual returned preparation member and its actual source-guard run;
frame validity is a conclusion, never a receipt field. -/
structure PreparedMember (input : Ix.Compile.CompileInput) (name : Lean.Name)
    (source : Lean.ConstantInfo) where
  sources : List (Lean.Name × Lean.ConstantInfo)
  prepared : input.prepare = .ok sources
  member : (name, source) ∈ sources
  accepted : Ix.CompileM.inspectSemanticSource source = .ok ()

theorem prepared_member_frames {input : Ix.Compile.CompileInput} {name : Lean.Name}
    {source : Lean.ConstantInfo} (receipt : PreparedMember input name source)
    (cache : Ix.CanonM.CanonState) :
    ConstFrames (Id.run ((Ix.CanonM.canonConst source).run cache)).1 := by
  rw [canonConst_run]
  exact guard_frames source receipt.accepted

end Ix.CompileCert.SemanticPresence
