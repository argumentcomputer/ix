import Ix.Compile.SourceContract.SemanticPresence
import Ix.CompileCert.SemanticFrames
import Ix.Cert.Canon

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

end Ix.CompileCert.SemanticPresence
