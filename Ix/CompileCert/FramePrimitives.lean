import Ix.CompileCert.SemanticFrames
import Ix.CompileCert.RewriteArityPrimitives
import Batteries.Tactic.OpenPrivate

open private Ix.Compile.Image.abstractFVars.go from Ix.Compile.Image.Expr

/-! Actual rewrite primitives preserve decoded semantic-frame placement.
This is not resource typing or value preservation. -/
namespace Ix.CompileCert.FramePrimitives
open Ix (Expr Name Level)
open Ix.Compile.Image Ix.Compile.Canon
open SemanticFrames

theorem shell_refl (e : Expr) : Shell e e := by cases e <;> simp [Shell]

theorem fits_liftP (kind : Ix.SemanticContract.Kind) (e : Expr) (n cutoff : Nat) :
    fits kind (TotalSpec.liftP e n cutoff) = fits kind e := by
  cases kind <;> cases e
  all_goals rw [TotalSpec.liftP]
  all_goals split
  all_goals try rfl
  all_goals split
  all_goals try rfl
  all_goals try split
  all_goals rfl

theorem fits_lowerP (kind : Ix.SemanticContract.Kind) (e : Expr) (n cutoff : Nat) :
    fits kind (TotalSpec.lowerP e n cutoff) = fits kind e := by
  cases kind <;> cases e
  all_goals rw [TotalSpec.lowerP]
  all_goals split
  all_goals try rfl
  all_goals split
  all_goals try rfl
  all_goals try split
  all_goals rfl

theorem liftP (e : Expr) (n cutoff : Nat) (valid : Frames e) :
    Frames (TotalSpec.liftP e n cutoff) ∧ Shell e (TotalSpec.liftP e n cutoff) := by
  induction e generalizing cutoff
  all_goals rw [TotalSpec.liftP]
  all_goals split
  all_goals try exact ⟨valid, shell_refl _⟩
  all_goals split
  all_goals try exact ⟨valid, shell_refl _⟩
  all_goals try split
  all_goals simp_all only [Frames, Root, Shell, fits_liftP, Expr.mkBVar, Expr.mkApp,
    Expr.mkLam, Expr.mkForallE, Expr.mkLetE, Expr.mkProj, Expr.mkMData, Id.run,
    Ix.Cert.Canon.idBind, and_true, implies_true]

theorem lowerP (e : Expr) (n cutoff : Nat) (valid : Frames e) :
    Frames (TotalSpec.lowerP e n cutoff) ∧ Shell e (TotalSpec.lowerP e n cutoff) := by
  induction e generalizing cutoff
  all_goals rw [TotalSpec.lowerP]
  all_goals split
  all_goals try exact ⟨valid, shell_refl _⟩
  all_goals split
  all_goals try exact ⟨valid, shell_refl _⟩
  all_goals try split
  all_goals simp_all only [Frames, Root, Shell, fits_lowerP, Expr.mkBVar, Expr.mkApp,
    Expr.mkLam, Expr.mkForallE, Expr.mkLetE, Expr.mkProj, Expr.mkMData, Id.run,
    Ix.Cert.Canon.idBind, and_true, implies_true]

theorem fits_shell (kind : Ix.SemanticContract.Kind) (e out : Expr)
    (nonLam : kind ≠ .lam) (kept : Shell e out) (matched : fits kind e = true) :
    fits kind out = true := by
  cases kind <;> cases e <;> simp_all only [fits, Bool.false_eq_true]
  all_goals cases out <;> simp_all [Shell]

theorem mdata_root_shell {data : Array (Name × Ix.DataValue)} {e out : Expr} {digest : Address}
    (valid : Root (.mdata data e digest)) (kept : Shell e out) (nonLam : fits .lam e = false) :
    Root (Expr.mkMData data out) := by
  intro present
  obtain ⟨contract, decoded, matched⟩ := valid present
  refine ⟨contract, decoded, fits_shell contract.kind e out ?_ kept matched⟩
  intro same
  rw [same, nonLam] at matched
  cases matched

private theorem fits_levels_go (kind : Ix.SemanticContract.Kind) (params : Array Name)
    (levels : Array Level) (e : Expr) :
    fits kind (substLevels.go params levels e) = fits kind e := by
  cases kind <;> cases e <;> rfl

private theorem levels_go (params : Array Name) (levels : Array Level) (e : Expr)
    (valid : Frames e) : Frames (substLevels.go params levels e) ∧ Shell e (substLevels.go params levels e) := by
  induction e
  all_goals simp_all only [substLevels.go, Frames, Root, Shell, fits_levels_go,
    Expr.mkSort, Expr.mkConst, Expr.mkApp, Expr.mkLam, Expr.mkForallE, Expr.mkLetE,
    Expr.mkProj, Expr.mkMData, Id.run, Ix.Cert.Canon.idBind, and_true, implies_true]

theorem substLevels (params : Array Name) (levels : Array Level) (e : Expr) (valid : Frames e) :
    Frames (Ix.Compile.Canon.substLevels params levels e) ∧ Shell e (Ix.Compile.Canon.substLevels params levels e) := by
  unfold Ix.Compile.Canon.substLevels
  split
  · exact ⟨valid, shell_refl _⟩
  · exact levels_go params levels e valid

private theorem fits_abstract_go (kind : Ix.SemanticContract.Kind) (xs : Array Name)
    (e : Expr) (depth : Nat) : fits kind (Ix.Compile.Image.abstractFVars.go xs e depth) = fits kind e := by
  cases kind <;> cases e
  all_goals simp only [Ix.Compile.Image.abstractFVars.go]
  all_goals try split
  all_goals rfl

private theorem abstract_go (xs : Array Name) (e : Expr) (depth : Nat) (valid : Frames e) :
    Frames (Ix.Compile.Image.abstractFVars.go xs e depth) ∧ Shell e (Ix.Compile.Image.abstractFVars.go xs e depth) := by
  induction e generalizing depth
  all_goals simp only [Ix.Compile.Image.abstractFVars.go]
  all_goals try split
  all_goals simp_all only [Frames, Root, Shell, fits_abstract_go, Expr.mkBVar, Expr.mkApp,
    Expr.mkLam, Expr.mkForallE, Expr.mkLetE, Expr.mkProj, Expr.mkMData, Id.run,
    Ix.Cert.Canon.idBind, and_true, implies_true]

theorem abstractFVars (xs : Array Name) (e : Expr) (valid : Frames e) :
    Frames (Ix.Compile.Image.abstractFVars xs e) ∧ Shell e (Ix.Compile.Image.abstractFVars xs e) := by
  unfold Ix.Compile.Image.abstractFVars
  split
  · exact ⟨valid, shell_refl _⟩
  · exact abstract_go xs e 0 valid

theorem liftM (e : Expr) (n cutoff : Nat) (valid : Frames e)
    {before after : DevState} {out : Expr}
    (run : (Ix.Compile.Image.liftM e n cutoff).run before = .ok (out, after)) : Frames out ∧ Shell e out := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (TotalMemo.liftGo hash hash e n cutoff ⟨before.range, before.lifted, before.nodes⟩).value = out at result
  rw [TotalMemo.liftGo_result] at result
  rw [← result]
  exact liftP e n cutoff valid

theorem lowerM (e : Expr) (n cutoff : Nat) (valid : Frames e)
    {before after : DevState} {out : Expr}
    (run : (Ix.Compile.Image.lowerM e n cutoff).run before = .ok (out, after)) : Frames out ∧ Shell e out := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (TotalMemo.lowerGo hash hash e n cutoff ⟨before.range, before.lowered, before.nodes⟩).value = out at result
  rw [TotalMemo.lowerGo_result] at result
  rw [← result]
  exact lowerP e n cutoff valid

theorem share_eq (e : Expr) {before after : DevState} {out : Expr}
    (run : (share e).run before = .ok (out, after)) : out = e := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (TotalMemo.share e before.nodes).value = out at result
  rw [(TotalMemo.share e before.nodes).correct] at result
  exact result.symm

theorem shareInput_eq (e : Expr) {before after : DevState} {out : Expr}
    (run : (shareInput e).run before = .ok (out, after)) : out = e := by
  unfold shareInput at run
  dsimp only [StateT.run] at run
  cases found : before.nodes.get? (hash e)
  · simp only [found] at run
    exact (congrArg Prod.fst (Except.ok.inj run)).symm
  · rename_i node
    simp only [found] at run
    split at run
    · have same := (RawExact.exprEq_eq_true node e).mp (by assumption)
      exact (congrArg Prod.fst (Except.ok.inj run)).symm.trans same
    · exact (congrArg Prod.fst (Except.ok.inj run)).symm

end Ix.CompileCert.FramePrimitives
