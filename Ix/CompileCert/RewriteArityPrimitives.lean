import Ix.CompileCert.RecordSourceShape
import Ix.Compile.Image.Develop

/-! Arity through actual rewrite primitives. These results do not supply
arbitrary hinst/RwState results, callbacks, images or clique outputs. -/
namespace Ix.CompileCert.RewriteArityPrimitives
open Ix (Expr Name Level)
open Ix.CompileCert.RecordSourceShape

private theorem levels_go (params : Array Name) (levels : Array Level) (e : Expr)
    (h : ContractArity e) : ContractArity (Ix.Compile.Canon.substLevels.go params levels e) := by
  induction e
  all_goals simp_all only [Ix.Compile.Canon.substLevels.go, ContractArity, Expr.mkSort,
    Expr.mkConst, Expr.mkApp, Expr.mkLam, Expr.mkForallE, Expr.mkLetE, Expr.mkProj,
    Expr.mkMData, Id.run, Ix.Cert.Canon.idBind, and_true, implies_true]

theorem substLevels (params : Array Name) (levels : Array Level) (e : Expr)
    (h : ContractArity e) : ContractArity (Ix.Compile.Canon.substLevels params levels e) := by
  unfold Ix.Compile.Canon.substLevels
  split
  · exact h
  · exact levels_go params levels e h

theorem liftP (e : Expr) (n cutoff : Nat) (h : ContractArity e) :
    ContractArity (Ix.Compile.Image.TotalSpec.liftP e n cutoff) := by
  induction e generalizing cutoff
  all_goals rw [Ix.Compile.Image.TotalSpec.liftP]
  all_goals split
  all_goals try exact h
  all_goals split
  all_goals try exact h
  all_goals try split
  all_goals simp_all only [ContractArity, Expr.mkBVar, Expr.mkApp, Expr.mkLam,
    Expr.mkForallE, Expr.mkLetE, Expr.mkProj, Expr.mkMData, Id.run, Ix.Cert.Canon.idBind,
    and_true, implies_true]

theorem lowerP (e : Expr) (n cutoff : Nat) (h : ContractArity e) :
    ContractArity (Ix.Compile.Image.TotalSpec.lowerP e n cutoff) := by
  induction e generalizing cutoff
  all_goals rw [Ix.Compile.Image.TotalSpec.lowerP]
  all_goals split
  all_goals try exact h
  all_goals split
  all_goals try exact h
  all_goals try split
  all_goals simp_all only [ContractArity, Expr.mkBVar, Expr.mkApp, Expr.mkLam,
    Expr.mkForallE, Expr.mkLetE, Expr.mkProj, Expr.mkMData, Id.run, Ix.Cert.Canon.idBind,
    and_true, implies_true]

/-- The actual certified helper result, including arbitrary carried tables. -/
theorem liftM (e : Expr) (n cutoff : Nat) (h : ContractArity e)
    {before after : Ix.Compile.Image.DevState} {out : Expr}
    (run : (Ix.Compile.Image.liftM e n cutoff).run before = .ok (out, after)) : ContractArity out := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (Ix.Compile.Image.TotalMemo.liftGo hash hash e n cutoff
    ⟨before.range, before.lifted, before.nodes⟩).value = out at result
  rw [Ix.Compile.Image.TotalMemo.liftGo_result] at result
  rw [← result]
  exact liftP e n cutoff h

theorem lowerM (e : Expr) (n cutoff : Nat) (h : ContractArity e)
    {before after : Ix.Compile.Image.DevState} {out : Expr}
    (run : (Ix.Compile.Image.lowerM e n cutoff).run before = .ok (out, after)) : ContractArity out := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (Ix.Compile.Image.TotalMemo.lowerGo hash hash e n cutoff
    ⟨before.range, before.lowered, before.nodes⟩).value = out at result
  rw [Ix.Compile.Image.TotalMemo.lowerGo_result] at result
  rw [← result]
  exact lowerP e n cutoff h

theorem share (e : Expr) (h : ContractArity e)
    {before after : Ix.Compile.Image.DevState} {out : Expr}
    (run : (Ix.Compile.Image.share e).run before = .ok (out, after)) : ContractArity out := by
  have result := congrArg Prod.fst (Except.ok.inj run)
  change (Ix.Compile.Image.TotalMemo.share e before.nodes).value = out at result
  rw [(Ix.Compile.Image.TotalMemo.share e before.nodes).correct] at result
  simpa only [← result] using h

theorem shareInput (e : Expr) (h : ContractArity e)
    {before after : Ix.Compile.Image.DevState} {out : Expr}
    (run : (Ix.Compile.Image.shareInput e).run before = .ok (out, after)) : ContractArity out := by
  unfold Ix.Compile.Image.shareInput at run
  dsimp only [StateT.run] at run
  cases found : before.nodes.get? (hash e)
  · simp only [found] at run
    cases (congrArg Prod.fst (Except.ok.inj run)); exact h
  · rename_i node
    simp only [found] at run
    split at run
    · have same := (Ix.Compile.Image.RawExact.exprEq_eq_true node e).mp (by assumption)
      cases (congrArg Prod.fst (Except.ok.inj run))
      simpa only [same] using h
    · cases (congrArg Prod.fst (Except.ok.inj run)); exact h

/-- An actual source producer supplies the input fact for the live universe
substitution primitive. This does not identify that input with another image. -/
theorem decorated_levels (contract : Ix.Compile.ResolvedSourceContract) (root : Ix.Compile.SourceRoot)
    (path : List Ix.Compile.SourceStep) (source : Lean.Expr) {decorated : Lean.Expr}
    (run : Ix.Compile.decorateExpr contract root path source = .ok decorated)
    (cache : Ix.CanonM.CanonState) (params : Array Name) (levels : Array Level) :
    ContractArity (Ix.Compile.Canon.substLevels params levels
      (Id.run ((Ix.CanonM.canonExpr decorated).run cache)).1) :=
  substLevels params levels _ (decorateExpr_canonical contract root path source run cache)

/-- The source-produced canonical expression through the actual cached shift. -/
theorem decorated_liftM (contract : Ix.Compile.ResolvedSourceContract) (root : Ix.Compile.SourceRoot)
    (path : List Ix.Compile.SourceStep) (source : Lean.Expr) {decorated : Lean.Expr}
    (run : Ix.Compile.decorateExpr contract root path source = .ok decorated)
    (cache : Ix.CanonM.CanonState) (n cutoff : Nat) {before after : Ix.Compile.Image.DevState} {out : Expr}
    (shift : (Ix.Compile.Image.liftM
      (Id.run ((Ix.CanonM.canonExpr decorated).run cache)).1 n cutoff).run before = .ok (out, after)) :
    ContractArity out :=
  liftM _ n cutoff (decorateExpr_canonical contract root path source run cache) shift

end Ix.CompileCert.RewriteArityPrimitives
