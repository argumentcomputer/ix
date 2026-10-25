import Ix.Cert.Canon
import Ix.Compile.SourceContract.Transport
import Ix.CompileCert.Loop

/-! Source-produced semantic-frame arity. This is not contract validity,
typing, acceptance, or provenance for a different post-rewrite expression. -/
namespace Ix.CompileCert.RecordSourceShape
open Ix.Compile Ix.SemanticContract Ix.Cert.Canon

def ContractArity : Ix.Expr → Prop
  | .app f a _ => ContractArity f ∧ ContractArity a
  | .lam _ t b _ _ | .forallE _ t b _ _ => ContractArity t ∧ ContractArity b
  | .letE _ t v b _ _ => ContractArity t ∧ ContractArity v ∧ ContractArity b
  | .proj _ _ e _ => ContractArity e
  | .mdata data e _ => (hasMetadata data = true → data.size = 3) ∧ ContractArity e
  | _ => True

private def LeanArity : Lean.Expr → Prop
  | .app f a => LeanArity f ∧ LeanArity a
  | .lam _ t b _ | .forallE _ t b _ => LeanArity t ∧ LeanArity b
  | .letE _ t v b _ => LeanArity t ∧ LeanArity v ∧ LeanArity b
  | .proj _ _ e => LeanArity e
  | .mdata data e => (hasContractLean data = true → data.entries.length = 3) ∧ LeanArity e
  | _ => True

private theorem canonical (e : Lean.Expr) (h : LeanArity e) : ContractArity (exprS e) := by
  induction e
  case mdata data e ih =>
    change (hasMetadata (mdataS data) = true → (mdataS data).size = 3) ∧ ContractArity (exprS e)
    refine ⟨?_, ih h.2⟩
    rw [hasMetadata_mdataS]
    simpa only [mdataS, List.size_toArray, List.length_map] using h.1
  all_goals try cases ‹Lean.Literal›
  all_goals simp_all only [LeanArity, exprS, Ix.Expr.mkBVar, Ix.Expr.mkFVar, Ix.Expr.mkMVar,
    Ix.Expr.mkSort, Ix.Expr.mkConst, Ix.Expr.mkApp, Ix.Expr.mkLam, Ix.Expr.mkForallE,
    Ix.Expr.mkLetE, Ix.Expr.mkLit, Ix.Expr.mkProj, Id.run, idBind,
    ContractArity, true_and]

private theorem metadata_size (c : Contract) : c.metadata.entries.length = 3 := rfl
private theorem attached (c : Contract) (e : Lean.Expr) (h : LeanArity e) :
    LeanArity (c.attach e) := ⟨fun _ => metadata_size c, h⟩

private theorem filtered_plain (data : Lean.MData) (allowed : (leanFields data).isEmpty = true) :
    hasContractLean ⟨data.entries.filter fun (key, _) => !sourceAnnotationKey.isPrefixOf key⟩ = false := by
  have empty : leanFields data = [] := List.isEmpty_iff.mp allowed
  apply List.any_eq_false.mpr
  intro p member
  have original := (List.mem_filter.mp member).1
  have absent : ¬p ∈ leanFields data := by rw [empty]; simp
  simp only [leanFields, List.mem_filter, original, true_and] at absent
  exact absent

-- The actual decorator's generated selector retains its module boundary.
private theorem finish (selected : Option ResolvedBinderContract) {value out : Lean.Expr}
    (h : LeanArity value)
    (run : decorateExpr.match_5 (fun _ => Except String Lean.Expr) selected
      (fun _ => Except.ok value)
      (fun binder => Except.ok (if binder.semantic.isOrdinary then value else binder.semantic.attach value)) =
      (Except.ok out : Except String Lean.Expr)) : LeanArity out := by
  cases selected with
  | none => cases Except.ok.inj run; exact h
  | some binder =>
    cases ordinary : binder.semantic.isOrdinary
    · cases (show binder.semantic.attach value = out by simpa [ordinary] using run)
      exact attached _ _ h
    · cases (show value = out by simpa [ordinary] using run)
      exact h

private theorem decorated (contract : ResolvedSourceContract) (root : SourceRoot)
    (path : List SourceStep) (e : Lean.Expr) {out : Lean.Expr}
    (run : decorateExpr contract root path e = .ok out) : LeanArity out := by
  induction e generalizing path out
  all_goals rw [decorateExpr] at run
  case bvar i =>
    exact finish _ (value := .bvar i) trivial (by simpa only [pure, Except.pure, bind, Except.bind] using run)
  case sort u =>
    exact finish _ (value := .sort u) trivial (by simpa only [pure, Except.pure, bind, Except.bind] using run)
  case const n us =>
    exact finish _ (value := .const n us) trivial (by simpa only [pure, Except.pure, bind, Except.bind] using run)
  case lit l =>
    exact finish _ (value := .lit l) trivial (by simpa only [pure, Except.pure, bind, Except.bind] using run)
  case fvar => cases run
  case mvar => cases run
  case app f a hf ha =>
    obtain ⟨f', rf, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨a', ra, tail⟩ := Loop.except_bind_ok.mp tail
    exact finish _ (value := .app f' a') ⟨hf _ rf, ha _ ra⟩
      (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
  case lam n t b bi ht hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨b', rb, tail⟩ := Loop.except_bind_ok.mp tail
    exact finish _ (value := .lam n t' b' bi) ⟨ht _ rt, hb _ rb⟩
      (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
  case forallE n t b bi ht hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨b', rb, tail⟩ := Loop.except_bind_ok.mp tail
    exact finish _ (value := .forallE n t' b' bi) ⟨ht _ rt, hb _ rb⟩
      (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
  case letE n t v b nd ht hv hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨v', rv, tail⟩ := Loop.except_bind_ok.mp tail
    obtain ⟨b', rb, tail⟩ := Loop.except_bind_ok.mp tail
    exact finish _ (value := .letE n t' v' b' nd) ⟨ht _ rt, hv _ rv, hb _ rb⟩
      (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
  case proj n i e ih =>
    obtain ⟨e', re, tail⟩ := Loop.except_bind_ok.mp run
    exact finish _ (value := .proj n i e') (ih _ (out := e') re)
      (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
  case mdata data e ih =>
    cases allowed : (leanFields data).isEmpty
    · simp [allowed] at run; cases run
    · simp only [allowed, ↓reduceIte] at run
      obtain ⟨e', re, tail⟩ := Loop.except_bind_ok.mp run
      let clean : Lean.MData := ⟨data.entries.filter fun (key, _) => !sourceAnnotationKey.isPrefixOf key⟩
      apply finish _ (value := if clean.entries.isEmpty then e' else .mdata clean e') ?_
        (by simpa only [pure, Except.pure, bind, Except.bind] using tail)
      split
      · exact ih _ re
      · exact ⟨fun present => by rw [filtered_plain data allowed] at present; contradiction, ih _ re⟩

/-- Actual decorator and canonicalizer runs supply the narrow arity fact;
no input-tree, cache, hash or metadata-presence premise is required. -/
theorem decorateExpr_canonical (contract : ResolvedSourceContract) (root : SourceRoot)
    (path : List SourceStep) (e : Lean.Expr) {out : Lean.Expr}
    (run : decorateExpr contract root path e = .ok out) (cache : Ix.CanonM.CanonState) :
    ContractArity (Id.run ((Ix.CanonM.canonExpr out).run cache)).1 := by
  rw [canonExpr_run]
  exact canonical out (decorated contract root path e run)

end Ix.CompileCert.RecordSourceShape
