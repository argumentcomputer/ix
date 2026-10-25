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

/-- The actual returned constant's type and optional value, including the
existing unsupported-kind refusals. No value is invented for an axiom. -/
theorem decorate_constant (contract : ResolvedSourceContract) {out : Lean.ConstantInfo}
    (run : contract.decorate = .ok out) (cache : Ix.CanonM.CanonState) :
    let ci := (Id.run ((Ix.CanonM.canonConst out).run cache)).1
    ContractArity ci.getCnst.type ∧
      ∀ value, Ix.LeanIngress.definitionValue ci = some value → ContractArity value := by
  rw [canonConst_run]
  unfold ResolvedSourceContract.decorate at run
  obtain ⟨type, typeRun, rest⟩ := Loop.except_bind_ok.mp run
  have ht := canonical type (decorated contract .type [] contract.source.type typeRun)
  cases source : contract.source <;> simp only [source] at rest
  case quotInfo => cases rest
  case inductInfo => cases rest
  case ctorInfo => cases rest
  case recInfo => cases rest
  case axiomInfo info =>
    cases Except.ok.inj rest
    exact ⟨ht, by intro value absent; cases absent⟩
  all_goals
    obtain ⟨value, valueRun, returned⟩ := Loop.except_bind_ok.mp rest
    cases Except.ok.inj returned
    refine ⟨ht, ?_⟩
    intro result found
    cases Option.some.inj found
    exact canonical value (decorated contract .body [] _ valueRun)

private theorem read_size {data : Array (Ix.Name × Ix.DataValue)} {c : Contract}
    (run : Ix.SemanticContract.read data = .ok c) : data.size = 3 := by
  by_contra wrong
  simp [Ix.SemanticContract.read, wrong] at run
  cases run

/-- Successful structural Source ingress supplies the arity fact for the
SAME expression, not an original body standing in for a rewritten one. -/
theorem ingress (σ : Ix.Name → Ix.Kernel.LevelParam) (e : Ix.Expr)
    {converted : Ix.Kernel.Expr .source}
    (run : Ix.LeanIngress.ingressExpr σ e = .ok converted) : ContractArity e := by
  induction e generalizing converted
  all_goals try exact True.intro
  all_goals rw [Ix.LeanIngress.ingressExpr] at run
  case app f a hash hf ha =>
    obtain ⟨f', rf, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨a', ra, _⟩ := Loop.except_bind_ok.mp tail
    exact ⟨hf rf, ha ra⟩
  case lam n t b bi hash ht hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨b', rb, _⟩ := Loop.except_bind_ok.mp tail
    exact ⟨ht rt, hb rb⟩
  case forallE n t b bi hash ht hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨b', rb, _⟩ := Loop.except_bind_ok.mp tail
    exact ⟨ht rt, hb rb⟩
  case letE n t v b nd hash ht hv hb =>
    obtain ⟨t', rt, tail⟩ := Loop.except_bind_ok.mp run
    obtain ⟨v', rv, tail⟩ := Loop.except_bind_ok.mp tail
    obtain ⟨b', rb, _⟩ := Loop.except_bind_ok.mp tail
    exact ⟨ht rt, hv rv, hb rb⟩
  case proj n i e hash ih =>
    obtain ⟨e', re, _⟩ := Loop.except_bind_ok.mp run
    exact ih re
  case mdata data e hash ih =>
    unfold Ix.LeanIngress.ingressMData at run
    by_cases frame : hasMetadata data = true
    · simp only [frame, ↓reduceIte] at run
      obtain ⟨c, readRun, tail⟩ := Loop.except_bind_ok.mp run
      have decoded : Ix.SemanticContract.read data = .ok c := by
        cases h : Ix.SemanticContract.read data with
        | error why => simp only [h, Except.mapError] at readRun; cases readRun
        | ok value =>
          have same : value = c := by simpa only [h, Except.mapError, Except.ok.injEq] using readRun
          exact congrArg Except.ok same
      obtain ⟨e', re, _⟩ := Loop.except_bind_ok.mp tail
      exact ⟨fun _ => read_size decoded, ih re⟩
    · simp only [frame] at run
      exact ⟨fun present => False.elim (frame present), ih run⟩

/-- The actual canonical output is tied to the successful direct Lean
source reading and its numbering by the existing CanonM correspondence. -/
theorem canonical_ingress (σ : Ix.Name → Ix.Kernel.LevelParam) (e : Lean.Expr)
    {converted : Ix.Kernel.Expr .source} (run : leanExpr (σ ∘ nameS) e = .ok converted)
    (cache : Ix.CanonM.CanonState) :
    ContractArity (Id.run ((Ix.CanonM.canonExpr e).run cache)).1 := by
  apply ingress σ
  rw [ingressExpr_canonExpr]
  exact run

end Ix.CompileCert.RecordSourceShape
