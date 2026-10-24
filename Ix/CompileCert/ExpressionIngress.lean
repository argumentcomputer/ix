import Ix.CompileCert.ExpressionState

/-! # The source relation is Source mode's reading

`Related names levels source target` was written case for case after
Source mode's term conversion `Ix.LeanIngress.ingressExpr`. This file states
that correspondence (CT-READING-PLAN §5.1, Q1): a source related to a reader
term converts, under any numbering `σ`, to a Source term that agrees with
the reader's term constructor for constructor (`Matches`), up to the keys
(a Source key is the ingress key of a name `names` relates to the reader's
key) and up to the levels (the ingress reading of a level is related to the
reader's level, `related_ingress`). With the compiler's level meaning, two
agreeing levels have the same value under every aligned pair of valuations
(`related_ingress_value`). The ingress keeps Lean's levels as they are, so
this is agreement by value at levels; a syntactic agreement needs the
ingress to canonicalize universes (CT-READING-PLAN §5.1, Q1). -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (CName CExpr)

/-- Source mode's term and the certified reader's term agree constructor for
constructor, up to `keys` at constants and projections and `levels` at
levels. Binder and let metadata, literals and indices are equal. -/
inductive Matches {md : Mode} (keys : Ix.Kernel.Key .source → CName md → Prop)
    (levels : Kernel.Level → Kernel.Level → Prop) : Ix.Kernel.Expr .source → CExpr md → Prop where
  | bvar (index : Nat) : Matches keys levels (.bvar index) (.bvar index)
  | sort {source target : Kernel.Level} (level : levels source target) :
      Matches keys levels (.sort source) (.sort target)
  | const {key : Ix.Kernel.Key .source} {key' : CName md} {sources targets : List Kernel.Level}
      (mapped : keys key key') (universes : List.Forall₂ levels sources targets) :
      Matches keys levels (.const key sources) (.const key' targets)
  | app {fn arg : Ix.Kernel.Expr .source} {fn' arg' : CExpr md}
      (fnMatch : Matches keys levels fn fn') (argMatch : Matches keys levels arg arg') :
      Matches keys levels (.app fn arg) (.app fn' arg')
  | lam {type body : Ix.Kernel.Expr .source} {type' body' : CExpr md} (m : Ix.Kernel.BinderMeta)
      (typeMatch : Matches keys levels type type') (bodyMatch : Matches keys levels body body') :
      Matches keys levels (.lam type body m) (.lam type' body' m)
  | forallE {type body : Ix.Kernel.Expr .source} {type' body' : CExpr md} (m : Ix.Kernel.BinderMeta)
      (typeMatch : Matches keys levels type type') (bodyMatch : Matches keys levels body body') :
      Matches keys levels (.forallE type body m) (.forallE type' body' m)
  | letE {type value body : Ix.Kernel.Expr .source} {type' value' body' : CExpr md}
      (l : Ix.Kernel.LetMeta) (typeMatch : Matches keys levels type type')
      (valueMatch : Matches keys levels value value') (bodyMatch : Matches keys levels body body') :
      Matches keys levels (.letE type value body l) (.letE type' value' body' l)
  | lit (literal : Ix.Kernel.Literal) : Matches keys levels (.lit literal) (.lit literal)
  | proj {key : Ix.Kernel.Key .source} {key' : CName md} {value : Ix.Kernel.Expr .source}
      {value' : CExpr md} (index : Nat) (mapped : keys key key') (valueMatch : Matches keys levels value value') :
      Matches keys levels (.proj key index value) (.proj key' index value')

section Ingress

variable {md : Mode} {keys : Ix.Kernel.Key .source → CName md → Prop}
  {levels : Kernel.Level → Kernel.Level → Prop}

/-- A contract frame on agreeing terms agrees: the ingress's
`Ix.LeanIngress.withContract` and the reader side's `withContract` put the
contract on the same binder. -/
theorem withContract_matches {c : Ix.SemanticContract.Contract} {e : Ix.Expr}
    {source : Ix.Kernel.Expr .source} {target result : CExpr md}
    (lowered : withContract c e target = some result) (agree : Matches keys levels source target) :
    ∃ source', Ix.LeanIngress.withContract c e source = .ok source' ∧ Matches keys levels source' result := by
  obtain ⟨kind, binder, valueContract, letKind⟩ := c
  cases kind <;> cases e <;> cases agree <;>
    simp only [withContract, Option.some.injEq, reduceCtorEq] at lowered
  all_goals
    subst lowered
    exact ⟨_, rfl, by constructor <;> assumption⟩

end Ingress

/-- Related universe arguments convert to agreeing levels. -/
theorem levels_ingress {levels : Ix.Level → Kernel.Level → Prop}
    {levelRel : Kernel.Level → Kernel.Level → Prop} (σ : Ix.Name → LevelParam)
    (levelsIngress : ∀ source level, levels source level →
      ∃ target, Ix.LeanIngress.ingressLevel σ source = .ok target ∧ levelRel target level)
    {sources : List Ix.Level} {targets : List Kernel.Level} (related : List.Forall₂ levels sources targets) :
    ∃ converted, sources.mapM (Ix.LeanIngress.ingressLevel σ) = .ok converted ∧
      List.Forall₂ levelRel converted targets := by
  induction related with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons head _ ih =>
    obtain ⟨level, converted, agree⟩ := levelsIngress _ _ head
    obtain ⟨rest, convertedRest, agreeRest⟩ := ih
    refine ⟨level :: rest, ?_, .cons agree agreeRest⟩
    rw [List.mapM_cons, converted, convertedRest]
    rfl

/-- **The source relation is Source mode's reading.** A source related to a
reader term converts, under the numbering `σ`, to a Source term that agrees
with the reader's term, up to keys related through `names` and levels whose
ingress readings are related to the reader's. -/
theorem related_ingress {md : Mode} {names : Ix.Name → CName md → Prop}
    {levels : Ix.Level → Kernel.Level → Prop} {levelRel : Kernel.Level → Kernel.Level → Prop}
    (σ : Ix.Name → LevelParam)
    (levelsIngress : ∀ source level, levels source level →
      ∃ target, Ix.LeanIngress.ingressLevel σ source = .ok target ∧ levelRel target level)
    {source : Ix.Expr} {target : CExpr md} (related : Related names levels source target) :
    ∃ converted, Ix.LeanIngress.ingressExpr σ source = .ok converted ∧
      Matches (fun key key' => ∃ name, key = Ix.LeanIngress.ingressKey name ∧ names name key') levelRel
        converted target := by
  induction related with
  | bvar index hash =>
    refine ⟨_, rfl, ?_⟩
    rw [Ix.Kernel.Expr.mkBvar_eq, Ix.Kernel.Expr.mkBvar_eq]
    exact .bvar index
  | sort hash meaning =>
    obtain ⟨level, converted, agree⟩ := levelsIngress _ _ meaning
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, converted]; rfl, .sort agree⟩
  | const hash sources targets mapped universes =>
    obtain ⟨converted, ok, agree⟩ := levels_ingress σ levelsIngress universes
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, ok]; rfl, .const ⟨_, rfl, mapped⟩ agree⟩
  | app hash _ _ fnIH argIH =>
    obtain ⟨fn, fnOk, fnMatch⟩ := fnIH
    obtain ⟨arg, argOk, argMatch⟩ := argIH
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, fnOk, argOk]; rfl, .app fnMatch argMatch⟩
  | lam name info hash _ _ typeIH bodyIH =>
    obtain ⟨type, typeOk, typeMatch⟩ := typeIH
    obtain ⟨body, bodyOk, bodyMatch⟩ := bodyIH
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, typeOk, bodyOk]; rfl, .lam _ typeMatch bodyMatch⟩
  | all name info hash _ _ typeIH bodyIH =>
    obtain ⟨type, typeOk, typeMatch⟩ := typeIH
    obtain ⟨body, bodyOk, bodyMatch⟩ := bodyIH
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, typeOk, bodyOk]; rfl, .forallE _ typeMatch bodyMatch⟩
  | letE name nonDep hash _ _ _ typeIH valueIH bodyIH =>
    obtain ⟨type, typeOk, typeMatch⟩ := typeIH
    obtain ⟨value, valueOk, valueMatch⟩ := valueIH
    obtain ⟨body, bodyOk, bodyMatch⟩ := bodyIH
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, typeOk, valueOk, bodyOk]; rfl,
      .letE _ typeMatch valueMatch bodyMatch⟩
  | nat value hash => exact ⟨_, rfl, .lit _⟩
  | str value hash => exact ⟨_, rfl, .lit _⟩
  | proj field hash mapped _ valueIH =>
    obtain ⟨value, valueOk, valueMatch⟩ := valueIH
    exact ⟨_, by rw [Ix.LeanIngress.ingressExpr, valueOk]; rfl, .proj field ⟨_, rfl, mapped⟩ valueMatch⟩
  | mdata data hash plain _ bodyIH =>
    obtain ⟨body, bodyOk, bodyMatch⟩ := bodyIH
    exact ⟨body, by rw [Ix.LeanIngress.ingressExpr_mdata_plain σ _ hash plain, bodyOk], bodyMatch⟩
  | contract data hash c frame read _ lowered bodyIH =>
    obtain ⟨body, bodyOk, bodyMatch⟩ := bodyIH
    obtain ⟨framed, framedOk, framedMatch⟩ := withContract_matches lowered bodyMatch
    refine ⟨framed, ?_, framedMatch⟩
    rw [Ix.LeanIngress.ingressExpr_mdata, Ix.LeanIngress.ingressMData]
    simp only [frame, ↓reduceIte]
    rw [bodyOk, read]
    exact framedOk

/-- **With the compiler's level meaning**: the Source term and the reader's
term agree at constants through `names`, and agree at every level by value,
under every pair of valuations aligned at the slots `nameIndex` gives. -/
theorem related_ingress_value {md : Mode} {names : Ix.Name → CName md → Prop}
    {params : List Ix.Name} {σ : Ix.Name → LevelParam} {param : Nat → LevelParam}
    {source : Ix.Expr} {target : CExpr md}
    (related : Related names (LevelMeaning params σ param) source target) :
    ∃ converted, Ix.LeanIngress.ingressExpr σ source = .ok converted ∧
      Matches (fun key key' => ∃ name, key = Ix.LeanIngress.ingressKey name ∧ names name key')
        (fun level level' => ∀ φ ψ : LevelParam → Nat,
          (∀ name index, Ix.Compile.ExactKey.nameIndex name params = some index →
            φ (σ name) = ψ (param index)) →
          Kernel.Level.eval φ level = Kernel.Level.eval ψ level')
        converted target :=
  related_ingress σ (fun _ _ meaning => meaning.value) related

end Ix.CompileCert.ExpressionState
