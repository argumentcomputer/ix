import Ix.Tc.Verify.Check.PreTranslationIngress

/-!
# Standalone declaration ingress

This module packages the expression-level raw-to-`PreTrKExprS` theorem at the
declaration boundary.  `StandaloneScope` is exactly the syntax and arithmetic
certificate that the production `validateConstWellScoped` proof must return
for axioms and definitions.  `PreDeclRel` is the untyped declaration relation
consumed by the two `checkConstMember` pipelines.

Neither relation contains a typing judgment or a declaration-WF premise.
-/

namespace Ix.Tc

open Lean4Lean (VDecl VExpr)

/-- Successful standalone validation facts, including the no-wrap budget
needed to interpret the validator's `UInt64` binder depth. -/
inductive StandaloneScope : KConst .anon -> Prop
  | axiom
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {isUnsafe : Bool} {levels : UInt64} {type : KExpr .anon} :
    type.Scoped 0 levels.toNat ->
    type.size < UInt64.size ->
    StandaloneScope (.axio name levelParams isUnsafe levels type)
  | defn
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {levels : UInt64}
      {type value : KExpr .anon}
      {leanAll : Mode.anon.F (Array (KId .anon))} {block : KId .anon} :
    type.Scoped 0 levels.toNat ->
    type.size < UInt64.size ->
    value.Scoped 0 levels.toNat ->
    value.size < UInt64.size ->
    StandaloneScope
      (.defn name levelParams kind safety hints levels type value leanAll block)

/-- Raw standalone correspondence after scoping validation, but before any
typing has been established. -/
inductive PreDeclRel (env : Lean4Lean.VEnv)
    (nameOf : Address -> Option Lean.Name) (trProj : RawProjRel)
    (id : KId .anon) : KConst .anon -> VDecl -> Prop
  | axiom
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {isUnsafe : Bool} {levels : UInt64} {type : KExpr .anon}
      {theoryName : Lean.Name} {typeV : VExpr} :
    nameOf id.addr = some theoryName ->
    PreTrKExprS env levels.toNat nameOf trProj [] type typeV ->
    PreDeclRel env nameOf trProj id
      (.axio name levelParams isUnsafe levels type)
      (.axiom { name := theoryName, uvars := levels.toNat, type := typeV })
  | defn
      {name : Mode.anon.F Name} {levelParams : Mode.anon.F (Array Name)}
      {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
      {hints : Lean.ReducibilityHints} {levels : UInt64}
      {type value : KExpr .anon}
      {leanAll : Mode.anon.F (Array (KId .anon))} {block : KId .anon}
      {theoryName : Lean.Name} {typeV valueV : VExpr} {decl : VDecl} :
    nameOf id.addr = some theoryName ->
    PreTrKExprS env levels.toNat nameOf trProj [] type typeV ->
    PreTrKExprS env levels.toNat nameOf trProj [] value valueV ->
    RawDefKindRel
      { name := theoryName, uvars := levels.toNat,
        type := typeV, value := valueV } kind decl ->
    PreDeclRel env nameOf trProj id
      (.defn name levelParams kind safety hints levels type value leanAll block)
      decl

namespace RawDeclRel

/-- The exact raw declaration becomes a pre-translation declaration once the
production validator's standalone certificate is available. -/
theorem toPre_of_scope
    {env : Lean4Lean.VEnv} {nameOf : Address -> Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon}
    (hprojection : trProj.SubstCompatible)
    (hliterals : forall literal, env.ContainsLits literal)
    {concrete : KConst .anon} {decl : VDecl}
    (hraw : RawDeclRel env nameOf trProj id concrete decl)
    (hscope : StandaloneScope concrete) :
    PreDeclRel env nameOf trProj id concrete decl := by
  cases hraw with
  | «axiom» hname htype =>
      cases hscope with
      | «axiom» hscoped hbound =>
          exact .axiom hname
            (htype.toPre_of_scoped hprojection hliterals hscoped hbound)
  | defn hname htype hvalue hkind =>
      cases hscope with
      | defn htypeScoped htypeBound hvalueScoped hvalueBound =>
          exact .defn hname
            (htype.toPre_of_scoped hprojection hliterals
              htypeScoped htypeBound)
            (hvalue.toPre_of_scoped hprojection hliterals
              hvalueScoped hvalueBound)
            hkind

end RawDeclRel

namespace PendingDecl

/-- A pending standalone target plus validator evidence reaches the exact
pre-translation declaration without assuming semantic acceptance. -/
theorem toPre_of_scope
    {trProj : RawProjRel} {world : VerifyWorld} {id : KId .anon}
    {decl : VDecl}
    (hprojection : trProj.SubstCompatible)
    (hliterals : forall literal, world.venv.ContainsLits literal)
    (hpending : PendingDecl trProj world id decl)
    {concrete : KConst .anon}
    (hcatalog : world.catalog id = some concrete)
    (hscope : StandaloneScope concrete) :
    PreDeclRel world.venv world.nameOf trProj id concrete decl := by
  obtain ⟨pendingConcrete, hpendingCatalog, hraw, _⟩ := hpending
  rw [hcatalog] at hpendingCatalog
  cases hpendingCatalog
  exact hraw.toPre_of_scope hprojection hliterals hscope

end PendingDecl

end Ix.Tc
